import ProofScript.Extension.Component.Core
import ProofScript.Computation.Json
import ProofScript.Computation.Registry
import ProofScript.Script.ExprJSON

open Lean
open Lean.Elab.Command (CommandElabM liftCoreM liftIO liftTermElabM)
open ProofScript.Extension


namespace ProofScript.Extension


/-- Stable description of the Lean declaration backing an interactive computation. -/
structure ComputationFunction where
  declaration : String
  type : String
  expression : Json
  implementation : Json
  expressions : Json
deriving Inhabited, ToJson

structure ComputationExecution where
  backend : String := "wasm"
  status : String := "pending"
  abi : String := "proof-script-json-v1"
  bundleId : String
  entry : String
  wrapper : String
  manifest : String
deriving Inhabited, ToJson

/--
Page-level contract for an interactive computation.

`payload` is interpreted by the named renderer. Proof-Script additionally exports a
structured Lean expression as provenance and an intermediate artifact; it is not a
browser execution ABI. Renderers should select an execution backend by `renderer`.
-/
structure ComputationComponent where
  schemaVersion : String := "1.1.0"
  metadata : ComponentMetadata
  renderer : String
  function : ComputationFunction
  execution : ComputationExecution
  payload : Json
deriving Inhabited, ToJson

private structure FunctionShape where
  input : Expr
  output : Expr
  errorMode : String

private def functionShape (stx : Syntax) (info : ConstantInfo) : CommandElabM FunctionShape :=
  liftTermElabM do
    unless info.levelParams.isEmpty do
      throwErrorAt stx "@computation does not yet support universe-polymorphic entry functions"
    let type ← Meta.whnf info.type
    let .forallE _ input result binderInfo := type
      | throwErrorAt stx "@computation requires a function with exactly one explicit argument"
    unless binderInfo == .default do
      throwErrorAt stx "@computation requires an explicit input argument"
    if result.hasLooseBVars then
      throwErrorAt stx "@computation does not support dependent output types"
    let result ← Meta.whnf result
    match result with
    | .forallE .. =>
        throwErrorAt stx "@computation requires a function with exactly one explicit argument"
    | _ => pure ()
    let (output, errorMode) ←
      match result with
      | .app (.app (.const ``Except _) errorType) output =>
          unless ← Meta.isDefEq errorType (.const ``String []) do
            throwErrorAt stx "@computation requires Except String as its error type"
          pure (output, "except")
      | output => pure (output, "pure")
    discard <| Meta.synthInstance (← Meta.mkAppM ``FromJson #[input])
    discard <| Meta.synthInstance (← Meta.mkAppM ``ToJson #[output])
    return { input, output, errorMode }

private def wrapperName (declaration : Name) : Name :=
  declaration.getPrefix ++ Name.str .anonymous s!"__proofScript_{declaration.getString!}"

private def addWrapper (declaration : Name) (shape : FunctionShape)
    : CommandElabM Name := do
  let name := wrapperName declaration
  let functionIdent := mkIdent declaration
  let term ← if shape.errorMode == "except" then
    `(fun input : String =>
        ProofScript.Computation.invokeJson $functionIdent input)
  else
    `(fun input : String =>
        ProofScript.Computation.invokeJson
          (fun request => Except.ok ($functionIdent request)) input)
  let wrapperType := .forallE `input (.const ``String []) (.const ``String []) .default
  let value ← liftTermElabM do
    let value ← Lean.Elab.Term.elabTerm term (some wrapperType)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  let env ← getEnv
  if env.contains name then
    let existing := env.constants.find! name
    let existingValue ← match existing with
      | .defnInfo info => pure info.value
      | .opaqueInfo info => pure info.value
      | _ => throwError s!"generated computation wrapper name '{name}' is already used"
    let compatible ← liftTermElabM do
      Meta.isDefEq existing.type wrapperType <&&> Meta.isDefEq existingValue value
    unless compatible do
      throwError s!"generated computation wrapper name '{name}' collides with an existing declaration"
  else
    liftCoreM <| addAndCompile <| .defnDecl {
      name
      levelParams := []
      type := wrapperType
      value
      hints := .opaque
      safety := .safe
    }
  return name

private def parseJsonAt (stx : Syntax) (source : String) : CommandElabM Json :=
  match Json.parse source with
  | .ok value => pure value
  | .error message => throwErrorAt stx s!"invalid @computation payload JSON: {message}"

private def resolveDeclaration (stx : Syntax) (name : Name) : CommandElabM Name := do
  let env ← getEnv
  let candidates := ((← getCurrNamespace) ++ name) :: (← getOpenDecls).filterMap fun
    | .simple ns _ => some (ns ++ name)
    | .explicit ns alias => if alias == name then some ns else none
  let candidates := candidates ++ [name]
  let some resolved := candidates.find? env.contains
    | throwErrorAt stx s!"unknown Lean declaration '{name}'"
  return resolved

private def addComputationComponent (metadataStx : Syntax)
                                    (rendererStx : TSyntax `str)
                                    (functionStx : TSyntax `ident)
                                    (payloadStx : TSyntax `str)
                                    : CommandElabM Unit := do
  let metadata ←  match parseComponentMetadata metadataStx with
                  | .ok metadata => pure metadata
                  | .error message => throwErrorAt metadataStx message
  let declaration ← resolveDeclaration functionStx.raw functionStx.getId
  let env ← getEnv
  let info := env.constants.find! declaration
  let implementation ← match info with
    | .defnInfo value => pure value.value
    | .opaqueInfo value => pure value.value
    | _ => throwErrorAt functionStx s!"@computation requires a definition with an implementation; '{declaration}' is not executable"
  liftIO ProofScript.resetExprJsonState
  let expression ← liftTermElabM do
    ProofScript.Expr2JSON (.const declaration [])
  let implementation ← liftTermElabM do
    ProofScript.Expr2JSON implementation
  let expressions ← liftIO ProofScript.getExprJsonTable
  let type ← liftTermElabM do
    return toString (← Meta.ppExpr info.type)
  let payload ← parseJsonAt payloadStx.raw payloadStx.getString
  let shape ← functionShape functionStx.raw info
  let wrapper ← addWrapper declaration shape
  let moduleName ← getMainModule
  let bundleId := moduleName.toString
  let location ← liftCoreM <| sourceLocation functionStx.raw
  let inputType ← liftTermElabM <| toString <$> Meta.ppExpr shape.input
  let outputType ← liftTermElabM <| toString <$> Meta.ppExpr shape.output
  let pending : ProofScript.Computation.PendingEntry := {
    bundleId
    entry := declaration.toString
    wrapper := wrapper.toString
    module := moduleName.toString
    functionType := { input := inputType, output := outputType, errorMode := shape.errorMode }
    source := location
  }
  let manifest ← liftIO <| ProofScript.Computation.writePendingEntry pending
  let labels := match metadata.label with
    | some label => #[(("figure" : ReferenceKind), label)]
    | none => #[]
  let value : ComputationComponent := {
    metadata
    renderer := rendererStx.getString
    function := { declaration := declaration.toString, type, expression, implementation, expressions }
    execution := {
      bundleId
      entry := declaration.toString
      wrapper := wrapper.toString
      manifest := manifest.toString
    }
    payload
  }
  addPageComponent functionStx.raw "computation" (toJson value) labels

/--
Adds an interactive computation backed by a Lean declaration.

The final JSON string is a renderer-specific, versioned manifest. Keeping execution
behind a named renderer avoids treating Lean compiler internals as a stable web ABI.
-/
elab "@""computation" "{" "metadata" " := " metadata:componentMeta ", "
  "renderer" " := " renderer:str ", " "function" " := " function:ident ", "
  "payload" " := " payload:str "}" : command =>
  addComputationComponent metadata.raw renderer function payload


end ProofScript.Extension
