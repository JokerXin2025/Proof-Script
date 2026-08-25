import ProofScript.References.State
import ProofScript.Extension.State

open Lean


namespace ProofScript


/-- 在当前位置加入页面 references 组件。 -/
syntax "#references" : command

private def referencesJson (refs : List Reference) : Json :=
  Json.arr <| refs.toArray.map fun reference =>
    Json.mkObj [
      ("name", Json.str reference.name.toString),
      ("info", toJson reference.info)
    ]

private def sourceLocation (stx : Syntax) : CoreM Extension.SourceLocation := do
  return {
    file := ← getFileName
    start := (stx.getPos?.getD 0).byteIdx
    stop := (stx.getTailPos?.getD (stx.getPos?.getD 0)).byteIdx
  }

open Lean.Elab.Command in
elab_rules : command
  | `(command| #references) => do
      let refs ← getTheoremRefs
      let refsJson := referencesJson refs
      let location ← liftCoreM <| sourceLocation (← getRef)
      let component : Extension.Component := {
        source := location
        data := .references refsJson
      }
      let (env, added) ← match Extension.addComponent (← getEnv) component with
        | .ok result => pure result
        | .error message => throwError message
      unless added do
        logWarning "page component appears after #page_end and was ignored"
      setEnv env
      clearTheoremRefs


end ProofScript
