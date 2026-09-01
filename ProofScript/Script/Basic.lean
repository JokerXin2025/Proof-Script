import ProofScript.Script.Config
import ProofScript.Script.Script
import ProofScript.References.Collect
import ProofScript.Extension.Component.Core
import ProofScript.Extension.Component.Latex

open Lean
open Meta (MetaM whnf isProp inferType isDefEq
           mkFreshExprMVar mkConstWithFreshMVarLevels)
open Elab (liftMacroM)
open Elab.Tactic (evalTactic elabTerm elabTermForApply getMainGoal getFVarId getGoals
                        replaceMainGoal withMainContext)
open Parser.Term (hole syntheticHole)
open Parser.Tactic (tacticSeq)
open ProofScript Extension


/-! ## Lean Native Tactics -/


script_macro
"assumption" : tactic => `(tactic| assumption)

script_macro
"change" equation:term : tactic => `(tactic| change $equation)

script_macro
"contradiction" : tactic => `(tactic| contradiction)

script_macro
"exfalso" : tactic => `(tactic| exfalso)

script_macro
"omega" : tactic => `(tactic| omega)

script_macro
"rfl" : tactic => `(tactic| rfl)

script_macro
"symm" : tactic => `(tactic| symm)

script_macro
"trivial" : tactic => `(tactic| trivial)

script_macro
"simp_only" "[" lemmas:(colGt ident)+ "]" : tactic => `(tactic|
  simp only [$[$lemmas:ident],*]
)

script_macro
"simp_only" "[" lemmas:(colGt ident)+ "]" "at" locations:(colGt ident)+ : tactic => `(tactic|
  simp only [$[$lemmas:ident],*] at $locations*
)

script_macro
"simp_only" "[" lemmas:(colGt ident)+ "]" "at" "*" : tactic => `(tactic|
  simp only [$[$lemmas:ident],*] at *
)

script_macro
"simp_only" "[" lemmas:(colGt ident)+ "]" "at" "⊢" : tactic => `(tactic|
  simp only [$[$lemmas:ident],*] at ⊢
)

script_macro
"simp_only" "[" lemmas:(colGt ident)+ "]" "at" locations:(colGt ident)+ "⊢" : tactic => `(tactic|
  simp only [$[$lemmas:ident],*] at $locations* ⊢
)

script_macro
"rewrite" "[" lemmas:(colGt ident)+ "]" : tactic => `(tactic| (
  rewrite [$[$lemmas:ident],*]
  try rfl
))

script_macro
"rewrite" "[" lemmas:(colGt ident)+ "]" "at" locations:(colGt ident)+ : tactic => `(tactic| (
  rewrite [$[$lemmas:ident],*] at $locations*
  try rfl
))

script_macro
"rewrite" "[" lemmas:(colGt ident)+ "]" "at" "*" : tactic => `(tactic| (
  rewrite [$[$lemmas:ident],*] at *
  try rfl
))

script_macro
"rewrite" "[" lemmas:(colGt ident)+ "]" "at" "⊢" : tactic => `(tactic| (
  rewrite [$[$lemmas:ident],*] at ⊢
  try rfl
))

script_macro
"rewrite" "[" lemmas:(colGt ident)+ "]" "at" locations:(colGt ident)+ "⊢" : tactic => `(tactic| (
  rewrite [$[$lemmas:ident],*] at $locations* ⊢
  try rfl
))

script_macro
"rewrite" "[" "←" lemmas:(colGt ident)+ "]" : tactic => `(tactic|(
  rewrite [$[← $lemmas:ident],*]
  try rfl
))

script_macro
"rewrite" "[" "←" lemmas:(colGt ident)+ "]" "at" locations:(colGt ident)+ : tactic => `(tactic|(
  rewrite [$[← $lemmas:ident],*] at $locations*
  try rfl
))

script_macro
"rewrite" "[" "←" lemmas:(colGt ident)+ "]" "at" "*" : tactic => `(tactic|(
  rewrite [$[← $lemmas:ident],*] at *
  try rfl
))

script_macro
"rewrite" "[" "←" lemmas:(colGt ident)+ "]" "at" "⊢" : tactic => `(tactic|(
  rewrite [$[← $lemmas:ident],*] at ⊢
  try rfl
))

script_macro
"rewrite" "[" "←" lemmas:(colGt ident)+ "]" "at" locations:(colGt ident)+ "⊢" : tactic => `(tactic|(
  rewrite [$[← $lemmas:ident],*] at $locations* ⊢
  try rfl
))

script_macro
"unfold" definitions:(colGt ident)+ : tactic => `(tactic|
  unfold $definitions*
)


/-! ## Script-Tactics -/


script_elab (intro := [h])
"intro_h" h:ident : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  match goalExpr with
  | .forallE _ domain body _ =>
    if !(← isProp domain) then
      throwError "to introduce a variable, please use `intro_var`"
    let bodyWhnf ← whnf body
    if bodyWhnf.isConstOf ``False then
      throwError "to solve the goal of form `... → False`, please use `contra`"
    let (_, newMVarId) ← mvarId.intro h.getId
    replaceMainGoal [newMVarId]
  | _ =>
    throwError "intro_h failed: the current goal is not an implication and has no premise to introduce."

script_elab (intro := [var])
"intro_var" var:ident : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  match goalExpr with
  | .forallE _ domain _ _ =>
    if ← isProp domain then
      throwError "to introduce a hypothesis, please use `intro_h`"
    let (_, newMVarId) ← mvarId.intro var.getId
    replaceMainGoal [newMVarId]
  | _ =>
    throwError "intro_var failed: the current goal has no universal quantifier and has no variable to introduce."

script_elab
"left" : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  if goalExpr.isAppOfArity ``Or 2 then
    let newMVarIds ← mvarId.apply (.const ``Or.inl [])
    replaceMainGoal newMVarIds
  else
    throwError "`left` can only be used with propositions connected by `∨`"

script_elab
"right" : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  if goalExpr.isAppOfArity ``Or 2 then
    let newMVarIds ← mvarId.apply (.const ``Or.inr [])
    replaceMainGoal newMVarIds
  else
    throwError "`right` can only be used with propositions connected by `∨`"

script_elab (intro := [h₁, h₂], clear := [h])
"unpack_and" "⟨" h₁:ident "," h₂:ident "⟩" ":=" h:ident : tactic => do
  let mvarId ← getMainGoal
  withMainContext do
    let fvarId ← getFVarId h
    let hExpr ← whnf (← fvarId.getType)
    if hExpr.isAppOfArity ``And 2 then
      let altNames := { varNames := [h₁.getId, h₂.getId] }
      let #[subgoal] ← mvarId.cases fvarId #[altNames]
      | throwError "unpack_and failed: cases produced an unexpected number of goals"
      replaceMainGoal [subgoal.mvarId]
    else
      throwError "unpack_and failed: variable '{h.getId}' is not a conjunction (And)"

script_elab (intro := [h₁, h₂], clear := [h])
"unpack_iff" "⟨" h₁:ident "," h₂:ident "⟩" ":=" h:ident : tactic => do
  let mvarId ← getMainGoal
  withMainContext do
    let fvarId ← getFVarId h
    let hExpr ← whnf (← fvarId.getType)
    unless hExpr.isAppOfArity ``Iff 2 do
      throwError "unpack_iff failed: variable '{h.getId}' is not an equivalence (Iff)"
    let altNames := { varNames := [h₁.getId, h₂.getId] }
    let #[subgoal] ← mvarId.cases fvarId #[altNames]
    | throwError "unpack_iff failed: destructuring produced an unexpected number of goals"
    replaceMainGoal [subgoal.mvarId]

script_elab (intro := [h₁, h₂], clear := [h])
"obtain_exist" "⟨" h₁:ident "," h₂:ident "⟩" ":=" h:ident : tactic => do
  let mvarId ← getMainGoal
  withMainContext do
    let fvarId ← getFVarId h
    let hExpr ← whnf (← fvarId.getType)
    if hExpr.isAppOfArity ``Exists 2 then
      let altNames := { varNames := [h₁.getId, h₂.getId] }
      let #[subgoal] ← mvarId.cases fvarId #[altNames]
        | throwError "obtain_exist failed: destructuring produced an unexpected number of goals"
      replaceMainGoal [subgoal.mvarId]
    else
      throwError "obtain_exist failed: variable '{h.getId}' is not an existential proposition (Exists)"

script_elab
"ext_fun" arg:ident : tactic => do
  let xName := arg.getId
  let target ← withMainContext <| whnf (← GetGoal)
  unless target.isAppOfArity ``Eq 3 do
    throwError "`ext_fun` can only be used on function equality goals"
  let lhsType ← withMainContext <| whnf (← inferType (target.getArg! 1))
  let rhsType ← withMainContext <| whnf (← inferType (target.getArg! 2))
  match lhsType, rhsType with
  | .forallE _ domain _ _, .forallE _ domain' _ _ =>
    unless ← isDefEq domain domain' do
      throwError "`ext_fun` requires both sides of the equality to have the same function domain"
    evalTactic (← `(tactic| funext $(mkIdent xName)))
  | _, _ => throwError "`ext_fun` can only be used on function equality goals"

script_elab
"provide" proof:term : tactic => do
  let goal ← getMainGoal
  let target ← withMainContext <| whnf (← goal.getType)
  let isWitnessDataGoal := match (← goal.getType) with
    | .mdata data _ => data.getBool witnessDataGoalMDataKey false
    | _ => false
  if isWitnessDataGoal then
    evalTactic (← `(tactic| exact $proof:term))
  else if target.isAppOfArity ``Exists 2 then
    evalTactic (← `(tactic| exists $proof:term))
  else
    throwError "`provide` can only be used in the `data` branch of `witness` or on an existential goal"

script_elab (clear := [proof])
"apply" proof:term : tactic => do
  let proofExpr ← withMainContext do
    instantiateMVars (← elabTermForApply proof)
  let proofType ← withMainContext <| whnf (← inferType proofExpr)
  let target ← withMainContext <| whnf (← GetGoal)
  let premise ← withMainContext do
    if proofType.isAppOfArity ``Iff 2 then
      let lhs := proofType.getArg! 0
      let rhs := proofType.getArg! 1
      if ← isDefEq target rhs then
        pure (proofType.getArg! 0, mkApp (.const ``Iff.mp []) proofExpr)
      else if ← isDefEq target lhs then
        pure (proofType.getArg! 1, mkApp (.const ``Iff.mpr []) proofExpr)
      else
        throwErrorAt proof "`apply` equivalence does not conclude the current target"
    else
      match proofType with
      | .forallE _ premiseType conclusion _ =>
        if !(← isProp premiseType) || !(← isProp conclusion) then
          throwErrorAt proof "`apply` expects a proposition of the form `P -> Q`"
        unless ← isDefEq target conclusion do
          throwErrorAt proof "`apply` implication does not conclude the current target"
        pure (premiseType, proofExpr)
      | _ =>
        throwErrorAt proof "`apply` expects a proposition of the form `P -> Q` or `P <-> Q`"
  let (premiseType, applied) := premise
  let premiseMVar ← withMainContext <| mkFreshExprMVar premiseType
  let goal ← getMainGoal
  goal.assign (mkApp applied premiseMVar)
  replaceMainGoal [premiseMVar.mvarId!]

script_macro (intro := [a])
"quot_induction" q:term "with" a:ident : tactic => `(tactic|
  refine Quot.inductionOn $q:term (fun $a:ident => ?_)
)


/-! ## Script-Strategy -/


/-! ### Assertions -/

script_elab (intro := [h], strategy := true)
"have" h:ident ":" type:term : tactic => do
  let goal ← getMainGoal
  let type ← withMainContext (elabTerm type none)
  let proofMVar ← withMainContext (mkFreshExprMVar type)
  proofMVar.mvarId!.setTag `proof
  let restMVar ← goal.assert h.getId type proofMVar
  let (_, restMVar') ← restMVar.intro1P
  replaceMainGoal [restMVar', proofMVar.mvarId!]

/-! ### Existential Construction -/

script_elab (strategy := true)
"witness" : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  if goalExpr.isAppOfArity ``Exists 2 then
    let mvarIds ← mvarId.apply (← mkConstWithFreshMVarLevels ``Exists.intro)
    match mvarIds with
    | [m₁, m₂] =>
      m₁.setTag `proof
      m₂.setTag `data
      let dataType ← m₂.getType
      m₂.setType (.mdata (Lean.MData.empty.setBool witnessDataGoalMDataKey true) dataType)
      replaceMainGoal [m₁, m₂]
    | _ =>
      throwError "unexpected error occurred during executing `witness`"
  else
    throwError "`witness` can only be used with propositions beginning with `∃`"

/-! ### Goal Decomposition: Conjunction -/

script_elab (strategy := true)
"split_and" : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  if !goalExpr.isAppOfArity ``And 2 then
    throwError "`split_and` can only be used with propositions connected by `∧`"
  else
    let mvarIds ← mvarId.apply (.const ``And.intro [])
    replaceMainGoal mvarIds

private partial def splitAndRec (mvarId : MVarId)
                                : MetaM (List MVarId) := do
  let goalExpr ← whnf (← mvarId.getType)
  if goalExpr.isAppOfArity ``And 2 then
    let mvarIds ← mvarId.apply (.const ``And.intro [])
    match mvarIds with
    | [m₁, m₂] =>
      let leftLeaves ← splitAndRec m₁
      let rightLeaves ← splitAndRec m₂
      return leftLeaves ++ rightLeaves
    | _ => return [mvarId]
  else
    return [mvarId]

script_elab
"split_and!" : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  if !goalExpr.isAppOfArity ``And 2 then
    throwError "`split_and!` can only be used with propositions connected by `∧`"
  let leaves ← splitAndRec mvarId
  let mut i := 1
  for leaf in leaves do
    let tagName := Name.mkSimple s!"goal{toRoman i}"
    leaf.setTag tagName
    i := i + 1
  replaceMainGoal leaves

/-! ### Goal Decomposition: Equivalence -/

script_elab (strategy := true)
"split_iff" : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  if !goalExpr.isAppOfArity ``Iff 2 then
    throwError "`split_iff` can only be used with propositions connected by `↔`"
  else
    let mvarIds ← mvarId.apply (.const ``Iff.intro [])
    match mvarIds with
    | [m₁, m₂] =>
      let (_, m₁') ← m₁.intro `_
      let (_, m₂') ← m₂.intro `_
      m₁'.setTag `suffice
      m₂'.setTag `necess
      replaceMainGoal [m₁', m₂']
    | _ =>
      throwError "unexpected error occurred during executing `split_iff`"

/-! ### Proposition Case Analysis -/

script_elab (clear := [h], strategy := true)
"cases_by" h:ident : tactic => do
  let mvarId ← getMainGoal
  withMainContext do
    let fvarId ← getFVarId h
    let hExpr ← whnf (← fvarId.getType)
    if hExpr.isAppOfArity ``Or 2 then
      let altNames := #[
        { varNames := [Name.mkSimple "hp"] },
        { varNames := [Name.mkSimple "hq"] }
      ]
      let subgoals ← mvarId.cases fvarId altNames
      match subgoals with
      | #[leftGoal, rightGoal] =>
          leftGoal.mvarId.setTag `left
          rightGoal.mvarId.setTag `right
          replaceMainGoal [leftGoal.mvarId, rightGoal.mvarId]
        | _ => throwError "cases_by failed: destructuring produced an unexpected number of goals"
    else
      throwError "cases_by failed: variable '{h.getId}' is not a disjunction (Or)"

script_elab (strategy := true)
"cases_by!" h:ident : tactic => do
  let mvarId ← getMainGoal
  withMainContext do
    let hId ← getFVarId h
    let hType ← whnf (← hId.getType)
    unless hType.isAppOfArity ``Or 2 do
      throwError "`cases_by!` can only be used on a disjunction hypothesis"
    let leaves ← mvarId.casesRec fun declaration => do
      pure ((declaration.fvarId == hId) ||
        (← whnf declaration.type).isAppOfArity ``Or 2)
    unless leaves.length >= 2 do
      throwError "cases_by! failed: destructuring produced an unexpected number of goals"
    let mut tagged : List MVarId := []
    let mut i := 1
    for leaf in leaves do
      leaf.setTag (Name.mkSimple s!"goal{toRoman i}")
      tagged := tagged ++ [leaf]
      i := i + 1
    replaceMainGoal tagged

/-! ### Data Case Analysis -/

script_elab (strategy := true)
"cases_on" value:term : tactic => do
  let (_valueExpr, valueType) ← withMainContext do
    let valueExpr ← elabTerm value none
    pure (valueExpr, ← whnf (← inferType valueExpr))
  if valueType == .sort .zero then
    evalTactic (← `(tactic| open Classical in
      by_cases h : $value:term))
    let goals ← getGoals
    match goals with
    | [trueGoal, falseGoal] =>
      trueGoal.setTag `true
      falseGoal.setTag `false
    | _ => throwError "cases_on failed: proposition case analysis produced an unexpected number of goals"
  else if ← isProp valueType then
    throwError "`cases_on` cannot be used on a proof of a proposition; pass the proposition itself"
  else
    evalTactic (← `(tactic| cases $value:term))

/-! ### Proof by Contradiction -/

script_elab (intro := [h], strategy := true)
"contra" h:ident : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  let isArrowToFalse := match goalExpr with
                        | .forallE _ _ body _ => body.isConstOf ``False
                        | _ => false
  if isArrowToFalse then
    let (_, newMVarId) ← mvarId.intro h.getId
    newMVarId.setTag `proof
    replaceMainGoal [newMVarId]
  else
    evalTactic (← `(tactic| by_contra $h))
    let newMVarId ← getMainGoal
    newMVarId.setTag `proof
    replaceMainGoal [newMVarId]

/-! ### Mathematical Induction -/

script_macro (clear := [n], strategy := true)
"induction" n:ident : tactic => `(tactic|
  induction $n:ident
)

/-! ### Strong (Complete) Induction -/

private theorem strongInductionOn {motive : Nat → Prop}
    (zero : motive 0) (t : Nat)
    (succ : (n : Nat) → ((m : Nat) → m < n.succ → motive m) → motive n.succ)
  : motive t
:= Nat.strongRecOn t <|
    fun n ih =>
      match n with
      | 0     => zero
      | n + 1 => succ n ih

script_macro (clear := [n], strategy := true)
"complete_induction" n:ident : tactic => `(tactic|
  induction $n:ident using strongInductionOn
)


/-! ## Metadata -/


/-! ### Remark -/

script_macro (clear := [text])
"remark" text:str : tactic => `(tactic| skip)

/-! ### SVG -/

script_macro (clear := [code])
"svg" code:str : tactic => `(tactic| skip)

/-! ### LaTeX (Compiled to SVG) -/

open Lean.Elab.Tactic in
private def recordLatexComponent  (metadata : ComponentMetadata)
                                  (code : String) :
                                  TacticM Unit := do
  let svg ← compileLatexToSvg code
  let svg ← Extension.writeTextResource "svg" "svg" "image/svg+xml" svg
  recordStep "latex" [
    ("metadata", componentMetadataJson metadata),
    ("language", Json.str "latex"),
    ("source", Json.str code),
    ("svg", svg)
  ] [] [] [] do
    evalTactic (← `(tactic| skip))

script_elab (recorder := exclusive)
"latex" _metadata:componentMeta _code:str : tactic => do
  evalTactic (← `(tactic| skip))

script_recorder
"latex" metadata:componentMeta code:str : tactic => do
  let metadata ←
    match parseComponentMetadata metadata.raw with
    | .ok value => pure value
    | .error message => throwErrorAt metadata message
  recordLatexComponent metadata code.getString

/-! ### Informal Proofs -/

script_elab (clear := [cause])
"cause" cause:str : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  logWarningAt cause m!"`sorryAx` will be used to prove: {target}"
  evalTactic (← `(tactic| sorry))

macro "cause" cause:str : term => do
  `(term| script cause $cause:str)


/-! ## Calculation Chains -/


script_macro (recorder := exclusive)
"calc" steps:calcSteps : tactic => do
  `(tactic| calc $steps:calcSteps)

/-- Parse `calcSteps` into one `(relation term, proof term)` pair per step.
    The native structure is `calcFirstStep (calcStep)*` (see
    `Lean.Elab.Calc.mkCalcStepViews`). Unlike `infer`, a `calc` relation
    (`=`/`≤` and so on) is embedded in the relation term itself, so it is
    extracted syntactically and decomposed after elaboration. -/
private def parseCalcSteps  (steps : Syntax)
                            : MacroM (Array (TSyntax `term × TSyntax `term)) := do
  -- `calcSteps` has a first-step node followed by a `many` node of later steps.
  let firstStep := steps[0]
  let restSteps := steps[1]
  let first ← match firstStep with
    | `(calcFirstStep| $term:term := $proof:term) => pure (term, proof)
    | `(calcFirstStep| $term:term) =>
        -- Without `:=`, complete the relation with `= _` and use `rfl`.
        let rel : TSyntax `term ← `($term:term = _)
        let rfl : TSyntax `term ← `(rfl)
        pure (rel, rfl)
    | _ => Macro.throwError s!"calc: invalid first-step syntax (kind: {firstStep.getKind})"
  let mut out := #[first]
  for i in [:restSteps.getArgs.size] do
    let step := restSteps[i]
    let `(Lean.calcStep| $term:term := $proof:term) := step
      | Macro.throwError s!"calc: invalid chain-step syntax (kind: {step.getKind})"
    out := out.push (term, proof)
  return out

/-- Check whether a syntax tree contains a synthetic hole `?_`. -/
private partial def calcContainsSyntheticHole (stx : Syntax) : Bool :=
  if stx.getKind == `Lean.Parser.Term.syntheticHole then true
  else stx.getArgs.any calcContainsSyntheticHole

/-- Decompose `e` into `(relation, left, right)`.
    The final two arguments are expected to be explicit, as in
    `Lean.Elab.Term.getCalcRelation?`. -/
private def decomposeCalcRelation (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.getAppNumArgs < 2 then none
  else some (e.appFn!.appFn!, e.appFn!.appArg!, e.appArg!)

/-- Recording elaborator for `_calc`: record the initial term and every chain step.
    `init` is the left side of the first relation; `chain` contains
    `{relation, rhs, proof}` entries, with proofs containing `?_` recorded as holes. -/
script_recorder
"calc" steps:calcSteps : tactic => do
  -- Parse the steps syntactically.
  let chain ← liftMacroM <| parseCalcSteps steps
  let mut chainJson := #[]
  let mut initJson : Json := Json.null
  for i in [:chain.size] do
    let (relTerm, prf) := chain[i]!
    let relExpr ← withMainContext do
      let e ← Lean.Elab.Tactic.elabTerm relTerm none
      instantiateMVars e
    let some (rel, lhs, rhs) := decomposeCalcRelation relExpr
      | throwErrorAt relTerm "calc: cannot extract a binary relation from the step"
    if i == 0 then
      initJson ← withMainContext <| ProofScript.Expr2JSON lhs
    let relJson ← withMainContext <| ProofScript.Expr2JSON rel
    let rhsJson ← withMainContext <| ProofScript.Expr2JSON rhs
    let prfJson ← withMainContext do
      if calcContainsSyntheticHole prf.raw then
        pure (Json.mkObj [("kind", "hole")])
      else
        let prfExpr ← Lean.Elab.Tactic.elabTerm prf (some relExpr)
        recordRefsFromExpr prfExpr
        ProofScript.Expr2JSON prfExpr
    chainJson := chainJson.push (Json.mkObj [
      ("relation", relJson),
      ("rhs", rhsJson),
      ("proof", prfJson)
    ])
  recordStep "calc"
    [("init", initJson), ("chain", Json.arr chainJson)]
    [] [] [] do
      withScriptMode <| evalTactic (← `(tactic| script_calc $steps:calcSteps))


/-! ## Inference Chains -/


/-! Wrap the entire sequence in a single `withPosition`: its saved position is
    the first step's column after trailing whitespace. `colGe` then requires
    later steps to be at least that indented, distinguishing nested steps from
    following tactics. An additional `withPosition` would overwrite this
    position and make a following tactic look like another step. -/

syntax inferStep := ppIndent(colGe term " => " term " := " term)
syntax inferSteps := withPosition(ppLine inferStep (ppLine linebreak inferStep)*)

/-- Check whether a syntax tree contains a synthetic hole `?_`. -/
private partial def inferContainsSyntheticHole (stx : Syntax) :=
  if stx.getKind == ``syntheticHole then true
  else stx.getArgs.any inferContainsSyntheticHole

open Lean.Meta in
/-- Recursively find a subexpression of `e` whose type is definitionally equal
    to `targetType`. Instantiate binders with `withLocalDecl`/`withLetDecl`
    before traversing their bodies so bound variables remain well-scoped. -/
private partial def inferFindSubtermOfType  (e : Expr)
                                    (targetType : Expr)
                                    : MetaM Bool := do
  let e ← instantiateMVars e
  let checkSelf : MetaM Bool := do
    try
      let ty ← inferType e
      isDefEqGuarded ty targetType
    catch _ => pure false
  if (← checkSelf) then return true
  match e with
  | .app f a => return (← inferFindSubtermOfType f targetType) || (← inferFindSubtermOfType a targetType)
  | .lam _ t b bi =>
      if (← inferFindSubtermOfType t targetType) then return true
      withLocalDecl `infer_x bi t fun x => inferFindSubtermOfType (b.instantiate1 x) targetType
  | .letE _ t v b _ =>
      if (← inferFindSubtermOfType t targetType) then return true
      if (← inferFindSubtermOfType v targetType) then return true
      withLetDecl `infer_x t v fun x => inferFindSubtermOfType (b.instantiate1 x) targetType
  | .forallE _ t b bi =>
      if (← inferFindSubtermOfType t targetType) then return true
      withLocalDecl `infer_x bi t fun x => inferFindSubtermOfType (b.instantiate1 x) targetType
  | .mdata _ b => inferFindSubtermOfType b targetType
  | .proj _ _ b => inferFindSubtermOfType b targetType
  | _ => pure false

open Lean.Elab.Term in
/-- Elaborate the first `P => Q := prf` step as a proof of `Q`, and ensure
    that it contains a proof of `P`; otherwise the initial proposition is meaningless. -/
elab "infer_check_first" P:term " => " Q:term " := " prf:term : term => do
  if inferContainsSyntheticHole prf.raw then
    throwErrorAt prf "infer: the first step cannot contain '?_'; provide a proof of the initial proposition"
  let pType ← elabType P
  let qType ← elabType Q
  let prfExpr ← elabTermEnsuringType prf qType
  unless (← inferFindSubtermOfType prfExpr pType) do
    let pStr := (Syntax.reprint P.raw).getD "?" |>.trimAscii
    throwErrorAt prf s!"infer: the first step must contain a proof of proposition '{pStr}'"
  return prfExpr

/-- Replace the unique `?_` in `stx` with `rep` and return the resulting syntax
    together with the number of holes encountered. -/
private partial def inferReplaceHole (stx : Syntax) (rep : TSyntax `term) : StateT Nat MacroM Syntax := do
  if stx.getKind == ``syntheticHole then
    modify (· + 1)
    return rep.raw
  else
    let args ← stx.getArgs.mapM fun a => inferReplaceHole a rep
    if args == stx.getArgs then return stx
    else return Syntax.node stx.getHeadInfo stx.getKind args

/-- Replace exactly one `?_` in `stx`; otherwise report an error. -/
private def inferReplaceSingleHole (stx : Syntax) (rep : TSyntax `term) : MacroM (TSyntax `term) := do
  let (stx', count) ← (inferReplaceHole stx rep).run 0
  if count != 1 then
    Macro.throwErrorAt stx s!"infer: each chain step must contain exactly one '?_', but found {count}"
  return ⟨stx'⟩

/-- Check whether `t` is `_` (a hole). -/
private def inferIsHoleTerm (t : TSyntax `term) :=
  t.raw.getKind == ``hole

/-- Expand an `infer` chain into successive anonymous `have`s. Each step is
    added to the local context, and a later `?_` refers to the preceding result.
    The final result is only attempted as a goal-closing term. -/
private def buildInferTactic (steps : Syntax) : MacroM (TSyntax `tactic) := do
  let mut tactics : Array Syntax := #[]
  let mut previous : Option (TSyntax `term) := none
  let firstStep := steps[0]
  let restSteps := steps[1]
  let `(inferStep| $P:term => $Q:term := $proof0:term) := firstStep
    | Macro.throwError "infer: invalid first-step syntax"
  let firstProof ← `(term| infer_check_first $P:term => $Q:term := $proof0:term)
  let firstName ← withFreshMacroScope <| MonadQuotation.addMacroScope `this
  let firstId : TSyntax `ident := ⟨mkIdent firstName⟩
  tactics := tactics.push (← `(tactic| have $firstId:ident : $Q:term := $firstProof:term)).raw
  previous := some (← `(term| $firstId:ident))
  for step in restSteps.getArgs do
    let `(inferStep| $L:term => $R:term := $proof:term) := step
      | Macro.throwError "infer: invalid chain-step syntax"
    let some previousTerm := previous
      | Macro.throwError "infer: internal error, missing the preceding conclusion"
    let previousTerm ← if inferIsHoleTerm L then pure previousTerm else `(($previousTerm : $L))
    let proof' ← inferReplaceSingleHole proof.raw previousTerm
    let stepName ← withFreshMacroScope <| MonadQuotation.addMacroScope `this
    let stepId : TSyntax `ident := ⟨mkIdent stepName⟩
    tactics := tactics.push (← `(tactic| have $stepId:ident : $R:term := $proof':term)).raw
    previous := some (← `(term| $stepId:ident))
  let some finalTerm := previous
    | Macro.throwError "infer: at least one chain step is required"
  tactics := tactics.push (← `(tactic| try exact $finalTerm:term)).raw
  let seq : TSyntax ``tacticSeq := ⟨buildTacticSeq tactics⟩
  `(tactic| ($seq:tacticSeq))

script_macro (recorder := exclusive)
"infer" steps:inferSteps : tactic => do
  buildInferTactic steps.raw

macro "infer" steps:inferSteps : term => do
  `(term| script infer $steps:inferSteps)

/-- Parse `inferSteps` and extract the initial proposition and each step.
    Returns `(initial proposition, [(right-hand proposition, proof term)])`. -/
private def parseInferSteps (steps : Syntax)
                            : MacroM (TSyntax `term × Array (TSyntax `term × TSyntax `term)) := do
  -- The actual structure is `inferStep (ppLine linebreak inferStep)*`.
  let firstStep := steps[0]
  let restSteps := steps[1]
  -- Parse the first step.
  let `(inferStep| $P:term => $Q:term := $prf1:term) := firstStep
    | Macro.throwError s!"infer: invalid first-step syntax, kind: {firstStep.getKind}"
  let mut chain := #[(Q, prf1)]
  -- Parse subsequent steps.
  for i in [:restSteps.getArgs.size] do
    let step := restSteps[i]
    let `(inferStep| $_:term => $R:term := $prf:term) := step
      | Macro.throwError s!"infer: invalid chain-step syntax, kind: {step.getKind}"
    chain := chain.push (R, prf)
  return (P, chain)

script_recorder
"infer" steps:inferSteps : tactic => do
  -- Parse the steps.
  let (init, chain) ← liftMacroM <|
    parseInferSteps steps
  -- Elaborate the initial proposition.
  let initExpr ← withMainContext do
    Lean.Elab.Tactic.elabTerm init none
  let initJson ← withMainContext <|
    ProofScript.Expr2JSON initExpr
  -- Elaborate each chain step (record rhs and proof without replacing holes).
  let mut chainJson := #[]
  for (rhs, prf) in chain do
    -- Elaborate rhs and prf directly; the tactic macro handles `?_` at execution time.
    let rhsExpr ← withMainContext do
      Lean.Elab.Tactic.elabTerm rhs none
    -- If prf contains `?_`, record only its syntax because the term macro
    -- supplies the actual value at runtime.
    let prfJson ← withMainContext do
      if inferContainsSyntheticHole prf.raw then
        -- Record a special marker for a proof containing `?_`.
        pure <| Json.mkObj [("kind", "hole")]
      else
        -- Elaborate proofs without `?_` normally.
        let prfExpr ← Lean.Elab.Tactic.elabTerm prf (some rhsExpr)
        recordRefsFromExpr prfExpr
        ProofScript.Expr2JSON prfExpr
    let rhsJson ← withMainContext <| ProofScript.Expr2JSON rhsExpr
    chainJson := chainJson.push (Json.mkObj [("rhs", rhsJson), ("proof", prfJson)])
  recordStep "infer"
    [("init", initJson), ("chain", Json.arr chainJson)]
    [] [] [] do
      evalTactic (← liftMacroM <| buildInferTactic steps.raw)
