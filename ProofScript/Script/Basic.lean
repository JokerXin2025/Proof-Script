import ProofScript.Script.Config
import ProofScript.Script.Script
import ProofScript.References.Collect
import ProofScript.Extension.Component.Core
import ProofScript.Extension.Component.Latex

open Lean
open Meta (MetaM whnf isProp inferType isDefEq
           mkFreshExprMVar mkConstWithFreshMVarLevels
           withLetDecl withLocalDecl isDefEqGuarded)
open Elab (liftMacroM)
open Elab.Term (elabType elabTermEnsuringType)
open Elab.Tactic (evalTactic elabTerm elabTermForApply getMainGoal getFVarId getGoals
                        replaceMainGoal withMainContext)
open Parser.Term (hole syntheticHole)
open Parser.Tactic (tacticSeq)
open ProofScript.Extension


namespace ProofScript


initialize witnessDataGoals : IO.Ref (List MVarId) ← IO.mkRef []


/-! ## Lean Native Tactics -/

script_macro
"change" equation:term : tactic => `(tactic| change $equation)

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
"rewrite" equation:ident : tactic => `(tactic| (
  rewrite [$equation:ident]
  try rfl
))

script_macro
"rewrite" "←" equation:ident : tactic => `(tactic|(
  rewrite [← $equation:ident]
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
    throwError "intro_h 失败：当前目标不是蕴含式 (→)，没有可以引入的前提。"

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
    throwError "intro_var 失败：当前目标没有全称量词 (∀)，没有可以引入的变量。"

script_elab
"prove_left" : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  if goalExpr.isAppOfArity ``Or 2 then
    let newMVarIds ← mvarId.apply (.const ``Or.inl [])
    replaceMainGoal newMVarIds
  else
    throwError "`prove_left` can only be used with propositions connected by `∨`"

script_elab
"prove_right" : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  if goalExpr.isAppOfArity ``Or 2 then
    let newMVarIds ← mvarId.apply (.const ``Or.inr [])
    replaceMainGoal newMVarIds
  else
    throwError "`prove_right` can only be used with propositions connected by `∨`"

script_elab (intro := [h₁, h₂], clear := [h])
"unpack_and" "⟨" h₁:ident "," h₂:ident "⟩" ":=" h:ident : tactic => do
  let mvarId ← getMainGoal
  withMainContext do
    let fvarId ← getFVarId h
    let hExpr ← whnf (← fvarId.getType)
    if hExpr.isAppOfArity ``And 2 then
      let altNames := { varNames := [h₁.getId, h₂.getId] }
      let #[subgoal] ← mvarId.cases fvarId #[altNames]
      | throwError "unpack_and 失败：内部错误，cases 产生了非预期的子目标数量"
      replaceMainGoal [subgoal.mvarId]
    else
      throwError "unpack_and 失败：变量 '{h.getId}' 的类型不是 ∧ (And)。"

script_elab (intro := [h₁, h₂], clear := [h])
"unpack_iff" "⟨" h₁:ident "," h₂:ident "⟩" ":=" h:ident : tactic => do
  let mvarId ← getMainGoal
  withMainContext do
    let fvarId ← getFVarId h
    let hExpr ← whnf (← fvarId.getType)
    unless hExpr.isAppOfArity ``Iff 2 do
      throwError "unpack_iff 失败：变量 '{h.getId}' 的类型不是等价命题 (Iff)。"
    let altNames := { varNames := [h₁.getId, h₂.getId] }
    let #[subgoal] ← mvarId.cases fvarId #[altNames]
    | throwError "unpack_iff 失败：解构等价命题产生了非预期的子目标数量"
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
        | throwError "obtain_exist 失败：解构存在性产生了非预期的子目标数量"
      replaceMainGoal [subgoal.mvarId]
    else
      throwError "obtain_exist 失败：变量 '{h.getId}' 的类型不是存在命题 (Exists)。"

script_elab
"ext_fun" arg:ident : tactic => do
  let xName := arg.getId
  let target ← withMainContext <| whnf (← GetGoal)
  unless target.isAppOfArity ``Eq 3 do
    throwError "`ext_fun` 只能用于函数等式目标"
  let lhsType ← withMainContext <| whnf (← inferType (target.getArg! 1))
  let rhsType ← withMainContext <| whnf (← inferType (target.getArg! 2))
  match lhsType, rhsType with
  | .forallE _ domain _ _, .forallE _ domain' _ _ =>
    unless ← isDefEq domain domain' do
      throwError "`ext_fun` 要求等式两侧具有相同的函数定义域"
    evalTactic (← `(tactic| funext $(mkIdent xName)))
  | _, _ => throwError "`ext_fun` 只能用于函数等式目标"

script_elab
"provide" proof:term : tactic => do
  let goal ← getMainGoal
  unless (← witnessDataGoals.get).contains goal do
    throwError "`provide` can only be used in the `data` branch of `witness`"
  evalTactic (← `(tactic| exact $proof:term))
  witnessDataGoals.modify (·.filter (· != goal))

script_elab (clear := [lemma])
"apply_h" lemma:term : tactic => do
  let lemmaExpr ← withMainContext do
    instantiateMVars (← elabTermForApply lemma)
  unless lemmaExpr.isFVar && (← withMainContext <| isProp (← inferType lemmaExpr)) do
    throwErrorAt lemma "`apply_h` expects a local hypothesis that proves a proposition"
  evalTactic (← `(tactic| apply $lemma:term))

script_elab
"apply_thm" thm:term : tactic => do
  let thmExpr ← withMainContext do
    instantiateMVars (← elabTermForApply thm)
  unless thmExpr.isConst && (← withMainContext <| isProp (← inferType thmExpr)) do
    throwErrorAt thm "`apply_thm` expects a theorem constant that proves a proposition"
  evalTactic (← `(tactic| apply $thm:term))

script_macro (intro := [a])
"quot_induction" q:term "with" a:ident : tactic => `(tactic|
  refine Quot.inductionOn $q:term (fun $a:ident => ?_)
)


/-! ## Script-Strategy -/

/-! ### 断言 -/

script_elab (intro := [h], kind := strategy)
"have" h:ident ":" type:term : tactic => do
  let goal ← getMainGoal
  let type ← withMainContext (elabTerm type none)
  let proofMVar ← withMainContext (mkFreshExprMVar type)
  proofMVar.mvarId!.setTag `proof
  let restMVar ← goal.assert h.getId type proofMVar
  let (_, restMVar') ← restMVar.intro1P
  replaceMainGoal [restMVar', proofMVar.mvarId!]

/-! ### 存在性构造 -/

script_elab (kind := strategy)
"witness" : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  if goalExpr.isAppOfArity ``Exists 2 then
    let mvarIds ← mvarId.apply (← mkConstWithFreshMVarLevels ``Exists.intro)
    match mvarIds with
    | [m₁, m₂] =>
      m₁.setTag `proof
      m₂.setTag `data
      witnessDataGoals.modify (m₂ :: ·)
      replaceMainGoal [m₁, m₂]
    | _ =>
      throwError "unexpected error occurred during executing `witness`"
  else
    throwError "`witness` can only be used with propositions beginning with `∃`"

/-! ### 目标分解 —— 合取 -/

script_elab (kind := strategy)
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

/-! ### 目标分解 —— 等价 -/

script_elab (kind := strategy)
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

/-! ### 基于命题的分类讨论 -/

script_elab (clear := [h], kind := strategy)
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
       | _ => throwError "cases_by 失败：解构析取产生了非预期的子目标数量"
    else
      throwError "cases_by 失败：变量 '{h.getId}' 的类型不是析取命题 (Or)。"

script_elab (kind := strategy)
"cases_by!" h:ident : tactic => do
  let mvarId ← getMainGoal
  withMainContext do
    let hId ← getFVarId h
    let hType ← whnf (← hId.getType)
    unless hType.isAppOfArity ``Or 2 do
      throwError "`cases_by!` 只能用于析取命题假设"
    let leaves ← mvarId.casesRec fun declaration => do
      pure ((declaration.fvarId == hId) ||
        (← whnf declaration.type).isAppOfArity ``Or 2)
    unless leaves.length >= 2 do
      throwError "cases_by! 失败：解构析取产生了非预期的子目标数量"
    let mut tagged : List MVarId := []
    let mut i := 1
    for leaf in leaves do
      leaf.setTag (Name.mkSimple s!"goal{toRoman i}")
      tagged := tagged ++ [leaf]
      i := i + 1
    replaceMainGoal tagged

/-! ### 基于数据类型的分类讨论 -/

script_elab (kind := strategy)
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
    | _ => throwError "cases_on 失败：命题分类产生了非预期的子目标数量"
  else if ← isProp valueType then
    throwError "`cases_on` 不能对命题证明项使用；请传入命题本身"
  else
    evalTactic (← `(tactic| cases $value:term))

/-! ### 反证法 -/

script_elab (intro := [h], kind := strategy)
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

/-! ### 数学归纳法 -/

script_macro (clear := [n], kind := strategy)
"induction" n:ident : tactic => `(tactic|
  induction $n:ident
)

/-! ### 强（完全）归纳法 -/

private theorem strongInductionOn {motive : Nat → Prop}
    (zero : motive 0) (t : Nat)
    (succ : (n : Nat) → ((m : Nat) → m < n.succ → motive m) → motive n.succ)
  : motive t
:= Nat.strongRecOn t <|
    fun n ih =>
      match n with
      | 0     => zero
      | n + 1 => succ n ih

script_macro (clear := [n], kind := strategy)
"complete_induction" n:ident : tactic => `(tactic|
  induction $n:ident using strongInductionOn
)


/-! ## Meta Data -/

/-! ### Remark -/

script_macro (clear := [text])
"remark" text:str : tactic => `(tactic| skip)

/-! ### SVG -/

script_macro (clear := [code])
"svg" code:str : tactic => `(tactic| skip)

/-! ### LaTeX Component (to SVG) -/

open Lean.Elab.Tactic in
private def recordLatexComponent  (metadata : ComponentMetadata)
                                  (code : String) :
                                  TacticM Unit := do
  let svg ← compileLatexToSvg code
  recordStep "latex" [
    ("metadata", componentMetadataJson metadata),
    ("language", Json.str "latex"),
    ("source", Json.str code),
    ("svg", Json.str svg)
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

/-! ### 非形式化证明 -/

script_elab (clear := [cause])
"cause" cause:str : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  logWarningAt cause m!"`sorryAx` will be used to prove: {target}"
  evalTactic (← `(tactic| sorry))
macro "cause" cause:str : term => do
  `(term| script
    cause $cause:str)


/-! ## 连续计算 `calc` -/

script_macro (recorder := exclusive)
"calc" steps:calcSteps : tactic => do
  `(tactic| calc $steps:calcSteps)

/-- 解析 `calcSteps`，返回 `(关系项, 证明项)` 数组，每步一个。
    `calcSteps` 原生结构：`calcFirstStep (calcStep)*`（见 `Lean.Elab.Calc.mkCalcStepViews`）。
    与 `infer` 不同，`calc` 的关系符（`=`/`≤` 等）**内嵌在关系项 term 里**（如 `a = b` 是
    单个 term），没有独立的 `calcOp` 节点，故此处只做语法级提取，关系的拆分放到 elaborate
    之后用 `decomposeCalcRelation` 完成。 -/
private def parseCalcSteps  (steps : Syntax)
                            : MacroM (Array (TSyntax `term × TSyntax `term)) := do
  -- `calcSteps` 结构：`calcFirstStep (calcStep)*`（`withPosition`/`ppLine` 均不产生节点，直接
  -- `steps[0]` = 首步、`steps[1]` = 后续步的 `many` 节点；同 `infer` 的 `parseInferSteps`）。
  let firstStep := steps[0]
  let restSteps := steps[1]
  let first ← match firstStep with
    | `(calcFirstStep| $term:term := $proof:term) => pure (term, proof)
    | `(calcFirstStep| $term:term) =>
        -- 首步无 `:=`（对齐关系符的写法 `calc abc`），关系补 `= _`、证明补 `rfl`
        let rel : TSyntax `term ← `($term:term = _)
        let rfl : TSyntax `term ← `(rfl)
        pure (rel, rfl)
    | _ => Macro.throwError s!"calc: 第一步语法无效（kind: {firstStep.getKind}）"
  let mut out := #[first]
  for i in [:restSteps.getArgs.size] do
    let step := restSteps[i]
    let `(Lean.calcStep| $term:term := $proof:term) := step
      | Macro.throwError s!"calc: 推导步骤语法无效（kind: {step.getKind}）"
    out := out.push (term, proof)
  return out

/-- 检查语法树中是否出现 `?_`（syntheticHole）。 -/
partial def calcContainsSyntheticHole (stx : Syntax) : Bool :=
  if stx.getKind == `Lean.Parser.Term.syntheticHole then true
  else stx.getArgs.any calcContainsSyntheticHole

/-- 把 `e` 拆成 `(关系, 左项, 右项)`。假设最后两个参数都是显式参数
    （同 `Lean.Elab.Term.getCalcRelation?`）。 -/
def decomposeCalcRelation (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.getAppNumArgs < 2 then none
  else some (e.appFn!.appFn!, e.appFn!.appArg!, e.appArg!)

/-- 录制版 `_calc`：录制初始项 + 推导链的每一步。
    - `init`: 第一步关系项的左侧
    - `chain`: 列表，每个元素 `{relation, rhs, proof}`；`proof` 含 `?_` 时录 `{"kind": "hole"}` -/
script_recorder
"calc" steps:calcSteps : tactic => do
  -- 解析步骤（语法级）
  let chain ← liftMacroM <| parseCalcSteps steps
  let mut chainJson := #[]
  let mut initJson : Json := Json.null
  for i in [:chain.size] do
    let (relTerm, prf) := chain[i]!
    let relExpr ← withMainContext do
      let e ← Lean.Elab.Tactic.elabTerm relTerm none
      instantiateMVars e
    let some (rel, lhs, rhs) := decomposeCalcRelation relExpr
      | throwErrorAt relTerm "calc: 无法从推导步骤中提取二元关系"
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
      evalTactic (← `(tactic| calc $steps:calcSteps))


/-! ## 连续推导 `infer` -/

/-! 用**单个** `withPosition` 包裹整个步骤序列：`withPosition` 的 savedPos 取「关键字
    skip 尾随空白后的位置」=「第一步起始列」，`colGe` 据此要求「每一步的缩进列 ≥ 第一步缩进」，
    从而可靠地区分「更深的步骤」与「同缩进的后续 tactic」（后者列 < 第一步列，`colGe` 失败终止块）。
    若再套一层 `withPosition((ppLine linebreak inferStep)*)`，savedPos 会被覆盖为「第一步后第一个
    token 列」（单步时即后续 tactic 列），导致单步后跟 tactic 被误当成步骤。 -/

syntax inferStep := ppIndent(colGe term " => " term " := " term)
syntax inferSteps := withPosition(ppLine inferStep (ppLine linebreak inferStep)*)

/-- 语法树中是否出现 `?_`（syntheticHole）。 -/
partial def inferContainsSyntheticHole (stx : Syntax) :=
  if stx.getKind == ``syntheticHole then true
  else stx.getArgs.any inferContainsSyntheticHole

/-- 递归查找 `e` 中是否存在类型与 `targetType` 定义相等的子项。
    对 binder 用 `withLocalDecl`/`withLetDecl` 实例化后再进入 body，避免 bvar 未绑定。 -/
partial def inferFindSubtermOfType  (e : Expr)
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

/-- 第一行 `P => Q := prf` 的 elaborator：elaborate `prf` 为 `Q` 的证明，并检查其中
    确实包含一个 `P` 的证明（否则 `P` 完全失去意义）。 -/
elab "infer_check_first" P:term " => " Q:term " := " prf:term : term => do
  if inferContainsSyntheticHole prf.raw then
    throwErrorAt prf "infer: 第一行不允许出现 '?_'，请直接填入开头命题的证明项"
  let pType ← elabType P
  let qType ← elabType Q
  let prfExpr ← elabTermEnsuringType prf qType
  unless (← inferFindSubtermOfType prfExpr pType) do
    let pStr := (Syntax.reprint P.raw).getD "?" |>.trimAscii
    throwErrorAt prf s!"infer: 第一行的推导失去意义——右侧证明项中必须包含命题 '{pStr}' 的证明"
  return prfExpr

/-- 把 `stx` 中唯一的一个 `?_` 替换为 `rep`，并返回替换后的语法与 `?_` 个数。 -/
partial def inferReplaceHole (stx : Syntax) (rep : TSyntax `term) : StateT Nat MacroM Syntax := do
  if stx.getKind == ``syntheticHole then
    modify (· + 1)
    return rep.raw
  else
    let args ← stx.getArgs.mapM fun a => inferReplaceHole a rep
    if args == stx.getArgs then return stx
    else return Syntax.node stx.getHeadInfo stx.getKind args

/-- 替换 `stx` 中有且仅有的一个 `?_`，否则报错。 -/
def inferReplaceSingleHole (stx : Syntax) (rep : TSyntax `term) : MacroM (TSyntax `term) := do
  let (stx', count) ← (inferReplaceHole stx rep).run 0
  if count != 1 then
    Macro.throwErrorAt stx s!"infer: 推导步骤要求有且只有一个 '?_'，但找到了 {count} 个"
  return ⟨stx'⟩

/-- `t` 是否是 `_`（hole）。 -/
def inferIsHoleTerm (t : TSyntax `term) :=
  t.raw.getKind == ``hole

/-- 将 `infer` 链展开为逐步匿名 `have`。每一步都进入局部上下文，后一步的 `?_` 用 `this`
    指向前一步刚产生的匿名条件。最后只尝试使用最后一步闭合目标。 -/
def buildInferTactic (steps : Syntax) : MacroM (TSyntax `tactic) := do
  let mut tactics : Array Syntax := #[]
  let mut previous : Option (TSyntax `term) := none
  let firstStep := steps[0]
  let restSteps := steps[1]
  let `(inferStep| $P:term => $Q:term := $proof0:term) := firstStep
    | Macro.throwError "infer: 第一步语法无效"
  let firstProof ← `(term| infer_check_first $P:term => $Q:term := $proof0:term)
  let firstName ← withFreshMacroScope <| MonadQuotation.addMacroScope `this
  let firstId : TSyntax `ident := ⟨mkIdent firstName⟩
  tactics := tactics.push (← `(tactic| have $firstId:ident : $Q:term := $firstProof:term)).raw
  previous := some (← `(term| $firstId:ident))
  for step in restSteps.getArgs do
    let `(inferStep| $L:term => $R:term := $proof:term) := step
      | Macro.throwError "infer: 推导步骤语法无效"
    let some previousTerm := previous
      | Macro.throwError "infer: 内部错误，缺少前一步结论"
    let previousTerm ← if inferIsHoleTerm L then pure previousTerm else `(($previousTerm : $L))
    let proof' ← inferReplaceSingleHole proof.raw previousTerm
    let stepName ← withFreshMacroScope <| MonadQuotation.addMacroScope `this
    let stepId : TSyntax `ident := ⟨mkIdent stepName⟩
    tactics := tactics.push (← `(tactic| have $stepId:ident : $R:term := $proof':term)).raw
    previous := some (← `(term| $stepId:ident))
  let some finalTerm := previous
    | Macro.throwError "infer: 需要至少一个推导步骤"
  tactics := tactics.push (← `(tactic| try exact $finalTerm:term)).raw
  let seq : TSyntax ``tacticSeq := ⟨buildTacticSeq tactics⟩
  `(tactic| ($seq:tacticSeq))

script_macro (recorder := exclusive)
"infer" steps:inferSteps : tactic => do
  buildInferTactic steps.raw

macro "infer" steps:inferSteps : term => do
  `(term| script infer $steps:inferSteps)

/-- 解析 `inferSteps`，提取初始命题和每一步的信息。
    返回：(初始命题, [(右侧命题, 证明项)]) -/
def parseInferSteps (steps : Syntax) : MacroM (TSyntax `term × Array (TSyntax `term × TSyntax `term)) := do
  -- inferSteps 结构实际是：inferStep (ppLine linebreak inferStep)*
  -- steps[0] = 第一个 inferStep
  -- steps[1] = (ppLine linebreak inferStep)* 的 node，但 .getArgs 后每个元素就是 inferStep
  let firstStep := steps[0]
  let restSteps := steps[1]
  -- 解析第一步
  let `(inferStep| $P:term => $Q:term := $prf1:term) := firstStep
    | Macro.throwError s!"infer: 第一步语法无效，kind: {firstStep.getKind}"
  let mut chain := #[(Q, prf1)]
  -- 解析后续步骤
  for i in [:restSteps.getArgs.size] do
    let step := restSteps[i]
    let `(inferStep| $_:term => $R:term := $prf:term) := step
      | Macro.throwError s!"infer: 推导步骤语法无效，kind: {step.getKind}"
    chain := chain.push (R, prf)
  return (P, chain)

script_recorder
"infer" steps:inferSteps : tactic => do
  -- 解析步骤
  let (init, chain) ← liftMacroM <|
    parseInferSteps steps
  -- Elaborate 初始命题
  let initExpr ← withMainContext do
    Lean.Elab.Tactic.elabTerm init none
  let initJson ← withMainContext <|
    ProofScript.Expr2JSON initExpr
  -- Elaborate 推导链的每一步（只录制 rhs 和 proof，不执行替换逻辑）
  let mut chainJson := #[]
  for (rhs, prf) in chain do
    -- 直接 elaborate rhs 和 prf（prf 中的 ?_ 在策略执行时由 infer tactic macro 处理）
    let rhsExpr ← withMainContext do
      Lean.Elab.Tactic.elabTerm rhs none
    -- 对于 prf，如果包含 ?_，我们只录制语法结构，不 elaborate
    -- 因为 ?_ 的实际值在运行时由 term macro 填充
    let prfJson ← withMainContext do
      if inferContainsSyntheticHole prf.raw then
        -- 包含 ?_，录制为特殊标记
        pure <| Json.mkObj [("kind", "hole")]
      else
        -- 不包含 ?_，正常 elaborate
        let prfExpr ← Lean.Elab.Tactic.elabTerm prf (some rhsExpr)
        recordRefsFromExpr prfExpr
        ProofScript.Expr2JSON prfExpr
    let rhsJson ← withMainContext <| ProofScript.Expr2JSON rhsExpr
    chainJson := chainJson.push (Json.mkObj [("rhs", rhsJson), ("proof", prfJson)])
  recordStep "infer"
    [("init", initJson), ("chain", Json.arr chainJson)]
    [] [] [] do
      evalTactic (← liftMacroM <| buildInferTactic steps.raw)
