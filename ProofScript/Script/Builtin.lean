import ProofScript.Config
import ProofScript.Script.Script
import ProofScript.References.Collect
import ProofScript.Extension.Components.Latex

open Lean
open Meta (MetaM whnf isProp inferType AltVarNames
           mkFreshExprMVar mkConstWithFreshMVarLevels
           withLetDecl withLocalDecl isDefEqGuarded)
open Elab (liftMacroM)
open Elab.Term (elabType elabTermEnsuringType)
open Elab.Tactic (evalTactic evalTacticAt elabTerm getMainGoal getFVarId
                       replaceMainGoal withMainContext)
open Parser.Term (hole syntheticHole)
open Parser.Tactic (tacticSeq)


namespace ProofScript


/-! ## Lean Native Tactics -/

script_macro
"change" equation:term : tactic => `(tactic| change $equation)

script_macro
"omega" : tactic => `(tactic| omega)

script_macro
"rfl" : tactic => `(tactic| rfl)

script_macro
"symm" : tactic => `(tactic| symm)

script_macro
"trivial" : tactic => `(tactic| trivial)


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
      throwError "to solve the goal of form `... → False`, please use `by_contra`"
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

script_macro
"provide" proof:term : tactic => `(tactic| exact $proof:term)

script_macro
"apply_h" lemma:term : tactic => `(tactic| apply $lemma:term)

script_macro
"apply_thm" thm:term : tactic => `(tactic| apply $thm:term)

script_macro
"simp" "only" "[" lemmas:term "]" : tactic => `(tactic| simp only [$lemmas:term])

script_macro
"rewrite" equation:term : tactic => `(tactic| (
  rewrite [$equation:term]
  try rfl
))

script_macro
"rewrite" "←" equation:term : tactic => `(tactic|(
  rewrite [← $equation:term]
  try rfl
))

script_macro
"unfold" definitions:(colGt ident)+ : tactic => `(tactic| unfold $definitions*)

script_macro (intro := [a])
"quot_induction" q:term "with" a:ident : tactic => `(tactic|
  refine Quot.inductionOn $q:term (fun $a:ident => ?_)
)


/-! ## Script-Strategy -/

script_elab (strategy := true)
"witness" : tactic => do
  let mvarId ← getMainGoal
  let goalExpr ← whnf (← mvarId.getType)
  if goalExpr.isAppOfArity ``Exists 2 then
    let mvarIds ← mvarId.apply (← mkConstWithFreshMVarLevels ``Exists.intro)
    match mvarIds with
    | [m₁, m₂] =>
      m₁.setTag `proof
      m₂.setTag `prep
      replaceMainGoal [m₁, m₂]
    | _ =>
      throwError "unexpected error occurred during executing `witness`"
  else
    throwError "`witness` can only be used with propositions beginning with `∃`"

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

script_elab (intro := [h], strategy := true)
"by_contra" h:ident : tactic => do
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
    evalTactic (← `(tactic| original_by_contra $h))
    let newMVarId ← getMainGoal
    newMVarId.setTag `proof
    replaceMainGoal [newMVarId]

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
"induction" n:ident : tactic => `(tactic|
  induction $n:ident
)

script_macro (clear := [n], strategy := true)
"complete_induction" n:ident : tactic => `(tactic|
  induction $n:ident using strongInductionOn
)


/-! ## 分类讨论 -/

/-- `by_cases h : p`：按命题 `p` 的真假分类讨论，产生 `caseI`（`h : p`）与
    `caseII`（`h : ¬p`）两个分支。 -/
script_elab (intro := [h], strategy := true)
"by_cases" h:ident ":" p:term : tactic => do
  evalTactic (← `(tactic| open Classical in refine if $h:ident : $p:term then ?caseI else ?caseII))


/-! ## Meta Data -/

script_macro (clear := [text])
"remark" text:str : tactic => `(tactic| skip)

script_macro (clear := [code])
"tex" code:str : tactic => `(tactic| skip)

script_macro (clear := [code])
"svg" code:str : tactic => `(tactic| skip)


/-! ## LaTeX Components -/

open ProofScript.Extension

private def defaultTikzMetadata : ComponentMetadata := { title := "TikZ" }

private def metadataFromOptional (metadata? : Option (TSyntax `ProofScript.Extension.componentMeta)) :
    Lean.Elab.Tactic.TacticM ComponentMetadata :=
  match metadata? with
  | some metadata =>
      match parseComponentMetadata metadata.raw with
      | .ok value => pure value
      | .error message => throwErrorAt metadata message
  | none => pure defaultTikzMetadata

private def recordLatexComponent (name : String) (metadata : ComponentMetadata) (code : String) :
    Lean.Elab.Tactic.TacticM Unit := do
  let svg ← compileLatexToSvg code
  recordStep name [
    ("metadata", componentMetadataJson metadata),
    ("language", Json.str "latex"),
    ("source", Json.str code),
    ("svg", Json.str svg)
  ] [] [] [] do
    evalTactic (← `(tactic| skip))

elab
"tikz" (ProofScript.Extension.componentMeta)? _code:str : tactic => do
  evalTactic (← `(tactic| skip))

script_recorder
"tikz" metadata:(ProofScript.Extension.componentMeta)? code:str : tactic => do
  let metadata ← metadataFromOptional metadata
  recordLatexComponent "tikz" metadata code.getString

script_elab (record := false)
"figure" _metadata:ProofScript.Extension.componentMeta _code:str : tactic => do
  evalTactic (← `(tactic| skip))

script_recorder
"figure" metadata:ProofScript.Extension.componentMeta code:str : tactic => do
  let metadata ←
    match parseComponentMetadata metadata.raw with
    | .ok value => pure value
    | .error message => throwErrorAt metadata message
  recordLatexComponent "figure" metadata code.getString

script_elab (record := false)
"table" _metadata:ProofScript.Extension.componentMeta _code:str : tactic => do
  evalTactic (← `(tactic| skip))

script_recorder
"table" metadata:ProofScript.Extension.componentMeta code:str : tactic => do
  let metadata ←
    match parseComponentMetadata metadata.raw with
    | .ok value => pure value
    | .error message => throwErrorAt metadata message
  recordLatexComponent "table" metadata code.getString

/-! ## 非形式化证明 `cause` -/

script_elab (clear := [cause])
"cause" cause:str : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  logWarningAt cause m!"`sorryAx` will be used to prove: {target}"
  evalTactic (← `(tactic| sorry))
macro "cause" cause:str : term => `(script_cause $cause:str)

/-! ## 局部断言 `have` -/

script_elab (intro := [h], strategy := true)
"have" h:ident ":" type:term : tactic => do
  let goal ← getMainGoal
  let type ← withMainContext (elabTerm type none)
  let proofMVar ← withMainContext (mkFreshExprMVar type)
  proofMVar.mvarId!.setTag `proof
  let restMVar ← goal.assert h.getId type proofMVar
  let (_, restMVar') ← restMVar.intro1P
  replaceMainGoal [restMVar', proofMVar.mvarId!]

/-! # `calc`：等式/不等式连续推导

直接委托 Lean 原生的 `calc` tactic（原生 tactic 已正确处理 `?_`——
`closeMainGoalUsing (checkNewUnassigned := false)` + `pushGoals`，把 `?_` 变成新的子目标），
使其能在 `:= script` 中使用。

录制格式仿照 `infer`：
- `init`: 第一行左侧的初始项
- `chain`: 列表，每个元素是 `{relation: 关系符, rhs: 右侧项, proof: := 后面的证明项}`
-/

/-- tactic 版 `calc`：委托 Lean 原生的 `calc` tactic。
    用 `macro` 而非 `script_macro`，与 `infer` 的 tactic 版保持一致——本体直接展开为原生
    `calc`（原生 kind `Lean.calcTactic`），录制版由下方手工实现。 -/
script_macro (record := false)
"calc" steps:calcSteps : tactic => do
  `(tactic| calc $steps:calcSteps)

/-! ### 录制版 `_calc`（手动实现）-/

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
    - `chain`: 列表，每个元素 `{relation, rhs, proof}`；`proof` 含 `?_` 时录 `{"kind": "hole"}`
    本体行为与 tactic `calc` 一致（委托原生 `calc` tactic）。 -/
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

/-! # `infer`：连续推导（have 语义）

结构仿 `calc`（连接符换成 `=>`），用于「因为…所以…进而有…」的**命题连续推导**。每一行
`lhs => rhs := prf`：

- 第一行 `P => Q := prf`：`prf` 直接给出 `Q` 的证明项，且其中必须包含一个类型为 `P` 的
  子项（否则 `P` 完全失去意义）。第一行不允许出现 `?_`。
- 后续行 `_ => Q := MyTheorem arg ?_`：`?_` 指代上一步推导出的结论，且必须有且仅有一个；
  `_` 也可换成上一步右侧的命题（自动校验链条衔接）。

**tactic 语义（逐步 `have` 式）**：每一行右侧命题都会作为匿名条件加入上下文。后续行的
`?_` 引用前一行刚加入的匿名条件。最后立刻尝试用最后一条条件闭合目标；若目标不是最后一行的
结论，则所有推导步骤都保留在上下文中供后续 tactic 使用。

**项语义**：`infer` 同时保留了 `term` 版本（求值出 `T` 的证明项），供 `provide` / `exact`
等需要项的场合使用。
-/

/-! ### 语法
    用**单个** `withPosition` 包裹整个步骤序列：`withPosition` 的 savedPos 取「关键字
    skip 尾随空白后的位置」=「第一步起始列」，`colGe` 据此要求「每一步的缩进列 ≥ 第一步缩进」，
    从而可靠地区分「更深的步骤」与「同缩进的后续 tactic」（后者列 < 第一步列，`colGe` 失败终止块）。
    若再套一层 `withPosition((ppLine linebreak inferStep)*)`，savedPos 会被覆盖为「第一步后第一个
    token 列」（单步时即后续 tactic 列），导致单步后跟 tactic 被误当成步骤。 -/

syntax inferStep := ppIndent(colGe term " => " term " := " term)
syntax inferSteps := withPosition(ppLine inferStep (ppLine linebreak inferStep)*)

/-! ### 第一行的深度检查 -/

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

/-! ### `?_` 替换（恰好一个） -/

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

/-! ### 项层 `infer`（链计算） -/

/-- 项版 `infer`：把后续步骤的 `?_` 依次替换为上一步结论，并对「显式左侧命题」与「本行右侧命题」
    分别加类型标注 `(前值 : L)` / `(证明 : R)` 以校验链条衔接与各行类型。 -/
script_macro (record := false)
"infer" steps:inferSteps : term => do
  match steps with
  | `(inferSteps|
        $step0:inferStep
        $rest*) => do
      let `(inferStep| $P:term => $Q:term := $prf1:term) := step0
        | Macro.throwError "infer: 第一步语法无效"
      let mut body : TSyntax `term ← `(infer_check_first $P:term => $Q:term := $prf1:term)
      for step in rest do
        let `(inferStep| $L:term => $R:term := $prf:term) := step
          | Macro.throwError "infer: 推导步骤语法无效"
        let prev ← if inferIsHoleTerm L then pure body else `(($body : $L))
        let prf' ← inferReplaceSingleHole prf.raw prev
        body ← `(($prf' : $R))
      return body
  | _ => Macro.throwError "infer: 需要至少一个推导步骤"

/-! ### tactic 层 `infer`（逐步匿名 have 语义） -/

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

/-- tactic 版 `infer`：每个推导结论都作为匿名条件加入上下文。 -/
script_macro (record := false)
"infer" steps:inferSteps : tactic => do
  buildInferTactic steps.raw

/-! ### 录制版 `_script_infer`（手动实现）-/

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

/-- 录制版 `_script_infer`：录制初始命题 + 推导链的每一步。
    - `init`: 第一行左侧的初始命题
    - `chain`: 列表，每个元素是 `{rhs: 右侧命题, proof: := 后面的证明项}`
    本体行为与 tactic `infer` 一致（逐步匿名 `have`，最后 `try exact this`）。 -/
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
    -- 直接 elaborate rhs 和 prf（prf 中的 ?_ 在实际执行时由 infer term macro 处理）
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
  -- 录制
  recordStep "infer"
    [("init", initJson), ("chain", Json.arr chainJson)]
    [] [] [] do
      evalTactic (← liftMacroM <| buildInferTactic steps.raw)
