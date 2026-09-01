import ProofScript.Utils
import ProofScript.Script.Core
import ProofScript.Script.JsonBox
import ProofScript.Script.ExprJSON
import ProofScript.References.Collect

open Lean (Json Name Syntax)
open Lean.Elab.Tactic (TacticM withMainContext elabTerm)


namespace ProofScript

/-!
# 录制辅助函数 (Recording Helpers)

每个步骤产生两个 JSON 对象：
1. **前导目标记录器** — 始终在步骤最前面执行：
   `{"_goal_": <当前目标 AST>}`
   若上一步有参数，额外包含 `"prev_<参数名>": <上一步参数值>` 字段。
2. **参数记录器** — 步骤本体执行后写入：
   `{"_step_": "<策略名>", "<参数名>": <参数值AST>, ...}`

- **`intro` 参数**（策略引入的新 fvar）：只能在执行**之后** elaborate + 序列化，否则
  ident 尚不存在，`elabTerm` 报 `unknown identifier`。值直接作为该键的值。
- **`clear` 参数**（策略删除的原 fvar）：只能在执行**之前** elaborate + 序列化，否则
  ident 已被清除，同样无法解析。值直接作为该键的值。
- **`neither` 参数**（既不在 `intro` 也不在 `clear`）：执行前、执行后**各序列化一次**——
  这些策略很可能修改参数引用的 fvar 状态。前后两份值包成
  `{"<名>": {"before": <前值>, "after": <后值>}}`。
-/

/-- 可 elaborate 的 `term`/`ident`/`ident+` 参数的原始语法：
    - `one`：单个 `term`/`ident`（`elabTerm` → 单棵表达式树）；
    - `many`：`ident+`（`many1 ident`，逐个 `elabTerm` → `Json.arr` 树数组）。 -/
inductive ParamRaw where
| one (raw : Syntax)
| many (raws : Array Syntax)

/-- 把 `term`/`ident`/`ident+` 参数的原始语法在当前主目标上下文中 elaborate，再递归导出整棵
    表达式树（`ident+` 导出树数组）。序列化时机由调用方决定（执行前 = `clear`/`neither` 的
    前值，执行后 = `intro`/`neither` 的后值），保证 ident 解析到正确时点的 local context 里的 fvar。 -/
structure ParamSnapshot where
  expressions : Array Lean.Expr
  json : Json

private def elaborateParamRaw : ParamRaw → TacticM (Array Lean.Expr)
  | .one raw => do
      let expression ← withMainContext <| elabTerm raw none
      pure #[expression]
  | .many raws => do
      let mut expressions := #[]
      for raw in raws do
        expressions := expressions.push (← withMainContext <| elabTerm raw none)
      pure expressions

private def snapshotParamRaw (raw : ParamRaw) : TacticM ParamSnapshot := do
  let expressions ← elaborateParamRaw raw
  let json ← match expressions.size with
    | 0 => pure (Json.arr #[])
    | 1 => withMainContext <| Expr2JSON expressions[0]!
    | _ => do
        let mut values := #[]
        for expression in expressions do
          values := values.push (← withMainContext <| Expr2JSON expression)
        pure (Json.arr values)
  pure { expressions, json }

private def recordSnapshotRefs (snapshot : ParamSnapshot) : TacticM Unit := do
  for expression in snapshot.expressions do
    recordRefsFromExpr expression

def serializeParamRaw (raw : ParamRaw) : TacticM Json := do
  return (← snapshotParamRaw raw).json
/-- 执行**后**序列化参数（`intro` 参数与 `neither` 参数的后值）。
    若策略执行后已无主目标（如 `provide`/`rewrite` 解决了全部子目标），无法再设上下文
    elaborate，此时返回 `none`——调用方对 `neither` 参数退回到「前值」（此类参数在
    解决目标的步骤中不会被修改，前后一致）。 -/
private def snapshotPostParam (pr : ParamRaw) : TacticM (Option ParamSnapshot) := do
  tryCatch (some <$> snapshotParamRaw pr) (fun _ => pure none)

/-- 将上一步参数展平为 `prev_` 前缀的键值对列表。无上一步时返回空列表。 -/
def prevFields  (prevOpt : Option (String × List (String × Json)))
                : List (String × Json) :=
  match prevOpt with
  | some (_, fields) => fields.map fun (k, v) => ("prev_" ++ k, v)
  | none => []

/-- 构建参数记录器的 JSON 对象。所有参数字段直接放在顶层，与 `_step_` 平级。 -/
def paramsRecJson (stepName : String)
                  (extraFields : List (String × Json)) :=
  Json.mkObj (("_step_", Json.str stepName) :: extraFields.map fun (k, v) => (k, v))

/-- 概略策略在主 box 中的临时占位符。分支录制结束后，`mergeStrategyBoxes` 会在原位
    替换它，保证策略节点位于策略后的普通续接步骤之前。 -/
def strategyPlaceholderJson (stepName : String) :=
  Json.mkObj [("_pending_strategy_", Json.str stepName)]

/-- 序列化 `neither` 参数为 `{"before": 前值, "after": 后值}`。
    前值在执行前已序列化（`beforeJson`）；后值在执行后序列化，若执行后已无目标则退回前值。 -/
private def serializeBoth (before : ParamSnapshot)
                          (after : Option ParamSnapshot) : Json :=
  Json.mkObj [("before", before.json),
              ("after", after.map (·.json) |>.getD before.json)]

/-- 录制单步策略。

    参数 `stepName`：策略名。
    参数 `inlineFields`：`str` 字面量参数，已在生成代码里内联序列化。
    参数 `preTerms`：`clear` 参数，执行前 elaborate，键名即参数名。
    参数 `postTerms`：`intro` 参数，执行后 elaborate，键名即参数名。
    参数 `bothTerms`：`neither` 参数，执行前、后各 elaborate 一次，
        合并为 `{"before": …, "after": …}`。
    参数 `action`：策略执行体（`evalTactic` 调用 macro 版本）。

    实现：
    1. 前导目标记录器：当前目标 AST + 上一步参数 → JSON 写入 box
    2. 执行前序列化 `preTerms`（clear）与 `bothTerms` 的前值
    3. 执行 action
    4. 执行后序列化 `postTerms`（intro）与 `bothTerms` 的后值
    5. 参数记录器：当前步骤名 + 全部参数 → JSON 写入 box
    6. 更新 prevStepRef -/
def recordStep  (stepName : String)
                (inlineFields : List (String × Json))
                (preTerms : List (String × ParamRaw))
                (postTerms : List (String × ParamRaw))
                (bothTerms : List (String × ParamRaw))
                (action : TacticM Unit)
                : TacticM Unit := do
  let tag ← currentBoxTag.get
  let boxName := Name.mkSimple tag
  -- ① 前导目标记录器（始终最先执行）
  --    `withMainContext` 设置主目标 local context，确保 goal 里的 fvar（如 `case` 分支引入的
  --    `induction` 变量）能经 `fvarId.getDecl` 正确序列化，避免「state 泄漏」到上一层 context。
  let goalJson ← withMainContext <|
    Expr2JSON (← GetGoal) { withTypes := true }
  let prevOpt ← getPrevStep
  let goalObj := Json.mkObj ([("_goal_", goalJson)] ++ prevFields prevOpt)
  addtoBox boxName goalObj
  -- ② 执行前序列化（clear 参数 + neither 参数的前值）
  let preElab ← preTerms.mapM fun (n, pr) => do
    let snapshot ← snapshotParamRaw pr
    if ← referencesEnabled then recordSnapshotRefs snapshot
    return (n, snapshot.json)
  let bothBefore ← bothTerms.mapM fun (n, pr) => do
    let snapshot ← snapshotParamRaw pr
    if ← referencesEnabled then recordSnapshotRefs snapshot
    return (n, snapshot)
  -- ③ 执行策略本体
  action
  -- ④ 执行后序列化（intro 参数 + neither 参数的后值；执行后已无目标则跳过/退回前值）
  let postElab ← postTerms.mapM fun (n, pr) => do
    match (← snapshotPostParam pr) with
    | some snapshot => return some (n, snapshot.json)
    | none => return none
  let bothFields ← bothTerms.mapM fun (n, pr) => do
    let before := (bothBefore.lookup n).getD { expressions := #[], json := Json.null }
    return (n, serializeBoth before (← snapshotPostParam pr))
  -- ⑤ 参数记录器：内联 + clear + intro + neither（before/after），全部参数合并写入
  let fields := inlineFields ++ preElab ++ postElab.filterMap id ++ bothFields
  addtoBox boxName (paramsRecJson stepName fields)
  -- ⑥ 更新 prevStepRef 供下一步使用
  setPrevStep (stepName, fields)

/-- 录制概略策略（如 `induction`、`split_and`，使用三级 box 模型）。
    参数 `stepName`：策略名称。
    参数 `nodes`：分支名列表（如 `["zero", "succ"]`）。
    参数 `inlineFields`/`preTerms`/`postTerms`/`bothTerms`：同 `recordStep`，写入 info 子 box。
    参数 `action`：执行策略本身（产生多分支子目标）。
    实现：
    1. 前导目标记录器 → 主 box
    2. 执行前序列化 `preTerms` + `bothTerms` 前值
    3. 启动策略分支
    4. 执行 action
    5. 执行后序列化 `postTerms` + `bothTerms` 后值
    6. 参数记录器 → `{tag}_info` 子 box
    7. 更新 prevStepRef -/
def recordStrategy (stepName : String) (nodes : List String)
                   (inlineFields : List (String × Json))
                   (preTerms : List (String × ParamRaw))
                   (postTerms : List (String × ParamRaw))
                   (bothTerms : List (String × ParamRaw))
                   (action : TacticM Unit)
                   : TacticM Unit := do
  let tag ← currentBoxTag.get
  let boxName := Name.mkSimple tag
  -- ① 前导目标记录器 → 主 box（`withMainContext` 保证 goal fvar 可序列化，同 `recordStep`）
  let goalJson ← withMainContext <|
    Expr2JSON (← GetGoal) { withTypes := true }
  let prevOpt ← getPrevStep
  let goalObj := Json.mkObj ([("_goal_", goalJson)] ++ prevFields prevOpt)
  addtoBox boxName goalObj
  addtoBox boxName (strategyPlaceholderJson stepName)
  -- ② 执行前序列化（clear 参数 + neither 参数的前值，如 `induction n` 的归纳变量）
  let preElab ← preTerms.mapM fun (n, pr) => do
    let snapshot ← snapshotParamRaw pr
    if ← referencesEnabled then recordSnapshotRefs snapshot
    return (n, snapshot.json)
  let bothBefore ← bothTerms.mapM fun (n, pr) => do
    let snapshot ← snapshotParamRaw pr
    if ← referencesEnabled then recordSnapshotRefs snapshot
    return (n, snapshot)
  -- ③ 启动策略分支（改变 currentBoxTag，但 info 子 box 用捕获的 `tag` 定位，不受影响）
  startStrategy tag nodes
  -- ④ 执行策略本体
  action
  -- ⑤ 执行后序列化（intro 参数 + neither 参数的后值，如 `cases_on p` 的 `h`）
  let postElab ← postTerms.mapM fun (n, pr) => do
    match (← snapshotPostParam pr) with
    | some snapshot => return some (n, snapshot.json)
    | none => return none
  let bothFields ← bothTerms.mapM fun (n, pr) => do
    let before := (bothBefore.lookup n).getD { expressions := #[], json := Json.null }
    return (n, serializeBoth before (← snapshotPostParam pr))
  -- ⑥ 参数记录器 → info 子 box
  let fields := inlineFields ++ preElab ++ postElab.filterMap id ++ bothFields
  let infoTag := tag ++ "_info"
  addtoBox (Name.mkSimple infoTag) (paramsRecJson stepName fields)
  -- ⑦ 更新 prev
  setPrevStep (stepName, fields)

end ProofScript
