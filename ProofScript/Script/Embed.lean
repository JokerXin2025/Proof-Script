import ProofScript.Script.Script

open Lean
open Lean.Elab.Tactic (evalTactic)
open Lean.Parser.Tactic (tacticSeq)

namespace ProofScript

/-! ## `embed`：嵌入定理证明

`embed <term> as <ident>` 把 `<term>`（一个**定理应用**，如 `dvd_trans h_ab h_bc`）的结论
作为局部假设引入上下文，等价于 `have <ident> := <term>`。`<term>` 必须是 `const` 头的应用。

录制版 `_embed` 额外做「证明嵌入」：若 `<term>` 的头常量是某个 `#theorem` 声明过的 script
定理，则从 ScriptDB 取回它的**原始脚本**，在当前证明的子 box 里以录制模式重放其每一步，
使导出 JSON 里自然嵌入了被应用定理的完整证明树（含其概略分支）；否则退回录一个不透明项。

重放采用「泛型重放」：被嵌入定理的每个 forall binder 都用 `withLocalDecl` 引入为新假设
（用定理自身 binder 名），子目标因此**自包含**（只引用 fresh fvar）。调用方实参通过 `embed`
步骤的 `args`（实参列表）与 `argKinds`（每项 `"data"`/`"proof"`，用 `isProp` 分类）字段记录，
供渲染端按 proof/data 分类代入。

> 注：这里曾尝试「真正代入」（把 data 实参 `b.instantiate1 arg` 代入子目标结论，或
> `withLetDecl` 绑到调用方实参），使子目标直接引用调用方 fvar / 实参。但这样构造的子目标
> 在 `evalTacticAt` 重放时（`trivial`/`provide` 等任意策略）会触发 Lean 内部
> `Lean.Expr.mvarId! "mvar expected"` panic（位于 `SynthInstance.consume` 的
> `subgoals.filterM (·.mvarId!.isAssigned)`，即类型类合成路径），无法用 `saveState/restore`
> 规避。因此保留自包含的泛型重放，代入交由渲染端依据 `args`/`argKinds` 完成。
-/

/-! ### 本体（非录制）：校验是定理应用，然后 `let h := term` -/

script_elab (recorder := exclusive)
"embed" proof:term "as" h:ident : tactic => do
  let e ← Lean.Elab.Tactic.withMainContext <| Lean.Elab.Tactic.elabTerm proof none
  let e ← Lean.instantiateMVars e
  unless e.getAppFn.isConst do
    throwError "embed: 参数必须是定理应用（如 `dvd_trans h_ab h_bc`）"
  evalTactic (← `(tactic| let $h:ident := $proof:term))

/-! ### 录制版 `_embed` -/

/-- 判断一个类型 `t` 是否为命题（`isProp`）。用于把 binder `(n : t)` 分类为 proof（`t` 是命题）
    还是 data（`t` 非命题）；对实参则传它的 `inferType`。`isProp` 失败（隐式参数未解出的 mvar）
    时按 data 处理，避免误判。 -/
private def isProofBinderType (t : Expr) : MetaM Bool :=
  try
    Lean.Meta.isProp t
  catch _ => pure false

/-- 在 `fullType` 的每个 forall binder 被 `withLocalDecl` 引入为新假设的**作用域内**创建子目标
    mvar。关键：`mkFreshExprMVar` 必须放在 `withLocalDecl` 内部调用，才能把这些新假设捕获进
    mvar 的 local context；若在外部（`withLocalDecl` 弹出后）调用，context 已恢复为调用方
    上下文，而结论类型里的新 fvar 会悬垂（`unknown free variable`）。

    以「定理自身的泛型证明」形式重放：参数作为新假设（用定理自身 binder 名），
    不依赖调用方名字匹配；调用方实参通过 `embed` 步骤的 `args`/`argKinds` 字段记录，
    供渲染端按 data/proof 分类代入。 -/
private partial def mkReplayGoalAux (fullType : Expr)
                                    : MetaM Expr := do
  match fullType with
  | .forallE n t b bi =>
      Lean.Meta.withLocalDecl n bi t fun x =>
        mkReplayGoalAux (b.instantiate1 x)
  | _ => Lean.Meta.mkFreshExprMVar fullType

private def mkReplayGoal (fullType : Expr) : MetaM Expr :=
  mkReplayGoalAux fullType

script_recorder
"embed" proof:term "as" h:ident : tactic => do
      let tag ← currentBoxTag.get
      let boxName := Name.mkSimple tag
      -- ① 前导目标记录器 → 主 box
      let goalJson ← Lean.Elab.Tactic.withMainContext <| Expr2JSON (← GetGoal) { withTypes := true }
      let prevOpt ← getPrevStep
      addtoBox boxName (Json.mkObj ([("_goal_", goalJson)] ++ prevFields prevOpt))
      -- ② elaborate 定理应用 → 头常量、结论类型、参数
      let e ← Lean.Elab.Tactic.withMainContext <| Lean.Elab.Tactic.elabTerm proof none
      let e ← Lean.instantiateMVars e
      let fnExpr := e.getAppFn
      let some (c, _) := fnExpr.const?
        | throwError "embed: 参数必须是定理应用（如 `dvd_trans h_ab h_bc`）"
      let conclType ← Lean.Elab.Tactic.withMainContext <| Lean.Meta.inferType e
      let typeJson ← Lean.Elab.Tactic.withMainContext <| Expr2JSON conclType
      let argsJson ← Json.arr <$> (e.getAppArgs.mapM fun a =>
        Lean.Elab.Tactic.withMainContext <| Expr2JSON a)
      let argKindsJson ← Json.arr <$> (e.getAppArgs.mapM fun a => do
        Lean.Elab.Tactic.withMainContext <| do
          let isProof ← try
            isProofBinderType (← Lean.Meta.inferType a)
          catch _ => pure false
          pure (Json.str (if isProof then "proof" else "data")))
      -- ③ 查 ScriptDB：有脚本则重放，否则退回不透明项
      let proofJson ← match findScript (← getEnv) c with
        | some data => do
            let (_, stmts) := scriptDataParts data
            let recTactics ← collectRecordTactics stmts
            let seq' : TSyntax ``tacticSeq := ⟨buildTacticSeq recTactics⟩
            -- 子目标 = 被嵌入定理的结论类型（其每个 binder 已作为新假设引入，见 mkReplayGoal）。
            let fullType ← Lean.Elab.Tactic.withMainContext <| Lean.Meta.inferType fnExpr
            let subGoal ← Lean.Elab.Tactic.withMainContext <| mkReplayGoal fullType
            let subTag := tag ++ "_embed_" ++ h.getId.toString
            pushBoxTag subTag
            let subGoals ← Lean.Elab.Tactic.evalTacticAt seq' subGoal.mvarId!
            popBoxTag
            unless subGoals.isEmpty do
              throwError "embed: 被嵌入定理的证明未闭合（剩余目标）"
            let subName := Name.mkSimple subTag
            let boxes ← JSON_boxes.get
            let proofArr := match boxes.findIdx? (fun (b, _) => b == subName) with
              | some idx => boxes[idx]!.2
              | none => #[]
            match boxes.findIdx? (fun (b, _) => b == subName) with
              | some idx => JSON_boxes.set (boxes.set! idx (subName, #[]))
              | none => pure ()
            pure (Json.arr proofArr)
        | none => Lean.Elab.Tactic.withMainContext <| Expr2JSON e
      -- ④ 引入 h
      evalTactic (← `(tactic| let $h:ident := $proof:term))
      let hJson ← serializeParamRaw (.one h.raw)
      -- ⑤ 参数记录器 → 主 box
      let fields := [("h", hJson), ("type", typeJson), ("theorem", Json.str c.toString),
                     ("args", argsJson), ("argKinds", argKindsJson), ("proof", proofJson)]
      addtoBox boxName (paramsRecJson "embed" fields)
      setPrevStep ("embed", fields)

end ProofScript
