import ProofScript.Script.Script

open Lean
open Lean.Elab.Tactic (evalTactic)
open Lean.Parser.Tactic (tacticSeq)

namespace ProofScript

/-! ## `embed`：嵌入定理证明

`embed <term> as <ident>` 把 `<term>`（一个**定理应用**，如 `dvd_trans h_ab h_bc`）的结论
作为局部假设引入上下文，等价于 `have <ident> := <term>`。`<term>` 必须是 `const` 头的应用。

录制版 `_embed` 在应用 `#theorem` 声明的 script 定理时，保存其完整 proof JSON 的
`$resource` 引用，而不在编译期重放并复制证明树。调用方实参仍通过 `args` 和 `argKinds`
（每项 `"data"`/`"proof"`）记录，供消费端按 proof/data 分类代入。若目标不是 script 定理，
则保留其完整表达式引用。
-/

/-! ### 本体（非录制）：校验是定理应用，然后 `have h := term` -/

script_elab (recorder := exclusive)
"embed" proof:term "as" h:ident : tactic => do
  let e ← Lean.Elab.Tactic.withMainContext <| Lean.Elab.Tactic.elabTerm proof none
  let e ← Lean.instantiateMVars e
  unless e.getAppFn.isConst do
    throwError "embed: 参数必须是定理应用（如 `dvd_trans h_ab h_bc`）"
  evalTactic (← `(tactic| have $h:ident := $proof:term))

/-! ### 录制版 `_embed` -/

/-- 判断一个类型 `t` 是否为命题（`isProp`）。用于把 binder `(n : t)` 分类为 proof（`t` 是命题）
    还是 data（`t` 非命题）；对实参则传它的 `inferType`。`isProp` 失败（隐式参数未解出的 mvar）
    时按 data 处理，避免误判。 -/
private def isProofBinderType (t : Expr) : MetaM Bool :=
  try
    Lean.Meta.isProp t
  catch _ => pure false

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
      -- ③ Reference the complete exported proof instead of replaying and duplicating it.
      let env ← getEnv
      let proofJson ← match findScriptArtifact env c with
        | some artifact => do
            let proofPath := System.FilePath.mk artifact.proofPath
            unless ← proofPath.pathExists do
              throwError m!"embed: proof resource for `{c}` is missing at '{proofPath}'"
            Extension.existingTextResource proofPath "application/vnd.proof-script.proof+json"
        | none => Lean.Elab.Tactic.withMainContext <| Expr2JSON e
      -- ④ 引入 h
      evalTactic (← `(tactic| have $h:ident := $proof:term))
      let hJson ← serializeParamRaw (.one h.raw)
      -- ⑤ 参数记录器 → 主 box
      let fields := [("h", hJson), ("type", typeJson), ("theorem", Json.str c.toString),
                     ("args", argsJson), ("argKinds", argKindsJson), ("proof", proofJson)]
      addtoBox boxName (paramsRecJson "embed" fields)
      setPrevStep ("embed", fields)

end ProofScript
