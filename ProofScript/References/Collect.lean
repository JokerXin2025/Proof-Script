import ProofScript.References.Config
import ProofScript.References.Metadata
import ProofScript.References.State

open Lean
open Elab.Tactic (TacticM)


namespace ProofScript


/-- 全常量 + 过滤：收集表达式中全部常量，只录入带 `theorem_info` 元数据的声明。
    关闭 `proofScript.references.enabled` 时立即返回，不遍历表达式、不查询环境扩展。 -/
def recordRefsFromExpr  (expr : Expr)
                        : TacticM Unit := do
  unless ← referencesEnabled do return
  let env ← getEnv
  for c in Lean.Expr.getUsedConstants expr do
    if let some info := findTheoremInfo env c then
      addTheoremRef { name := c, info := info }


end ProofScript
