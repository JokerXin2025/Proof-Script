import Lean


namespace ProofScript


/-- 控制 `#theorem`/`#lemma` 是否自动采集被引用定理的信息。 -/
register_option proofScript.references.enabled : Bool := {
  defValue := true
  descr := "enable automatic theorem-reference collection during Proof-Script recording"
}

/-- 查询当前选项中是否启用了文献引用采集。 -/
def referencesEnabled {m : Type → Type} [Monad m] [Lean.MonadOptions m] : m Bool := do
  return (← Lean.getOptions).getBool `proofScript.references.enabled true


end ProofScript
