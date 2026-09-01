import ProofScript

@[theorem_info (name := "Referenced declaration", label := "referenced-declaration")]
theorem declarationModeReference (P : Prop) (h : P) : P := h

/-- error: `:= by` cannot use Proof-Script tactics; use ordinary Lean tactics -/
#guard_msgs in
@theorem rejectedScriptTactic : True := by
  script_trivial

@theorem recordedTheorem : True := script
  trivial

@lemma @[theorem_info (name := "Recorded lemma", label := "recorded-lemma")]
  recordedLemma : True := script
  trivial

@theorem tacticTheorem (P : Prop) (h : P) : P := by
  exact h

-- Native tactics must remain available in ordinary Lean proofs even when the
-- corresponding Proof-Script strategy is registered.
@theorem ordinaryTrivial : True := by
  trivial

@theorem ordinaryRfl (n : Nat) : n = n := by
  rfl

@lemma @[theorem_info (name := "Tactic lemma", label := "tactic-lemma")]
  tacticLemma (P : Prop) (h : P) : P := by
  exact declarationModeReference P h

@references
page_end
