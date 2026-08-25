import ProofScript

project_info {
  title := "Cross Module Paper",
  authors := "Carol"
}

@[theorem_info (tags := "cross")]
theorem cross_lemma (P : Prop) (h : P) : P := h
