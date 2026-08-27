import ProofScript

example : ∃ n : Nat, n = 0 := by
  witness
  case data => provide 0
  case proof => rfl

example (P : Prop) (h : P) : P := by
  fail_if_success provide h
  fail_if_success apply_thm h
  apply_h h

example : Nat := by
  fail_if_success provide 0
  exact 0

example : True := by
  fail_if_success apply_h True.intro
  apply_thm True.intro

example (n : Nat) : 0 + n + 0 = n := by
  simp_only [Nat.zero_add Nat.add_zero]
