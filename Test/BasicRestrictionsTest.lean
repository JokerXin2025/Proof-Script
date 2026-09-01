import ProofScript

example (P : Prop) (h : P) : P := script
  assumption

example : ∃ n : Nat, n = 0 := script
  witness
  | data => provide 0
  | proof => rfl

example (P : Prop) (h : P) : P := script
  assumption

example : True := script
  trivial

example (n : Nat) : 0 + n + 0 = n := script
  simp_only [Nat.zero_add Nat.add_zero]

example (n : Nat) (h : 0 + n = n) : 0 + n + 0 = n := script
  simp_only [Nat.zero_add Nat.add_zero] at h ⊢

example (n : Nat) (h : 0 + n = n) : 0 + n + 0 = n := script
  simp_only [Nat.zero_add Nat.add_zero] at *

example (n : Nat) (h : 0 + n = n) : 0 + n = n := script
  rewrite [Nat.zero_add] at h ⊢

example (n : Nat) (h : 0 + n = n) : n = n := script
  rewrite [Nat.zero_add] at *

example : ∃ n : Nat, n = 0 := script
  provide 0
