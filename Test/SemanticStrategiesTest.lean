import ProofScript

/- These examples rely on the old unrestricted `provide` behavior and recorded JSON shape.
   Re-enable them after their proof scripts are redesigned for the restricted tactics.

/-! Tests for the first semantic strategies added for the Sphere-Packing Demo. -/

#theorem obtain_witness_test (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n := script
  obtain_exist ⟨n, hn⟩ := h
  witness
  | data => provide n
  | proof => apply_h hn

#theorem cases_by_test (P Q : Prop) (h : P ∨ Q) : P ∨ Q := script
  cases_by h
  | left =>
    prove_left
    apply_h hp
  | right =>
    prove_right
    apply_h hq

theorem cases_by_bang_test (P Q : Prop) (h : P ∨ Q) : True := script
  cases_by! h
  | goalI => trivial
  | goalII => trivial

#theorem unpack_iff_test (P Q : Prop) (h : P ↔ Q) : P ↔ Q := script
  unpack_iff ⟨hForward, hBackward⟩ := h
  split_iff
  | suffice hp =>
    apply_h hForward
    apply_h hp
  | necess hq =>
    apply_h hBackward
    apply_h hq

theorem cases_on_prop_test (P : Prop) : P ∨ ¬ P := script
  cases_on P
  | true h =>
    prove_left
    apply_h h
  | false h =>
    prove_right
    apply_h h

theorem cases_on_data_test (n : Nat) : n = 0 ∨ ∃ k, n = k + 1 := script
  cases_on n
  | zero =>
    prove_left
    rfl
  | succ k =>
    prove_right
    witness
    | data => provide k
    | proof => rfl

theorem ext_fun_test (f g : Nat → Nat) (h : ∀ n, f n = g n) : f = g := script
  ext_fun n
  apply_h h
-/
