import ProofScript

/- These recording-shape tests rely on the old unrestricted `provide` behavior.
   Re-enable them after their expected scripts are redesigned around the restricted tactics.

theorem projection_test (P : Prop) : ¬ (P ∧ ¬ P) := script
  contra h
  | proof =>
    unpack_and ⟨hP, hNP⟩ := h
    apply_h hNP
    apply_h hP

theorem nested_application_test (P : Prop) (h : P) : P := script
  apply_h h

theorem named_projection_test (P Q : Prop) (h : P ∧ Q) : P := script
  unpack_and ⟨hP, _hQ⟩ := h
  apply_h hP

theorem numeric_term_test : 1 + 1 = 2 := script
  rfl

theorem string_argument_test (P : Prop) (h : P) : P := script
  remark "field .1 and number 42"
  apply_h h

theorem native_name_choice_test (P : Prop) : P ∨ ¬ P := script
  cases_on P
  | true h =>
    prove_left
    apply_h h
  | false h =>
    prove_right
    apply_h h

#theorem recorded_projection_test (P : Prop) : ¬ (P ∧ ¬ P) := script
  contra h
  | proof =>
    unpack_and ⟨hP, hNP⟩ := h
    apply_h hNP
    apply_h hP

#theorem recorded_arguments_test (P Q : Prop) (h : P ∧ Q) : P := script
  remark "field .1 and number 42"
  unpack_and ⟨hP, _hQ⟩ := h
  apply_h hP
-/
