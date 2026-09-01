import ProofScript

theorem projection_test (P : Prop) : ¬ (P ∧ ¬ P) := script
  contra h
  | proof =>
    unpack_and ⟨hP, hNP⟩ := h
    contradiction

theorem nested_application_test (P : Prop) (h : P) : P := script
  assumption

theorem named_projection_test (P Q : Prop) (h : P ∧ Q) : P := script
  unpack_and ⟨hP, _hQ⟩ := h
  assumption

theorem numeric_term_test : 1 + 1 = 2 := script
  rfl

theorem string_argument_test (P : Prop) (h : P) : P := script
  remark "field .1 and number 42"
  assumption

theorem native_name_choice_test (P : Prop) : P ∨ ¬ P := script
  cases_on P
  | true h =>
    left
    assumption
  | false h =>
    right
    assumption

theorem recorded_projection_test (P : Prop) : ¬ (P ∧ ¬ P) := script
  contra h
  | proof =>
    unpack_and ⟨hP, hNP⟩ := h
    contradiction

theorem recorded_arguments_test (P Q : Prop) (h : P ∧ Q) : P := script
  remark "field .1 and number 42"
  unpack_and ⟨hP, _hQ⟩ := h
  assumption
