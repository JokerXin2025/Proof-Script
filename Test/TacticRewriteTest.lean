import ProofScript

theorem projection_test (P : Prop) : ¬ (P ∧ ¬ P) := script
  by_contra h
  | proof => provide (h.2 h.1)

theorem nested_application_test (P : Prop) (h : P) : P := script
  provide (id (id h))

theorem named_projection_test (P Q : Prop) (h : P ∧ Q) : P := script
  provide h.left

theorem numeric_term_test : 1 + 1 = 2 := script
  provide rfl

theorem string_argument_test (P : Prop) (h : P) : P := script
  remark "field .1 and number 42"
  provide h

theorem native_name_choice_test (P : Prop) : P ∨ ¬ P := script
  by_cases h : P
  | caseI => provide (Or.inl h)
  | caseII => provide (Or.inr h)

#theorem recorded_projection_test (P : Prop) : ¬ (P ∧ ¬ P) := script
  by_contra h
  | proof => provide (h.2 h.1)

#theorem recorded_arguments_test (P Q : Prop) (h : P ∧ Q) : P := script
  remark "field .1 and number 42"
  provide (id h.left)
