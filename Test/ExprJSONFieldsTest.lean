import ProofScript

#theorem exprJSONFields
    (P : Prop) (h : P) (x : Nat) : P := script
  apply_h h
