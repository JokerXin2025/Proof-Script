import ProofScript

#theorem exprJSONFields
    (P : Prop) (h : P) (x : Nat) : P := script
  provide (let _sum := x + x; id h)
