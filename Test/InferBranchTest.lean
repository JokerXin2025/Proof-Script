import ProofScript

/- This recording test relies on the old unrestricted `provide` behavior.

-- 测试：不在分支内
#theorem test_no_branch (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := script
  intro_h hp
  infer
  P => Q := hPQ hp
  _ => R := hQR ?_

-- 测试：在 split_and 分支内
#theorem test_with_branch (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : (P → R) ∧ (P → R) := script
  split_and
  | left =>
    intro_h hp
    infer
    P => Q := hPQ hp
    _ => R := hQR ?_
  | right =>
    intro_h hp
    apply_h hQR
    apply_h hPQ
    apply_h hp
-/
