import ProofScript

theorem test_infer_term (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hp : P) : R :=
  infer
    P => Q := hPQ hp
    _ => R := hQR ?_

-- 测试1：在 := script 模式下，infer 能正确录制
theorem test_infer_script (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hp : P) : R := script
  infer
    P => Q := hPQ hp
    _ => R := hQR ?_

-- 测试2：用 #theorem 会怎样（应该失败或生成 sorry）
@theorem test_infer_export (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := script
  intro_h hp
  infer
    P => Q := hPQ hp
    _ => R := hQR ?_

-- infer 的每一步都应作为匿名条件保留，而不只是保留最后一步。
theorem test_infer_keeps_each_step (P Q R : Prop) (hp : P)
    (hPQ : P → Q) (hQR : Q → R) : Q ∧ R := script
  infer
    P => Q := hPQ hp
    _ => R := hQR ?_
  split_and
  | left => trivial
  | right => trivial

@theorem test_recorded_infer_keeps_each_step (P Q R : Prop) (hp : P)
    (hPQ : P → Q) (hQR : Q → R) : Q ∧ R := script
  infer
    P => Q := hPQ hp
    _ => R := hQR ?_
  split_and
  | left => trivial
  | right => trivial
