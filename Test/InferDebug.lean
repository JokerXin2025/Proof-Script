import ProofScript

-- 简单测试：infer 录制格式
#theorem test_infer_debug (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := script
  intro_h hp
  infer
  P => Q := hPQ hp
  _ => R := hQR ?_
