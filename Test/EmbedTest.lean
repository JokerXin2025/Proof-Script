import ProofScript

/- These embedded recording tests rely on the old unrestricted `provide` behavior.

/- 被嵌入的定理：其 script 证明里直接引用自己的参数（`#theorem` 编译成 def 时参数已在上下文中）。 -/
#theorem le_trans_script (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := script
  apply_thm Nat.le_trans
  apply_h hab
  apply_h hbc

/- 使用 `embed` 的定理：把 `le_trans_script a b c hab hbc` 的结论作为 `hac` 嵌入。 -/
#theorem demo (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := script
  embed (le_trans_script a b c hab hbc) as hac
  apply_h hac

/- 非 #theorem 的普通脚本模式也应当能用 embed（校验 + let 路径）。 -/
example (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := script
  embed (le_trans_script a b c hab hbc) as hac
  apply_h hac

/- ③ 隐式参数 + 调用方名字不同：`{a b c}` 由 `hxy hyz` 推出；
   `embed` 的 `args` 应记录调用方实参 `x y z hxy hyz`，
   `argKinds` 应分类为 `data data data proof proof`。 -/
#theorem demo_imp {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := script
  apply_thm Nat.le_trans
  apply_h hab
  apply_h hbc

#theorem demo_imp_caller (x y z : Nat) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := script
  embed (demo_imp hxy hyz) as hxz
  apply_h hxz
-/
