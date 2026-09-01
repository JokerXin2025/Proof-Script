# Proof-Script Mathlib 扩展

本文件说明 Proof-Script 中可选的 Mathlib 扩展模块 `ProofScript.Mathlib`。

该模块不由核心入口 `ProofScript.lean` 导入，也不属于当前项目的默认 Lake target。安装
Mathlib 后，可在下游项目中显式导入：

```lean
import ProofScript
import ProofScript.Mathlib
```

本模块不是运行时插件。Lean parser、macro 和 elaborator 会在导入模块时注册。

## 语法约定

所有包装只使用 `ident`、`term` 等基础参数类别，以便自动记录器稳定处理参数；不直接暴露
Mathlib 的 `optConfig`、`location`、`simpArgs`、discharger 或 binder parser。

方括号中的参数使用空白分隔，展开后转换成 Mathlib 所需的逗号列表：

```lean
linarith [h₁ h₂]
norm_num [Nat.add_zero Nat.zero_add]
```

支持位置参数的策略通常提供以下形式：

```lean
norm_cast
norm_cast at h
norm_cast at h₁ h₂
norm_cast at *
norm_cast at ⊢
norm_cast at h₁ h₂ ⊢
```

带附加 lemma 的 `norm_num`、`push_cast`、`qify`、`rify` 和 `zify` 也支持对应组合：

```lean
qify [hab hdiv] at h₁ h₂ ⊢
push_cast only [Int.cast_add] at *
```

## 策略清单

所有包装在 `ProofScript/Mathlib.lean` 中按字母顺序定义。

### `continuity`

```lean
continuity
```

### `exact_mod_cast`

```lean
exact_mod_cast proof
```

### `field`

```lean
field
field [h₁ h₂]
```

### `gcongr`

```lean
gcongr
gcongr pattern
gcongr with x y
gcongr pattern with x y
```

### `itaotu` / `itauto`

```lean
itauto
itauto *
itauto [P Q]
itauto!
itauto! *
itauto! [P Q]
```

### `linarith` / `nlinarith`

两者以及各自的 `!` 版本支持：

```lean
linarith
linarith [h₁ h₂]
linarith only
linarith only [h₁ h₂]

nlinarith!
nlinarith! [h₁ h₂]
nlinarith! only
nlinarith! only [h₁ h₂]
```

### `measurability`

```lean
measurability
```

### `norm_cast`

支持默认形式及全部简化 `at` 形式：

```lean
norm_cast
norm_cast at h
norm_cast at h₁ h₂
norm_cast at *
norm_cast at ⊢
norm_cast at h₁ h₂ ⊢
```

### `norm_num`

支持默认 simp 集、附加 lemma、`only` 以及对应的 `at` 组合：

```lean
norm_num
norm_num [l₁ l₂]
norm_num only
norm_num only [l₁ l₂]
norm_num [l₁ l₂] at h₁ h₂ ⊢
norm_num only [l₁ l₂] at *
```

### `positivity`

```lean
positivity
positivity [h₁ h₂]
```

### `push_cast`

支持 lemma 列表、`only` 以及与 `norm_num` 相同的 `at` 位置组合：

```lean
push_cast
push_cast [l₁ l₂]
push_cast only
push_cast only [l₁ l₂] at h ⊢
```

### `qify` / `rify` / `zify`

三者均支持默认形式、附加 lemma 和完整的简化 `at` 组合：

```lean
qify
qify [hab] at h ⊢
rify at *
zify [hab] at h₁ h₂
```

### `ring` / `ring_nf`

```lean
ring
ring!
ring_nf
ring_nf!
ring_nf at h₁ h₂ ⊢
ring_nf! at *
```

### `tauto`

```lean
tauto
```

### `wlog`

```lean
wlog h : P
wlog h : P generalizing x y
wlog h : P with H
wlog h : P generalizing x y with H
```

以上四种形式均有对应的 `wlog!` 版本。

## 未包装语法

为了保持脚本参数可稳定录制，本模块不包装 Mathlib 的配置对象、自定义 discharger、任意 tactic
block，以及 `continuity?`、`measurability?` 等仅输出建议的变体。需要这些高级形式时，应在普通
Lean `by` 证明中直接使用 Mathlib 原生策略。
