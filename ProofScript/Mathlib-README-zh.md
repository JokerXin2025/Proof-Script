# Proof-Script Mathlib 扩展

本文件说明 Proof-Script 中可选的 Mathlib 扩展模块 `ProofScript.Mathlib`。

该模块不由核心入口 `ProofScript.lean` 导入，也不属于当前项目的默认 Lake target。已安装 Mathlib
的下游项目可以显式导入：

```lean
import ProofScript
import ProofScript.Mathlib
```

当前提供以下脚本策略包装：

```text
norm_num
linarith
nlinarith
ring
ring_nf
positivity
field
```

每个策略暂时只公开最常用的无参数形式。Mathlib 的 `only [...]`、`at h`、自定义 discharger 和 tactic
block 等变体暂不包装，因为它们需要额外的语义字段或目标位置模型。

本模块不是运行时插件。Lean parser、macro 和 elaborator 会在下游项目显式导入该模块时注册。
