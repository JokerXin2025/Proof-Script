import ProofScript

/-! ## `embed` 跨模块测试（⑥）——声明方

本文件声明一个 `#theorem` script 定理，其原始脚本经 `ScriptDB`（`MapDeclarationExtension`）
持久化进 `.olean`。**先**编译本文件，再编译 `EmbedCrossModuleUse.lean`（import 本文件），
验证 `embed` 能跨模块取回脚本并重放。

编译顺序（在项目根目录）：
```bash
LEAN_PATH=".lake/build/lib/lean" lake env lean -o EmbedCrossModuleDecl.olean Test/EmbedCrossModuleDecl.lean
LEAN_PATH=".lake/build/lib/lean:." lake env lean Test/EmbedCrossModuleUse.lean
``` -/

#theorem le_trans_script (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := script
  apply_thm Nat.le_trans
  apply_h hab
  apply_h hbc
