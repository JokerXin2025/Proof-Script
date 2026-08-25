import Test.EmbedCrossModuleDecl

/-! ## `embed` 跨模块测试（⑥）——使用方

import 上面的声明方模块，验证 `embed` 能从 `.olean` 里取回 `le_trans_script` 的脚本并重放。
编译前请先编译 `EmbedCrossModuleDecl.lean`（见其文件头注释）。 -/

#theorem demo (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := script
  embed (le_trans_script a b c hab hbc) as hac
  provide hac
