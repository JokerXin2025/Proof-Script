import ProofScript


-- 在项目根目录配置 ProjectInfo
project_info {
  title := "A Test Paper on References",
  authors := "Alice, Bob",
  keywords := "formal proof, reference management",
  year := "2026"
}

-- 标记论文中的定理
@[theorem_info (tags := "main, key")]
theorem lemma_ref (P : Prop) (h : P) : P := h

@[theorem_info (note := "secondary result")]
theorem lemma_other (P : Prop) (h : P) : P := h

-- 其它作者使用该定理时自动识别并加入文献暂存区
@theorem use_ref (P : Prop) (h : P) : P := script
  apply (lemma_ref P)
  assumption

@theorem use_two (P : Prop) (h : P) : P := script
  apply (lemma_other P)
  assumption

-- 将文献暂存区中的内容导出
@references
page_end
