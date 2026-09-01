import Test.PaperConfig

@theorem use_cross (P : Prop) (h : P) : P := script
  apply (cross_lemma P)
  assumption

@references
page_end
