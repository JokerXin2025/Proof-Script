import Test.PaperConfig

#theorem use_cross (P : Prop) (h : P) : P := script
  apply_thm cross_lemma
  apply_h h

#references
#page_end
