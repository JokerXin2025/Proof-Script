import ProofScript

@[theorem_info (tags := "option")]
theorem option_ref (P : Prop) (h : P) : P := h

set_option proofScript.references.enabled false in
#theorem references_disabled (P : Prop) (h : P) : P := script
  provide (option_ref P h)

#references

#theorem references_enabled (P : Prop) (h : P) : P := script
  provide (option_ref P h)

#references
#page_end
