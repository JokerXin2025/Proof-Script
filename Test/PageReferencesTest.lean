import ProofScript

project_info {
  title := "Reference Test Project",
  authors := "Alice, Bob",
  year := "2026"
}

@[theorem_info (name := "Referenced Result", label := "referenced-result")]
theorem referencedResult (P : Prop) (h : P) : P := h

@text r#"
= References Test <references-test>
"#

@theorem @[theorem_info (name := "Uses Reference", label := "uses-reference")] usesReference
    (P : Prop) (h : P) : P := script
  apply (referencedResult P)
  assumption

@references

@text r#"
The references component appears before this paragraph.
"#

page_end
