import ProofScript

theorem commandMetadataTarget (P : Prop) (h : P) : P := h

theorem_info commandMetadataTarget {
  name := "Command Metadata Target",
  label := "command-metadata-target",
  tags := "command, metadata"
}

#eval "theorem_info command registered"
