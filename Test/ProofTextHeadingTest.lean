import ProofScript

open ProofScript.Extension

#guard (ProofText.parse "==== Level 4").isOk
#guard !(ProofText.parse "===== Level 5").isOk
#guard !(ProofText.parse "====== Level 6").isOk
