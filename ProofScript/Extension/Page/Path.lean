import Lean

open Lean System


namespace ProofScript.Extension


def outputRoot : FilePath := ".Proof-Script"

private def modulePath (moduleName : Name) : FilePath :=
  FilePath.mk <|
    String.intercalate "/" <|
      moduleName.components.map (·.toString)

def pageOutputPath (moduleName : Name) : FilePath :=
  let path := modulePath moduleName
  let parent := path.parent.getD (FilePath.mk "")
  outputRoot / "pages" / parent / s!"{path.fileName.getD "Page"}.json"

def proofOutputPath (moduleName declName : Name) : FilePath :=
  let moduleDir := modulePath moduleName
  let declPath := modulePath declName
  let declFile := s!"{declPath.fileName.getD "proof"}.json"
  outputRoot / "proofs" / moduleDir / declFile

def ensureParentDir (path : FilePath) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent


end ProofScript.Extension
