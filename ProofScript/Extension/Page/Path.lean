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

def resourceOutputPath (kind hash extension : String) : FilePath :=
  outputRoot / "resources" / kind / s!"{hash}.{extension}"

def ensureParentDir (path : FilePath) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent

def contentHash (content : String) : String :=
  toString (hash content)

def resourceJson (path : FilePath) (content mediaType : String) : Json :=
  Json.mkObj [("$resource", Json.mkObj [
    ("path", Json.str path.toString),
    ("hash", Json.str (contentHash content)),
    ("mediaType", Json.str mediaType),
    ("encoding", Json.str "utf-8")
  ])]

private partial def chooseResourcePath (kind extension content hash : String)
    (suffix : Nat) : IO FilePath := do
  let name := if suffix == 0 then hash else s!"{hash}-{suffix}"
  let path := resourceOutputPath kind name extension
  if !(← path.pathExists) then return path
  if (← IO.FS.readFile path) == content then return path
  chooseResourcePath kind extension content hash (suffix + 1)

def writeTextResource (kind extension mediaType content : String) : IO Json := do
  let hash := contentHash content
  let path ← chooseResourcePath kind extension content hash 0
  ensureParentDir path
  unless ← path.pathExists do
    IO.FS.writeFile path content
  return resourceJson path content mediaType

def existingTextResource (path : FilePath) (mediaType : String) : IO Json := do
  let content ← IO.FS.readFile path
  return resourceJson path content mediaType


end ProofScript.Extension
