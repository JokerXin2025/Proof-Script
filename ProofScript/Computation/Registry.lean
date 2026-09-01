import ProofScript.Extension.Page.Path
import ProofScript.Extension.Page.Data

open Lean System

namespace ProofScript.Computation

structure EntryType where
  input : String
  output : String
  errorMode : String
deriving Inhabited, ToJson

structure PendingEntry where
  schemaVersion : String := "1.0.0"
  abi : String := "proof-script-json-v1"
  bundleId : String
  entry : String
  wrapper : String
  module : String
  functionType : EntryType
  source : ProofScript.Extension.SourceLocation
deriving Inhabited, ToJson

def pendingEntryPath (moduleName declaration : String) : FilePath :=
  let modulePath := String.intercalate "/" <| moduleName.splitOn "."
  let declarationPath := String.intercalate "/" <| declaration.splitOn "."
  ProofScript.Extension.outputRoot / "computations" / "pending" /
    FilePath.mk modulePath / s!"{declarationPath}.json"

def writePendingEntry (entry : PendingEntry) : IO FilePath := do
  let path := pendingEntryPath entry.module entry.entry
  ProofScript.Extension.ensureParentDir path
  IO.FS.writeFile path (toJson entry).pretty
  return path

end ProofScript.Computation
