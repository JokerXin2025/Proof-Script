import Lean

namespace ProofScript

open Lean

/-- Compact index for locating the complete proof resource of a script theorem. -/
structure ScriptArtifact where
  proofPath : String
deriving Inhabited

initialize scriptDB : MapDeclarationExtension ScriptArtifact ←
  mkMapDeclarationExtension `ProofScript.scriptDB

def registerScriptArtifact (env : Environment) (name : Name) (proofPath : System.FilePath) :
    Environment :=
  scriptDB.insert env name { proofPath := proofPath.toString }

def findScriptArtifact (env : Environment) (name : Name) : Option ScriptArtifact :=
  scriptDB.find? env name

end ProofScript
