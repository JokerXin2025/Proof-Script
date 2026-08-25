import Lean

open Lean


namespace ProofScript


structure ProjectInfo where
  title    : String := ""
  authors  : List String := []
  abstract : String := ""
  keywords : List String := []
  journal  : String := ""
  year     : String := ""
  url      : String := ""
  license  : String := ""
  arxivId  : String := ""
  doi      : String := ""
  note     : String := ""
  extra    : List (String × String) := []
  deriving Inhabited, Repr, ToJson, FromJson

def defaultProjectInfo : ProjectInfo := {}

structure TheoremInfo where
  project : ProjectInfo := {}
  name : String := ""
  label : Option String := none
  tags  : List String := []
  extra : List (String × String) := []
  deriving Inhabited, Repr, ToJson, FromJson

structure Reference where
  name : Name
  info : TheoremInfo
  deriving Inhabited, Repr, ToJson, FromJson


end ProofScript
