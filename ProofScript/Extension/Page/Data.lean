import Lean
import ProofScript.References.Data

open Lean


namespace ProofScript.Extension


structure SourceLocation where
  file : String
  start : Nat
  stop : Nat
deriving Inhabited, Repr, ToJson, FromJson

abbrev ReferenceKind := String

structure DeclarationComponent where
  declName : Name := .anonymous
  name : String
  label : Option String := none
  proof : String
  sorryAx : Bool := false
deriving Inhabited, Repr, FromJson

instance declarationComponentToJson : ToJson DeclarationComponent where
  toJson value := Json.mkObj [
    ("name", Json.str value.name),
    ("label", toJson value.label),
    ("proof", Json.str value.proof),
    ("sorryAx", Json.bool value.sorryAx)
  ]

inductive ComponentData where
| theorem (value : DeclarationComponent)
| lemma (value : DeclarationComponent)
| component (kind : String) (value : Json)
deriving Inhabited

instance : ToJson ComponentData where
  toJson
  | .theorem value => Json.mkObj [("theorem", Json.mkObj [("value", toJson value)])]
  | .lemma value => Json.mkObj [("lemma", Json.mkObj [("value", toJson value)])]
  | .component kind value => Json.mkObj [(kind, Json.mkObj [("value", value)])]

structure Component where
  source : SourceLocation
  data : ComponentData
deriving Inhabited, ToJson

structure Page where
  schemaVersion : Nat × Nat × Nat := (0, 3, 0)
  projectInfo : ProofScript.ProjectInfo := {}
  module : Name
  source : String
  components : Array Component
deriving Inhabited

instance : ToJson Page where
  toJson page :=
    let (major, minor, patch) := page.schemaVersion
    Json.mkObj [
      ("schemaVersion", Json.str s!"{major}.{minor}.{patch}"),
      ("ProjectInfo", toJson page.projectInfo),
      ("module", Json.str page.module.toString),
      ("source", Json.str page.source),
      ("components", toJson page.components)
    ]


end ProofScript.Extension
