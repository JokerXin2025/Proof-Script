import Lean
import ProofScript.References.Data

open Lean


namespace ProofScript.Extension

structure SourceLocation where
  file : String
  start : Nat
  stop : Nat
  deriving Inhabited, Repr, ToJson, FromJson

inductive ReferenceKind where
  | heading
  | theorem
  | figure
  deriving Inhabited, Repr, BEq, Hashable, ToJson, FromJson

inductive Inline where
  | text (value : String)
  | strong (content : Array Inline)
  | emphasis (content : Array Inline)
  | strongEmphasis (content : Array Inline)
  | code (value : String)
  | strike (content : Array Inline)
  | underline (content : Array Inline)
  | highlight (content : Array Inline)
  | superscript (content : Array Inline)
  | subscript (content : Array Inline)
  | link (content : Array Inline) (url : String)
  | reference (kind : ReferenceKind) (label : String)
  | math (latex : String)
  | softBreak
  | hardBreak
  deriving Inhabited, Repr, ToJson, FromJson

mutual

  inductive Block where
    | paragraph (content : Array Inline)
    | heading (level : Nat) (label : Option String) (content : Array Inline)
    | code (language : Option String) (source : String)
    | orderedList (start : Nat) (items : Array ListItem)
    | unorderedList (items : Array ListItem)
    | quote (content : Array Block)
    | displayMath (latex : String)
    deriving Inhabited, Repr, ToJson, FromJson

  structure ListItem where
    ordinal : Option Nat := none
    content : Array Block
    deriving Inhabited, Repr, ToJson, FromJson

end

structure TextComponent where
  source : String
  blocks : Array Block
  deriving Inhabited, Repr, ToJson, FromJson

structure TheoremComponent where
  declName : Name := .anonymous
  name : String
  label : Option String := none
  proof : String
  sorryAx : Bool := false
  deriving Inhabited, Repr, FromJson

instance theoremComponentToJson : ToJson TheoremComponent where
  toJson value := Json.mkObj [
    ("name", Json.str value.name),
    ("label", toJson value.label),
    ("proof", Json.str value.proof),
    ("sorryAx", Json.bool value.sorryAx)
  ]

structure ComponentMetadata where
  title : String
  label : Option String := none
  extra : List (String × String) := []
  deriving Inhabited, Repr, ToJson, FromJson

structure LatexComponent where
  metadata : ComponentMetadata
  language : String := "latex"
  source : String
  svg : String
  deriving Inhabited, Repr, ToJson, FromJson

structure FigureComponent where
  metadata : ComponentMetadata
  path : String
  extension : String
  deriving Inhabited, Repr, ToJson, FromJson

inductive ComponentData where
  | text (value : TextComponent)
  | theorem (value : TheoremComponent)
  | latex (value : LatexComponent)
  | figure (value : FigureComponent)
  | references (value : Json)
  | custom (kind : String) (value : Json)
  deriving Inhabited, ToJson, FromJson

structure Component where
  source : SourceLocation
  data : ComponentData
  deriving Inhabited, ToJson, FromJson

structure Page where
  schemaVersion : Nat × Nat × Nat := (0, 2, 0)
  projectInfo : ProofScript.ProjectInfo := {}
  module : Name
  source : String
  components : Array Component
  deriving Inhabited, FromJson

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
