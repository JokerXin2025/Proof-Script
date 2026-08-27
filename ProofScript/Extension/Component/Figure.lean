import ProofScript.Extension.Component.Core

open Lean
open Lean.Elab.Command (CommandElabM)

namespace ProofScript.Extension

private def addFigureComponent (metadataStx : Syntax) (pathStx : TSyntax `str) : CommandElabM Unit := do
  let metadata ← match parseComponentMetadata metadataStx with
    | .ok metadata => pure metadata
    | .error message => throwErrorAt metadataStx message
  let path := pathStx.getString
  let filePath := System.FilePath.mk path
  if filePath.isAbsolute then
    throwErrorAt pathStx "#figure requires a relative resource path"
  let some extension := filePath.extension
    | throwErrorAt pathStx "#figure resource path must include a file extension"
  let labels := match metadata.label with
    | some label => #[(ReferenceKind.figure, label)]
    | none => #[]
  addPageComponent pathStx.raw (.figure { metadata, path, extension }) labels

syntax "#figure" componentMeta str : command

open Lean.Elab.Command in
elab_rules : command
  | `(command| #figure $metadata:componentMeta $path:str) =>
      addFigureComponent metadata.raw path

end ProofScript.Extension
