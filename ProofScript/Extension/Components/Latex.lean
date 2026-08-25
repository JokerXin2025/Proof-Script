import ProofScript.Extension.Command
import ProofScript.Extension.Latex

open Lean
open Lean.Elab.Command (CommandElabM)


namespace ProofScript.Extension


syntax componentMetaEntry := ident " := " str
syntax componentMeta := "(" sepBy1(componentMetaEntry, ", ") ")"

def validComponentLabel (label : String) : Bool :=
  match label.toList with
  | [] => false
  | first :: rest =>
      first.isAlpha && rest.all fun c => c.isAlphanum || c == '-' || c == '_'

def parseComponentMetadata (stx : Syntax) : Except String ComponentMetadata := do
  let mut title : Option String := none
  let mut label : Option String := none
  let mut extra := []
  let entries := stx.getArgs[1]!.getSepArgs
  for entry in entries do
    match entry with
    | `(componentMetaEntry| $key:ident := $value:str) =>
      let key := key.getId.toString
      let value := value.getString
      match key with
      | "title" =>
        if title.isSome then throw "duplicate component metadata field 'title'"
        title := some value
      | "label" =>
        if label.isSome then throw "duplicate component metadata field 'label'"
        unless validComponentLabel value do
          throw "component label must match [A-Za-z][A-Za-z0-9_-]*"
        label := some value
      | other => extra := extra ++ [(other, value)]
    | _ => throw "invalid component metadata"
  let some titleValue := title | throw "component metadata requires 'title'"
  return { title := titleValue, label, extra }

def componentMetadataJson (metadata : ComponentMetadata) := toJson metadata

private def sourceLocation (stx : Syntax) : CoreM SourceLocation := do
  return {
    file := ← getFileName
    start := (stx.getPos?.getD 0).byteIdx
    stop := (stx.getTailPos?.getD (stx.getPos?.getD 0)).byteIdx
  }

private def addPageComponent (metadataStx : Syntax)
                               (valueStx : TSyntax `str)
                               (makeData : ComponentMetadata → String → CommandElabM ComponentData)
                               : CommandElabM Unit := do
  let metadata ← match parseComponentMetadata metadataStx with
    | .ok metadata => pure metadata
    | .error message => throwErrorAt metadataStx message
  let value := valueStx.getString
  let location ← Lean.Elab.Command.liftCoreM <| sourceLocation valueStx.raw
  let mut env ← getEnv
  if let some label := metadata.label then
    env ← match registerLabel env .figure label location with
      | .ok nextEnv => pure nextEnv
      | .error message => throwErrorAt metadataStx message
  let data ← makeData metadata value
  let (nextEnv, added) ← match addComponent env { source := location, data := data } with
    | .ok result => pure result
    | .error message => throwErrorAt valueStx message
  unless added do
    logWarningAt valueStx "page component appears after #page_end and was ignored"
  setEnv nextEnv

private def addLatexComponent (metadataStx : Syntax)
                               (codeStx : TSyntax `str)
                               : CommandElabM Unit := do
  addPageComponent metadataStx codeStx fun metadata code => do
    let svg ← Lean.Elab.Command.liftIO <| compileLatexToSvg code
    pure <| .latex { metadata, source := code, svg }

private def addFigureComponent (metadataStx : Syntax) (pathStx : TSyntax `str) : CommandElabM Unit :=
  addPageComponent metadataStx pathStx fun metadata path => do
    let filePath := System.FilePath.mk path
    if filePath.isAbsolute then
      throwErrorAt pathStx "#figure requires a relative resource path"
    let some extension := filePath.extension
      | throwErrorAt pathStx "#figure resource path must include a file extension"
    pure <| .figure { metadata, path, extension }

elab "#LaTeX" metadata:componentMeta code:str : command =>
  addLatexComponent metadata.raw code
elab "#figure" metadata:componentMeta path:str : command =>
  addFigureComponent metadata.raw path


end ProofScript.Extension
