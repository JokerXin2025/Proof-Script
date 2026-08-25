import ProofScript.Extension.Path
import ProofScript.Extension.State
import ProofScript.Extension.Text.Parser
import ProofScript.References.Metadata

open Lean


namespace ProofScript.Extension


private def sourceLocation (stx : Syntax) : CoreM SourceLocation := do
  return {
    file := ← getFileName
    start := (stx.getPos?.getD 0).byteIdx
    stop := (stx.getTailPos?.getD (stx.getPos?.getD 0)).byteIdx
  }

private partial def headingLabels (blocks : Array Block) : Array String := Id.run do
  let mut labels := #[]
  for block in blocks do
    match block with
    | .heading _ (some label) _ => labels := labels.push label
    | .quote content => labels := labels ++ headingLabels content
    | .orderedList _ items | .unorderedList items =>
        for item in items do labels := labels ++ headingLabels item.content
    | _ => pure ()
  return labels

private def enrichTheorems  (env : Environment)
                            (components : Array Component)
                            : Except String (Array Component) := do
  let mut labels : Std.HashSet String := {}
  let mut result := #[]
  for component in components do
    match component.data with
    | .theorem theoremData =>
        let info := ProofScript.findTheoremInfo env theoremData.declName
        let name := info.map (·.name) |>.filter (!·.isEmpty) |>.getD theoremData.name
        let label := info.bind (·.label)
        if let some label := label then
          if labels.contains label then
            throw s!"duplicate theorem label '{label}'"
          labels := labels.insert label
        result := result.push {
          component with data := .theorem { theoremData with name := name, label := label }
        }
    | _ => result := result.push component
  return result

syntax "#text" str : command
syntax "#page_end" : command

open Lean.Elab.Command (liftIO liftCoreM) in
elab_rules : command
  | `(command| #text $source:str) => do
      let raw := source.getString
      let blocks ← match ProofText.parse raw with
        | .ok blocks => pure blocks
        | .error message => throwErrorAt source message
      let location ← liftCoreM <| sourceLocation source.raw
      let mut env ← getEnv
      for label in headingLabels blocks do
        env ← match registerLabel env .heading label location with
          | .ok nextEnv => pure nextEnv
          | .error message => throwErrorAt source message
      let component : Component := {
        source := location
        data := .text { source := raw, blocks := blocks }
      }
      let (nextEnv, added) ← match addComponent env component with
        | .ok result => pure result
        | .error message => throwErrorAt source message
      unless added do
        logWarningAt source "page component appears after #page_end and was ignored"
      setEnv nextEnv
  | `(command| #page_end) => do
      let env ← getEnv
      let state := getPageState env
      let components ← match enrichTheorems env state.components with
        | .ok components => pure components
        | .error message => throwError message
      let moduleName ← getMainModule
      let fileName ← getFileName
      let page : Page := {
        projectInfo := ProofScript.getProjectInfo env
        module := moduleName
        source := fileName
        components := components
      }
      let path := pageOutputPath moduleName
      liftIO do
        ensureParentDir path
        IO.FS.writeFile path (toJson page).pretty
      let env ← match closePage env with
        | .ok env => pure env
        | .error message => throwError message
      setEnv env

end ProofScript.Extension
