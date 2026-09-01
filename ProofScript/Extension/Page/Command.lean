import ProofScript.Extension.Page.Path
import ProofScript.Extension.Page.State
import ProofScript.References.Metadata

open Lean


namespace ProofScript.Extension


private def enrichDeclarations  (env : Environment)
                                (components : Array Component)
                                : Except String (Array Component) := do
  let mut labels : Std.HashSet String := {}
  let mut result := #[]
  for component in components do
    let enrich (declarationData : DeclarationComponent) : Except String DeclarationComponent := do
        let info := ProofScript.findTheoremInfo env declarationData.declName
        let name := info.map (·.name)
                    |>.filter (!·.isEmpty)
                    |>.getD declarationData.name
        let label := info.bind (·.label)
        if let some label := label then
          if labels.contains label then
            throw s!"duplicate theorem label '{label}'"
        return {
          declarationData with
            name := name,
            label := label
        }
    match component.data with
    | .theorem theoremData =>
        let theoremData ← enrich theoremData
        if let some label := theoremData.label then labels := labels.insert label
        result := result.push { component with data := .theorem theoremData }
    | .lemma lemmaData =>
        let lemmaData ← enrich lemmaData
        if let some label := lemmaData.label then labels := labels.insert label
        result := result.push { component with data := .lemma lemmaData }
    | .component _ _ => result := result.push component
  return result

syntax "page_end" : command

open Lean.Elab.Command (liftIO) in
elab_rules : command
  | `(command| page_end) => do
      let env ← getEnv
      let state := getPageState env
      let components ←  match enrichDeclarations env state.components with
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
