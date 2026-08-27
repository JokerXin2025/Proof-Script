import ProofScript.Extension.Page.Path
import ProofScript.Extension.Page.State
import ProofScript.References.Metadata

open Lean


namespace ProofScript.Extension


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

syntax "#page_end" : command

open Lean.Elab.Command (liftIO) in
elab_rules : command
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
