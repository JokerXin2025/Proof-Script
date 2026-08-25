import ProofScript.References.Data

open Lean

/-!
# 论文与定理元数据

`project_info` 注册项目基本信息；`theorem_info` 将这些信息和定理级附加信息
持久化到声明环境中，随 `.olean` 跨模块读取。
-/


namespace ProofScript

initialize projectInfoExt : SimplePersistentEnvExtension ProjectInfo (Option ProjectInfo) ←
  registerSimplePersistentEnvExtension {
    name := `ProofScript.projectInfo
    addEntryFn    := fun _ p => some p
    addImportedFn := fun as =>
      as.foldl (init := none) fun acc es =>
        match es.toList.getLast? with
        | some p => some p
        | none => acc
  }

/-- 读取当前注册的论文基本信息；未注册时回退到全空默认值。 -/
def getProjectInfo (env : Environment) : ProjectInfo :=
  (projectInfoExt.getState env).getD defaultProjectInfo

initialize theoremInfoExt : MapDeclarationExtension TheoremInfo ←
  mkMapDeclarationExtension `ProofScript.theoremInfo

/-- 查询定理 `n` 的元数据；`none` 表示该声明没有 `theorem_info`。 -/
def findTheoremInfo (env : Environment) (n : Name) : Option TheoremInfo :=
  theoremInfoExt.find? env n

/-! ## `project_info` -/

syntax projectInfoField := ident " := " str
syntax (name := projectInfoCmd) "project_info" "{" sepBy1(projectInfoField, ", ") "}" : command

private def setProjectField (info : ProjectInfo) (k : String) (v : String) : ProjectInfo :=
  match k with
  | "title"    => { info with title := v }
  | "authors"  => { info with authors := (v.splitOn ",").map (·.trimAscii.toString) }
  | "abstract" => { info with abstract := v }
  | "keywords" => { info with keywords := (v.splitOn ",").map (·.trimAscii.toString) }
  | "journal"  => { info with journal := v }
  | "year"     => { info with year := v }
  | "url"      => { info with url := v }
  | "license"  => { info with license := v }
  | "arxivId"  => { info with arxivId := v }
  | "doi"      => { info with doi := v }
  | "note"     => { info with note := v }
  | other       => { info with extra := info.extra ++ [(other, v)] }

elab_rules : command
  | `(command| project_info%$_tk { $[$fields:projectInfoField],* }) => do
      let mut info : ProjectInfo := {}
      for f in fields do
        match f with
        | `(projectInfoField| $k:ident := $v:str) =>
            info := setProjectField info k.getId.toString v.getString
        | _ => pure ()
      modifyEnv fun env => projectInfoExt.addEntry env info

/-! ## `theorem_info` -/

syntax theoremInfoEntry := ident " := " str
syntax (name := theorem_info) "theorem_info"
  (ppSpace "(" sepBy1(theoremInfoEntry, ", ") ")")? : attr
syntax (name := theoremInfoCmd) "theorem_info" ident
  (ppSpace "{" sepBy1(theoremInfoEntry, ", ") "}")? : command

private def theoremInfoEntryToPair (e : Syntax) : Option (String × String) :=
  match e with
  | `(theoremInfoEntry| $k:ident := $v:str) =>
      some (k.getId.toString, v.getString)
  | _ => none

private def validLabel (label : String) : Bool :=
  match label.toList with
  | [] => false
  | first :: rest =>
       first.isAlpha && rest.all fun c => c.isAlphanum || c == '-' || c == '_'

private def buildTheoremInfo (entries : List (String × String)) : CoreM TheoremInfo := do
  let project := getProjectInfo (← getEnv)
  let mut name := ""
  let mut label : Option String := none
  let mut tags : List String := []
  let mut extra : List (String × String) := []
  for (k, v) in entries do
    match k with
    | "name" => name := v
    | "label" =>
        unless validLabel v do
          throwError "theorem_info label must match [A-Za-z][A-Za-z0-9_-]*"
        label := some v
    | "tags" => tags := (v.splitOn ",").map (·.trimAscii.toString)
    | other  => extra := extra ++ [(other, v)]
  return { project := project, name := name, label := label, tags := tags, extra := extra }

private partial def attrEntries (stx : Syntax) : List (String × String) :=
  if stx.getKind == ``theoremInfoEntry then
    (theoremInfoEntryToPair stx).toList
  else
    stx.getArgs.toList.flatMap attrEntries

initialize registerBuiltinAttribute {
  name  := `theorem_info
  descr := "把注册的论文基本信息与附加元数据永久地附加到该定理"
  add   := fun decl stx _kind => do
    let info ← buildTheoremInfo (attrEntries stx)
    modifyEnv fun env => theoremInfoExt.insert env decl info
}

open Lean.Elab.Command in
private def registerTheoremInfo (declId : TSyntax `ident)
    (entries : Array Syntax) : CommandElabM Unit := do
    let decl ← Lean.resolveGlobalConstNoOverload declId.raw
    unless (← getEnv).contains decl do
      throwErrorAt declId m!"unknown declaration '{declId.getId}'"
    let info ← liftCoreM <| buildTheoremInfo (entries.toList.filterMap theoremInfoEntryToPair)
    modifyEnv fun env => theoremInfoExt.insert env decl info

open Lean.Elab.Command in
elab_rules : command
  | `(command| theorem_info $declId:ident) => registerTheoremInfo declId #[]
  | `(command| theorem_info $declId:ident { $[$entries:theoremInfoEntry],* }) =>
      registerTheoremInfo declId (entries.map (·.raw))


end ProofScript
