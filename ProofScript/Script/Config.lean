import Lean.Elab.Command
import Lean.Elab.Tactic
import Lean.Parser.Term
import ProofScript.Script.Record

open Lean (Syntax TSyntax getEnv quote mkIdent mkNode mkNullNode Name.mkSimple)
open Lean.Parser (atomic darrow sepBy optional ppSpace many1 termParser withPosition
                   nonReservedSymbol runParserCategory suppressInsideQuot)
open Lean.Parser.Term (ident doSeqItem doSeqIndent)
open Lean.Parser.Command (macroArg macroRhs docComment)
open Lean.Parser.Tactic (quot)
open Lean.Elab.Command (CommandElabM elabCommand liftIO expandMacroArg elabSyntax)


namespace ProofScript

register_option proofScript.scriptMode.active : Bool := {
  defValue := false
  descr := "internal guard for executing script_ tactics"
}

def ensureScriptMode : Lean.Elab.Tactic.TacticM Unit := do
  unless (← Lean.getOptions).getBool `proofScript.scriptMode.active false do
    throwError "Proof-Script tactics can only be used in `:= script` proofs"

def withScriptMode {α} (action : Lean.Elab.Tactic.TacticM α) : Lean.Elab.Tactic.TacticM α :=
  Lean.withOptions (·.setBool `proofScript.scriptMode.active true) action

elab "ensure_script_mode" : tactic => ensureScriptMode

def wrapScriptMacroResult (tactic : TSyntax `tactic) : Lean.MacroM Syntax := do
  return (← `(tactic| (ensure_script_mode; $tactic:tactic))).raw

initialize ScriptStrategiesRef
  : IO.Ref (List String) ← IO.mkRef []
initialize ScriptRecordingKindsRef
  : IO.Ref (List (String × Lean.Name)) ← IO.mkRef []
initialize ScriptTacticKindsRef
  : IO.Ref (List (String × Lean.Name)) ← IO.mkRef []

structure ScriptTacticRegistration where
  name : String
  sourceKind : Lean.Name
  executionKind : Lean.Name
  recordingKind : Option Lean.Name
  strategy : Bool
  deriving Repr

initialize ScriptTacticRegistrationsRef
  : IO.Ref (List ScriptTacticRegistration) ← IO.mkRef []

def getScriptStrategies : IO (List String) := ScriptStrategiesRef.get
def getScriptRecordingKinds : IO (List (String × Lean.Name)) := ScriptRecordingKindsRef.get
def getScriptTacticKinds : IO (List (String × Lean.Name)) := ScriptTacticKindsRef.get
def getScriptTacticRegistrations : IO (List ScriptTacticRegistration) :=
  ScriptTacticRegistrationsRef.get

/-! ### 语法级辅助：从 `macroArg` 节点构造录制版 elab（纯 antiquotation，不经字符串） -/

open Lean.Parser.Syntax in
/-- 从 `stx` 片段（`macroArg` 的类型部分）判断参数类型，替代 reprint 字符串巧合：
    - `term`/`ident`/`str` → `Lean.Parser.Syntax.cat` 节点，名字是 category ident；
    - `ident+`（`many1(ident)`）→ `stx_+` 节点。 -/
def stxKindType (stx : Syntax) :=
  if stx.getKind == ``cat then
    match stx with
    | `(cat| $c:ident) => c.getId.toString
    | _ => "term"
  else if stx.getKind == Name.mkSimple "stx_+" then
    "ident+"
  else
    "term"

def allowedParamCats := ["term", "ident", "str", "num"]

open Lean.Parser.Syntax in
/-- 校验参数类别：`str` 内联、`term`/`ident`/`num` 单类别、`+`（many1）数组；
    其余（`binderIdent`、`tactic`、`level` 等非 term 类别，以及 `*`/`,` 分隔等）在录制版
    `elabTerm` 时会失败，提前在编译期拒绝。返回错误信息（`none` = 支持）。
    注意 `+`（many1）整体放行，不检查元素类别（`(colGt ident)+` 等修饰内层是合法的 term 元素）。 -/
def checkParamKind (stx : Syntax) : Option String :=
  if stx.getKind == ``cat then
    match stx with
    | `(cat| $c:ident) =>
        let cn := c.getId.toString
        if allowedParamCats.contains cn then none
        else some s!"参数类别 '{cn}' 无法当作 term 精化，录制版不支持（仅支持 {allowedParamCats} 与 `+` 重复）"
    | _ => some "无法识别的单类别参数"
  else if stx.getKind == Name.mkSimple "stx_+" then
    none
  else
    some s!"参数语法不被录制版支持（仅支持单类别 {allowedParamCats} 与 `+`（many1）重复，不支持 `*`/`,` 分隔或复合序列）"

/-- 校验所有命名参数的类别（`checkParamKind`），提前拒绝录制版无法 elaborate 的类别。 -/
private def validateParamKinds  (name : String)
                                (args : Array (TSyntax ``macroArg))
                                : CommandElabM Unit := do
  for arg in args[1:] do
    match arg with
    | `(macroArg| $id:ident:$stx) =>
        match checkParamKind stx with
        | some msg => throwError m!"[script config] '{name}': 参数 '{id.getId}' {msg}"
        | none => pure ()
    | _ => pure ()

open Lean.Parser.Syntax in
/-- 从完整策略名构造 `macroArg`（str 字面量，含引号）。 -/
def mkRawNameArg (name : String) : Syntax :=
  mkNode ``macroArg #[
    mkNullNode,
    mkNode ``atom #[mkNode `str #[Lean.mkAtom ("\"" ++ name ++ "\"")]]
  ]

def mkNameArg (name : String) : Syntax := mkRawNameArg ("_" ++ name)

def mkScriptNameArg (name : String) : Syntax := mkRawNameArg ("script_" ++ name)

/-- 把 `doElem` 数组拼成 `doSeqIndent` 节点（`do` 块的 body）。 -/
def mkDoSeq (elems : Array Syntax) : Syntax :=
  let items := elems.map fun e => mkNode ``doSeqItem #[e, mkNullNode]
  mkNode ``doSeqIndent #[mkNullNode items]

/-- 擦除语法树中所有 ident 的宏作用域（`✝`）。
    录制版 elab 经 `(command| …)`/`(doElem| …)` 引号构造，字面量 ident（如 `ProofScript.recordStep`
    等全局名）会被 hygiene 加 `_hyg` 作用域而无法解析；擦除后按名解析。参数名（`lemma` 等）也一并
    擦成无作用域——binder 与引用同时擦除仍同名匹配，作用域封闭，安全。 -/
partial def eraseMacroScopes (stx : Syntax) : Syntax :=
  match stx with
  | .ident info raw val pre => .ident info raw val.eraseMacroScopes pre
  | .node info kind args => .node info kind (args.map eraseMacroScopes)
  | _ => stx

private def registerTacticRegistration (registration : ScriptTacticRegistration) :
    CommandElabM Unit := do
  liftIO <| ScriptTacticRegistrationsRef.modify fun cur =>
    cur.filter (fun r => r.name != registration.name || r.sourceKind != registration.sourceKind) ++
      [registration]
  let init ← `(command| initialize do ProofScript.ScriptTacticRegistrationsRef.modify (fun cur =>
    cur.filter (fun r => r.name != $(Lean.quote registration.name) ||
      r.sourceKind != $(Lean.quote registration.sourceKind)) ++ [{
      name := $(Lean.quote registration.name)
      sourceKind := $(Lean.quote registration.sourceKind)
      executionKind := $(Lean.quote registration.executionKind)
      recordingKind := $(Lean.quote registration.recordingKind)
      «strategy» := $(Lean.quote registration.strategy)
    }]))
  elabCommand (eraseMacroScopes init.raw)

private def setRegistrationRecordingKind (name : String) (recordingKind : Lean.Name) :
    CommandElabM Unit := do
  liftIO <| ScriptTacticRegistrationsRef.modify fun cur =>
    cur.map fun r => if r.name == name then { r with recordingKind := some recordingKind } else r
  let init ← `(command| initialize do ProofScript.ScriptTacticRegistrationsRef.modify (fun cur =>
    cur.map (fun r => if r.name == $(Lean.quote name) then
      { r with recordingKind := some $(Lean.quote recordingKind) } else r)))
  elabCommand (eraseMacroScopes init.raw)

/-- 为 `str` 字面量参数生成内联萃取语句 `let {id}Str := Lean.Json.str …`（`doElem`）。
    动态 ident `{id}Str`（unhygienic 但作用域封闭，安全；留意参数名与 `{name}Str` 冲突）。
    `term`/`ident`/`ident+` 参数不在此处萃取——它们按 `intro`/`clear`/neither 时序交由
    `recordStep`/`recordStrategy` 在正确时机 elaborate（见 `buildRawPair`）。 -/
def extractInlineDoElem (arg : TSyntax ``macroArg)
                        : CommandElabM (TSyntax `doElem) := do
  match arg with
  | `(macroArg| $id:ident:$_:stx) =>
      let idStr : TSyntax `ident := ⟨mkIdent (Name.mkSimple (id.getId.toString ++ "Str"))⟩
      `(doElem| let $idStr:ident := Lean.Json.str (Lean.TSyntax.getString $id))
  | _ => `(doElem| pure ())

/-- 用 antiquotation 组装 `(name, idStr)` 的 pair 列表（内联 `str` 参数字段）。
    不手拼 `pair` 节点——手拼极易拼错隐藏标点/NullNode，`evalTactic` 展开时直接 panic。 -/
private def buildFields (names : Array String)
                        (vals : Array (TSyntax `ident))
                        : CommandElabM (Array (TSyntax `term)) := do
  let mut fields : Array (TSyntax `term) := #[]
  for i in [:names.size] do
    let v : TSyntax `ident := vals[i]!
    fields := fields.push (← `(term| ($(Lean.quote names[i]!), $v:ident)))
  return fields

/-- 用 antiquotation 组装单个 `(键名, ParamRaw)` pair（`preTerms`/`postTerms` 的一项）。
    `isMany` 为真时是 `ident+`（`ParamRaw.many (id.map (·.raw))`），否则是单个
    `term`/`ident`（`ParamRaw.one (id.raw)`）；交给 `recordStep`/`recordStrategy`
    在执行前/后 elaborate。 -/
private def buildRawPair  (key : String)
                          (val : TSyntax `ident)
                          (isMany : Bool)
                          : CommandElabM (TSyntax `term) := do
  if isMany then
    `(term| ($(Lean.quote key), ParamRaw.many (($val:ident).map (fun x => x.raw))))
  else
    `(term| ($(Lean.quote key), ParamRaw.one (($val:ident).raw)))

/-- 记录器生成方式。`exclusive` 表示仅使用手写的 `script_recorder`。 -/
inductive ScriptRecorder where
  | auto
  | exclusive
  deriving BEq

/-- 策略录制配置。所有字段在编译期求值。
    - `intro`：由该策略**产生**的新 fvar 对应的**参数名**列表（如 `intro_h` 的 `name`），
      只在策略执行**之后** elaborate + 记录。
    - `clear`：由该策略**删除**的原 fvar 对应的**参数名**列表（如 `induction` 的 `n`），
      只在策略执行**之前** elaborate + 记录。
    - `strategy`：是否为概略策略；具体分支名由每次调用后连续的 `| case =>` 自动收集。 -/
structure ScriptCfg where
  intro : List String := []
  clear : List String := []
  recorder : ScriptRecorder := .auto
  strategy : Bool := false

def emptyScriptCfg : ScriptCfg := {
  intro := [],
  clear := [],
  recorder := .auto,
  strategy := false
}

/-- 注册策略的录制 parser kind，同时覆盖同名的旧映射。 -/
private def registerRecordingKind (name : String) (kind : Lean.Name) : CommandElabM Unit := do
  liftIO <| ScriptRecordingKindsRef.modify fun cur =>
    cur.filter (fun (n, _) => n != name) ++ [(name, kind)]
  let init ← `(command| initialize do ProofScript.ScriptRecordingKindsRef.modify (fun cur =>
    cur.filter (fun (n, _) => n != $(Lean.quote name)) ++ [($(Lean.quote name), $(Lean.quote kind))]))
  elabCommand (eraseMacroScopes init.raw)

/-- 生成录制版 `_*` elab（纯语法级 antiquotation 构造，不经字符串、不经 reparse）。
    `pat` 是本体定义步骤算出的 `macro` pattern（kind + patArgs），录制版直接复用；
    参数按 `cfg.intro`/`cfg.clear` 分三组（内联 / 执行前 / 执行后），分别交给
    `recordStep`/`recordStrategy` 在正确时机序列化。 -/
private def genRecording  (name : String)
                            (syntaxName : String)
                           (args : Array (TSyntax ``macroArg))
                           (pat : Syntax)
                           (cfg : ScriptCfg)
                           : CommandElabM Unit := do
  let tacticCat : TSyntax `ident := ⟨mkIdent `tactic⟩
  -- ① 录制版参数模式：args[0]（策略名字面量）换成 "_name"，其余原样
  let mut recArgs := args.mapIdx fun i a => if i == 0 then ⟨mkNameArg syntaxName⟩ else a
  let strategyCasesId : TSyntax `ident := ⟨mkIdent `strategyCases⟩
  if cfg.strategy then
    recArgs := recArgs.push (← `(macroArg| "_strategy_cases"))
    recArgs := recArgs.push (← `(macroArg| strategyCases:str))
  -- ② 本体调用：patArgs 每个元素——`token_antiquot`（名字/字面量 token）取 `.getArg 0`（裸 atom），
  --    命名参数 antiquot（`$id:type` splice）原样；包成 quotation term `` `(tactic| …) `` 供 `evalTactic` 使用
  let patArgs := pat.getArgs
  let callArgs := patArgs.mapIdx fun _ a => if a.getKind == `token_antiquot then a.getArg 0 else a
  let call := mkNode pat.getKind callArgs
  let callQuot : TSyntax `term := ⟨mkNode ``quot #[Lean.mkAtom "`(tactic| ", call, Lean.mkAtom ")"]⟩
  -- ③ 参数分组（按 intro/clear/neither 时序）：
  --    - `str` → 内联萃取（字符串字面量，无表达式状态）
  --    - `intro` 参数 → 执行后 elaborate（`postTerms`，键名 = 参数名）
  --    - `clear` 参数 → 执行前 elaborate（`preTerms`，键名 = 参数名）
  --    - 其余（neither）→ 执行前、后各 elaborate 一次（`bothTerms`，键名 = 参数名），
  --      由 `recordStep`/`recordStrategy` 合并为 `{"before":…, "after":…}`
  let mut inlineElems : Array Syntax := #[]
  let mut inlineNames : Array String := #[]
  let mut inlineVals : Array (TSyntax `ident) := #[]
  let mut preFields : Array (TSyntax `term) := #[]
  let mut postFields : Array (TSyntax `term) := #[]
  let mut bothFields : Array (TSyntax `term) := #[]
  for arg in args[1:] do
    match arg with
    | `(macroArg| $id:ident:$stx) =>
        let pname := id.getId.toString
        let kind := stxKindType stx
        let isMany := kind == "ident+"
        if kind == "str" then
          inlineElems := inlineElems.push (← extractInlineDoElem arg).raw
          inlineNames := inlineNames.push pname
          inlineVals := inlineVals.push (⟨mkIdent (Name.mkSimple (pname ++ "Str"))⟩ : TSyntax `ident)
        else if cfg.intro.contains pname then
          postFields := postFields.push (← buildRawPair pname id isMany)
        else if cfg.clear.contains pname then
          preFields := preFields.push (← buildRawPair pname id isMany)
        else
          bothFields := bothFields.push (← buildRawPair pname id isMany)
    | _ => pure ()
  -- ④ recordStep / recordStrategy 调用（内联字段 / clear / intro / neither 四组传入）
  let inlineFields ← buildFields inlineNames inlineVals
  let recCall ← if cfg.strategy then
      `(doElem| recordStrategy $(Lean.quote name) (($strategyCasesId:ident).getString.splitOn "\n") [$inlineFields,*] [$preFields,*] [$postFields,*] [$bothFields,*] (ProofScript.withScriptMode (Lean.Elab.Tactic.evalTactic (← $callQuot:term))))
    else
      `(doElem| recordStep $(Lean.quote name) [$inlineFields,*] [$preFields,*] [$postFields,*] [$bothFields,*] (ProofScript.withScriptMode (Lean.Elab.Tactic.evalTactic (← $callQuot:term))))
  let bodyElems := inlineElems.push recCall.raw
  -- ⑤ 组装录制版 elab 并执行：先 `elabSyntax` 算录制版 kind（一次），再 `elab_rules (kind := …)` 注册，
  --    避免 `elab` 命令内部二次 `elabSyntax` 因 `mkUnusedBaseName` 冲突产生不一致的 `_1` 后缀。
  --    同时把「名字 → 录制版 kind」存进 ref，供录制重写精确替换 kind
  --    （`by_cases` 等与 Lean 原生同名策略，本体 kind 带 `_1` 后缀，无法从本体 kind 字符串截取推导）。
  let (recStxParts, recPatArgs) := (← recArgs.mapM expandMacroArg).unzip
  let recKind ← elabSyntax (← `(syntax $[$recStxParts]* : $tacticCat))
  let recPat := ⟨mkNode recKind recPatArgs⟩
  let recKindId : TSyntax `ident := ⟨mkIdent recKind⟩
  let doSeq : TSyntax ``doSeqIndent := ⟨mkDoSeq bodyElems⟩
  let recCmd ← `(command| elab_rules (kind := $recKindId) : $tacticCat | `($recPat) => do $doSeq:doSeqIndent)
  elabCommand (eraseMacroScopes recCmd.raw)
  -- ⑥ 存「名字 → 录制版 kind」映射，两路：
  --    编译时 `IO.Ref.modify`（同文件可见）+ 生成 `initialize` 块（后续 import 的模块运行时可见）。
  --    这样录制路径能精确替换本体 kind（含 `_1` 后缀）为录制版 kind。
  registerRecordingKind name recKind

/-! ### 配置项（`intro` / `clear` / `recorder` / `strategy`） -/

/-- 配置值：`[ident, ident, …]`（可空 `[]`）。直接写标识符名（与 `syntax` 参数名一致），
    不带双引号、不经 `evalExprWithElab` 求值——从语法树里直接取 ident 名字。 -/
def scriptCfgIdents := leading_parser "[" >> sepBy ident ", " >> "]"

def scriptCfgBool := leading_parser nonReservedSymbol "true" <|> nonReservedSymbol "false"

def scriptCfgItem := leading_parser
  (atomic ("intro" >> ":=" >> scriptCfgIdents)) <|>
  (atomic ("clear" >> ":=" >> scriptCfgIdents)) <|>
  (atomic (nonReservedSymbol "recorder" >> ":=" >>
    (nonReservedSymbol "auto" <|> nonReservedSymbol "exclusive"))) <|>
  (atomic ("strategy" >> ":=" >> scriptCfgBool))

def scriptCfg := leading_parser "(" >> sepBy scriptCfgItem ", " >> ")"

/-- 递归收集语法树中所有 ident 的名字（配置值 `[a, b]` 里只有 ident 与 `[`/`]`/`,` 标点，
    直接遍历取 ident 名）。 -/
partial def collectIdentNames (stx : Syntax) : List String :=
  if stx.isIdent then [stx.getId.toString]
  else stx.getArgs.toList.flatMap collectIdentNames

/-- 递归收集配置项中的 atom，用于不依赖内部节点下标地读取关键字与布尔值。 -/
partial def collectAtomValues (stx : Syntax) : List String :=
  if stx.isAtom then [stx.getAtomVal]
  else stx.getArgs.toList.flatMap collectAtomValues

/-- 解析 `script_macro`/`script_elab` 的配置括号，返回 `ScriptCfg`。
    配置值是标识符列表，名字直接取自语法树，不再经编译期 `evalExprWithElab` 求值。 -/
private def parseScriptCfg  (cfg : Syntax)
                            : CommandElabM ScriptCfg := do
  let mut result : ScriptCfg := {
    intro := [],
    clear := [],
    recorder := .auto,
    strategy := false
  }
  for item in cfg.getArgs[1]!.getArgs do
    if item.isAtom then continue
    let atoms := collectAtomValues item
    match atoms.head? with
    | some "intro" => result := { result with intro := collectIdentNames item }
    | some "clear" => result := { result with clear := collectIdentNames item }
    | some "recorder" =>
        result := { result with recorder := if atoms.contains "exclusive" then .exclusive else .auto }
    | some "strategy" => result := { result with strategy := atoms.contains "true" }
    | _ => pure ()
  pure result

/-- 校验 `intro`/`clear` 配置里提到的参数名都真实存在于 syntax 参数中（`cases` 是分支名，不校验），
    把拼写错误从「静默失效」变成编译期报错。 -/
private def validateCfgParams (name : String)
                              (cfg : ScriptCfg)
                              (args : Array (TSyntax ``macroArg))
                              : CommandElabM Unit := do
  let paramNames : List String := (args.filterMap fun
    | `(macroArg| $id:ident:$_) => some id.getId.toString
    | _ => none).toList
  for p in cfg.intro ++ cfg.clear do
    unless paramNames.contains p do
      throwError m!"[script config] '{name}': 配置里的参数 '{p}' 不在 syntax 参数 {paramNames} 中"

/-! ### `script_macro` / `script_elab` 命令 -/

 /-- 记录概略策略元数据。策略合法性由 `ScriptTacticKindsRef` 判断。 -/
private def registerStrategyMetadata (name : String)
                                     (strategy : Bool)
                                     : CommandElabM Unit := do
  if strategy then
    liftIO <| ScriptStrategiesRef.modify <|
      fun cur => if cur.contains name then cur else cur ++ [name]
    let stratInit := s!"initialize do ProofScript.ScriptStrategiesRef.modify (fun cur => if cur.contains \"{name}\" then cur else cur ++ [\"{name}\"])"
    match runParserCategory (← getEnv) `command stratInit with
    | .ok stx => elabCommand stx
    | .error e => throwError m!"[script config] strategy metadata initialization failed for '{name}': {e}"

/-- 提取策略名（首个字符串字面量）。 -/
private def extractName (args : Array Syntax)
                        : CommandElabM String := do
  match args[0]! with
  | `(macroArg| $s:str) => pure s.getString
  | _ => throwError "script_macro/script_elab/script_recorder: 第一个参数必须是字符串字面量（策略名）"

def tacticCategory := nonReservedSymbol "tactic"
def scriptMacroTacticTail := leading_parser atomic (" : " >> tacticCategory) >> darrow >> macroRhs
def scriptElabTacticTail := leading_parser
  atomic (" : " >> tacticCategory) >> darrow >> withPosition termParser

/-! These names are already parsed by Lean (or by an explicitly imported tactic
    package). A second parser declaration with the same spelling changes the
    parser choice used by ordinary `by` proofs. They remain valid script
    strategies through their generated `script_` entry points. -/
def nativeTacticNames : List String := [
  "assumption", "apply", "change", "contradiction", "exact", "exfalso", "have",
  "intro", "rfl", "simp", "simpa", "symm", "trivial", "unfold", "omega", "rw",
  "rename_i", "clear", "constructor", "cases", "induction", "refine", "first",
  "all_goals", "focus", "repeat", "try", "solve", "done", "continuity",
  "exact_mod_cast", "field", "gcongr", "itauto", "itauto!", "linarith", "linarith!",
  "measurability", "nlinarith", "nlinarith!", "norm_cast", "norm_num", "positivity",
  "qify", "rify", "ring", "tauto", "wlog", "zify"
]

def isNativeTacticName (name : String) : Bool := nativeTacticNames.contains name

 /-- `script_macro`：生成 `script_` 执行入口和独立录制入口。
     复用 `macro` 命令的参数和 RHS parser，但固定为显式的 `: tactic`。 -/
@[command_parser] def scriptMacro := leading_parser
  suppressInsideQuot <|
    optional docComment >> "script_macro" >> optional scriptCfg >> many1 (ppSpace >> macroArg) >> scriptMacroTacticTail

 /-- `script_elab`：生成 `script_` 执行入口和独立录制入口。 -/
@[command_parser] def scriptElab := leading_parser
  suppressInsideQuot <|
    optional docComment >> "script_elab" >> optional scriptCfg >> many1 (ppSpace >> macroArg) >> scriptElabTacticTail

/-- `script_recorder`：为禁用自动录制的策略手写 `_script_<name>` elaborator。
    参数形式与 `script_elab` 相同，但首个字符串仍填写不带前缀的原策略名。 -/
@[command_parser] def scriptRecorder := leading_parser
  suppressInsideQuot <|
    optional docComment >> "script_recorder" >> many1 (ppSpace >> macroArg) >> scriptElabTacticTail

open Lean.Elab.Command in
elab_rules : command
  | `(command| $[$doc?:docComment]? script_macro%$_tk $[$cfg:scriptCfg]? $args:macroArg* : tactic => $rhs) => do
    let tacticCat : TSyntax `ident := ⟨mkIdent `tactic⟩
    let name ← extractName args
    let cfg' ← match cfg with
      | some c => parseScriptCfg c
      | none => pure emptyScriptCfg
    validateCfgParams name cfg' args
    if cfg'.recorder == .auto then validateParamKinds name args
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    let kind ← if isNativeTacticName name then
      pure `tactic
    else
      elabSyntax (← `(syntax $[$stxParts]* : $tacticCat))
    let _pat : TSyntax `term := ⟨mkNode kind patArgs⟩
    let prefixedArgs : Array (TSyntax ``macroArg) := args.mapIdx fun i a => if i == 0 then (⟨mkScriptNameArg name⟩ : TSyntax ``macroArg) else a
    let (prefixedParts, prefixedPatArgs) := (← prefixedArgs.mapM expandMacroArg).unzip
    let prefixedKind ← elabSyntax (← `(syntax $[$prefixedParts]* : $tacticCat))
    let prefixedPat : TSyntax `term := ⟨mkNode prefixedKind prefixedPatArgs⟩
    let rhsRaw := rhs.raw
    let macroRulesCmd ←
      if rhsRaw.getArgs.size == 1 then
        let rhsTerm := ⟨rhsRaw[0]⟩
        `(macro_rules | `($prefixedPat) => $rhsTerm >>= ProofScript.wrapScriptMacroResult)
      else
        let rhsBody := ⟨rhsRaw[1]⟩
        `(macro_rules | `($prefixedPat) => `($rhsBody) >>= ProofScript.wrapScriptMacroResult)
    -- The generated name is prefixed, so this cannot shadow Lean's native
    -- tactic even when `name` itself is a native tactic.
    elabCommand macroRulesCmd
    -- ② 生成录制版（复用本体的 `pat`，纯语法级）；`exclusive` 时由用户手写录制版
    if cfg'.recorder == .auto then genRecording name ("script_" ++ name) args prefixedPat.raw cfg' else pure ()
    liftIO <| ScriptTacticKindsRef.modify (fun cur =>
      if cur.any (fun (n, _) => n == name) then cur else cur ++ [(name, prefixedKind)])
    let kindInit ← `(command| initialize do ProofScript.ScriptTacticKindsRef.modify (fun cur =>
      if cur.any (fun (n, _) => n == $(Lean.quote name)) then cur
      else cur ++ [($(Lean.quote name), $(Lean.quote prefixedKind))]))
    elabCommand (eraseMacroScopes kindInit.raw)
    let recordingKind ← if cfg'.recorder == .auto then do
      pure <| (← getScriptRecordingKinds).find? (fun (n, _) => n == name) |>.map Prod.snd
    else pure none
    registerTacticRegistration {
      name := name
      sourceKind := kind
      executionKind := prefixedKind
      recordingKind := recordingKind
      «strategy» := cfg'.strategy
    }
    -- ③ 记录策略元数据
    registerStrategyMetadata name cfg'.strategy

open Lean.Elab.Command in
elab_rules : command
  | `(command| $[$doc?:docComment]? script_elab%$_tk $[$cfg:scriptCfg]? $args:macroArg* : tactic => $rhs) => do
    let tacticCat : TSyntax `ident := ⟨mkIdent `tactic⟩
    let name ← extractName args
    let cfg' ← match cfg with
      | some c => parseScriptCfg c
      | none => pure emptyScriptCfg
    validateCfgParams name cfg' args
    if cfg'.recorder == .auto then validateParamKinds name args
    -- 定义仅带 `script_` 前缀的执行版 elaborator。
    let (stxParts, patArgs) := (← args.mapM expandMacroArg).unzip
    let kind ← if isNativeTacticName name then
      pure `tactic
    else
      elabSyntax (← `(syntax $[$stxParts]* : $tacticCat))
    let _pat : TSyntax `term := ⟨mkNode kind patArgs⟩
    let prefixedArgs : Array (TSyntax ``macroArg) := args.mapIdx fun i a => if i == 0 then (⟨mkScriptNameArg name⟩ : TSyntax ``macroArg) else a
    let (prefixedParts, prefixedPatArgs) := (← prefixedArgs.mapM expandMacroArg).unzip
    let prefixedKind ← elabSyntax (← `(syntax $[$prefixedParts]* : $tacticCat))
    let prefixedPat : TSyntax `term := ⟨mkNode prefixedKind prefixedPatArgs⟩
    elabCommand (← `(elab_rules : $tacticCat | `($prefixedPat) => ProofScript.withScriptMode $rhs))
    -- ② 生成录制版（复用本体的 `pat`，纯语法级）；`exclusive` 时由用户手写录制版
    if cfg'.recorder == .auto then genRecording name ("script_" ++ name) args prefixedPat.raw cfg' else pure ()
    liftIO <| ScriptTacticKindsRef.modify (fun cur =>
      if cur.any (fun (n, _) => n == name) then cur else cur ++ [(name, prefixedKind)])
    let kindInit ← `(command| initialize do ProofScript.ScriptTacticKindsRef.modify (fun cur =>
      if cur.any (fun (n, _) => n == $(Lean.quote name)) then cur
      else cur ++ [($(Lean.quote name), $(Lean.quote prefixedKind))]))
    elabCommand (eraseMacroScopes kindInit.raw)
    let recordingKind ← if cfg'.recorder == .auto then do
      pure <| (← getScriptRecordingKinds).find? (fun (n, _) => n == name) |>.map Prod.snd
    else pure none
    registerTacticRegistration {
      name := name
      sourceKind := kind
      executionKind := prefixedKind
      recordingKind := recordingKind
      «strategy» := cfg'.strategy
    }
    -- ③ 记录策略元数据
    registerStrategyMetadata name cfg'.strategy

open Lean.Elab.Command in
elab_rules : command
  | `(command| $[$doc?:docComment]? script_recorder%$_tk $args:macroArg* : tactic => $rhs) => do
    let tacticCat : TSyntax `ident := ⟨mkIdent `tactic⟩
    let name ← extractName args
    let recArgs : Array (TSyntax ``macroArg) := args.mapIdx fun i a =>
      if i == 0 then (⟨mkNameArg ("script_" ++ name)⟩ : TSyntax ``macroArg) else a
    let (recParts, recPatArgs) := (← recArgs.mapM expandMacroArg).unzip
    let recKind ← elabSyntax (← `(syntax $[$recParts]* : $tacticCat))
    let recPat : TSyntax `term := ⟨mkNode recKind recPatArgs⟩
    elabCommand (← `(elab_rules : $tacticCat | `($recPat) => $rhs))
    registerRecordingKind name recKind
    setRegistrationRecordingKind name recKind

end ProofScript
