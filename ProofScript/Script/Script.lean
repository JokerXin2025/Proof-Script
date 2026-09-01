import ProofScript.Script.Core
import ProofScript.Script.Record
import ProofScript.Script.Config
import ProofScript.Script.ScriptDB
import ProofScript.Extension.Page.Path
import ProofScript.Extension.Page.State
import ProofScript.References.Metadata

open Lean
open Lean.Parser.Tactic (tacticSeq tacticSeq1Indented inductionAlt case caseArg)
open Lean.Elab.Tactic (evalTactic)


namespace ProofScript

/-! ## `script` 脚本语法

脚本 body 的每一行既可以是普通 tactic（`tacticSeq`），也可以是模式匹配分支
`| branch => ...`（复用 Lean 的 `inductionAlt`）。后者不是独立 tactic，
需要在 macro 展开时转换为 `case branch => ...` -/

syntax scriptStmt := (ppDedent(ppLine) tacticSeq) <|> inductionAlt

/-! 缩进敏感的 `scriptStmt+`：仿 `inferSteps`，用单个 `withPosition` 包裹整个序列，
    `colGe` 要求每个 scriptStmt 的缩进列 ≥ 首 stmt 缩进列，从而把「同缩进/更浅的后续 tactic」
    排除在 script 块之外（避免 `have h : P := script …` 的子证明贪婪吞掉下一行 tactic）。 -/
syntax scriptStmts := withPosition(ppLine (colGe scriptStmt) (ppLine linebreak (colGe scriptStmt))*)

/-- 从 `scriptStmts` 节点提取 scriptStmt 数组。结构：`[首 stmt, (linebreak colGe scriptStmt)* 节点]`。 -/
def scriptStmtsToArray (stmts : Syntax) : Array Syntax :=
  if h : stmts.getArgs.size >= 2 then
    #[stmts[0]] ++ stmts[1].getArgs
  else
    #[stmts[0]]

/-! ## `| branch =>` → `case branch =>` 语法转换（保留位置） -/

/-- 将 `ident` 节点包装为 `binderIdent` 节点（`case` 的 tag/binder 需要）。 -/
private def identToBinderIdent (id : Syntax) : Syntax := Syntax.node id.getHeadInfo `Lean.binderIdent #[id]

/-- 将 `inductionAlt`（`| tag binders => body`）转换为 `case tag binders => body`，
    复用原始 ident / tacticSeq 节点并继承其位置。 -/
def inductionAltToCase (alt : Syntax) : Syntax :=
  let lhs := alt.getArg 0 |>.getArg 0
  let body := alt.getArg 1 |>.getArg 1
  let lhsArgs := lhs.getArgs
  let tagIdent := lhsArgs[1]!.getArgs[1]!
  let binderIdents := lhsArgs[2]!.getArgs
  let tagBI := identToBinderIdent tagIdent
  let binderBIs := binderIdents.map identToBinderIdent
  let caseArg := Syntax.node tagIdent.getHeadInfo ``caseArg #[tagBI, mkNullNode binderBIs]
  Syntax.node alt.getHeadInfo ``case #[mkAtomFrom alt "case", mkNullNode #[caseArg], mkAtomFrom alt "=>", body]

/-- 提取 `| tag binders => body` 的分支标签。 -/
def inductionAltTag (alt : Syntax) : String :=
  let lhs := alt.getArg 0 |>.getArg 0
  lhs.getArgs[1]!.getArgs[1]!.getId.toString

/-- 从 `scriptStmt+` 提取所有 tactic（普通行展平，`|` 行转成 `case`）。 -/
def collectTactics (stmts : Array Syntax) : Array Syntax :=
  stmts.foldl (fun tactics s =>
    let inner := s.getArg 0
    if inner.getKind == ``inductionAlt then
      tactics.push (inductionAltToCase inner)
    else
      let seqNode := inner.getArg 0
      if seqNode.getKind == ``tacticSeq1Indented then
        seqNode.getArgs.foldl (fun ts n =>
          n.getArgs.foldl (fun ts2 x => if x.isAtom then ts2 else ts2.push x) ts
        ) tactics
      else
        tactics.push inner
  ) #[]

/-- 将 tactic 数组组装为 `tacticSeq`（tactic 间插入 `;` 分隔符），
    容器节点继承第一个 tactic 的位置，避免错误定位到文件开头。 -/
def buildTacticSeq (tactics : Array Syntax) : Syntax :=
  let headInfo := if tactics.isEmpty then SourceInfo.none else tactics[0]!.getHeadInfo
  let parts := tactics.toList.foldl (fun acc t =>
    if acc.isEmpty then [t] else acc ++ [mkAtomFrom t ";", t]) []
  let nullNode := mkNullNode parts.toArray
  let seq1 := Syntax.node headInfo ``tacticSeq1Indented #[nullNode]
  Syntax.node headInfo ``tacticSeq #[seq1]

/-! ## 策略名验证 -/

/-- 找到 tactic 语法中的第一个 atom（即策略名，如 `provide`/`exact`/`split_and`）。 -/
partial def findFirstAtom (t : Syntax) : Option Syntax :=
  if t.isAtom then some t
  else t.getArgs.findSome? findFirstAtom

/-- 从策略名 atom 构造 ident（位置关联到原 atom），用于 `check_script_step` 参数。 -/
def tacticNameIdent (t : Syntax) : Option Syntax :=
  match findFirstAtom t with
  | some atom =>
      let s := atom.getAtomVal
      if s.all (fun c => c.isAlphanum || c == '_') then
        some (mkIdentFrom atom s.toName)
      else none
  | none => none

/-- 从 tactic 语法中提取策略名字符串（先序遍历第一个 atom）。 -/
def firstAtomName (t : Syntax) : Option String :=
  match findFirstAtom t with
  | some atom => some atom.getAtomVal
  | none => none

/-- 换节点 kind 并保留 SourceInfo。`mkNode` 用 `SourceInfo.none` 会丢位置信息，
    悬浮提示/报错定位会漂到生成器而非用户代码，故用 `Syntax.node stx.getHeadInfo …`。 -/
def changeNodeKind (stx : Syntax) (newKind : Name) (args : Array Syntax) : Syntax :=
  Syntax.node stx.getHeadInfo newKind args

def scriptTacticName (name : String) : String := "script_" ++ name

def recordingTacticName (name : String) : String := "_" ++ scriptTacticName name

def scriptTacticBaseName? (name : String) : Option String :=
  if name.startsWith "script_" then some (name.drop 7 |>.toString) else none

/-- Select the registered parser candidate without descending into tactic arguments. -/
def registeredTacticCall (registrations : List ScriptTacticRegistration) (name : String)
    (t : Syntax) : Option (ScriptTacticRegistration × Syntax) :=
  let matching := registrations.filter (·.name == name)
  let exact := if t.getKind == `choice then
    t.getArgs.findSome? fun candidate =>
      registrations.find? (fun r => r.name == name && r.sourceKind == candidate.getKind)
        |>.map (·, candidate)
  else
    registrations.find? (fun r => r.name == name && r.sourceKind == t.getKind)
      |>.map (·, t)
  exact <|> match matching with
    | [registration] =>
        if t.getKind == `choice then
          t.getArgs.findSome? fun candidate =>
            if firstAtomName candidate == some name then some (registration, candidate) else none
        else some (registration, t)
    | _ => none

/-- Rewrite only a tactic call's root kind and direct keyword token. All parameter syntax is reused. -/
def rewriteTacticCall (call : Syntax) (sourceName targetName : String)
    (targetKind : Name) : Except String Syntax := do
  let some tokenIdx := call.getArgs.findIdx? fun arg =>
      arg.isAtom && arg.getAtomVal == sourceName
    | throw s!"cannot find tactic keyword `{sourceName}` in registered call"
  let args := call.getArgs.set! tokenIdx (mkAtomFrom call.getArgs[tokenIdx]! targetName)
  return changeNodeKind call targetKind args

/-- 把一个 `scriptStmt` 的内层语法展平为 tactic 数组（处理 `;` 与缩进序列）。
    跳过 atom（`;` 分隔符）与 `null`（`;` 的 optional 包裹/空标记）节点。 -/
def flattenTactics (inner : Syntax) : Array Syntax :=
  let seqNode := inner.getArg 0
  if seqNode.getKind == ``tacticSeq1Indented then
    seqNode.getArgs.foldl (fun ts n =>
      n.getArgs.foldl (fun ts2 x => if x.isAtom || x.getKind == `null then ts2 else ts2.push x) ts
    ) #[]
  else
    #[inner]

/-- 收集策略调用后连续出现的 `| case =>` 分支名。 -/
def collectFollowingStrategyCases (stmts : Array Syntax) (start : Nat) : List String := Id.run do
  let mut nodes : List String := []
  let mut i := start
  while i < stmts.size do
    let inner := stmts[i]!.getArg 0
    if inner.getKind != ``inductionAlt then break
    nodes := nodes ++ [inductionAltTag inner]
    i := i + 1
  return nodes

/-- Hint mapping table for Lean native tactics -/
def nativeHintMap : List (String × String) := [
  ("apply", "Use `apply` with a proposition of the form `P -> Q` or `P <-> Q`."),
  ("exact", "Use `provide` only for existential witnesses; it is not a general `exact`."),
  ("intro", "Use `intro_h` or `by_contra` instead of `intro`."),
  ("rw", "Use `rewrite` instead of `rw`."),
  ("rfl", "Use `trivial` instead of `rfl`."),
  ("assumption", "Use `trivial` instead of `assumption`."),
  ("trivial", "`trivial` is already allowed in `script` blocks."),
  ("contradiction", "Use `trivial` instead of `contradiction`."),
  ("tauto", "Use `trivial` instead of `tauto`."),
  ("symm", "Use `symm` — it is allowed in `script` blocks."),
  ("unfold", "Use `unfold` — it is allowed in `script` blocks."),
  ("change", "Use `rewrite` instead of `change`."),
  ("simp", "Use `simp` — it is allowed in `script` blocks."),
  ("omega", "Use `omega` — it is allowed in `script` blocks."),
  ("dsimp", "Use `simp` instead of `dsimp`."),
  ("simpa", "Use `simp` instead of `simpa`."),
  ("ring", "Use `ring` — it is allowed in `script` blocks."),
  ("linarith", "Use `linarith` — it is allowed in `script` blocks."),
  ("nlinarith", "Use `nlinarith` — it is allowed in `script` blocks."),
  ("norm_num", "Use `norm_num` — it is allowed in `script` blocks."),
  ("field", "Use `field` — it is allowed in `script` blocks."),
  ("field_simp", "Use `field` instead of `field_simp`."),
  ("have", "Use a subgoal block instead of `have`."),
  ("refine", "Use `provide` or `apply` instead of `refine`."),
  ("rcases", "Use `cases_on` or `obtain_exist` instead of `rcases`."),
  ("obtain", "Use `obtain` — it is allowed in `script` blocks."),
  ("by_cases", "Use `cases_on` — it is allowed in `script` blocks."),
  ("by_contra", "Use `by_contra` — it is allowed in `script` blocks."),
  ("exfalso", "Use `trivial` instead of `exfalso`.")
]

/-- Validate and execute one script tactic through its registered prefixed parser kind. -/
elab "run_script_step" name:ident call:tactic : tactic => do
  let nameStr := name.getId.toString
  let registrations ← getScriptTacticRegistrations
  let some (registration, sourceCall) := registeredTacticCall registrations nameStr call.raw
    | let hint := (ProofScript.nativeHintMap.lookup nameStr).getD "unknown script tactic"
      withRef name (throwError hint)
  let rewritten ← match rewriteTacticCall sourceCall nameStr (scriptTacticName nameStr)
      registration.executionKind with
    | .ok rewritten => pure rewritten
    | .error message => withRef call (throwError message)
  withScriptMode <| evalTactic (⟨rewritten⟩ : TSyntax `tactic)

/-! ## `:= script` Syntax -/

/-- 递归检查 tactic 序列：普通 tactic 前注入 `check_script_step` 验证；`case` 分支递归
     检查其 body 内的 tactic（否则分支内的策略会绕过校验）。 -/
private partial def checkScriptStep (t : Syntax)
                                    : MacroM (Array Syntax) := do
  if t.getKind == ``case then
    let body := t[3]
    let mut checkedInner := #[]
    for x in flattenTactics body do
      checkedInner := checkedInner ++ (← checkScriptStep x)
    let newBody := buildTacticSeq checkedInner
    let newCase := Syntax.node t.getHeadInfo ``case #[t[0], t[1], t[2], newBody]
    return #[newCase]
  else if t.getKind == `Lean.Parser.Tactic.bullet then
    Macro.throwError "Bullets (·) are not allowed in `script` block. Use explicit `| branch =>` syntax."
  else
    match tacticNameIdent t with
    | some name =>
        let name' : TSyntax `ident := ⟨name⟩
        let call : TSyntax `tactic := ⟨t⟩
        let run ← `(tactic| run_script_step $name':ident $call:tactic)
        return #[run]
    | none => return #[t]

/-- `:= script` term：展开为 `by <tactic 序列>`，每个策略（含 `| branch =>` 分支内的）前
    注入 `check_script_step` 验证。禁止 `·` bullet（要求用 `| branch =>` 显式分支）。 -/
macro "script" stmts:scriptStmts : term => do
  let stmtsArray := scriptStmtsToArray stmts
  let tactics := collectTactics stmtsArray
  let mut checked := #[]
  for t in tactics do
    checked := checked ++ (← checkScriptStep t)
  let seq := ⟨buildTacticSeq checked⟩
  `(by $seq:tacticSeq)

/-! ## `#theorem` / `#lemma` Syntax -/

/-! ## 录制版代码生成（语法级）
1. 普通 tactic 与 `case` 分支内的 tactic 切换到注册的录制入口；
2. 概略分支之间插入 `_next_strategy_case`（推进录制 box）；
3. 末尾生成 `ProofScript` 合并命令（串起 info 与各分支子 box）。 -/
open Lean.Elab.Command in
 /-- 递归校验并改写：普通 tactic 校验注册表后切换录制入口；`case` 分支递归校验其 body
     （否则分支内的策略会绕过校验）。
    泛型到任意具备 `MonadRef`/`MonadError`/`MonadOptions` 的 monad，使 `CommandElabM`
    （`#theorem`）与 `TacticM`（`embed` 重放）都能调用。 -/
private partial def validateAndUnderscore {m : Type → Type}
                                          [Monad m]
                                          [MonadRef m]
                                          [MonadError m]
                                          [MonadOptions m]
                                            (registrations : List ScriptTacticRegistration)
                                           (t : Syntax)
                                           : m Syntax := do
  if t.getKind == ``case then
    let body := t[3]
    let mut newInner : Array Syntax := Array.empty
    for x in flattenTactics body do
      newInner := newInner.push (← validateAndUnderscore (m := m) registrations x)
    let newBody := buildTacticSeq newInner
    return Syntax.node t.getHeadInfo ``case #[t[0], t[1], t[2], newBody]
  else
    match firstAtomName t with
    | some nm =>
      let some (registration, sourceCall) := registeredTacticCall registrations nm t
        | let hint := (nativeHintMap.lookup nm).getD "未知script策略"
          withRef t (throwError hint)
      let some recordingKind := registration.recordingKind
        | withRef t (throwError m!"script strategy `{nm}` has no recorder")
      match rewriteTacticCall sourceCall nm (recordingTacticName nm) recordingKind with
      | .ok rewritten => return rewritten
      | .error message => withRef t (throwError message)
    | none => return t

/-- 给自动生成的概略录制 tactic 追加调用处推导出的隐藏分支参数。节点 kind 已换成
    `_strategy` 的录制 kind，参数布局末尾与 `genRecording`
    生成的 `"_strategy_cases" str` 一致。 -/
def appendStrategyCases (t : Syntax) (nodes : List String) : Syntax :=
  let encoded := String.intercalate "\n" nodes
  changeNodeKind t t.getKind <|
    t.getArgs.push (mkAtomFrom t "_strategy_cases") |>.push (Syntax.mkStrLit encoded t.getHeadInfo)

syntax "_merge_strategy" str str : tactic

open Lean.Elab.Command in
/-- 语法级录制变换：把 `scriptStmt` 序列转成录制版 tactic 序列。
    调用处动态收集每个概略策略后连续的 `| branch =>`，注入录制 tactic，并在分支结束时
    插入即时合并步骤。校验策略名合法性（含分支内），
    非法时用 `nativeHintMap` 报错。
    泛型到 `CommandElabM`（`#theorem`）与 `TacticM`（`embed` 重放）。 -/
def collectRecordTactics {m : Type → Type} [Monad m] [MonadQuotation m] [MonadRef m]
    [MonadError m] [MonadOptions m] [MonadLiftT IO m]
                                  (stmts : Array Syntax)
                                   : m (Array Syntax) := do
  let registrations ← getScriptTacticRegistrations
  let strategies := registrations.filterMap fun r => if r.strategy then some r.name else none
  let mut out : Array Syntax := #[]
  let mut pendingStrategy : Option (String × List String) := none
  let mut needsAdvance := false
  for i in [:stmts.size] do
    let s := stmts[i]!
    let inner := s.getArg 0
    if inner.getKind == ``inductionAlt then
      let caseStx := inductionAltToCase inner
      let caseStx' ← validateAndUnderscore (m := m) registrations caseStx
      if needsAdvance then
        out := out.push (← `(tactic| _next_strategy_case)).raw
      out := out.push caseStx'
      needsAdvance := true
     else
      -- 概略策略的最后一个分支结束后，若还有普通续接步骤（如 `have h : P | proof => …` 之后的
      -- `<rest>`），先插入 `_next_strategy_case` 把录制 box 从分支推进回主 box，再处理续接步骤。
      if needsAdvance then
        out := out.push (← `(tactic| _next_strategy_case)).raw
        needsAdvance := false
        match pendingStrategy with
        | some (name, nodes) =>
            let encoded := String.intercalate "\n" nodes
            out := out.push (← `(tactic| _merge_strategy $(Syntax.mkStrLit name) $(Syntax.mkStrLit encoded))).raw
            pendingStrategy := none
        | none => pure ()
      for t in flattenTactics inner do
        match firstAtomName t with
        | some nm =>
          if strategies.contains nm then
            let nodes := collectFollowingStrategyCases stmts (i + 1)
            if nodes.isEmpty then
              withRef t <| throwError m!"strategy `{nm}` requires at least one explicit `| case =>` branch"
            pendingStrategy := some (nm, nodes)
            needsAdvance := false
        | none => pure ()
        let t' ← validateAndUnderscore (m := m) registrations t
        let t' := match firstAtomName t with
          | some nm =>
              if strategies.contains nm then
                appendStrategyCases t' (collectFollowingStrategyCases stmts (i + 1))
              else t'
          | none => t'
        out := out.push t'
  if needsAdvance then
    out := out.push (← `(tactic| _next_strategy_case)).raw
    match pendingStrategy with
    | some (name, nodes) =>
        let encoded := String.intercalate "\n" nodes
        out := out.push (← `(tactic| _merge_strategy $(Syntax.mkStrLit name) $(Syntax.mkStrLit encoded))).raw
        pendingStrategy := none
    | none => pure ()
  return out

/-- 概略策略的合并：把 info 子 box 与各分支子 box 合并进主 box（直接操作 `JSON_boxes`，
    替代旧的 `ProofScript <box> <-` 命令，不再依赖 `Tactics.lean`）。
    合并结果原位替换 `recordStrategy` 写入主 box（`mainTag`）的占位符；找不到占位符时
    退回追加（兼容手写录制策略）：
    `{"name": stepName, "info": <info 子 box 第一个值>, <node>: [<分支子 box 数组>], ...}`
    - `mainTag_info`：取第一个 JSON 值，键 `"info"`，随后清空该子 box。
    - `mainTag_<node>`：取整个 JSON 数组，键 `<node>`，随后清空该子 box。 -/
def mergeStrategyBoxes (mainTag : String) (stepName : String) (nodes : List String) : IO Unit := do
  let mainName := Name.mkSimple mainTag
  let infoName := Name.mkSimple (mainTag ++ "_info")
  let mut fields : List (String × Json) := [("name", Json.str stepName)]
  let boxes ← JSON_boxes.get
  if let some idx := boxes.findIdx? (fun (b, _) => b == infoName) then
    if !boxes[idx]!.2.isEmpty then
      fields := fields ++ [("info", boxes[idx]!.2[0]!)]
      JSON_boxes.set (boxes.set! idx (infoName, #[]))
  for node in nodes do
    let nodeName := Name.mkSimple (mainTag ++ "_" ++ node)
    let boxes ← JSON_boxes.get
    if let some idx := boxes.findIdx? (fun (b, _) => b == nodeName) then
      fields := fields ++ [(node, Json.arr boxes[idx]!.2)]
      JSON_boxes.set (boxes.set! idx (nodeName, #[]))
  JSON_boxes.modify fun arr =>
    match arr.findIdx? (fun (b, _) => b == mainName) with
    | some idx =>
      let (b, items) := arr[idx]!
      let merged := Json.mkObj fields
      let placeholder := strategyPlaceholderJson stepName
      match items.findIdx? (· == placeholder) with
      | some itemIdx => arr.set! idx (b, items.set! itemIdx merged)
      | none => arr.set! idx (b, items.push merged)
    | none => arr.push (mainName, #[Json.mkObj fields])

elab_rules : tactic
  | `(tactic| _merge_strategy $name:str $nodes:str) => do
      let tag ← currentBoxTag.get
      mergeStrategyBoxes tag name.getString (nodes.getString.splitOn "\n")

syntax declarationKind := "@theorem" <|> "@lemma"
syntax declarationKind ("@[" sepBy1(Lean.Parser.Term.attrInstance, ", ") "]")?
  ident (bracketedBinder)* ":" term ":=" "script" scriptStmts : command
syntax declarationKind ("@[" sepBy1(Lean.Parser.Term.attrInstance, ", ") "]")?
  ident (bracketedBinder)* ":" term ":=" "by " Lean.Parser.Tactic.tacticSeqIndentGt : command

private inductive RecordedDeclarationKind where
  | theorem
  | lemma

private partial def syntaxContainsAtom (value : String) (stx : Syntax) : Bool :=
  (stx.isAtom && stx.getAtomVal == value) || stx.getArgs.any (syntaxContainsAtom value)

private def declarationKindOfSyntax (stx : Syntax) : RecordedDeclarationKind :=
  if syntaxContainsAtom "@lemma" stx then .lemma else .theorem

private partial def findScriptTacticAtom? (stx : Syntax) : Option Syntax :=
  if stx.isAtom then
    let value := stx.getAtomVal
    if value.startsWith "script_" || value.startsWith "_script_" then some stx else none
  else
    stx.getArgs.findSome? findScriptTacticAtom?

private def mkDeclarationComponent (kind : RecordedDeclarationKind)
    (data : Extension.DeclarationComponent) : Extension.ComponentData :=
  match kind with
  | .theorem => .theorem data
  | .lemma => .lemma data

open Lean.Elab.Command in
private def addRecordedDeclaration (kind : RecordedDeclarationKind)
    (name : TSyntax `ident) (declName : Name) (proofPath : System.FilePath) : CommandElabM Unit := do
  let location : Extension.SourceLocation := {
    file := ← getFileName
    start := (name.raw.getPos?.getD 0).byteIdx
    stop := (name.raw.getTailPos?.getD (name.raw.getPos?.getD 0)).byteIdx
  }
  let env ← getEnv
  let sorryAx := (← Lean.collectAxioms declName).contains ``sorryAx
  let data : Extension.DeclarationComponent := {
    declName := declName
    name := name.getId.toString
    label := none
    proof := proofPath.toString
    sorryAx := sorryAx
  }
  let component : Extension.Component := {
    source := location
    data := mkDeclarationComponent kind data
  }
  let (nextEnv, added) ← match Extension.addComponent env component with
    | .ok result => pure result
    | .error message => throwErrorAt name message
  unless added do
    logWarningAt name "page component appears after page_end and was ignored"
  setEnv nextEnv

open Lean.Elab.Command in
private def collectDeclarationReferences (declName : Name) : CommandElabM Unit := do
  unless ← referencesEnabled do return
  let env ← getEnv
  let some value := (env.find? declName).bind (·.value? (allowOpaque := true))
    | return
  for constant in value.getUsedConstants do
    if let some info := findTheoremInfo env constant then
      liftIO <| addTheoremRef { name := constant, info := info }

open Lean.Elab.Command in
/-- `#theorem`/`#lemma := script` validates and records each script step. -/
elab_rules : command
| `(command|
    $kind:declarationKind $[@[$attrs:attrInstance,*]]? $name:ident
      $[$bs:bracketedBinder]* : $type:term := script $stmts:scriptStmts
  ) => do
    let kind := declarationKindOfSyntax kind.raw
    let declarationName := name.getId.toString
    let declName := (← getCurrNamespace) ++ name.getId
    let commandStx ← getRef
    let code := String.Pos.Raw.extract (← getFileMap).source
      (commandStx.getPos?.getD 0) (commandStx.getTailPos?.getD (commandStx.getPos?.getD 0))
    resetScriptState
    resetExprJsonState
    pushBoxTag declarationName
    let tactics ← collectRecordTactics (scriptStmtsToArray stmts)
    let seq : TSyntax ``tacticSeq := ⟨buildTacticSeq tactics⟩
    let defCmd ← `(command|
      $[@[$attrs,*]]? def $name $[$bs]* : $type := by $seq:tacticSeq
    )
    elabCommand defCmd
    Lean.Elab.addDeclarationRangesFromSyntax declName (← getRef) name.raw
    let moduleName ← getMainModule
    let proofPath := Extension.proofOutputPath moduleName declName
    let expressions ← getExprJsonTable
    liftCoreM <| exportBoxToFile (Name.mkSimple declarationName) proofPath code expressions
    modifyEnv fun env => registerScriptArtifact env declName proofPath
    addRecordedDeclaration kind name declName proofPath

open Lean.Elab.Command in
/-- `#theorem`/`#lemma := by` accepts arbitrary Lean tactics and exports source only. -/
elab_rules : command
| `(command|
    $kind:declarationKind $[@[$attrs:attrInstance,*]]? $name:ident
      $[$bs:bracketedBinder]* : $type:term := by $seq:tacticSeq
  ) => do
    let kind := declarationKindOfSyntax kind.raw
    let declName := (← getCurrNamespace) ++ name.getId
    if let some tacticName := findScriptTacticAtom? seq.raw then
      throwErrorAt tacticName "`:= by` cannot use Proof-Script tactics; use ordinary Lean tactics"
    let commandStx ← getRef
    let code := String.Pos.Raw.extract (← getFileMap).source
      (commandStx.getPos?.getD 0) (commandStx.getTailPos?.getD (commandStx.getPos?.getD 0))
    let defCmd ← `(command|
      $[@[$attrs,*]]? def $name $[$bs]* : $type := by $seq:tacticSeq
    )
    elabCommand defCmd
    Lean.Elab.addDeclarationRangesFromSyntax declName (← getRef) name.raw
    collectDeclarationReferences declName
    let moduleName ← getMainModule
    let proofPath := Extension.proofOutputPath moduleName declName
    liftCoreM <| exportCodeOnlyProofToFile proofPath code
    addRecordedDeclaration kind name declName proofPath
