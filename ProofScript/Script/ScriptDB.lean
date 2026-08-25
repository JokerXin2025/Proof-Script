import Lean

/-!
# Script 数据库（供 `embed` 重放）

`#theorem T … := script …` 在声明定理时，把**原始脚本语法**（未经
underscore、未经展平）连同定理类型语法一起注册到这里，随环境持久化进 `.olean`，
跨模块可读。`embed` 在应用某个定理时据此重放它的证明步骤。

存储的是**原始 `scriptStmt+` 语法树**（含 `| branch =>`、原始策略名），
不做任何变换——这样未来 `embed` 若要「改写被嵌入的脚本」做优化（如参数代入、
分类 proof/data 参数），拿到的是最完整、最容易改写的输入。
-/

namespace ProofScript

open Lean

/-- 存储 `Name → Syntax` 的持久环境扩展。键是定理名，值是一个 `scriptData` 节点。 -/
initialize scriptDB : MapDeclarationExtension Syntax ←
  mkMapDeclarationExtension `ProofScript.scriptDB

/-- `scriptData` 节点的布局：`[0]` = 定理类型语法（`term`），`[1..]` = 各 `scriptStmt`。
    用单一 `Syntax` 节点打包，是因为 `MapDeclarationExtension` 的条目类型经
    `DataValue.ofSyntax` 序列化，必须是单个 `Syntax`。 -/
def mkScriptData (typeStx : Syntax) (stmts : Array Syntax) : Syntax :=
  Syntax.node (typeStx.getHeadInfo) `ProofScript.scriptData
    (stmts.foldl (init := #[typeStx]) (fun acc s => acc.push s))

/-- 注册一个定理的脚本（由 `#theorem` 调用）。返回更新后的环境。 -/
def registerScript (env : Environment) (name : Name) (typeStx : Syntax)
    (stmts : Array Syntax) : Environment :=
  scriptDB.insert env name (mkScriptData typeStx stmts)

/-- 查询定理的脚本数据节点；`none` = 未注册（不是 script 书写的定理）。 -/
def findScript (env : Environment) (name : Name) : Option Syntax :=
  scriptDB.find? env name

/-- 从 `scriptData` 节点解出 `(类型语法, scriptStmt 数组)`。 -/
def scriptDataParts (data : Syntax) : Syntax × Array Syntax :=
  (data.getArg 0, data.getArgs[1:])

end ProofScript
