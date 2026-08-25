# Proof-Script

Proof-Script 是一个面向 [Lean 4](https://lean-lang.org/) 的编译期语言扩展.
它提供一套结构化、可扩展且语义增强的证明 DSL, 将 Lean 证明的实时目标、策略参数和分支结构录制并导出为 JSON,
同时, Proof-Script 还集成了 ProofText 正文、定理表述、图片、LaTeX SVG 等页面组件, 这些数据将被自动编译并导出为 JSON, 供渲染器或其他下游工具消费.

当前 Proof-Script 使用轻量化命令行工具 Mitar 完成渲染. 您可以通过下面的步骤来快速体验其功能:

1. 从 Github 下载仓库 [JokerXin2025/Mitar](https://www.github.com/JokerXin2025/Mitar)
2. 将 Proof-Script 和 Mitar 仓库并排放置在某目录下
3. 进入目录 `Mitar/` 并使用 `make install` 同时安装 Proof-Script 和 Mitar
4. 进入 `Mitar/demo/` , 使用 `lake exe cache get` 拉取 Mathlib 缓存并使用 `mitar .` 来编译该项目
5. 生成的页面可以在 `Mitar/demo/.Mitar/build/` 中查看

## 目录

- [快速开始](#快速开始)
- [形式化证明](#形式化证明)
- [ProofText](#prooftext)
- [自动文献管理系统](#自动文献管理系统)
- [其它页面组件](#其它页面组件)
- [页面导出](#页面导出)
- [环境要求](#环境要求)
- [当前限制](#当前限制)
- [相关文档](#相关文档)

## 快速开始

在 `lakefile.toml` 中添加 Proof-Script 作为依赖并执行 `lake update` 后, 即可在 Lean 项目中使用.

```lean
import ProofScript

project_info {
  title := "An Example Formal Paper",
  authors := "Alice, Bob",
  abstract := "A small demonstration of Proof-Script.",
  keywords := "Lean, formal proof, structured proof",
  year := "2026"
}

#text r#"
= Introduction <introduction>

This page contains a recorded theorem. See @thm:main-result.
"#

#theorem mainResult (P : Prop) (h : P) : P := script
  provide h

theorem_info mainResult {
  name := "Main Result",
  label := "main-result"
}

#references

#page_end
```

假设上述 Lean 文件为 `./Project/Module/Page.lean` , 则编译后证明和页面信息将分别导出至:

```text
./.Proof-Script/pages/Project/Module/Page.json
./.Proof-Script/proofs/Project/Module/Page/mainResult.json
```


## 形式化证明

### 脚本模式

Proof-Script 中引入了由 `:= script` 引导的脚本模式来代替策略模式. 其在语法上和策略模式一致 （并且实际上正是基于策略模式构建）, 脚本模式大致包含以下三类基本元素:

1. 步骤: `intro_h` , `apply_thm` 等作为形式化证明中的逻辑单元, 它们相比一般的 Lean 策略具有更强的语义性.
2. 概略: `split_and` , `by_contra` , `induction` 等在宏观上确定了证明的结构, 并且具有统一的语法形式.
3. 元数据: `remark` , `figure` , `tikz` 等可在证明脚本嵌入解释性文本/图表等元数据.

以上三类元素可以统称为脚本策略. 这种约束使证明脚本更适合稳定地映射为自然语言或交互式展示, 同时兼备 Lean 形式化验证能力, 下面的代码提供了一个完整示例.

```lean
theorem implicationChain
    (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := script
  intro_h hP
  infer
    P => Q := hPQ hP
    _ => R := hQR ?_
```

### Proof-Script 内置脚本策略

#### 步骤

##### Lean 原生策略

请注意, 对于下面的 Mathlib 原生策略, 其未被列出的语法可能不受 Proof-Script 支持.

- `omega`
- `rfl`
- `symm`
- `trivial`

##### 专属脚本策略

| 策略 | 作用 | 对应原生策略 | 限制 |
| :- | :- | :- |
| `intro_h ⟨h⟩` | 引入命题假设 | `intro` | 只能对证明项使用 |
| `intro_var ⟨val⟩` | 引入数据变量 | `intro` | 只能对变量使用 |
| `provide ⟨h⟩` | 提供证明项闭合目标 | `exact` | 只能在 `witness` 的 `prep` 分支中使用 |
| `apply_h ⟨h⟩` | 应用局部假设, 留下前提子目标 | `apply` | 只能对上下文中的变量使用 |
| `apply_thm ⟨thm⟩` | 应用定理, 留下前提子目标 | `apply` | 只能对作为常量的定理使用 |
| `quot_induction q with a` | 商类型归纳 | `induction` |

#### 概略

概略策略将目标拆分为若干带有**语义化命名**的分支, 从而在宏观上确定证明的框架.
对于每个概略产生的目标分支, 请使用 `| case => …` 的语法来完成证明, 在脚本模式中匿名分支 `·` 将被禁止使用.

##### 存在性构造

`witness` 作用于形如 `∃ x, P x` 的存在性命题, 并将其拆分为两个分支:

- `prep` : 构造符合条件的对象
- `proof` : 证明该对象满足 `P`

```lean
theorem demo_witness : ∃ n : Nat, n = 0 := script
  witness
  | prep => provide 0
  | proof => trivial
```

##### 目标拆解 —— 合取

`split_and` 作用于形如 `P ∧ Q` 的合取命题, 并将其拆分为两个分支:

- `left` : 左分支
- `right` : 右分支

`split_and!` 会递归地拆解形如 `P₁ ∧ P₂ ∧ ... ∧ Pₙ` 的合取命题, 并将其拆分为分支 `goalI` , `goalII` 等.

```lean
variable {P Q R : Prop}
theorem demo_split_and (hP : P) (hQ : Q) : P ∧ Q := script
  split_and
  | left => provide hP
  | right => provide hQ
theorem nestedAnd (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := script
  split_and!
  | goalI => provide hP
  | goalII => provide hQ
  | goalIII => provide hR
```

##### 目标拆解 —— 等价

`split_iff` 作用于形如 `P ↔ Q` 的等价命题, 并将其拆分为两个分支:

- `suffice` : 充分性, 即 `P → Q`
- `necess` : 必要性, 即 `Q → P`

```lean
variable {P Q : Prop}
theorem demo_split_iff (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := script
  split_iff
  | suffice h₁ => provide hPQ h₁
  | necess h₂ => provide hQP h₂
```

##### 反证法

在脚本模式中, `by_contra` 可以:

1. 作用于形如 `¬ P` 的否定命题, 并产生一个分支 `proof` , 该分支中引入了 `P` 作为假设
2. 作用于其它命题, 并产生一个分支 `proof` , 该分支中引入了 `¬ P` 作为假设

在 `proof` 分支中, 目标被修改为 `False` , 即通过导出矛盾来完成证明.

```lean
theorem demo_by_contra_pos (P : Prop) (h : ¬ P → False) : P := script
  by_contra hnp
  | proof => provide (h hnp)
theorem demo_by_contra_neg (P : Prop) : ¬ (P ∧ ¬ P) := script
  by_contra h
  | proof => provide (h.2 h.1)
```

##### 数学归纳法

在脚本模式中, `induction n` 对自然数 `n` 作数学归纳, 并产生 `zero` / `succ k ih` 两个分支:

```lean
theorem demo_induction (n : Nat) : n + 0 = n := script
  induction n
  | zero => rfl
  | succ k ih => rfl
```

##### 强（完全）归纳法

`complete_induction n` 对自然数 `n` 作强归纳, 同样产生 `zero` / `succ k ih` 两个分支, 但 `succ` 分支的归纳假设 `ih : ∀ m < k + 1, P m` 覆盖所有更小的自然数:

```lean
theorem demo_complete_induction (n : Nat) : n + 0 = n := script
  complete_induction n
  | zero => rfl
  | succ k ih => rfl
```

##### 分类讨论 `by_cases`

`by_cases h : p` 按命题 `p` 的真假分类讨论, 产生 `caseI` (`h : p`) 与 `caseII` (`h : ¬p`) 两个分支:

```lean
theorem demo_by_cases (n : Nat) : n = 0 ∨ n ≠ 0 := script
  by_cases h : n = 0
  | caseI => provide (Or.inl h)
  | caseII => provide (Or.inr h)
```

#### 元数据

##### 非正式证明

使用 `cause` 策略可以使用一段自然语言作为未形式化证明, 其使用 `sorry` 来临时填补证明, 例如:

```lean
theorem draft (P : Prop) : P := cause "This result has not been formalized yet."
```

同时 `cause` 也可以作为项使用, 例如 `:= cause "尚未形式化"` .

##### 注解

使用 `remark` 策略可以插入一段自然语言注解, 从而帮助阅读者更好地理解证明中的某个部分, 例如:

```lean
#theorem demo_remark {P : Prop} (h_P : P) : P := script
  remark "这是一则简单的证明"
  provide h_P
```

##### LaTeX (SVG)

证明内部提供 `tikz`、`figure`、`table` 三种元数据策略. 它们接收 LaTeX 源码, 在录制时
调用本地 LaTeX 工具链生成 SVG, 并把 metadata、源码和 SVG 一同写入证明树. 例如:

```lean
#theorem proofWithDiagram (P : Prop) (h : P) : P := script
  tikz (title := "推导图", label := "proof-diagram") r#"
    \begin{tikzpicture}
      \draw[->] (0,0) -- (1,0);
    \end{tikzpicture}
  "#
  provide h
```

为了保证预编译器顺利工作, 请确保 TeXLive 已本地安装. 这里是证明内部策略；页面级任意
LaTeX 使用后文的 `#LaTeX` 命令.

#### 连续计算 `calc`

Proof-Script 支持 `calc` 计算块, 所以可以在脚本模式下直接使用.

#### 连续推导 `infer`

众所周知, `calc` 计算块可以很大程度上简化传递性关系的连续计算过程, 而连续推导 `infer` 则以类似的语法实现一般的连续推导过程简化, 例如:

```lean
theorem divisibility_chain {a b c d e : ℕ}
    (h_ab : a ∣ b) (h_bc : b ∣ c)
    (h_pos : 0 < c * d * e)
  : a ≤ c * d * e
:= script
  remark "这里我们通过整除性来证明不等式"
  infer
    (a ∣ b) => (a ∣ c)
                := dvd_trans h_ab h_bc
    _       => (a ∣ c * d)
                := dvd_mul_of_dvd_left ?_ d
    _       => (a ∣ c * d * e)
                := dvd_mul_of_dvd_left ?_ e
    _       => (a ≤ c * d * e)
                := Nat.le_of_dvd h_pos ?_
```

其中 `:=` 的语法相当于使用 `refine` 策略, 但必须遵循以下规则:

* 初始步骤不能使用 `?_` , 并且必须有一个参数是 `=>` 左侧命题的项;
* 除了初始步骤之外的每一步都必须有且仅有一个 `?_` , 作为上一步右侧命题的项的占位符.

`infer` 可以

- 作为中间步骤使用, 将所有出现的新结论匿名地添加到上下文中（类似 `have`）.
- 作为终结策略闭合目标.
- 直接作为项使用（即写作 `:= infer`）, 这与 `calc` 是相似的.

### 自定义脚本策略

使用 `script_macro` / `script_elab` 可以创建一个脚本策略, 它们的用法和 `macro` / `elab` 一致, 例如:

```lean
script_macro (record := false)
"finish" proof:term : tactic => `(tactic| exact $proof:term)

script_elab (intro := [h])
"intro_named" h:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro $h:ident))
```

在创建脚本策略时, 你可能需要提供一些额外信息以使得 Proof-Script 能够正确地处理它们, 这些参数包括:

| 参数名 | 值 | 说明 | 默认值 |
| - | - | - | - |
| `intro` | 语法参数列表 | 表示由该脚本策略引入的参数, 这些参数只在执行后序列化 | `[]` |
| `clear` | 语法参数列表 | 表示由该脚本策略消除的参数, 这些参数只在执行前序列化 | `[]` |
| `strategy` | `true` , `false` | 用于标注该脚本策略是否为概略 | `false` |
| `record` | `true` , `false` | 用于指定是否自动生成记录器 | `true` |

Proof-Script 默认将导出该脚本策略全体参数在执行前后的信息, 而对于

- 除了 `term` , `ident` , `str` , `num` 以及 `+` 重复形式之外的复杂语法参数
- 一些需要导出特定元数据（例如 `tikz` 会自动编译 LaTeX 为 SVG 编码）

请设置 `record := false` 并使用 `script_recorder` 来手动创建记录器. `script_recorder` 接收
不带 `script_` 前缀的原策略名, 自动定义 `_script_` 录制入口并完成 kind 注册:

```lean
script_recorder
"finish" proof:term : tactic => do
  ProofScript.recordStep "finish" [] [] []
    [("proof", ProofScript.ParamRaw.one proof.raw)] do
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $proof:term))
```

暂不支持使用像 `macro_rules` / `elab_rules` 一样的方式定义脚本策略.

### 导出证明树

要完整导出某个定理的证明树, 只需要将 `theorem` 命令替换为 `#theorem` 即可.
Proof-Script 会在目录 `.../.Proof-Script/proofs/` 下存放这些数据, 其中 `.../` 代表 Lean 项目根目录.
每个证明树顶层都包含 `schemaVersion`、完整 Lean 源码 `code` 和步骤数组 `proof`.


## ProofText

`#text` 接受一个 Lean 字符串字面量, 并作为专属的轻量标记语言 ProofText 进行解析, 其在语法上与 Typst 大致相近.

````lean
#text r#"
= ProofText Overview <overview>

This paragraph contains *bold*, _emphasis_, *_bold emphasis_*,
~~deleted~~, __underlined__, ==highlighted==, x^2^, a~n~,
`inline code`, $x + y$, and [a link](https://example.com).

- First item
- Second item

+ First step
4. Forced fourth step
+ Automatically numbered fifth step

> A quoted paragraph.

$$
\int_0^1 x^2\,dx = \frac{1}{3}
$$

```lean
theorem example : True := by
  trivial
```
"#
````

### 块级结构

- 1 至 4 级标题: 置于行首的 `= TITLE` / ... / `==== TITLE` , 其中 `TITLE` 为标题名称
- 自定义标签的标题: `== TITLE <label>` , 其中 `label` 为标签名称
- 普通段落
- 无序列表: 由行首的 `-` 引导
- 有序列表: 由行首的 `+` 引导
- 强制序号的有序列表: 由行首的 `n.` 引导, 其中 `n` 是任意自然数
- 引用块: 由行首的 `>` 引导
- 行间公式: 由独占整行的 `$$` 包裹
- 整段代码块: 由 <code>```</code> 包裹, 支持语言标注

### 行内结构

| 语法 | 含义 |
| --- | --- |
| `*text*` | 粗体 |
| `_text_` | 强调 |
| `*_text_*` | 粗体强调 |
| `~~text~~` | 删除线 |
| `__text__` | 下划线 |
| `==text==` | 高亮 |
| `x^2^` | 上标 |
| `a~n~` | 下标 |
| `` `code` `` | 行内代码 |
| `$x + y$` | 行内数学公式 |
| `[text](url)` | 链接 |
| `@<label>` | 标题引用 |
| `@thm:label` | 定理引用 |
| `@fig:label` | 图片或 LaTeX 组件引用 |

ProofText 源代码和解析后的语义 AST 将由 Proof-Script 统一导出至页面 JSON 文件中, 以下文档供参考:

- [ProofText 中文语法](docs/ProofText-Syntax-zh.md)
- [ProofText English syntax](docs/ProofText-Syntax.md)


## 自动文献管理系统

### 文献信息注册

`project_info` 注册当前项目或论文的全局元数据, 并持久化至 `.olean` 环境中

```lean
project_info {
  title := "Project Title",
  authors := "Alice, Bob",
  abstract := "Abstract text",
  keywords := "Lean, logic",
  journal := "Journal Name",
  year := "2026",
  url := "https://example.com",
  license := "...",
  arxivId := "...",
  doi := "...",
  note := "..."
}
```



### 定理信息注册

普通 Lean theorem 和 `#theorem` 都可以附加定理元数据：

```lean
@[theorem_info (
  name := "Displayed theorem name",
  label := "theorem-label",
  tags := "algebra, foundational",
  customField := "custom value"
)]
theorem referencedTheorem (P : Prop) (h : P) : P := h
```

也可以在声明之后使用 command 形式, 其配置使用与 `project_info` 一致的大括号:

```lean
theorem_info referencedTheorem {
  name := "Displayed theorem name",
  label := "theorem-label",
  tags := "algebra, foundational"
}
```

标准字段为 `name`、`label`、`tags`；未知字段进入 `extra`。为保证与 JSON Schema 兼容，公共 label 应满足：

```text
[A-Za-z][A-Za-z0-9_-]*
```

### 自动文献采集

在 `#theorem` 录制表达式参数时, Proof-Script 会自动遍历其中使用的定理常量, 如果这些定理携带 `theorem_info` 信息, 它们就会被添加至当前页面的暂存区, 并且不会重复添加, 因此将始终保留其首次出现的顺序.

下面的命令可以用来局部关闭文献自动采集:

```lean
set_option proofScript.references.enabled false in
#theorem noReferences (P : Prop) (h : P) : P := script
  provide h
```

在页面的任何位置, 使用命令 `#references` 即可把当前暂存区中的全部文献信息作为页面组件
输出, 此操作将清空文献暂存区. 该命令不接受文件名, 也不会单独写出 references JSON.

## 其它页面组件

### 任意 LaTeX

`#LaTeX` 接收任意 LaTeX 源码并在编译期生成 SVG. `title` 必填, `label` 可选, 其它字段会
保存在 metadata 的 `extra` 中:

```lean
#LaTeX (
  title := "交换图",
  label := "commutative-diagram"
) r#"
\begin{tikzpicture}
  \draw[->] (0,0) -- (1,0);
\end{tikzpicture}
"#
```

### 图片资源

`#figure` 接收包含后缀的相对图片资源路径. Proof-Script 只导出路径和扩展名, 不读取或复制文件:

```lean
#figure (
  title := "架构图",
  label := "architecture",
  width := "wide"
) "assets/architecture.png"
```

### 自定义页面组件

页面 JSON Schema 预留了 `custom` 标签, 但当前尚未提供公开的 Lean command 注册任意 custom
页面组件. 如需扩展, 应在 `ProofScript.Extension.ComponentData` 和页面 command 层增加新的
通用组件类型, 并同步更新 JSON Schema.

## 页面导出

`#page_end` 是最终的导出命令, 该命令之后的任何页面组件都会被忽略.

## 环境要求

### 必需环境

已完整安装 Lean + Lake + Elan

### 可选 LaTeX 环境

如果需要使用页面组件 `#LaTeX` , 系统 `PATH` 中还必须存在:

```bash
latex --version
dvisvgm --version
```

## 当前限制

- `script` 只允许已注册策略，不支持任意 Lean tactic，也不支持 bullet `·`。
- 自动 recorder 只支持有限的 parser 参数形式；复杂策略必须手写 `script_recorder`。
- `complete_induction` 当前是自然数强归纳模板。
- 自动引用只扫描录制器接触到的表达式，并且只采集已注册 `theorem_info` 元数据的声明，不是完整依赖分析。
- ProofText 引用在 elaboration 时只检查语法，不验证引用目标一定存在；跨页面索引应由下游消费者建立。
- ProofText 是小型专用语言，不提供完整 Markdown/Typst 能力。
- 页面按单模块、一次导出模型工作；`#page_end` 之后的组件会产生警告并被忽略。
- LaTeX 组件要求本机 `latex`、`dvisvgm` 和相应 TeX 宏包，且编译失败会中断 Lean elaboration。
- 页面 source 路径当前通常为绝对路径；源码位置使用 UTF-8 字节偏移。
- Lean 表达式 JSON 与 Lean 内部 AST 紧密相关，仍属于可扩展接口，跨 Lean 版本使用时应谨慎。
- 当前 universe level 的 `max`/`imax` 序列化实现存在重复键问题，不应依赖其左右操作数能够被完整区分。
- 本仓库不包含正式的 JSON 到 HTML 渲染器源码；`.Mitar/` 和 `Demo/*.html` 不属于 Proof-Script 核心可复现构建链。

## 相关文档

- [旧版中文速览](README-zh.md)，内容可能过时，仅供历史参考
- [ProofText 中文语法](docs/ProofText-Syntax-zh.md)
- [ProofText English syntax](docs/ProofText-Syntax.md)
- [JSON 格式中文说明](docs/JSON-Schemas-zh.md)
- [JSON format documentation](docs/JSON-Schemas.md)
- [页面 JSON Schema](docs/schema/page.schema.json)
- [证明树 JSON Schema](docs/schema/proof.schema.json)
