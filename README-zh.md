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

@text r#"
= Introduction <introduction>

This page contains a recorded theorem. See @thm:main-result.
"#

@theorem mainResult (P : Prop) (h : P) : P := script
  assumption

theorem_info mainResult {
  name := "Main Result",
  label := "main-result"
}

@references

page_end
```

假设上述 Lean 文件为 `./Project/Module/Page.lean` , 则编译后证明和页面信息将分别导出至:

```text
./.Proof-Script/pages/Project/Module/Page.json
./.Proof-Script/proofs/Project/Module/Page/mainResult.json
```


## 形式化证明

### 脚本模式

Proof-Script 中引入了由 `:= script` 引导的脚本模式来代替策略模式. 在 `:= script` 中，用户应使用不带前缀的脚本策略名；框架会自动将其改写为内部执行入口 `script_<name>`，录制时使用 `_script_<name>`. 其在语法上和策略模式一致 （并且实际上正是基于策略模式构建）, 脚本模式大致包含以下三类基本元素:

1. 步骤: `intro_h`、`apply` 等作为形式化证明中的逻辑单元, 它们相比一般的 Lean 策略具有更强的语义性.
2. 概略: `split_and`、`contra`、`induction` 等在宏观上确定了证明的结构, 并且具有统一的语法形式.
3. 元数据: `remark`、`latex` 等可在证明脚本嵌入解释性文本或图表等元数据.

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

核心模块包装了下列 Lean 策略。这里只支持列出的简化语法：

| 策略 | 作用 |
| :- | :- |
| `assumption` | 使用上下文中的匹配假设闭合目标 |
| `change t` | 将目标改写为定义等价的 `t` |
| `contradiction` | 从上下文矛盾闭合目标 |
| `exfalso` | 将当前命题目标改为 `False` |
| `omega` | 求解 Presburger 算术目标 |
| `rfl` | 用自反性闭合目标 |
| `simp_only [l₁ l₂ ...]` / `simp_only [l₁ l₂ ...] at h₁ h₂` / `simp_only [l₁ l₂ ...] at *` / `simp_only [l₁ l₂ ...] at ⊢` | 只使用空白分隔的指定标识符进行化简，可作用于指定假设、全部假设或目标 |
| `symm` | 交换对称关系两侧 |
| `trivial` | 求解简单目标 |
| `rewrite [h₁ h₂ ...]` / `rewrite [← h₁ h₂ ...]`，可加 `at h₁ h₂`、`at *` 或 `at ⊢` | 使用等式重写，并随后尝试原生 `rfl` |
| `unfold d₁ d₂ ...` | 展开一个或多个空白分隔的定义 |

##### 专属脚本策略

| 策略 | 作用 | 对应原生策略 | 限制 |
| :- | :- | :- |
| `intro_h ⟨h⟩` | 引入命题假设 | `intro` | 只能对证明项使用 |
| `intro_var ⟨val⟩` | 引入数据变量 | `intro` | 只能对变量使用 |
| `provide ⟨h⟩` | 在 `witness.data` 中提供见证，或为存在目标提供见证 | `exact` / `exists` | 不是一般的 `exact`，只能用于这两种上下文 |
| `apply t` | 应用形如 `P → Q` 或 `P ↔ Q` 的命题，留下一个前提目标 | `apply` / `Iff.mp` / `Iff.mpr` | 最外层必须是蕴含或等价，且只能产生一个目标 |
| `ext_fun x` | 将函数等式化为逐点等式 | `funext` | 等式两侧必须是同定义域函数 |
| `obtain_exist ⟨x, hx⟩ := h` | 解构局部存在性假设 | `cases` | `h` 必须证明存在命题 |
| `left` / `right` | 选择析取目标的左侧或右侧 | `apply Or.inl/inr` | 当前目标必须是析取命题 |
| `quot_induction q with a` | 商类型归纳 | `induction` |
| `unpack_and ⟨h₁, h₂⟩ := h` | 解构局部合取假设 | `cases` | `h` 必须证明合取命题 |
| `unpack_iff ⟨h₁, h₂⟩ := h` | 解构局部等价假设 | `cases` | `h` 必须证明等价命题 |

`apply` 接受一个最外层为蕴含或等价命题的项。它只应用最外层蕴含，因此 `P → Q → R` 只产生一个 `P` 目标，并保留剩余的蕴含结论。对于等价命题，它会根据当前目标选择对应的方向：

```lean
theorem compose (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := script
  apply hQR
  apply hPQ
  assumption
```

#### 概略

概略策略将目标拆分为若干带有**语义化命名**的分支, 从而在宏观上确定证明的框架.
对于每个概略产生的目标分支, 请使用 `| case => …` 的语法来完成证明, 在脚本模式中匿名分支 `·` 将被禁止使用.

当前概略和结构策略包括：

| 策略 | 作用或分支 |
| :- | :- |
| `have h : P` | 产生后续目标和名为 `proof` 的断言证明目标 |
| `witness` | 存在性构造，产生 `data`、`proof` |
| `split_and` | 二元合取，产生 `left`、`right` |
| `split_and!` | 递归合取，产生 `goalI`、`goalII` 等 |
| `split_iff` | 等价证明，产生 `suffice`、`necess` |
| `cases_by h` | 对局部析取假设分类，产生 `left`、`right` |
| `cases_by! h` | 递归拆解局部析取，产生 `goalI`、`goalII` 等 |
| `cases_on t` | 对命题真假或数据构造子分类 |
| `contra h` | 反证，产生 `proof` |
| `induction n` | 自然数归纳 |
| `complete_induction n` | 自然数强归纳 |

##### 存在性构造

`witness` 作用于形如 `∃ x, P x` 的存在性命题, 并将其拆分为两个分支:

- `data` : 构造符合条件的对象
- `proof` : 证明该对象满足 `P`

```lean
theorem demo_witness : ∃ n : Nat, n = 0 := script
  witness
  | data => provide 0
  | proof => trivial
```

`provide` 也可以直接构造存在命题，不必使用 `witness` 的两个分支；它不能作为一般的 `exact` 步骤使用:

```lean
theorem provide_witness : ∃ n : Nat, n = 0 := script
  provide 0
  rfl
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
  | left => assumption
  | right => assumption
theorem nestedAnd (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := script
  split_and!
  | goalI => assumption
  | goalII => assumption
  | goalIII => assumption
```

##### 目标拆解 —— 等价

`split_iff` 作用于形如 `P ↔ Q` 的等价命题, 并将其拆分为两个分支:

- `suffice` : 充分性, 即 `P → Q`
- `necess` : 必要性, 即 `Q → P`

```lean
variable {P Q : Prop}
theorem demo_split_iff (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := script
  split_iff
  | suffice h₁ =>
    apply hPQ
    assumption
  | necess h₂ =>
    apply hQP
    assumption
```

##### 反证法

在脚本模式中, `contra h` 可以:

1. 作用于形如 `¬ P` 的否定命题, 并产生一个分支 `proof` , 该分支中引入了 `P` 作为假设
2. 作用于其它命题, 并产生一个分支 `proof` , 该分支中引入了 `¬ P` 作为假设

在 `proof` 分支中, 目标被修改为 `False` , 即通过导出矛盾来完成证明.

```lean
theorem demo_by_contra_pos (P : Prop) (h : ¬ P → False) : P := script
  contra hnp
  | proof =>
    apply h
    assumption
theorem demo_by_contra_neg (P : Prop) : ¬ (P ∧ ¬ P) := script
  contra h
  | proof =>
    unpack_and ⟨hP, hNP⟩ := h
    apply hNP
    assumption
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

##### 分类讨论 `cases_on`

`cases_on p` 对命题 `p` 按真假分类讨论, 产生 `true h` (`h : p`) 与 `false h` (`h : ¬p`) 两个分支:

```lean
theorem demo_cases_on (n : Nat) : n = 0 ∨ n ≠ 0 := script
  cases_on (n = 0)
  | true h =>
    left
    assumption
  | false h =>
    right
    assumption
```

#### 元数据

核心模块提供以下元数据策略：

| 策略 | 作用 |
| :- | :- |
| `remark "text"` | 插入自然语言注解 |
| `svg "code"` | 插入原始 SVG 元数据 |
| `latex (title := "...", ...) "source"` | 编译并记录任意 LaTeX 源码及 SVG |
| `cause "reason"` | 使用 `sorry` 暂时闭合目标并记录原因 |

##### 非正式证明

使用 `cause` 策略可以使用一段自然语言作为未形式化证明, 其使用 `sorry` 来临时填补证明, 例如:

```lean
theorem draft (P : Prop) : P := script
  cause "This result has not been formalized yet."
```

如需项形式，可使用普通项宏 `cause`，例如 `:= cause "尚未形式化"`；它不是可直接执行的脚本策略名。

##### 注解

使用 `remark` 策略可以插入一段自然语言注解, 从而帮助阅读者更好地理解证明中的某个部分, 例如:

```lean
@theorem demo_remark {P : Prop} (h_P : P) : P := script
  remark "这是一则简单的证明"
  assumption
```

##### LaTeX (SVG)

证明内部提供统一的 `latex` 元数据策略. 它与页面组件 `#latex` 一样接收 metadata 和任意
LaTeX 源码，在录制时调用本地 LaTeX 工具链生成 SVG，并把 metadata、源码和 SVG 一同写入
证明树。例如:

```lean
@theorem proofWithDiagram (P : Prop) (h : P) : P := script
  latex (title := "推导图", label := "proof-diagram") r#"
    \begin{tikzpicture}
      \draw[->] (0,0) -- (1,0);
    \end{tikzpicture}
  "#
  assumption
```

为了保证预编译器顺利工作，请确保 TeXLive 已本地安装。这里是证明内部策略；页面级任意
LaTeX 使用后文的 `#latex` 命令。

#### 连续计算 `calc`

Proof-Script 将 `calc` 计算块包装为脚本策略，所以可以在脚本模式下使用.

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
- 直接作为项使用（即写作 `:= infer`）；这里的 `infer` 是普通项宏，而不是无前缀的可执行脚本策略.

### 可选 Mathlib 脚本策略

安装 Mathlib 后，可以显式导入可选扩展：

```lean
import ProofScript
import ProofScript.Mathlib
```

该模块不由核心 `ProofScript` 自动导入，也不属于默认 Lake target。当前包装按字母顺序包括：

| 策略 | 支持的简化形式 |
| :- | :- |
| `script_continuity` | 默认形式 |
| `script_exact_mod_cast` | `script_exact_mod_cast proof` |
| `script_field` | 默认、`script_field [lemmas...]` |
| `script_gcongr` | 默认、pattern、`with names...` 及两者组合 |
| `script_itaotu` / `script_itauto` | 默认、`*`、命题列表及 `!` 变体 |
| `linarith` | 默认、事实列表、`only` 及 `!` 变体 |
| `script_measurability` | 默认形式 |
| `script_nlinarith` | 默认、事实列表、`only` 及 `!` 变体 |
| `script_norm_cast` | 默认及 `at` 形式 |
| `norm_num` | 默认、lemma 列表、`only` 及对应 `at` 形式 |
| `script_positivity` | 默认、事实列表 |
| `script_push_cast` | 默认、lemma 列表、`only` 及对应 `at` 形式 |
| `qify` / `rify` / `zify` | 默认、lemma 列表及对应 `at` 形式 |
| `script_ring` | `script_ring`、`script_ring!` |
| `script_ring_nf` | 默认、`!` 及对应 `at` 形式 |
| `script_tauto` | 默认形式 |
| `script_wlog` | 默认、`generalizing`、`with`、两者组合及 `script_wlog!` |

为保持参数可稳定录制，包装只使用 `ident`、`term` 等基础类别。方括号中的参数使用空白分隔：

```lean
linarith [h₁ h₂]
qify [hab] at h ⊢
norm_num only [Nat.add_zero Nat.zero_add] at *
```

支持位置参数的策略可使用 `at h`、`at h₁ h₂`、`at *`、`at ⊢` 和
`at h₁ h₂ ⊢`。配置对象、自定义 discharger、任意 tactic block 以及仅输出建议的 `?`
变体没有包装。完整说明参见 [Mathlib 扩展文档](ProofScript/Mathlib-README-zh.md)。

### 自定义脚本策略

使用 `script_macro` / `script_elab` 可以创建一个脚本策略。用户在 `:= script` 中仍写无前缀的 `name`，框架会自动改写到执行入口 `script_name`，录制时再改写到 `_script_name`；无前缀名称不会成为普通 `:= by` 中可执行的策略。两者以及 `script_recorder` 都只支持
显式的 `: tactic` 类别；需要提供项版本时，应使用普通 `macro` 将它包装为 `script` 证明。例如:

```lean
script_macro (recorder := exclusive)
"finish" proof:term : tactic => `(tactic| exact $proof:term)

script_elab (intro := [h])
"intro_named" h:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro $h:ident))

macro "finish" proof:term : term => `(script
  finish $proof:term)
```

在创建脚本策略时, 你可能需要提供一些额外信息以使得 Proof-Script 能够正确地处理它们, 这些参数包括:

| 参数名 | 值 | 说明 | 默认值 |
| - | - | - | - |
| `intro` | 语法参数列表 | 表示由该脚本策略引入的参数, 这些参数只在执行后序列化 | `[]` |
| `clear` | 语法参数列表 | 表示由该脚本策略消除的参数, 这些参数只在执行前序列化 | `[]` |
| `strategy` | `true`, `false` | 用于标注该脚本策略是否为概略 | `false` |
| `recorder` | `auto`, `exclusive` | 自动生成记录器，或仅使用手写记录器 | `auto` |

Proof-Script 默认将导出该脚本策略全体参数在执行前后的信息, 而对于

- 除了 `term` , `ident` , `str` , `num` 以及 `+` 重复形式之外的复杂语法参数
- 一些需要导出特定元数据（例如 `latex` 会自动编译 LaTeX 为 SVG 编码）

请设置 `recorder := exclusive` 并使用 `script_recorder` 来手动创建记录器. `script_recorder` 接收
不带 `script_` 前缀的原策略名, 为已有的 `script_<name>` 执行入口自动定义 `_script_<name>` 录制入口并完成 kind 注册；它同样不会创建无前缀的可执行策略:

```lean
script_recorder
"finish" proof:term : tactic => do
  ProofScript.recordStep "finish" [] [] []
    [("proof", ProofScript.ParamRaw.one proof.raw)] do
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $proof:term))
```

暂不支持使用像 `macro_rules` / `elab_rules` 一样的方式定义脚本策略.

### 导出证明树

要导出某个定理或引理，只需使用 `#theorem` 或 `#lemma`。两者在页面 JSON 中分别使用
`"theorem"` 和 `"lemma"` 标签。
Proof-Script 会在目录 `.../.Proof-Script/proofs/` 下存放这些数据, 其中 `.../` 代表 Lean 项目根目录.
每个证明树顶层都包含 `schemaVersion`、完整 Lean 源码 `code` 和步骤数组 `proof`.

`:= script` 中直接使用无前缀 DSL 名称，框架会自动补全 `script_` 前缀并检查、记录每一步；`:= by` 接受普通 Lean
策略，但不能使用 Proof-Script 的脚本策略。后者只保留 `schemaVersion` 与完整 `code`，不输出
`expressions` 或 `proof`。两种模式都会自动采集文献引用。


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
@theorem noReferences (P : Prop) (h : P) : P := script
  assumption
```

在页面的任何位置, 使用命令 `#references` 即可把当前暂存区中的全部文献信息作为页面组件
输出, 此操作将清空文献暂存区. 该命令不接受文件名, 也不会单独写出 references JSON.

## 其它页面组件

### 任意 LaTeX

`#latex` 接收任意 LaTeX 源码并在编译期生成 SVG. `title` 必填, `label` 可选, 其它字段会
保存在 metadata 的 `extra` 中:

```lean
#latex (
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

扩展模块可以调用 `ProofScript.Extension.addCustomComponent` 注册开放式 JSON 组件。需要嵌入式
计算时，优先使用内置 `#computation`：它接收组件元数据、下游 renderer ID、Lean 函数声明和
renderer 专用的 JSON manifest：

```lean
def chooseOffset (large : Bool) : Nat := if large then 128 else 112

#computation
  (title := "有限计算", label := "finite-computation")
  "my-renderer/table-v1"
  chooseOffset
  r#"{"execution":{"backend":"table"},"results":[112,128]}"#
```

输出包含声明全名、可读类型、函数实现体和结构化 Lean 表达式表。这些字段是来源信息和中间产物，
不承诺 Lean 编译器内部 IR 的浏览器 ABI；实际执行方式由版本化 renderer ID 和 manifest 共同决定。
详见 `docs/Embedded-Computation-Renderer-zh.md`。

计算入口必须形如 `α → β` 或 `α → Except String β`，并存在 `Lean.FromJson α` 与
`Lean.ToJson β`。命令会生成 `String → String` wrapper 和 pending build manifest；实际 Wasm
resource 由后续 bundler 阶段生成。

生成 pending manifests 后，可在项目根目录运行：

```bash
source "$HOME/Developer/emsdk/emsdk_env.sh"
PROOF_SCRIPT_LEAN_WASM_PREFIX=/path/to/lean-wasm-prefix \
  node /path/to/Proof-Script/scripts/build-computations.mjs
```

该命令按模块生成多入口 bundle 到 `.Proof-Script/computations/bundles/`。页面 resource 回填由
finalize 阶段完成：

```bash
node /path/to/Proof-Script/scripts/finalize-computations.mjs
```

Finalize 将资源发布到内容寻址目录并把页面 execution 更新为 `ready`。前端实现参见
`docs/Frontend-Computation-Handoff-zh.md`。

SpherePaper 的 E8 新版交互计算设计参见 `docs/E8-Embedded-Computation-Design-zh.md`。

前端 renderer 可先使用 `docs/Embedded-Computation-Quickstart-zh.md` 中的 Fibonacci 示例做端到端测试。

## 页面导出

`#page_end` 是最终的导出命令, 该命令之后的任何页面组件都会被忽略.

## 环境要求

### 必需环境

已完整安装 Lean + Lake + Elan

### 可选 LaTeX 环境

如果需要使用页面组件 `#latex` , 系统 `PATH` 中还必须存在:

```bash
latex --version
dvisvgm --version
```

## 当前限制

- `script` 只允许带 `script_` 前缀的已注册策略，不支持任意 Lean tactic，也不支持 bullet `·`。
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
