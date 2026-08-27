# Proof-Script JSON 模式

本文档规定了 Proof-Script 输出的公开 JSON 格式。

机器可读的 JSON Schema 文件如下：

- `docs/schema/page.schema.json`
- `docs/schema/proof.schema.json`

这两个模式均使用 JSON Schema Draft 2020-12。

## 1. 版本控制

当前模式版本为 `0.2.0`。

页面 JSON 与证明树 JSON 都在顶层 `schemaVersion` 字段中嵌入版本号。

版本变更遵循以下规则：

- 补丁版本：修正文档，或调整不会改变所接受 JSON 的约束。
- 次版本：添加向后兼容的字段或组件种类。
- 主版本：以不兼容的方式更改现有字段、标签或语义。

使用方应拒绝不支持的主版本，并可忽略由较新且兼容的次版本引入的未知字段。

## 2. 页面 JSON

### 2.1 位置

对于 Lean 模块 `Paper.Chapter.Main`，页面文件为：

```text
.Proof-Script/pages/Paper/Chapter/Main.json
```

### 2.2 顶层对象

```json
{
  "schemaVersion": "0.2.0",
  "ProjectInfo": {},
  "module": "Paper.Chapter.Main",
  "source": "/project/Paper/Chapter/Main.lean",
  "components": []
}
```

字段：

| 字段 | 类型 | 含义 |
| --- | --- | --- |
| `schemaVersion` | 字符串 | 模式的语义化版本。 |
| `ProjectInfo` | 对象 | 由 `project_info` 注册的项目元数据。 |
| `module` | 字符串 | 完全限定的 Lean 模块名称。 |
| `source` | 字符串 | Lean 报告的源文件路径。目前通常为绝对路径。 |
| `components` | 数组 | 按源码顺序排列的组件。 |

### 2.3 源码位置

每个组件都包含：

```json
{
  "file": "/project/Paper/Main.lean",
  "start": 120,
  "stop": 180
}
```

`start` 和 `stop` 是 Lean 源文件中的 UTF-8 字节偏移量，而非行号和列号。

### 2.4 组件封装结构

```json
{
  "source": { "file": "...", "start": 0, "stop": 10 },
  "data": {
    "text": { "value": {} }
  }
}
```

`data` 是一个带标签的对象。应当恰好包含一个组件标签。

当前标签包括：

- `text`
- `theorem`
- `latex`
- `figure`
- `references`
- `custom`（保留；目前尚无公开的注册命令）

### 2.5 文本组件

```json
{
  "text": {
    "value": {
      "source": "= Title <title>\n",
      "blocks": []
    }
  }
}
```

原始 ProofText 源码和解析后的语义 AST 均会保留。

当前的行内标签包括：

- `text`
- `strong`
- `emphasis`
- `strongEmphasis`
- `code`
- `strike`
- `underline`
- `highlight`
- `superscript`
- `subscript`
- `link`
- `reference`
- `math`
- `softBreak`
- `hardBreak`

当前的块级标签包括：

- `paragraph`
- `heading`
- `code`
- `orderedList`
- `unorderedList`
- `quote`
- `displayMath`

### 2.6 定理组件

```json
{
  "theorem": {
    "value": {
      "name": "主要定理",
      "label": "main-theorem",
      "proof": ".Proof-Script/proofs/Paper/Main/mainTheorem.json",
      "sorryAx": false
    }
  }
}
```

`name` 来自 `theorem_info` 中的展示名；未指定时采用 Lean 声明的非限定名称。`label` 可为
null。`proof` 是独立证明树 JSON 文件的路径。`sorryAx` 表示该声明是否传递依赖 Lean 的
`sorryAx`。页面不会嵌入证明树。

### 2.7 LaTeX 与图片组件

```json
{
  "latex": {
    "value": {
      "metadata": {
        "title": "交换图",
        "label": "main-diagram",
        "extra": []
      },
      "language": "latex",
      "source": "\\begin{tikzpicture}...",
      "svg": "<svg ...>...</svg>"
    }
  }
}
```

`#latex` 接受任意 LaTeX 源码，将其编译为 SVG，并导出上述 `latex` 标签。

`#figure` 接受一个相对图片资源路径：

```json
{
  "figure": {
    "value": {
      "metadata": {
        "title": "概览图片",
        "label": "overview-image",
        "extra": [["width", "wide"]]
      },
      "path": "assets/overview.png",
      "extension": "png"
    }
  }
}
```

两类组件共用 `figure` 引用命名空间。图片路径必须是包含扩展名的相对路径。Proof-Script
只记录路径和扩展名，不复制或读取图片文件。

### 2.8 引用组件

不带参数的 `#references` 命令会插入：

```json
{
  "references": {
    "value": [
      {
        "name": "Library.result",
        "info": {
          "project": {},
          "name": "显示名称",
          "label": "result",
          "tags": [],
          "extra": []
        }
      }
    ]
  }
}
```

该组件会被准确放置在 `#references` 出现的位置。插入后，引用暂存区会被清空。
`#references` 不再支持导出独立 JSON 文件。

## 3. 证明树 JSON

### 3.1 位置

证明树写入以下路径：

```text
.Proof-Script/proofs/<module path>/<declaration path>.json
```

### 3.2 顶层对象

顶层对象包含模式版本、完整 Lean 源代码和证明步骤数组：

```json
{
  "schemaVersion": "0.2.0",
  "code": "#theorem mainTheorem : True := script\n  trivial",
  "proof": [
    { "_goal_": {} },
    { "_step_": "provide", "proof": {} }
  ]
}
```

每一项均为以下逻辑形式之一。

目标记录：

```json
{
  "_goal_": {},
  "prev_proof": {}
}
```

步骤记录：

```json
{
  "_step_": "provide",
  "proof": {}
}
```

合并策略记录：

```json
{
  "name": "split_and",
  "info": {},
  "left": [],
  "right": []
}
```

策略步骤的确切字段取决于策略及其记录器。使用方必须使用 `_step_` 或 `name` 作为判别字段，
并保留未知字段。

### 3.3 表达式值

目标和策略参数可能包含序列化的 Lean 表达式。表达式对象使用 `kind` 判别字段，其值包括：

- `bvar`
- `fvar`
- `mvar`
- `sort`
- `const`
- `app`
- `lam`
- `forall`
- `let`
- `lit`
- `mdata`
- `proj`

`proof.schema.json` 特意允许扩展表达式对象，因为可选的类型信息和策略专用封装结构会改变其字段。

每个序列化表达式节点都包含 `isProp`，它通过 Lean 的 `Meta.isProp` 对该节点本身计算。
因此可以区分命题 `P`、证明 `h : P` 和数据表达式，无需根据名字或 JSON 结构猜测。

application 节点保留二叉 `fn`、`arg` 字段，并额外提供：

```json
{
  "headConstant": "HAdd.hAdd",
  "arguments": [
    {
      "expr": {},
      "binderInfo": "instImplicit",
      "isExplicit": false,
      "isTypeclass": true
    }
  ]
}
```

`headConstant` 是完全限定声明名；函数头不是常量时为 null。`arguments` 是按调用顺序展平
的参数数组。binder 信息来自 head declaration 实例化后的 forall telescope；无法可靠匹配
时相关字段为 null。

表达式节点还可能包含 `sourceRange`，格式与页面组件相同，采用
`{file,start,stop}` UTF-8 字节偏移。只有 Lean 在表达式 metadata 中保留了源码 Syntax 时
才会输出；无法确定的位置会省略，而不会猜测。

### 3.4 LaTeX 组件步骤

证明内的 `latex` 策略与页面级 `#latex` 组件一样，接收 metadata 和任意 LaTeX 源码，
生成的步骤记录包含：

```json
{
  "_step_": "latex",
  "metadata": {
    "title": "Inline figure",
    "label": "inline-figure",
    "extra": []
  },
  "language": "latex",
  "source": "\\begin{figure}...",
  "svg": "<svg ...>...</svg>"
}
```

## 4. 兼容性要求

写入方必须：

- 保持源组件的顺序；
- 以语义化版本字符串的形式输出页面 `schemaVersion`；
- 对源码位置使用 UTF-8 字节偏移量；
- 保持证明树独立于页面 JSON；
- 对缺失的可选标签使用 `null`；
- 按顺序保留 `extra` 元数据键值对。

读取方应：

- 拒绝不支持的模式主版本；
- 忽略兼容的未知组件字段；
- 保留未知的证明步骤字段；
- 相对于项目工作目录解析定理的 `proof` 路径；
- 加载所有页面文件后，构建跨页面标签索引。

## 5. 已知的模式限制

- Lean 表达式的序列化目前仅在结构层面进行描述，并且仍可扩展。
- 源文件路径目前通常为绝对路径。
- 自定义页面组件已被保留，但尚无法公开注册。
- 跨页面引用的有效性将由未来的渲染器检查，而非由各个 Lean 模块检查。
