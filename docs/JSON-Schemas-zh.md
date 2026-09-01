# Proof-Script JSON 模式

本文档规定了 Proof-Script 输出的公开 JSON 格式。

面向下游渲染器的 `0.2.0 → 0.3.0` 迁移步骤、TypeScript 示例和验收清单见
[`Renderer-Migration-0.3.0-zh.md`](Renderer-Migration-0.3.0-zh.md)。

机器可读的 JSON Schema 文件如下：

- `docs/schema/page.schema.json`
- `docs/schema/proof.schema.json`

这两个模式均使用 JSON Schema Draft 2020-12。

## 1. 版本控制

当前模式版本为 `0.3.0`。

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
  "schemaVersion": "0.3.0",
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
- `lemma`
- `latex`
- `figure`
- `references`

组件信封是开放的：模块可以添加新的标签，而无需修改 Proof-Script 的页面模型。自定义命令将
组件专属的数据序列化后，通过 `ProofScript.Extension.addPageComponent` 提交标签、JSON 数据和
可选标签即可。`theorem` 和 `lemma` 是页面导出器特殊处理的组件，以便在 `#page_end` 时解析
声明元数据。

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

### 2.6 定理与引理组件

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

使用 `#lemma` 声明时，值结构相同，但组件标签明确为 `lemma`：

```json
{
  "lemma": {
    "value": {
      "name": "辅助引理",
      "label": null,
      "proof": ".Proof-Script/proofs/Paper/Main/supportingLemma.json",
      "sorryAx": false
    }
  }
}
```

`name` 来自 `theorem_info` 中的展示名；未指定时采用 Lean 声明的非限定名称。`label` 可为
null。`proof` 是独立证明树 JSON 文件的路径。`sorryAx` 表示该声明是否传递依赖 Lean 的
`sorryAx`。页面不会嵌入证明文档。`#theorem` 和 `#lemma` 均支持 `:= script` 与不受策略
白名单限制的 `:= by`。

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
      "svg": {
        "$resource": {
          "path": ".Proof-Script/resources/svg/123.svg",
          "hash": "123",
          "mediaType": "image/svg+xml",
          "encoding": "utf-8"
        }
      }
    }
  }
}
```

`@latex` 接受任意 LaTeX 源码并将其编译为 SVG。完整 SVG 存入引用的 UTF-8 资源文件；内容
hash 用于完整性校验，相同 SVG 会共享同一资源文件，不会丢弃任何 SVG 信息。

`@figure` 接受一个相对图片资源路径：

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

不带参数的 `@references` 命令会插入：

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
`@references` 不再支持导出独立 JSON 文件。

## 3. 证明树 JSON

### 3.1 位置

证明树写入以下路径：

```text
.Proof-Script/proofs/<module path>/<declaration path>.json
```

### 3.2 顶层对象

顶层对象包含模式版本、完整 Lean 源代码、表达式表和证明步骤数组：

```json
{
  "schemaVersion": "0.3.0",
  "code": "#theorem mainTheorem : True := script\n  trivial",
  "expressions": {
    "e0": { "kind": "const", "name": "True", "levels": [], "isProp": true },
    "e1": { "kind": "const", "name": "True.intro", "levels": [], "isProp": false }
  },
  "proof": [
    { "_goal_": { "$ref": "e0" } },
    { "_step_": "provide", "proof": { "$ref": "e1" } }
  ]
}
```

当 `#theorem` 或 `#lemma` 使用 `:= by` 时，Proof-Script 接受任意可通过 Lean 编译的策略，
不检查策略合法性，也不记录具体步骤，而是输出代码-only 文档：

```json
{
  "schemaVersion": "0.3.0",
  "code": "#lemma supportingLemma : True := by\n  trivial"
}
```

该模式仍会直接扫描 elaboration 后的 proof term，自动采集带 `theorem_info` 的引用。

每一项均为以下逻辑形式之一。

目标记录：

```json
{
  "_goal_": { "$ref": "e0" },
  "prev_proof": { "$ref": "e1" }
}
```

步骤记录：

```json
{
  "_step_": "provide",
  "proof": { "$ref": "e1" }
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

目标和策略参数使用 `{ "$ref": "eN" }` 形式的表达式引用。`eN` 在顶层 `expressions`
对象中解析，所有被引用的条目都必须存在。表达式条目使用 `kind` 判别字段，其值包括：

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

表达式表构成有向无环图。递归表达式字段（`fn`、`arg`、`type`、`body`、`value`、`expr`、
`typeOf` 以及每个 `arguments[].expr`）使用引用而非复制子树。解析全部引用后，可以无损恢复
0.2.0 输出的所有字段。ID 仅在当前证明文档内有效。

每个序列化表达式节点都包含 `isProp`，它通过 Lean 的 `Meta.isProp` 对该节点本身计算。
因此可以区分命题 `P`、证明 `h : P` 和数据表达式，无需根据名字或 JSON 结构猜测。

application 节点保留二叉 `fn`、`arg` 字段，并额外提供：

```json
{
  "headConstant": "HAdd.hAdd",
  "arguments": [
    {
      "expr": { "$ref": "e7" },
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
  "svg": {
    "$resource": {
      "path": ".Proof-Script/resources/svg/123.svg",
      "hash": "123",
      "mediaType": "image/svg+xml",
      "encoding": "utf-8"
    }
  }
}
```

### 3.5 外部资源与 embed

大型不可变数据使用资源引用：

```json
{
  "$resource": {
    "path": ".Proof-Script/proofs/Library/Theorem.json",
    "hash": "123",
    "mediaType": "application/vnd.proof-script.proof+json",
    "encoding": "utf-8"
  }
}
```

路径相对于项目工作目录。读取方必须读取完整 UTF-8 文件，并验证其内容 hash 与引用一致。
SVG 资源包含原始完整 SVG。`embed` 步骤引用原始完整证明文档，不再复制和重放证明树；父步骤
仍保留 `theorem`、`type`、`args`、`argKinds` 和引入的 `h` 字段，因此原有信息均可取得。

0.3.0 将内联表达式树和 SVG 字符串替换为引用。这是模式迁移而非信息删除：读取方解析
`$ref` 与 `$resource` 后即可获得相同数据。

## 4. 兼容性要求

写入方必须：

- 保持源组件的顺序；
- 以语义化版本字符串的形式输出页面 `schemaVersion`；
- 对源码位置使用 UTF-8 字节偏移量；
- 保持证明树独立于页面 JSON；
- 对缺失的可选标签使用 `null`；
- 按顺序保留 `extra` 元数据键值对。
- 输出证明记录或其他表达式节点引用的每一个表达式 ID；
- 在引用路径保留完整资源内容。

读取方应：

- 拒绝不支持的模式主版本；
- 忽略兼容的未知组件字段；
- 保留未知的证明步骤字段；
- 相对于项目工作目录解析定理的 `proof` 路径；
- 加载所有页面文件后，构建跨页面标签索引。
- 根据当前证明文档的 `expressions` 表解析 `$ref`；
- 相对于项目工作目录解析 `$resource`，并验证内容 hash。

## 5. 已知的模式限制

- Lean 表达式的序列化目前仅在结构层面进行描述，并且仍可扩展。
- 源文件路径目前通常为绝对路径。
- 自定义页面组件已被保留，但尚无法公开注册。
- 跨页面引用的有效性将由未来的渲染器检查，而非由各个 Lean 模块检查。
