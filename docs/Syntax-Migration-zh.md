# 页面命令语法迁移

当前页面组件命令已从 `#` 前缀迁移到 `@` 前缀。此次迁移只改变 Lean 源码语法，不改变
Page JSON、Proof JSON 或其 schema。

## 页面组件

| 旧语法 | 新语法 |
| --- | --- |
| `#text` | `@text` |
| `#latex` | `@latex` |
| `#figure` | `@figure` |
| `#references` | `@references` |
| `#computation` | `@computation` |
| `#theorem` | `@theorem` |
| `#lemma` | `@lemma` |
| `#page_end` | `page_end` |

示例：

```lean
@text r#"= Overview <overview>"#

@latex (title := "Diagram") r#"\begin{tikzpicture} ... \end{tikzpicture}"#

@figure (title := "Image") "assets/overview.png"

@references
page_end
```

## Computation

`@computation` 的全部参数必须位于一个配置对象中：

```lean
@computation {
  metadata := (title := "Finite computation", label := "finite-computation"),
  renderer := "example/table-v1",
  function := chooseOffset,
  payload := r#"{"inputs": []}"#}
```

四个键分别表示：

- `metadata`：页面组件元数据，至少包含 `title`。
- `renderer`：下游渲染器 ID 字符串。
- `function`：Lean 函数声明标识符。
- `payload`：渲染器使用的 JSON 字符串。

## JSON 兼容性

语法迁移不会改变页面 JSON、Proof JSON、组件 kind、`$ref`、`$resource` 或 schema 版本。
下游渲染器无需修改 JSON 解码逻辑。
