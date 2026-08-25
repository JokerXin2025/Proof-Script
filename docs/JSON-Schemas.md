# Proof-Script JSON Schemas

This document specifies the public JSON formats emitted by Proof-Script.

The machine-readable JSON Schema files are:

- `docs/schema/page.schema.json`
- `docs/schema/proof.schema.json`

Both schemas use JSON Schema Draft 2020-12.

## 1. Versioning

The current schema version is `0.2.0`.

Page JSON and proof-tree JSON both embed the version in their top-level `schemaVersion` field.

Version changes follow these rules:

- Patch: documentation corrections or constraints that do not change accepted JSON.
- Minor: backward-compatible fields or component kinds are added.
- Major: existing fields, tags, or meanings change incompatibly.

Consumers should reject unsupported major versions and may ignore unknown fields introduced by a
newer compatible minor version.

## 2. Page JSON

### 2.1 Location

For Lean module `Paper.Chapter.Main`, the page file is:

```text
.Proof-Script/pages/Paper/Chapter/Main.json
```

### 2.2 Top-level object

```json
{
  "schemaVersion": "0.2.0",
  "ProjectInfo": {},
  "module": "Paper.Chapter.Main",
  "source": "/project/Paper/Chapter/Main.lean",
  "components": []
}
```

Fields:

| Field | Type | Meaning |
| --- | --- | --- |
| `schemaVersion` | string | Semantic schema version. |
| `ProjectInfo` | object | Project metadata registered by `project_info`. |
| `module` | string | Fully qualified Lean module name. |
| `source` | string | Source file path reported by Lean. Currently usually absolute. |
| `components` | array | Components in source order. |

### 2.3 Source location

Every component has:

```json
{
  "file": "/project/Paper/Main.lean",
  "start": 120,
  "stop": 180
}
```

`start` and `stop` are UTF-8 byte offsets in the Lean source file. They are not line and column
numbers.

### 2.4 Component envelope

```json
{
  "source": { "file": "...", "start": 0, "stop": 10 },
  "data": {
    "text": { "value": {} }
  }
}
```

`data` is a tagged object. Exactly one component tag is expected.

Current tags:

- `text`
- `theorem`
- `latex`
- `figure`
- `references`
- `custom` (reserved; no public registration command yet)

### 2.5 Text component

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

The original ProofText source and parsed semantic AST are both preserved.

Inline tags currently include:

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

Block tags currently include:

- `paragraph`
- `heading`
- `code`
- `orderedList`
- `unorderedList`
- `quote`
- `displayMath`

### 2.6 Theorem component

```json
{
  "theorem": {
    "value": {
      "name": "Main theorem",
      "label": "main-theorem",
      "proof": ".Proof-Script/proofs/Paper/Main/mainTheorem.json",
      "sorryAx": false
    }
  }
}
```

`name` is the display name from `theorem_info`; when omitted it defaults to the Lean declaration's
unqualified name. `label` is nullable. `proof` is the path to the independent proof-tree JSON file.
`sorryAx` is true when the declaration transitively uses Lean's `sorryAx`. The page does not embed
the proof tree.

### 2.7 LaTeX and figure components

```json
{
  "latex": {
    "value": {
      "metadata": {
        "title": "Commutative diagram",
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

`#LaTeX` accepts arbitrary LaTeX source, compiles it to SVG, and emits the `latex` tag above.

`#figure` accepts a relative image resource path:

```json
{
  "figure": {
    "value": {
      "metadata": {
        "title": "Overview image",
        "label": "overview-image",
        "extra": [["width", "wide"]]
      },
      "path": "assets/overview.png",
      "extension": "png"
    }
  }
}
```

Both component kinds use the `figure` reference namespace. Figure paths must be relative and include
a file extension. Proof-Script records the path and extension but does not copy or read the image.

### 2.8 References component

The no-argument `#references` command inserts:

```json
{
  "references": {
    "value": [
      {
        "name": "Library.result",
        "info": {
          "project": {},
          "name": "Display name",
          "label": "result",
          "tags": [],
          "extra": []
        }
      }
    ]
  }
}
```

The component is placed exactly where `#references` occurs. The reference staging area is cleared
after insertion. `#references` does not support standalone file export.

## 3. Proof-tree JSON

### 3.1 Location

Proof trees are written below:

```text
.Proof-Script/proofs/<module path>/<declaration path>.json
```

### 3.2 Top-level object

The top level contains the schema version, complete Lean source code, and proof-step array:

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

Each item is one of the following logical forms.

Goal record:

```json
{
  "_goal_": {},
  "prev_proof": {}
}
```

Step record:

```json
{
  "_step_": "provide",
  "proof": {}
}
```

Merged strategy record:

```json
{
  "name": "split_and",
  "info": {},
  "left": [],
  "right": []
}
```

The exact fields of tactic steps depend on the tactic and its recorder. Consumers must use
`_step_` or `name` as the discriminator and preserve unknown fields.

### 3.3 Expression values

Goals and tactic parameters may contain serialized Lean expressions. Expression objects use a
`kind` discriminator such as:

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

Expression objects are intentionally left extensible in `proof.schema.json`, because optional
type information and tactic-specific wrappers change their fields.

Every serialized expression node includes `isProp`, computed using Lean's `Meta.isProp` for that
exact expression. This distinguishes propositions such as `P`, proofs such as `h : P`, and data
expressions without relying on names or structural guesses.

Application nodes retain the binary `fn` and `arg` fields and additionally provide:

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

`headConstant` is a fully qualified declaration name or null when the application head is not a
constant. `arguments` is flattened and ordered. Binder metadata is derived from the head
declaration's instantiated forall telescope; fields are null when no reliable telescope entry is
available.

Expression nodes may contain `sourceRange` using the same `{file,start,stop}` UTF-8 byte-offset
format as page components. It is emitted only when Lean retained source syntax in expression
metadata; absent ranges are omitted rather than inferred.

### 3.4 LaTeX component steps

The `tikz`, `figure`, and `table` proof tactics produce step records containing:

```json
{
  "_step_": "figure",
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

## 4. Compatibility Requirements

Writers must:

- preserve source component order;
- emit page `schemaVersion` as a semantic-version string;
- use UTF-8 byte offsets for source locations;
- keep proof trees independent from page JSON;
- use `null` for absent optional labels;
- preserve `extra` metadata pairs in order.

Readers should:

- reject unsupported major schema versions;
- ignore unknown compatible component fields;
- preserve unknown proof-step fields;
- resolve theorem `proof` paths relative to the project working directory;
- build cross-page label indexes after loading all page files.

## 5. Known Schema Limitations

- Lean expression serialization is described only structurally and remains extensible.
- Source paths are currently commonly absolute.
- Custom page components are reserved but not publicly registrable.
- Cross-page reference validity is checked by the future renderer, not by individual Lean modules.
