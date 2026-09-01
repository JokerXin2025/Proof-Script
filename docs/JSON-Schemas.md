# Proof-Script JSON Schemas

This document specifies the public JSON formats emitted by Proof-Script.

The downstream renderer migration checklist is available in
[`Renderer-Migration-0.3.0-zh.md`](Renderer-Migration-0.3.0-zh.md).

The machine-readable JSON Schema files are:

- `docs/schema/page.schema.json`
- `docs/schema/proof.schema.json`
- `docs/schema/computation-pending.schema.json`
- `docs/schema/computation-bundle.schema.json`
- `docs/schema/computation-published-bundle.schema.json`
- `docs/schema/computation-index.schema.json`

Both schemas use JSON Schema Draft 2020-12.

## 1. Versioning

The current schema version is `0.3.0`.

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
  "schemaVersion": "0.3.0",
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
- `lemma`
- `latex`
- `figure`
- `references`
- `computation`

The component envelope is open: modules may define additional tags without changing Proof-Script's
page model. A custom command serializes its component-specific value and calls
`ProofScript.Extension.addPageComponent` with the tag, JSON value, and optional labels. Only the
`theorem` and `lemma` components are handled specially by the page exporter so their declaration
metadata can be resolved at `#page_end`.

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

### 2.6 Theorem and lemma components

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

A declaration introduced with `#lemma` has the same value shape but uses a distinct component tag:

```json
{
  "lemma": {
    "value": {
      "name": "Supporting lemma",
      "label": null,
      "proof": ".Proof-Script/proofs/Paper/Main/supportingLemma.json",
      "sorryAx": false
    }
  }
}
```

`name` is the display name from `theorem_info`; when omitted it defaults to the Lean declaration's
unqualified name. `label` is nullable. `proof` is the path to the independent proof-tree JSON file.
`sorryAx` is true when the declaration transitively uses Lean's `sorryAx`. The page does not embed
the proof document. Both `#theorem` and `#lemma` support `:= script` and unrestricted `:= by`.

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

`#latex` accepts arbitrary LaTeX source and compiles it to SVG. The complete SVG is stored in the
referenced UTF-8 resource file. Its content hash enables integrity checks and identical SVG values
share one resource file; no SVG information is discarded.

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

### 2.8 Computation component

`@computation` connects a Lean function declaration to a versioned downstream renderer manifest.
All arguments are enclosed in one configuration object:

```lean
@computation {
  metadata := (title := "Explorer"),
  renderer := "example/table-v1",
  function := Paper.compute,
  payload := r#"{"execution":{"backend":"table"}}"#}
```

```json
{
  "computation": {
    "value": {
      "schemaVersion": "1.1.0",
      "metadata": {"title": "Explorer", "label": "explorer", "extra": []},
      "renderer": "example/table-v1",
      "function": {
        "declaration": "Paper.compute",
        "type": "Bool → Nat",
        "expression": {"$ref": "e0"},
        "implementation": {"$ref": "e4"},
        "expressions": {"e0": {"kind": "const", "name": "Paper.compute"}}
      },
      "execution": {
        "backend": "wasm",
        "status": "pending",
        "abi": "proof-script-json-v1",
        "bundleId": "Paper.Main",
        "entry": "Paper.compute",
        "wrapper": "Paper.__proofScript_compute",
        "manifest": ".Proof-Script/computations/pending/Paper/Main/Paper/compute.json"
      },
      "payload": {"execution": {"backend": "table"}}
    }
  }
}
```

`expression` identifies the declaration and `implementation` points to its elaborated function body
in the shared, self-contained expression table. This compiler-produced intermediate artifact is
declaration provenance and suitable for analysis, but is not a stable executable Lean IR. The
renderer chooses and validates an execution backend from its own versioned payload contract. See
`Embedded-Computation-Renderer-zh.md`.

During Lean elaboration, `#computation` validates a single-argument pure function, synthesizes
`FromJson`/`ToJson`, creates a `String → String` wrapper using `proof-script-json-v1`, and writes the
pending manifest referenced by `execution.manifest`. Both `α → β` and
`α → Except String β` are accepted; the former is lifted through `Except.ok`. The pending status is
replaced by a Wasm resource only in the later bundling/finalization stage.

Pending entry manifests are written below:

```text
.Proof-Script/computations/pending/<module path>/<declaration path>.json
```

They contain the stable module bundle ID, original declaration, generated wrapper, ABI, source
location, pretty-printed input/output types, and `pure`/`except` error mode. Renderer configuration
remains in the page component because multiple visualizations may share one compiled entry.

### 2.10 Computation bundle

The stage 4 bundler scans pending manifests, groups entries by `bundleId`, verifies each generated
wrapper is present in the module C IR, and emits one multi-entry Wasm module per group below:

```text
.Proof-Script/computations/bundles/<bundleId>/bundle.{mjs,wasm,json}
```

`bundle.json` follows `docs/schema/computation-bundle.schema.json`. It records sorted entry IDs,
wrapper declarations, linked C modules, artifact paths, byte size, SHA-256, and the generic
unknown-entry smoke-test result. Bundles currently use `module-local` linking: the computation
support module and the declaring module are linked, while project-level dependency closure and
content-addressed publication are deferred to later stages.

### 2.11 Finalized computation resources

`scripts/finalize-computations.mjs` validates pending entries against built bundles and publishes
each module/wasm pair into a content-addressed directory:

```text
.Proof-Script/resources/computation/<bundleHash>/bundle.{json,mjs,wasm}
```

`bundleHash` is SHA-256 over the module bytes, a zero separator, and the Wasm bytes. Every resource
also carries its own SHA-256 and byte size. Page execution changes from `pending` to `ready` and
contains resource references for the published manifest, ES module, and Wasm binary. The finalizer
writes changed pages and `.Proof-Script/computations/index.json` through temporary files followed by
atomic rename. It rejects missing bundles, stale bundle entries, missing page components, and hash
mismatches before changing any page.

Published bundle and index formats are specified by
`computation-published-bundle.schema.json` and `computation-index.schema.json`.

### 2.9 References component

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

The top level contains the schema version, complete Lean source code, an expression table, and the
proof-step array:

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

For `#theorem` or `#lemma` declarations written with `:= by`, Proof-Script accepts any Lean tactic,
does not validate or record individual steps, and emits a code-only document:

```json
{
  "schemaVersion": "0.3.0",
  "code": "#lemma supportingLemma : True := by\n  trivial"
}
```

Reference collection remains enabled for this mode and scans the elaborated proof term directly.

Each item is one of the following logical forms.

Goal record:

```json
{
  "_goal_": { "$ref": "e0" },
  "prev_proof": { "$ref": "e1" }
}
```

Step record:

```json
{
  "_step_": "provide",
  "proof": { "$ref": "e1" }
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

Goals and tactic parameters contain expression references of the form `{ "$ref": "eN" }`.
`eN` resolves against the top-level `expressions` object. Every referenced entry must exist.
Expression entries use a `kind` discriminator such as:

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

The table represents a directed acyclic graph. Recursive expression fields (`fn`, `arg`, `type`,
`body`, `value`, `expr`, `typeOf`, and every `arguments[].expr`) are references rather than copied
subtrees. Resolving all references reconstructs every field emitted by version 0.2.0 without loss.
The IDs are local to one proof document and have no meaning outside it.

Every serialized expression node includes `isProp`, computed using Lean's `Meta.isProp` for that
exact expression. This distinguishes propositions such as `P`, proofs such as `h : P`, and data
expressions without relying on names or structural guesses.

Application nodes retain the binary `fn` and `arg` fields and additionally provide:

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

`headConstant` is a fully qualified declaration name or null when the application head is not a
constant. `arguments` is flattened and ordered. Binder metadata is derived from the head
declaration's instantiated forall telescope; fields are null when no reliable telescope entry is
available.

Expression nodes may contain `sourceRange` using the same `{file,start,stop}` UTF-8 byte-offset
format as page components. It is emitted only when Lean retained source syntax in expression
metadata; absent ranges are omitted rather than inferred.

### 3.4 LaTeX component steps

The `latex` proof tactic accepts the same metadata and arbitrary LaTeX source as the page-level
`#latex` component. It produces a step record containing:

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

### 3.5 External resources and embed

Large immutable values use a resource reference:

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

Paths are relative to the project working directory. Readers must load the complete UTF-8 file and
verify that its `hash` equals Proof-Script's string hash recorded in the reference. SVG resources
contain the original complete SVG. An `embed` step references the original complete proof document
instead of duplicating and replaying its proof tree; its `theorem`, `type`, `args`, `argKinds`, and
introduced `h` fields remain in the parent step, so all former information remains available.

Version 0.3.0 intentionally replaces inline expression trees and SVG strings with references. This
is a schema migration rather than information removal: consumers obtain the same data by resolving
`$ref` and `$resource` objects.

## 4. Compatibility Requirements

Writers must:

- preserve source component order;
- emit page `schemaVersion` as a semantic-version string;
- use UTF-8 byte offsets for source locations;
- keep proof trees independent from page JSON;
- use `null` for absent optional labels;
- preserve `extra` metadata pairs in order.
- emit every expression ID referenced by a proof record or another expression node;
- retain complete resource contents at the referenced paths.

Readers should:

- reject unsupported major schema versions;
- ignore unknown compatible component fields;
- preserve unknown proof-step fields;
- resolve theorem `proof` paths relative to the project working directory;
- build cross-page label indexes after loading all page files.
- resolve `$ref` against the current proof document's `expressions` table;
- resolve `$resource` paths relative to the project working directory and verify their hashes.

## 5. Known Schema Limitations

- Lean expression serialization is described only structurally and remains extensible.
- Source paths are currently commonly absolute.
- Custom page components are intentionally open and therefore do not receive component-specific
  validation from the core schema unless promoted to a built-in tag.
- Cross-page reference validity is checked by the future renderer, not by individual Lean modules.
