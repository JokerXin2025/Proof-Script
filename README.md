# Proof-Script

Proof-Script is a compile-time language extension for [Lean 4](https://lean-lang.org/).
It provides a structured, extensible, and semantically enriched proof DSL that records Lean's live proof goals, tactic arguments, and branch structure and exports them as JSON.
Proof-Script also integrates page components such as ProofText body content, theorem statements, images, and LaTeX SVG. This data is automatically compiled and exported as JSON for renderers or other downstream tools to consume.

## Table of Contents

- [Quick Start](#quick-start)
- [Formal Proofs](#formal-proofs)
- [ProofText](#prooftext)
- [Automatic Reference Management](#automatic-reference-management)
- [Other Page Components](#other-page-components)
- [Page Export](#page-export)
- [Requirements](#requirements)
- [Current Limitations](#current-limitations)
- [Related Documentation](#related-documentation)

## Quick Start

Add Proof-Script as a dependency in `lakefile.toml` and run `lake update`. You can then use it in a Lean project.

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

Assuming the Lean file above is `./Project/Module/Page.lean`, the proof and page information will be exported after compilation to, respectively:

```text
./.Proof-Script/pages/Project/Module/Page.json
./.Proof-Script/proofs/Project/Module/Page/mainResult.json
```

## Formal Proofs

### Script Mode

Proof-Script introduces script mode, initiated by `:= script`, as an alternative to tactic mode. Within `:= script`, users write script tactic names without prefixes; the framework automatically rewrites them to the internal execution entry point `script_<name>` and uses `_script_<name>` while recording. Its syntax is consistent with tactic mode (and is in fact built on tactic mode). Script mode broadly contains the following three kinds of basic elements:

1. Steps: `intro_h`, `apply`, and others serve as logical units in formal proofs and carry stronger semantics than ordinary Lean tactics.
2. Strategies: `split_and`, `contra`, `induction`, and others determine the proof structure at a high level and share a uniform syntax.
3. Metadata: `remark`, `latex`, and others embed explanatory text, diagrams, and other metadata in proof scripts.

These three kinds of elements are collectively called script tactics. These constraints make proof scripts more suitable for stable mapping to natural language or interactive presentations while retaining Lean's formal verification capabilities. The following code provides a complete example.

```lean
theorem implicationChain
    (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := script
  intro_h hP
  infer
    P => Q := hPQ hP
    _ => R := hQR ?_
```

### Built-in Proof-Script Tactics

#### Steps

##### Native Lean Tactics

The core module wraps the following Lean tactics. Only the simplified syntax listed here is supported:

| Tactic | Effect |
| :- | :- |
| `assumption` | Closes the goal using a matching hypothesis from the context |
| `change t` | Replaces the goal with the definitionally equal `t` |
| `contradiction` | Closes the goal from a contradiction in the context |
| `exfalso` | Changes the current proposition goal to `False` |
| `omega` | Solves Presburger arithmetic goals |
| `rfl` | Closes the goal by reflexivity |
| `simp_only [l₁ l₂ ...]` / `simp_only [l₁ l₂ ...] at h₁ h₂` / `simp_only [l₁ l₂ ...] at *` / `simp_only [l₁ l₂ ...] at ⊢` | Simplifies using only the specified whitespace-separated identifiers, on selected hypotheses, all hypotheses, or the target |
| `symm` | Swaps the two sides of a symmetric relation |
| `trivial` | Solves simple goals |
| `rewrite [h₁ h₂ ...]` / `rewrite [← h₁ h₂ ...]` with `at h₁ h₂`, `at *`, or `at ⊢` | Rewrites using equalities, then attempts native `rfl` |
| `unfold d₁ d₂ ...` | Unfolds one or more whitespace-separated definitions |

##### Dedicated Script Tactics

| Tactic | Effect | Corresponding Native Tactic | Restriction |
| :- | :- | :- | :- |
| `intro_h ⟨h⟩` | Introduces a propositional hypothesis | `intro` | May only be used on proof terms |
| `intro_var ⟨val⟩` | Introduces a data variable | `intro` | May only be used on variables |
| `provide ⟨h⟩` | Supplies a witness in `witness.data`, or for an existential target | `exact` / `exists` | It is not a general `exact`; it is restricted to these two contexts |
| `apply t` | Applies a proposition of the form `P → Q` or `P ↔ Q`, leaving exactly one premise subgoal | `apply` / `Iff.mp` / `Iff.mpr` | The outermost proposition must be an implication or equivalence; only one goal is produced |
| `ext_fun x` | Reduces a function equality to pointwise equality | `funext` | Both sides of the equality must be functions with the same domain |
| `obtain_exist ⟨x, hx⟩ := h` | Destructures a local existential hypothesis | `cases` | `h` must prove an existential proposition |
| `left` / `right` | Selects the left or right side of a disjunction goal | `apply Or.inl/inr` | The current goal must be a disjunction |
| `quot_induction q with a` | Performs quotient induction | `induction` | |
| `unpack_and ⟨h₁, h₂⟩ := h` | Destructures a local conjunction hypothesis | `cases` | `h` must prove a conjunction |
| `unpack_iff ⟨h₁, h₂⟩ := h` | Destructures a local equivalence hypothesis | `cases` | `h` must prove an equivalence |

`apply` accepts a term whose outermost proposition is an implication or equivalence. It applies only the outermost implication layer, so a chain such as `P → Q → R` produces the single premise goal `P`, with the remaining implication retained in the conclusion. For an equivalence, it selects the direction matching the current target:

```lean
theorem compose (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := script
  apply hQR
  apply hPQ
  assumption
```

#### Strategies

Strategy tactics split a goal into branches with **semantic names**, thereby establishing the proof's high-level structure.
For each goal branch produced by a strategy, complete the proof using `| case => …` syntax. Anonymous `·` branches are prohibited in script mode.

The currently available strategy and structural tactics are:

| Tactic | Effect or Branches |
| :- | :- |
| `have h : P` | Produces the continuation goal and an assertion proof goal named `proof` |
| `witness` | Constructs an existential, producing `data` and `proof` |
| `split_and` | Splits a binary conjunction, producing `left` and `right` |
| `split_and!` | Recursively splits a conjunction, producing `goalI`, `goalII`, and so on |
| `split_iff` | Proves an equivalence, producing `suffice` and `necess` |
| `cases_by h` | Splits on a local disjunction hypothesis, producing `left` and `right` |
| `cases_by! h` | Recursively splits a local disjunction, producing `goalI`, `goalII`, and so on |
| `cases_on t` | Splits on the truth of a proposition or the constructors of data |
| `contra h` | Proves by contradiction, producing `proof` |
| `induction n` | Performs natural-number induction |
| `complete_induction n` | Performs strong induction on natural numbers |

##### Existential Construction

`witness` operates on an existential proposition of the form `∃ x, P x` and splits it into two branches:

- `data`: construct an object satisfying the condition
- `proof`: prove that the object satisfies `P`

```lean
theorem demo_witness : ∃ n : Nat, n = 0 := script
  witness
  | data => provide 0
  | proof => trivial
```

`provide` can also construct an existential directly, without the two branches of `witness`. It cannot be used as a general `exact` step:

```lean
theorem provide_witness : ∃ n : Nat, n = 0 := script
  provide 0
  rfl
```

##### Goal Decomposition: Conjunction

`split_and` operates on a conjunction of the form `P ∧ Q` and splits it into two branches:

- `left`: the left branch
- `right`: the right branch

`split_and!` recursively decomposes a conjunction of the form `P₁ ∧ P₂ ∧ ... ∧ Pₙ` into branches named `goalI`, `goalII`, and so on.

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

##### Goal Decomposition: Equivalence

`split_iff` operates on an equivalence proposition of the form `P ↔ Q` and splits it into two branches:

- `suffice`: sufficiency, namely `P → Q`
- `necess`: necessity, namely `Q → P`

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

##### Proof by Contradiction

In script mode, `contra h` can:

1. Operate on a negation of the form `¬ P` and produce a `proof` branch in which `P` is introduced as a hypothesis.
2. Operate on another proposition and produce a `proof` branch in which `¬ P` is introduced as a hypothesis.

In the `proof` branch, the goal is changed to `False`, so the proof is completed by deriving a contradiction.

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

##### Mathematical Induction

In script mode, `induction n` performs mathematical induction on the natural number `n` and produces two branches, `zero` and `succ k ih`:

```lean
theorem demo_induction (n : Nat) : n + 0 = n := script
  induction n
  | zero => rfl
  | succ k ih => rfl
```

##### Strong (Complete) Induction

`complete_induction n` performs strong induction on the natural number `n`. It likewise produces `zero` and `succ k ih` branches, but the induction hypothesis in the `succ` branch, `ih : ∀ m < k + 1, P m`, covers every smaller natural number:

```lean
theorem demo_complete_induction (n : Nat) : n + 0 = n := script
  complete_induction n
  | zero => rfl
  | succ k ih => rfl
```

##### Case Analysis with `cases_on`

`cases_on p` performs case analysis on whether proposition `p` is true or false, producing the two branches `true h` (`h : p`) and `false h` (`h : ¬p`):

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

#### Metadata

The core module provides the following metadata tactics:

| Tactic | Effect |
| :- | :- |
| `remark "text"` | Inserts a natural-language annotation |
| `svg "code"` | Inserts raw SVG metadata |
| `latex (title := "...", ...) "source"` | Compiles and records arbitrary LaTeX source and its SVG |
| `cause "reason"` | Temporarily closes the goal with `sorry` and records the reason |

##### Informal Proofs

The `cause` tactic lets you use natural language in place of a proof that has not yet been formalized. It uses `sorry` to fill the proof temporarily, for example:

```lean
theorem draft (P : Prop) : P := script
  cause "This result has not been formalized yet."
```

For term form, use the ordinary term macro `cause`, for example `:= cause "Not yet formalized"`; it is not a directly executable script tactic name.

##### Annotations

The `remark` tactic inserts a natural-language annotation to help readers better understand part of a proof, for example:

```lean
@theorem demo_remark {P : Prop} (h_P : P) : P := script
  remark "This is a simple proof"
  assumption
```

##### LaTeX (SVG)

Proofs provide a unified `latex` metadata tactic. Like the page component `#latex`, it accepts metadata and arbitrary LaTeX source. During recording, it invokes the local LaTeX toolchain to generate SVG and writes the metadata, source, and SVG into the proof tree. For example:

```lean
@theorem proofWithDiagram (P : Prop) (h : P) : P := script
  latex (title := "Derivation Diagram", label := "proof-diagram") r#"
    \begin{tikzpicture}
      \draw[->] (0,0) -- (1,0);
    \end{tikzpicture}
  "#
  assumption
```

To ensure that the precompiler works correctly, make sure TeX Live is installed locally. This is the proof-level tactic; use the `#latex` command described below for arbitrary page-level LaTeX.

#### Calculation Chains with `calc`

Proof-Script wraps `calc` blocks as a script tactic, so they can be used in script mode.

#### Inference Chains with `infer`

As is well known, `calc` blocks greatly simplify chained calculations over transitive relations. Inference chains with `infer` use similar syntax to simplify general chains of deductions, for example:

```lean
theorem divisibility_chain {a b c d e : ℕ}
    (h_ab : a ∣ b) (h_bc : b ∣ c)
    (h_pos : 0 < c * d * e)
  : a ≤ c * d * e
:= script
  remark "Here we prove the inequality using divisibility"
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

The `:=` syntax here is equivalent to using the `refine` tactic, but it must follow these rules:

- The initial step must not use `?_`, and one of its arguments must be a term of the proposition on the left side of `=>`.
- Every step after the initial step must contain exactly one `?_`, used as a placeholder for a term of the proposition on the right side of the preceding step.

`infer` can:

- Be used as an intermediate step, anonymously adding every new conclusion to the context (similar to `have`).
- Close the goal as a terminating tactic.
- Be used directly as a term (written `:= infer`); here, `infer` is an ordinary term macro rather than an unprefixed executable script tactic.

### Optional Mathlib Script Tactics

After installing Mathlib, explicitly import the optional extension:

```lean
import ProofScript
import ProofScript.Mathlib
```

This module is not imported automatically by the core `ProofScript` module and is not part of the default Lake target. The currently wrapped tactics, in alphabetical order, are:

| Tactic | Supported Simplified Forms |
| :- | :- |
| `script_continuity` | Default form |
| `script_exact_mod_cast` | `script_exact_mod_cast proof` |
| `script_field` | Default; `script_field [lemmas...]` |
| `script_gcongr` | Default; pattern; `with names...`; and combinations of both |
| `script_itaotu` / `script_itauto` | Default; `*`; proposition lists; and `!` variants |
| `linarith` | Default; fact lists; `only`; and `!` variants |
| `script_measurability` | Default form |
| `script_nlinarith` | Default; fact lists; `only`; and `!` variants |
| `script_norm_cast` | Default and `at` forms |
| `norm_num` | Default; lemma lists; `only`; and corresponding `at` forms |
| `script_positivity` | Default and fact-list forms |
| `script_push_cast` | Default; lemma lists; `only`; and corresponding `at` forms |
| `qify` / `rify` / `zify` | Default; lemma lists; and corresponding `at` forms |
| `script_ring` | `script_ring`; `script_ring!` |
| `script_ring_nf` | Default; `!`; and corresponding `at` forms |
| `script_tauto` | Default form |
| `script_wlog` | Default; `generalizing`; `with`; combinations of both; and `script_wlog!` |

To keep arguments stable for recording, the wrappers use only basic categories such as `ident` and `term`. Arguments in square brackets are whitespace-separated:

```lean
linarith [h₁ h₂]
qify [hab] at h ⊢
norm_num only [Nat.add_zero Nat.zero_add] at *
```

Tactics that support locations may use `at h`, `at h₁ h₂`, `at *`, `at ⊢`, and `at h₁ h₂ ⊢`. Configuration objects, custom dischargers, arbitrary tactic blocks, and suggestion-only `?` variants are not wrapped. See the [Mathlib extension documentation](ProofScript/Mathlib-README-zh.md) for complete details.

### Custom Script Tactics

Use `script_macro` / `script_elab` to create a script tactic. Within `:= script`, users still write the unprefixed `name`; the framework automatically rewrites it to the execution entry point `script_name` and then to `_script_name` during recording. The unprefixed name does not become an executable tactic in ordinary `:= by` blocks. Both commands, as well as `script_recorder`, support only an explicit `: tactic` category. When a term version is needed, use an ordinary `macro` to wrap it as a `script` proof. For example:

```lean
script_macro (recorder := exclusive)
"finish" proof:term : tactic => `(tactic| exact $proof:term)

script_elab (intro := [h])
"intro_named" h:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro $h:ident))

macro "finish" proof:term : term => `(script
  finish $proof:term)
```

When creating a script tactic, you may need to provide additional information so that Proof-Script can process it correctly. The available parameters are:

| Parameter | Values | Description | Default |
| - | - | - | - |
| `intro` | List of syntax arguments | Arguments introduced by this script tactic; serialized only after execution | `[]` |
| `clear` | List of syntax arguments | Arguments removed by this script tactic; serialized only before execution | `[]` |
| `strategy` | `true`, `false` | Marks whether this script tactic is a strategy | `false` |
| `recorder` | `auto`, `exclusive` | Generates a recorder automatically or uses only a handwritten recorder | `auto` |

By default, Proof-Script exports information about every argument to the script tactic both before and after execution. For:

- Complex syntax arguments other than `term`, `ident`, `str`, `num`, and `+` repetition forms
- Tactics that need to export specific metadata (for example, `latex` automatically compiles LaTeX to SVG)

set `recorder := exclusive` and use `script_recorder` to create a recorder manually. `script_recorder` accepts the original tactic name without the `script_` prefix. For an existing `script_<name>` execution entry point, it automatically defines the `_script_<name>` recording entry point and registers its kind; likewise, it does not create an executable unprefixed tactic:

```lean
script_recorder
"finish" proof:term : tactic => do
  ProofScript.recordStep "finish" [] [] []
    [("proof", ProofScript.ParamRaw.one proof.raw)] do
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $proof:term))
```

Defining script tactics in the style of `macro_rules` / `elab_rules` is not currently supported.

### Exporting Proof Trees

To export a theorem or lemma, simply use `#theorem` or `#lemma`. In page JSON, they use the tags `"theorem"` and `"lemma"`, respectively.
Proof-Script stores this data under `.../.Proof-Script/proofs/`, where `.../` represents the root of the Lean project.
At the top level, every proof tree contains `schemaVersion`, the complete Lean source in `code`, and the step array `proof`.

Within `:= script`, use unprefixed DSL names directly; the framework automatically adds the `script_` prefix and checks and records every step. `:= by` accepts ordinary Lean tactics but cannot use Proof-Script's script tactics. The latter retains only `schemaVersion` and the complete `code`, and does not output `expressions` or `proof`. Both modes collect references automatically.

## ProofText

`#text` accepts a Lean string literal and parses it as ProofText, a dedicated lightweight markup language with syntax broadly similar to Typst.

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

### Block-Level Structures

- Level 1 through 4 headings: `= TITLE` / ... / `==== TITLE` at the start of a line, where `TITLE` is the heading text
- Headings with custom labels: `== TITLE <label>`, where `label` is the label name
- Ordinary paragraphs
- Unordered lists: introduced by `-` at the start of a line
- Ordered lists: introduced by `+` at the start of a line
- Ordered lists with forced numbering: introduced by `n.` at the start of a line, where `n` is any natural number
- Block quotes: introduced by `>` at the start of a line
- Display formulas: enclosed by `$$` lines
- Full code blocks: enclosed by <code>```</code>, with optional language annotations

### Inline Structures

| Syntax | Meaning |
| --- | --- |
| `*text*` | Bold |
| `_text_` | Emphasis |
| `*_text_*` | Bold emphasis |
| `~~text~~` | Strikethrough |
| `__text__` | Underline |
| `==text==` | Highlight |
| `x^2^` | Superscript |
| `a~n~` | Subscript |
| `` `code` `` | Inline code |
| `$x + y$` | Inline math |
| `[text](url)` | Link |
| `@<label>` | Heading reference |
| `@thm:label` | Theorem reference |
| `@fig:label` | Image or LaTeX component reference |

Proof-Script exports both the ProofText source and the parsed semantic AST to the page JSON file. See the following documentation:

- [ProofText syntax in Chinese](docs/ProofText-Syntax-zh.md)
- [ProofText English syntax](docs/ProofText-Syntax.md)

## Automatic Reference Management

### Registering Publication Information

`project_info` registers global metadata for the current project or paper and persists it in the `.olean` environment.

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

### Registering Theorem Information

Both ordinary Lean theorems and `#theorem` declarations can have theorem metadata attached:

```lean
@[theorem_info (
  name := "Displayed theorem name",
  label := "theorem-label",
  tags := "algebra, foundational",
  customField := "custom value"
)]
theorem referencedTheorem (P : Prop) (h : P) : P := h
```

You can also use the command form after the declaration. Its configuration uses braces, as in `project_info`:

```lean
theorem_info referencedTheorem {
  name := "Displayed theorem name",
  label := "theorem-label",
  tags := "algebra, foundational"
}
```

The standard fields are `name`, `label`, and `tags`; unknown fields are placed in `extra`. To remain compatible with the JSON Schema, public labels should match:

```text
[A-Za-z][A-Za-z0-9_-]*
```

### Automatic Reference Collection

When `#theorem` records expression arguments, Proof-Script automatically traverses the theorem constants used in them. If those theorems carry `theorem_info`, they are added to the current page's staging area without duplication, so the order of first occurrence is always preserved.

The following command locally disables automatic reference collection:

```lean
set_option proofScript.references.enabled false in
@theorem noReferences (P : Prop) (h : P) : P := script
  assumption
```

At any point on a page, use the `#references` command to output all reference information in the current staging area as a page component. This operation clears the reference staging area. The command does not accept a filename and does not write a separate references JSON file.

## Other Page Components

### Arbitrary LaTeX

`#latex` accepts arbitrary LaTeX source and generates SVG at compile time. `title` is required, `label` is optional, and other fields are stored in the metadata's `extra`:

```lean
#latex (
  title := "Commutative Diagram",
  label := "commutative-diagram"
) r#"
\begin{tikzpicture}
  \draw[->] (0,0) -- (1,0);
\end{tikzpicture}
"#
```

### Image Assets

`#figure` accepts a relative image asset path that includes a file extension. Proof-Script exports only the path and extension; it does not read or copy the file:

```lean
#figure (
  title := "Architecture Diagram",
  label := "architecture",
  width := "wide"
) "assets/architecture.png"
```

### Custom Page Components

Extension modules can call `ProofScript.Extension.addCustomComponent` to register open-ended JSON components. For embedded computation, prefer the built-in `#computation`: it accepts component metadata, a downstream renderer ID, a Lean function declaration, and a renderer-specific JSON manifest:

```lean
def chooseOffset (large : Bool) : Nat := if large then 128 else 112

#computation
  (title := "Finite Computation", label := "finite-computation")
  "my-renderer/table-v1"
  chooseOffset
  r#"{"execution":{"backend":"table"},"results":[112,128]}"#
```

The output includes the declaration's full name, readable type, function body, and a structured Lean expression table. These fields are source information and intermediate artifacts; they do not promise a browser ABI for Lean compiler internals. Actual execution is jointly determined by the versioned renderer ID and manifest. See `docs/Embedded-Computation-Renderer-zh.md` for details.

The computation entry point must have the form `α → β` or `α → Except String β`, with `Lean.FromJson α` and `Lean.ToJson β` instances available. The command generates a `String → String` wrapper and a pending build manifest; the actual Wasm resource is generated by a later bundler stage.

After generating pending manifests, run the following from the project root:

```bash
source "$HOME/Developer/emsdk/emsdk_env.sh"
PROOF_SCRIPT_LEAN_WASM_PREFIX=/path/to/lean-wasm-prefix \
  node /path/to/Proof-Script/scripts/build-computations.mjs
```

This command generates a multi-entry bundle for each module under `.Proof-Script/computations/bundles/`. Page resource backfilling is completed by the finalize stage:

```bash
node /path/to/Proof-Script/scripts/finalize-computations.mjs
```

Finalization publishes resources to a content-addressed directory and updates page execution to `ready`. For the frontend implementation, see `docs/Frontend-Computation-Handoff-zh.md`.

For SpherePaper's new E8 interactive computation design, see `docs/E8-Embedded-Computation-Design-zh.md`.

Frontend renderers can use the Fibonacci example in `docs/Embedded-Computation-Quickstart-zh.md` for an initial end-to-end test.

## Page Export

`#page_end` is the final export command. Any page component after this command is ignored.

## Requirements

### Required Environment

A complete installation of Lean + Lake + Elan.

### Optional LaTeX Environment

To use the `#latex` page component, the following commands must also be available on the system `PATH`:

```bash
latex --version
dvisvgm --version
```

## Current Limitations

- `script` permits only registered tactics with the `script_` prefix; it does not support arbitrary Lean tactics or `·` bullets.
- The automatic recorder supports only a limited set of parser argument forms; complex tactics require a handwritten `script_recorder`.
- `complete_induction` is currently a strong-induction template for natural numbers.
- Automatic references scan only expressions touched by the recorder and collect only declarations with registered `theorem_info` metadata; this is not complete dependency analysis.
- ProofText references are checked only for syntax during elaboration; the referenced target is not guaranteed to exist. Cross-page indexes should be built by downstream consumers.
- ProofText is a small, specialized language and does not provide the full capabilities of Markdown or Typst.
- Pages follow a single-module, single-export model; components after `#page_end` produce a warning and are ignored.
- LaTeX components require local `latex`, `dvisvgm`, and the relevant TeX packages; compilation failures interrupt Lean elaboration.
- Page source paths are currently usually absolute; source locations use UTF-8 byte offsets.
- Lean expression JSON is tightly coupled to Lean's internal AST and remains an extensible interface; use it with care across Lean versions.
- The current serialization of universe-level `max`/`imax` has a duplicate-key issue; do not rely on its left and right operands being fully distinguishable.

## Related Documentation

- [Chinese README](README-zh.md)
- [ProofText syntax in Chinese](docs/ProofText-Syntax-zh.md)
- [ProofText English syntax](docs/ProofText-Syntax.md)
- [JSON format documentation in Chinese](docs/JSON-Schemas-zh.md)
- [JSON format documentation](docs/JSON-Schemas.md)
- [Page JSON Schema](docs/schema/page.schema.json)
- [Proof tree JSON Schema](docs/schema/proof.schema.json)
