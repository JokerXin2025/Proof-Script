import ProofScript
import Mathlib.Tactic.Field
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Proof-Script Mathlib tactic extension

This module is intentionally not imported by the core `ProofScript` module and is not included in
the default Lake targets. A downstream project with Mathlib installed may import it explicitly.

The wrappers expose one deliberately narrow, stable syntax for each tactic. More permissive
Mathlib variants are left to ordinary Lean proofs until they have a separate Proof-Script semantic
representation.
-/


/-! ## Mathlib Native Tactics -/

script_macro
"field" : tactic => `(tactic| field)

script_macro
"gcongr" : tactic => `(tactic| gcongr)

script_macro
"linarith" : tactic => `(tactic| linarith)

script_macro
"nlinarith" : tactic => `(tactic| nlinarith)

script_macro
"norm_num" : tactic => `(tactic| norm_num)

script_macro
"positivity" : tactic => `(tactic| positivity)

script_macro
"ring" : tactic => `(tactic| ring)

script_macro
"ring_nf" : tactic => `(tactic| ring_nf)

script_macro
"tauto" : tactic => `(tactic| tauto)
