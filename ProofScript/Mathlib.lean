import ProofScript
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Field
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.ITauto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.WLOG
import Mathlib.Tactic.Zify

/-!
# Proof-Script Mathlib tactic extension

This module is intentionally not imported by the core `ProofScript` module and is not included in
the default Lake targets. A downstream project with Mathlib installed may import it explicitly.

The wrappers deliberately use only basic syntax categories supported by automatic script
recording. Lists inside brackets are whitespace-separated in Proof-Script and are forwarded to
Mathlib as comma-separated lists.
-/

/-! ## Mathlib Native Tactics -/

script_macro
"continuity" : tactic => `(tactic| continuity)

script_macro
"exact_mod_cast" proof:term : tactic => `(tactic| exact_mod_cast $proof:term)

script_macro
"field" : tactic => `(tactic| field)

script_macro
"field" "[" lemmas:(colGt term)+ "]" : tactic => `(tactic| field [$[$lemmas:term],*])

script_macro
"gcongr" : tactic => `(tactic| gcongr)

script_macro
"gcongr" template:term : tactic => `(tactic| gcongr $template:term)

script_macro (intro := [names])
"gcongr" "with" names:(colGt ident)+ : tactic => `(tactic| gcongr with $names*)

script_macro (intro := [names])
"gcongr" template:term "with" names:(colGt ident)+ : tactic =>
  `(tactic| gcongr $template:term with $names*)

script_macro
"itauto" : tactic => `(tactic| itauto)

script_macro
"itauto" "*" : tactic => `(tactic| itauto *)

script_macro
"itauto" "[" propositions:(colGt term)+ "]" : tactic =>
  `(tactic| itauto [$[$propositions:term],*])

script_macro
"itauto!" : tactic => `(tactic| itauto!)

script_macro
"itauto!" "*" : tactic => `(tactic| itauto! *)

script_macro
"itauto!" "[" propositions:(colGt term)+ "]" : tactic =>
  `(tactic| itauto! [$[$propositions:term],*])

script_macro
"linarith" : tactic => `(tactic| linarith)

script_macro
"linarith" "[" facts:(colGt term)+ "]" : tactic => `(tactic| linarith [$[$facts:term],*])

script_macro
"linarith" "only" : tactic => `(tactic| linarith only)

script_macro
"linarith" "only" "[" facts:(colGt term)+ "]" : tactic =>
  `(tactic| linarith only [$[$facts:term],*])

script_macro
"linarith!" : tactic => `(tactic| linarith!)

script_macro
"linarith!" "[" facts:(colGt term)+ "]" : tactic => `(tactic| linarith! [$[$facts:term],*])

script_macro
"linarith!" "only" : tactic => `(tactic| linarith! only)

script_macro
"linarith!" "only" "[" facts:(colGt term)+ "]" : tactic =>
  `(tactic| linarith! only [$[$facts:term],*])

script_macro
"measurability" : tactic => `(tactic| measurability)

script_macro
"nlinarith" : tactic => `(tactic| nlinarith)

script_macro
"nlinarith" "[" facts:(colGt term)+ "]" : tactic => `(tactic| nlinarith [$[$facts:term],*])

script_macro
"nlinarith" "only" : tactic => `(tactic| nlinarith only)

script_macro
"nlinarith" "only" "[" facts:(colGt term)+ "]" : tactic =>
  `(tactic| nlinarith only [$[$facts:term],*])

script_macro
"nlinarith!" : tactic => `(tactic| nlinarith!)

script_macro
"nlinarith!" "[" facts:(colGt term)+ "]" : tactic =>
  `(tactic| nlinarith! [$[$facts:term],*])

script_macro
"nlinarith!" "only" : tactic => `(tactic| nlinarith! only)

script_macro
"nlinarith!" "only" "[" facts:(colGt term)+ "]" : tactic =>
  `(tactic| nlinarith! only [$[$facts:term],*])

script_macro
"norm_cast" : tactic => `(tactic| norm_cast)

script_macro
"norm_cast" "at" locations:(colGt ident)+ : tactic => `(tactic| norm_cast at $locations*)

script_macro
"norm_cast" "at" "*" : tactic => `(tactic| norm_cast at *)

script_macro
"norm_cast" "at" "⊢" : tactic => `(tactic| norm_cast at ⊢)

script_macro
"norm_cast" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| norm_cast at $locations* ⊢)

script_macro
"norm_num" : tactic => `(tactic| norm_num)

script_macro
"norm_num" "[" lemmas:(colGt term)+ "]" : tactic =>
  `(tactic| norm_num [$[$lemmas:term],*])

script_macro
"norm_num" "only" : tactic => `(tactic| norm_num only)

script_macro
"norm_num" "only" "at" locations:(colGt ident)+ : tactic =>
  `(tactic| norm_num only at $locations*)

script_macro
"norm_num" "only" "at" "*" : tactic => `(tactic| norm_num only at *)

script_macro
"norm_num" "only" "at" "⊢" : tactic => `(tactic| norm_num only at ⊢)

script_macro
"norm_num" "only" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| norm_num only at $locations* ⊢)

script_macro
"norm_num" "only" "[" lemmas:(colGt term)+ "]" : tactic =>
  `(tactic| norm_num only [$[$lemmas:term],*])

script_macro
"norm_num" "at" locations:(colGt ident)+ : tactic => `(tactic| norm_num at $locations*)

script_macro
"norm_num" "at" "*" : tactic => `(tactic| norm_num at *)

script_macro
"norm_num" "at" "⊢" : tactic => `(tactic| norm_num at ⊢)

script_macro
"norm_num" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| norm_num at $locations* ⊢)

script_macro
"norm_num" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ : tactic =>
  `(tactic| norm_num [$[$lemmas:term],*] at $locations*)

script_macro
"norm_num" "[" lemmas:(colGt term)+ "]" "at" "*" : tactic =>
  `(tactic| norm_num [$[$lemmas:term],*] at *)

script_macro
"norm_num" "[" lemmas:(colGt term)+ "]" "at" "⊢" : tactic =>
  `(tactic| norm_num [$[$lemmas:term],*] at ⊢)

script_macro
"norm_num" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| norm_num [$[$lemmas:term],*] at $locations* ⊢)

script_macro
"norm_num" "only" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ : tactic =>
  `(tactic| norm_num only [$[$lemmas:term],*] at $locations*)

script_macro
"norm_num" "only" "[" lemmas:(colGt term)+ "]" "at" "*" : tactic =>
  `(tactic| norm_num only [$[$lemmas:term],*] at *)

script_macro
"norm_num" "only" "[" lemmas:(colGt term)+ "]" "at" "⊢" : tactic =>
  `(tactic| norm_num only [$[$lemmas:term],*] at ⊢)

script_macro
"norm_num" "only" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| norm_num only [$[$lemmas:term],*] at $locations* ⊢)

script_macro
"positivity" : tactic => `(tactic| positivity)

script_macro
"positivity" "[" facts:(colGt term)+ "]" : tactic =>
  `(tactic| positivity [$[$facts:term],*])

script_macro
"push_cast" : tactic => `(tactic| push_cast)

script_macro
"push_cast" "[" lemmas:(colGt term)+ "]" : tactic =>
  `(tactic| push_cast [$[$lemmas:term],*])

script_macro
"push_cast" "only" : tactic => `(tactic| push_cast only)

script_macro
"push_cast" "only" "at" locations:(colGt ident)+ : tactic =>
  `(tactic| push_cast only at $locations*)

script_macro
"push_cast" "only" "at" "*" : tactic => `(tactic| push_cast only at *)

script_macro
"push_cast" "only" "at" "⊢" : tactic => `(tactic| push_cast only at ⊢)

script_macro
"push_cast" "only" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| push_cast only at $locations* ⊢)

script_macro
"push_cast" "only" "[" lemmas:(colGt term)+ "]" : tactic =>
  `(tactic| push_cast only [$[$lemmas:term],*])

script_macro
"push_cast" "at" locations:(colGt ident)+ : tactic => `(tactic| push_cast at $locations*)

script_macro
"push_cast" "at" "*" : tactic => `(tactic| push_cast at *)

script_macro
"push_cast" "at" "⊢" : tactic => `(tactic| push_cast at ⊢)

script_macro
"push_cast" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| push_cast at $locations* ⊢)

script_macro
"push_cast" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ : tactic =>
  `(tactic| push_cast [$[$lemmas:term],*] at $locations*)

script_macro
"push_cast" "[" lemmas:(colGt term)+ "]" "at" "*" : tactic =>
  `(tactic| push_cast [$[$lemmas:term],*] at *)

script_macro
"push_cast" "[" lemmas:(colGt term)+ "]" "at" "⊢" : tactic =>
  `(tactic| push_cast [$[$lemmas:term],*] at ⊢)

script_macro
"push_cast" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| push_cast [$[$lemmas:term],*] at $locations* ⊢)

script_macro
"push_cast" "only" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ : tactic =>
  `(tactic| push_cast only [$[$lemmas:term],*] at $locations*)

script_macro
"push_cast" "only" "[" lemmas:(colGt term)+ "]" "at" "*" : tactic =>
  `(tactic| push_cast only [$[$lemmas:term],*] at *)

script_macro
"push_cast" "only" "[" lemmas:(colGt term)+ "]" "at" "⊢" : tactic =>
  `(tactic| push_cast only [$[$lemmas:term],*] at ⊢)

script_macro
"push_cast" "only" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| push_cast only [$[$lemmas:term],*] at $locations* ⊢)

script_macro
"qify" : tactic => `(tactic| qify)

script_macro
"qify" "[" lemmas:(colGt term)+ "]" : tactic => `(tactic| qify [$[$lemmas:term],*])

script_macro
"qify" "at" locations:(colGt ident)+ : tactic => `(tactic| qify at $locations*)

script_macro
"qify" "at" "*" : tactic => `(tactic| qify at *)

script_macro
"qify" "at" "⊢" : tactic => `(tactic| qify at ⊢)

script_macro
"qify" "at" locations:(colGt ident)+ "⊢" : tactic => `(tactic| qify at $locations* ⊢)

script_macro
"qify" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ : tactic =>
  `(tactic| qify [$[$lemmas:term],*] at $locations*)

script_macro
"qify" "[" lemmas:(colGt term)+ "]" "at" "*" : tactic =>
  `(tactic| qify [$[$lemmas:term],*] at *)

script_macro
"qify" "[" lemmas:(colGt term)+ "]" "at" "⊢" : tactic =>
  `(tactic| qify [$[$lemmas:term],*] at ⊢)

script_macro
"qify" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| qify [$[$lemmas:term],*] at $locations* ⊢)

script_macro
"rify" : tactic => `(tactic| rify)

script_macro
"rify" "[" lemmas:(colGt term)+ "]" : tactic => `(tactic| rify [$[$lemmas:term],*])

script_macro
"rify" "at" locations:(colGt ident)+ : tactic => `(tactic| rify at $locations*)

script_macro
"rify" "at" "*" : tactic => `(tactic| rify at *)

script_macro
"rify" "at" "⊢" : tactic => `(tactic| rify at ⊢)

script_macro
"rify" "at" locations:(colGt ident)+ "⊢" : tactic => `(tactic| rify at $locations* ⊢)

script_macro
"rify" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ : tactic =>
  `(tactic| rify [$[$lemmas:term],*] at $locations*)

script_macro
"rify" "[" lemmas:(colGt term)+ "]" "at" "*" : tactic =>
  `(tactic| rify [$[$lemmas:term],*] at *)

script_macro
"rify" "[" lemmas:(colGt term)+ "]" "at" "⊢" : tactic =>
  `(tactic| rify [$[$lemmas:term],*] at ⊢)

script_macro
"rify" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| rify [$[$lemmas:term],*] at $locations* ⊢)

script_macro
"ring" : tactic => `(tactic| ring)

script_macro
"ring!" : tactic => `(tactic| ring!)

script_macro
"ring_nf" : tactic => `(tactic| ring_nf)

script_macro
"ring_nf" "at" locations:(colGt ident)+ : tactic => `(tactic| ring_nf at $locations*)

script_macro
"ring_nf" "at" "*" : tactic => `(tactic| ring_nf at *)

script_macro
"ring_nf" "at" "⊢" : tactic => `(tactic| ring_nf at ⊢)

script_macro
"ring_nf" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| ring_nf at $locations* ⊢)

script_macro
"ring_nf!" : tactic => `(tactic| ring_nf!)

script_macro
"ring_nf!" "at" locations:(colGt ident)+ : tactic => `(tactic| ring_nf! at $locations*)

script_macro
"ring_nf!" "at" "*" : tactic => `(tactic| ring_nf! at *)

script_macro
"ring_nf!" "at" "⊢" : tactic => `(tactic| ring_nf! at ⊢)

script_macro
"ring_nf!" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| ring_nf! at $locations* ⊢)

script_macro
"tauto" : tactic => `(tactic| tauto)

script_macro (intro := [h])
"wlog" h:ident ":" proposition:term : tactic => `(tactic| wlog $h:ident : $proposition:term)

script_macro (intro := [h])
"wlog" h:ident ":" proposition:term "generalizing" variables:(colGt ident)+ : tactic =>
  `(tactic| wlog $h:ident : $proposition:term generalizing $variables*)

script_macro (intro := [h, hypothesis])
"wlog" h:ident ":" proposition:term "with" hypothesis:ident : tactic =>
  `(tactic| wlog $h:ident : $proposition:term with $hypothesis:ident)

script_macro (intro := [h, hypothesis])
"wlog" h:ident ":" proposition:term "generalizing" variables:(colGt ident)+
    "with" hypothesis:ident : tactic =>
  `(tactic| wlog $h:ident : $proposition:term generalizing $variables* with $hypothesis:ident)

script_macro (intro := [h])
"wlog!" h:ident ":" proposition:term : tactic => `(tactic| wlog! $h:ident : $proposition:term)

script_macro (intro := [h])
"wlog!" h:ident ":" proposition:term "generalizing" variables:(colGt ident)+ : tactic =>
  `(tactic| wlog! $h:ident : $proposition:term generalizing $variables*)

script_macro (intro := [h, hypothesis])
"wlog!" h:ident ":" proposition:term "with" hypothesis:ident : tactic =>
  `(tactic| wlog! $h:ident : $proposition:term with $hypothesis:ident)

script_macro (intro := [h, hypothesis])
"wlog!" h:ident ":" proposition:term "generalizing" variables:(colGt ident)+
    "with" hypothesis:ident : tactic =>
  `(tactic| wlog! $h:ident : $proposition:term generalizing $variables* with $hypothesis:ident)

script_macro
"zify" : tactic => `(tactic| zify)

script_macro
"zify" "[" lemmas:(colGt term)+ "]" : tactic => `(tactic| zify [$[$lemmas:term],*])

script_macro
"zify" "at" locations:(colGt ident)+ : tactic => `(tactic| zify at $locations*)

script_macro
"zify" "at" "*" : tactic => `(tactic| zify at *)

script_macro
"zify" "at" "⊢" : tactic => `(tactic| zify at ⊢)

script_macro
"zify" "at" locations:(colGt ident)+ "⊢" : tactic => `(tactic| zify at $locations* ⊢)

script_macro
"zify" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ : tactic =>
  `(tactic| zify [$[$lemmas:term],*] at $locations*)

script_macro
"zify" "[" lemmas:(colGt term)+ "]" "at" "*" : tactic =>
  `(tactic| zify [$[$lemmas:term],*] at *)

script_macro
"zify" "[" lemmas:(colGt term)+ "]" "at" "⊢" : tactic =>
  `(tactic| zify [$[$lemmas:term],*] at ⊢)

script_macro
"zify" "[" lemmas:(colGt term)+ "]" "at" locations:(colGt ident)+ "⊢" : tactic =>
  `(tactic| zify [$[$lemmas:term],*] at $locations* ⊢)
