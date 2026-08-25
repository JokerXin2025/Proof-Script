import ProofScript

theorem readmeImplicationChain
    (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) : P → R := script
  intro_h hP
  infer
    P => Q := hPQ hP
    _ => R := hQR ?_

script_macro (record := false)
"readme_finish" proof:term : tactic => `(tactic| exact $proof:term)

script_recorder
"readme_finish" proof:term : tactic => do
  ProofScript.recordStep "readme_finish" [] [] []
    [("proof", ProofScript.ParamRaw.one proof.raw)] do
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $proof:term))

script_elab (intro := [h])
"readme_intro_named" h:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro $h:ident))

example (P : Prop) (h : P) : P := script
  readme_finish h

example : ∃ n : Nat, n = 0 := script
  witness
  | prep => provide 0
  | proof => trivial
