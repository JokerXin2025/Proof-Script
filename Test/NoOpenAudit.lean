import ProofScript

/- This audit fixture relies on the old unrestricted `provide` recording behavior.

project_info {
  title := "No Open Audit"
}

@[theorem_info]
theorem noOpenBase (P : Prop) (h : P) : P := h

script_macro
"audit_provide" proof:term : tactic => `(tactic| exact $proof:term)

script_macro
"audit_remark" text:str : tactic => `(tactic| skip)

#theorem noOpenScript (P : Prop) (h : P) : P := script
  audit_remark "no open"
  audit_provide h

theorem noOpenEmbed (P : Prop) (h : P) : P := script
  embed (noOpenBase P h) as h'
  apply_h h'

namespace Client

script_macro
"client_provide" proof:term : tactic => `(tactic| exact $proof:term)

script_elab
"client_assumption" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| assumption))

#theorem namespacedNoOpen (P : Prop) (h : P) : P := script
  client_assumption

#theorem noOpenBranch (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := script
  split_and
  | left => apply_h hP
  | right => apply_h hQ

#theorem noOpenCalc (n : Nat) : n = n := script
  calc
    n = n := rfl

#theorem noOpenInfer (P : Prop) (hP : P) : P := script
  infer
    P => P := hP

theorem noOpenCause : True := script
  cause "audit"

end Client
-/
