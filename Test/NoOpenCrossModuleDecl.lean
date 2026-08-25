import ProofScript

namespace AuditLibrary

script_macro
"cross_audit_provide" proof:term : tactic => `(tactic| exact $proof:term)

#theorem crossAuditBase (P : Prop) (h : P) : P := script
  cross_audit_provide h

end AuditLibrary
