import Test.NoOpenCrossModuleDecl

@theorem crossAuditUse (P : Prop) (h : P) : P := script
  cross_audit_provide h
