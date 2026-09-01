import ProofScript

@theorem embeddedResult : True := script
  trivial

@theorem usesEmbeddedResult : True := script
  embed embeddedResult as h
  trivial
