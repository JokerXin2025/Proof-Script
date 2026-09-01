import Test.EmbedResourceDecl

@theorem usesCrossModuleEmbeddedResult : True := script
  embed crossModuleEmbeddedResult as h
  trivial
