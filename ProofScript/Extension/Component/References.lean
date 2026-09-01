import ProofScript.References.State
import ProofScript.Extension.Component.Core

open Lean
open ProofScript


private def referencesJson (refs : List Reference) : Json :=
  Json.arr <| refs.toArray.map fun reference =>
    Json.mkObj [
      ("name", Json.str reference.name.toString),
      ("info", toJson reference.info)
    ]

elab "@""references" : command => do
  let refs ← getTheoremRefs
  let refsJson := referencesJson refs
  let ref ← getRef
  Extension.addPageComponent ref "references" refsJson
  clearTheoremRefs
