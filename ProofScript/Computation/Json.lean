module

public import Lean.Data.Json

open Lean

public section

namespace ProofScript.Computation

structure ErrorBody where
  code : String
  message : String
deriving ToJson

private def success (value : Json) : Json :=
  Json.mkObj [("ok", true), ("value", value)]

private def failure (code message : String) : Json :=
  Json.mkObj [("ok", false), ("error", toJson ({ code, message } : ErrorBody))]

/-- Executes a typed pure function behind the `proof-script-json-v1` string ABI. -/
def invokeJson [FromJson α] [ToJson β]
    (f : α → Except String β) (input : String) : String :=
  let result := do
    let json ← Json.parse input |>.mapError fun error => failure "invalid-json" error
    let request ← fromJson? json |>.mapError fun error => failure "invalid-input" error
    let response ← f request |>.mapError fun error => failure "computation-error" error
    return success (toJson response)
  Json.compress <| match result with
    | .ok response => response
    | .error error => error

end ProofScript.Computation
