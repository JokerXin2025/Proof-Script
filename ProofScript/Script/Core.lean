import ProofScript.Script.JsonBox

open Lean (Json)
open Lean.Name (mkSimple)


namespace ProofScript

initialize stepCounter : IO.Ref Nat ← IO.mkRef 0
initialize currentBoxTag : IO.Ref String ← IO.mkRef ""
initialize boxTagStack  : IO.Ref (List String) ← IO.mkRef []
initialize prevStepRef : IO.Ref (Option (String × List (String × Json))) ← IO.mkRef none
/-- Stack of (mainTag, remainingNodes) per active strategy. -/
initialize strategyBranchStack : IO.Ref (List (String × List String)) ← IO.mkRef []

def freshStep : IO Nat := do
  let n ← stepCounter.get
  stepCounter.set (n + 1)
  return n

def pushBoxTag (tag : String) : IO Unit := do
  let stack ← boxTagStack.get
  boxTagStack.set (tag :: stack)
  currentBoxTag.set tag

def popBoxTag : IO Unit := do
  let stack ← boxTagStack.get
  match stack with
  | _ :: rest => boxTagStack.set rest ; match rest with | top :: _ => currentBoxTag.set top | [] => currentBoxTag.set ""
  | [] => pure ()

def getPrevStep : IO (Option (String × List (String × Json))) := prevStepRef.get
def setPrevStep (info : String × List (String × Json)) : IO Unit := prevStepRef.set (some info)

def resetScriptState : IO Unit := do
  stepCounter.set 0
  currentBoxTag.set ""
  boxTagStack.set []
  prevStepRef.set none

/-! ## Strategy branch tracking -/

/-- Start a new strategy -/
def startStrategy (mainTag : String) (nodes : List String) : IO Unit := do
  for node in nodes do
    let nodeTag := mainTag ++ "_" ++ node
    JSON_boxes.modify fun arr =>
      match arr.findIdx? (fun (b, _) => b == mkSimple nodeTag) with
      | some _ => arr
      | none => arr.push (mkSimple nodeTag, #[])
  match nodes with
  | firstNode :: remaining =>
    pushBoxTag (mainTag ++ "_" ++ firstNode)
    let cur ← strategyBranchStack.get
    strategyBranchStack.set ((mainTag, remaining) :: cur)
  | [] => pure ()

/-- Advance to the next branch -/
def advanceStrategyCase : IO Unit := do
  let stack ← strategyBranchStack.get
  match stack with
  | [] => pure ()
  | (mainTag, nodeList) :: rest =>
    popBoxTag
    match nodeList with
    | [] => strategyBranchStack.set rest
    | nextNode :: remaining =>
      pushBoxTag (mainTag ++ "_" ++ nextNode)
      strategyBranchStack.set ((mainTag, remaining) :: rest)

/-- `_next_strategy_case`：它不调用任何 tactic，只推进录制 box 状态，在分支之间自动插入。 -/
elab "_next_strategy_case" : tactic => do
  advanceStrategyCase

end ProofScript
