import Lean.Meta

open Lean (CoreM Name Json logWarning)


namespace ProofScript

def proofSchemaVersion := "0.2.0"

initialize JSON_boxes : IO.Ref (Array (Name × Array Json)) ← IO.mkRef #[]

/-- Add JSON objects to the JSON array -/
def addtoBox  (box : Name)
              (json_obj : Json)
              : BaseIO Unit := do
  JSON_boxes.modify fun arr =>
    match arr.findIdx? (fun (b, _) => b == box) with
    | some idx =>
      let (b, items) := arr[idx]!
      arr.set! idx (b, items.push json_obj)
    | none =>
      /- create the JSON array for the first time -/
      arr.push (box, #[json_obj])

/-- Export the JSON box and clear it -/
def exportBoxToFile (boxName : Name)
                     (fileName : System.FilePath)
                     (code : String)
                     : CoreM Unit := do
  let arr ← JSON_boxes.get
  match arr.findIdx? (fun (b, _) => b == boxName) with
  | some idx =>
    let (_, currentData) := arr[idx]!
    if currentData.isEmpty then
      logWarning m! "[Proof-Script] Box '{boxName}' has been dumped."
    else
      if let some parent := fileName.parent then
        IO.FS.createDirAll parent
       let proofJson := Json.mkObj [
         ("schemaVersion", Json.str proofSchemaVersion),
         ("code", Json.str code),
         ("proof", Json.arr currentData)
      ]
      IO.FS.writeFile fileName proofJson.pretty
      JSON_boxes.set (arr.set! idx (boxName, #[]))
  | none =>
    logWarning m! "[Proof-Script] Box '{boxName}' has not been initialized."

end ProofScript
