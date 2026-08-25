import ProofScript.References.Data


namespace ProofScript


initialize theoremRefsRef : IO.Ref (List Reference) ← IO.mkRef []

def clearTheoremRefs : IO Unit := theoremRefsRef.set []
def getTheoremRefs : IO (List Reference) := theoremRefsRef.get

/-- 按声明名去重后追加，保持首次出现顺序。 -/
def addTheoremRef (ref : Reference)
                  : IO Unit :=
  theoremRefsRef.modify fun cur =>
    if cur.any (fun x => x.name == ref.name) then cur
    else cur ++ [ref]


end ProofScript
