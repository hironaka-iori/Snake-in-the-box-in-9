import TabAll
import CoverDefs
/-! `lean --run CovExport.lean c5 out.cnf` or `... c6 <r5> out.cnf`: the Lean cover CNFs as DIMACS. -/
open Dim8Lift.Tab

def writeCnf (f : List (List Int)) (path : String) : IO Unit := do
  let nv := f.foldl (fun m cl => cl.foldl (fun m l => max m l.natAbs) m) 0
  let h ← IO.FS.Handle.mk path .write
  h.putStrLn s!"p cnf {nv} {f.length}"
  for cl in f do
    h.putStrLn (String.intercalate " " (cl.map toString) ++ " 0")

def main (args : List String) : IO Unit := do
  if args[0]! == "c5" then
    writeCnf (c5Cnf (t5.map (·.1))) args[1]!
  else if args[0]! == "list5" then
    IO.println (String.intercalate " " (q5reps.map toString))
  else
    let r5 := args[1]!.toNat!
    writeCnf (c6Cnf r5 ((t6.filter (·.1 == r5)).map (·.2.1))) args[2]!
