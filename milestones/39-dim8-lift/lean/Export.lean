import CubeCnf
/-! `lean --run Export.lean c L Ahex k out.cnf`: writes `cubeCnf c L A k` as DIMACS. -/
open Dim8Lift.Cube

def hexVal (s : String) : Nat := s.foldl (fun n ch =>
  16 * n + (if ch.isDigit then ch.toNat - 48 else ch.toLower.toNat - 87)) 0

def main (args : List String) : IO Unit := do
  let c := args[0]!.toNat!; let L := args[1]!.toNat!; let A := hexVal args[2]!; let k := args[3]!.toNat!
  let f := if args.length > 5 then (if args[5]! == "c4" then cubeCnfC4 c L A k else cubeCnfNoCyc c L A k) else cubeCnf c L A k
  let nv := f.foldl (fun m cl => cl.foldl (fun m l => max m l.natAbs) m) 0
  let h ← IO.FS.Handle.mk args[4]! .write
  h.putStrLn s!"p cnf {nv} {f.length}"
  for cl in f do
    h.putStrLn (String.intercalate " " (cl.map toString) ++ " 0")
