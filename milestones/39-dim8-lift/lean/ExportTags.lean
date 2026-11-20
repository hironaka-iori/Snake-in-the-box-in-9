import Prov
/-! `lean --run ExportTags.lean c L Ahex k out`: every tag with its clause, one per line: `t0 t1 ... | l1 l2 ...` -/
open Dim8Lift.Prov
def hexVal (s : String) : Nat := s.foldl (fun n ch => 16 * n + (if ch.isDigit then ch.toNat - 48 else ch.toLower.toNat - 87)) 0
def main (args : List String) : IO Unit := do
  let c := args[0]!.toNat!; let L := args[1]!.toNat!; let A := hexVal args[2]!; let k := args[3]!.toNat!
  let h ← IO.FS.Handle.mk args[4]! .write
  for t in allTags c L k do
    match genQ c L A k t with
    | some cl => h.putStrLn (String.intercalate " " (t.map toString) ++ " | " ++ String.intercalate " " (cl.map toString))
    | none => pure ()
