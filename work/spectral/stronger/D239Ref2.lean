import WinG1Gen
/-! Packaged refutation of a two-centre window (`0,1,3,7`, centres `1, 3`), next to
`WinG1.Refuted3/4`. -/
namespace D239
open WinCNF W223G1 WinG1

/-- A checked, refuted window CNF with window `0,1,3,7` and centre ranges at `1, 3`. -/
def Refuted2 (lo1 hi1 lo2 hi2 : Nat) : Prop :=
  ∃ (T : Tables) (F : CNF), unsat F ∧ blocksOK T = true ∧ F.all (check T) = true ∧
    tabOK T [(cornerVerts 1 0 1, lo1, hi1), (cornerVerts 3 1 2, lo2, hi2)] = true ∧
    T.window = [0, 1, 3, 7]

end D239
