import GenericWindow
namespace Snake9.LocalWindow.FamilyCharge67
open CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Rejected24
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 49, 48, 16]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 1, 0, 5]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected24
end Snake9.LocalWindow.FamilyCharge67
