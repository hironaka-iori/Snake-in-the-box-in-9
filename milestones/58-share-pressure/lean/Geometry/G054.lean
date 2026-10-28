import ForcedShareBridge

namespace Snake9.LocalWindow.ForcedShare58.G054
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 24]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 2]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 21, 23, 25, 30, 31, 33, 35, 39, 45, 47, 60, 61, 65, 67, 71, 77, 79, 92, 93, 129, 131, 135, 141, 143, 156, 157, 257, 259, 263, 269, 271, 284, 285]
def C : List Nat := [7, 15, 13, 29, 28]

theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 4 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel

theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 8 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+3)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP

#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end Snake9.LocalWindow.ForcedShare58.G054
