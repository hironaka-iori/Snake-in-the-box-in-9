import ForcedShareBridge

namespace Snake9.LocalWindow.ForcedShare58.G027
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 20]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 3]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 60, 65, 67, 71, 76, 78, 79, 92, 129, 131, 135, 140, 142, 143, 156, 257, 259, 263, 268, 270, 271, 284]
def C : List Nat := [7, 15, 14, 12, 28]

theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 5 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel

theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 8 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+3)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP

#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end Snake9.LocalWindow.ForcedShare58.G027
