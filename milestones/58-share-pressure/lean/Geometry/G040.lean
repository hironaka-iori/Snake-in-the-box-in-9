import ForcedShareBridge

namespace Snake9.LocalWindow.ForcedShare58.G040
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 58]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 5]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 22, 23, 24, 27, 28, 31, 33, 35, 39, 46, 47, 62, 65, 67, 71, 78, 79, 90, 94, 129, 131, 135, 142, 143, 154, 158, 257, 259, 263, 270, 271, 282, 286]
def C : List Nat := [7, 15, 14, 30, 26]

theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 18 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel

theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 8 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    18 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+3)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP

#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end Snake9.LocalWindow.ForcedShare58.G040
