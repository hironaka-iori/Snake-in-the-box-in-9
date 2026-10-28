import ForcedShareBridge

namespace Snake9.LocalWindow.ForcedShare58.G120
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 43]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 51, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 123, 127, 129, 131, 135, 143, 159, 187, 191, 257, 259, 263, 271, 287, 315, 319]
def C : List Nat := [7, 15, 31, 63, 59]

theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 12 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel

theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 8 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    12 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+3)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP

#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end Snake9.LocalWindow.ForcedShare58.G120
