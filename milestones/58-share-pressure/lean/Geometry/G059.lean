import ForcedShareBridge

namespace Snake9.LocalWindow.ForcedShare58.G059
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 25, 57]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 2, 5]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 24, 27, 28, 31, 33, 35, 39, 45, 47, 61, 65, 67, 71, 77, 79, 89, 93, 129, 131, 135, 141, 143, 153, 157, 257, 259, 263, 269, 271, 281, 285]
def C : List Nat := [7, 15, 13, 29, 25]

theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem credit : 11 ≤
    (C.map (shareLocal 12 (fun x => !D.contains x))).sum := by decide +kernel

theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 8 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    11 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+3)))).sum :=
  credit_in_snake canonical rfl rfl forced supported credit p P r hr hP

#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms credit
#print axioms in_snake
end Snake9.LocalWindow.ForcedShare58.G059
