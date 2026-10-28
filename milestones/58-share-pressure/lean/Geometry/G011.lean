import ForcedShareBridge

namespace Snake9.LocalWindow.ForcedShare58.G011
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 63]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 5]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 46, 62, 65, 67, 70, 71, 78, 94, 95, 129, 131, 134, 135, 142, 158, 159, 257, 259, 262, 263, 270, 286, 287]
def C : List Nat := [7, 6, 14, 30, 31]

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
end Snake9.LocalWindow.ForcedShare58.G011
