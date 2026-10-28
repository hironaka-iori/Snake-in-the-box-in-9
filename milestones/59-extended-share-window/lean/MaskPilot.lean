import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59.MaskPilot
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 6, 14, 12, 13, 29, 31]
def D : List Nat := [2, 4, 5, 8, 9, 10, 11, 15, 17, 19, 21, 22, 23, 25, 28, 30, 33, 35, 38, 39, 44, 45, 46, 61, 65, 67, 70, 71, 76, 77, 78, 93, 129, 131, 134, 135, 140, 141, 142, 157, 257, 259, 262, 263, 268, 269, 270, 285]
def C : List Nat := [6, 14, 12, 13, 29]
def mask : Nat := 62168747932007968537249441206973745867391071697185125725666631108441409366116501458740
theorem checked : maskCheck mask D = true := by decide +kernel
theorem credit : 7 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
#print axioms checked
#print axioms credit
def ds : List Nat := [0, 1, 2, 0, 3, 1, 0, 4, 1]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+9≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=7) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported checked credit p P r hr hP
#print axioms in_snake
end Snake9.LocalWindow.ExtendedShare59.MaskPilot
