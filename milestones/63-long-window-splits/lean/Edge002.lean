import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E002
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 27, 59, 57, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 2, 5, 1, 0]
def C : List Nat := [30, 31, 27, 59, 57]
def D0 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 25, 26, 28, 29, 33, 35, 38, 39, 41, 43, 46, 49, 51, 58, 61, 62, 63, 65, 67, 70, 71, 78, 91, 94, 95, 121, 123, 129, 131, 134, 135, 142, 155, 158, 159, 185, 187, 257, 259, 262, 263, 270, 283, 286, 287, 313, 315]
def D1 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 25, 26, 28, 29, 33, 35, 38, 39, 40, 41, 43, 46, 48, 49, 51, 58, 60, 61, 62, 63, 65, 67, 70, 71, 78, 91, 94, 95, 120, 121, 123, 129, 131, 134, 135, 142, 155, 158, 159, 184, 185, 187, 257, 259, 262, 263, 270, 283, 286, 287, 312, 313, 315]
def mask0 : Nat := 83436993979196249066293439707557806189974480118358116987888614830208878144712753324762170302004
def mask1 : Nat := 91780693338262304075648993247282619137665814587467646092229308891194613811355337310383662341684
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (24::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (24::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 28 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 28 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    28 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=24) (mask0:=mask0) (mask1:=mask1) (L:=28) (start:=6)
    canonical (by decide) (by decide) rfl forced0 forced1 supported
    checked_mask0 checked_mask1 credit0 credit1 p P r hr hP
#print axioms canonical
#print axioms forced0
#print axioms forced1
#print axioms supported
#print axioms checked_mask0
#print axioms checked_mask1
#print axioms credit0
#print axioms credit1
#print axioms in_snake
end Snake9.LocalWindow.LongWindow63.E002
