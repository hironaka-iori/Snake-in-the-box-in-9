import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E007
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 25, 57, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 1, 5, 0]
def C : List Nat := [30, 26, 27, 25, 57]
def D0 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 29, 31, 33, 35, 38, 39, 41, 46, 49, 58, 59, 61, 62, 65, 67, 70, 71, 78, 89, 90, 91, 94, 121, 129, 131, 134, 135, 142, 153, 154, 155, 158, 185, 257, 259, 262, 263, 270, 281, 282, 283, 286, 313]
def D1 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 16, 17, 18, 19, 22, 23, 24, 28, 29, 31, 32, 33, 35, 38, 39, 41, 46, 49, 58, 59, 61, 62, 64, 65, 67, 70, 71, 78, 89, 90, 91, 94, 121, 128, 129, 131, 134, 135, 142, 153, 154, 155, 158, 185, 256, 257, 259, 262, 263, 270, 281, 282, 283, 286, 313]
def mask0 : Nat := 16687398869662204139910064737584949975974497754411752914761532327607678099136777380569809854260
def mask1 : Nat := 16687398869662204255702153974901145399545482763099660768371799360169180602076182739992712289844
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (8::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (8::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 11 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 11 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    11 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=8) (mask0:=mask0) (mask1:=mask1) (L:=11) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E007
