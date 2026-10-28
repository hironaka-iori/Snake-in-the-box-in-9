import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E010
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55, 53, 52]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3, 1, 0]
def C : List Nat := [30, 62, 63, 55, 53]
def D0 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 21, 22, 23, 26, 28, 31, 33, 35, 37, 38, 39, 46, 47, 49, 51, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 117, 119, 126, 127, 129, 131, 134, 135, 142, 158, 181, 183, 190, 191, 257, 259, 262, 263, 270, 286, 309, 311, 318, 319]
def D1 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 21, 22, 23, 26, 28, 31, 33, 35, 36, 37, 38, 39, 46, 47, 48, 49, 51, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 116, 117, 119, 126, 127, 129, 131, 134, 135, 142, 158, 180, 181, 183, 190, 191, 257, 259, 262, 263, 270, 286, 308, 309, 311, 318, 319]
def mask0 : Nat := 1607205089164431575807152251254754951434105866235342116812184850652144569011884751200979831660084
def mask1 : Nat := 1607726570374373204245236973350987752243336574639661462381206144030956177491049840906369927650868
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (20::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (20::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 29 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 29 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    29 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=20) (mask0:=mask0) (mask1:=mask1) (L:=29) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E010
