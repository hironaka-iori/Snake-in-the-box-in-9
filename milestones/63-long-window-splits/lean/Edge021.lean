import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E021
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 62, 63, 59]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 2]
def C : List Nat := [12, 28, 60, 62, 63]
def D0 : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 54, 55, 56, 58, 61, 65, 67, 71, 76, 78, 79, 92, 124, 126, 127, 129, 131, 135, 140, 142, 143, 156, 188, 190, 191, 257, 259, 263, 268, 270, 271, 284, 316, 318, 319]
def D1 : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 27, 29, 30, 31, 33, 35, 39, 43, 44, 46, 47, 52, 54, 55, 56, 57, 58, 61, 65, 67, 71, 76, 78, 79, 92, 123, 124, 126, 127, 129, 131, 135, 140, 142, 143, 156, 187, 188, 190, 191, 257, 259, 263, 268, 270, 271, 284, 315, 316, 318, 319]
def mask0 : Nat := 1735489466716828325898042824759881366389579545893800579817747578785827321202539225414577562464116
def mask1 : Nat := 1802239061589356765972887253077679869971110221646676812652473131273713206535670813539101360926580
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (51::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (51::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 6 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 6 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=51) (mask0:=mask0) (mask1:=mask1) (L:=6) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E021
