import SplitShare
namespace Snake9.LocalWindow.SplitShare62.E21
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 18, 50]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 2, 5]
def C : List Nat := [15, 14, 30, 22, 18]
def D0 : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 16, 17, 19, 20, 23, 26, 28, 31, 33, 35, 39, 46, 47, 54, 62, 65, 67, 71, 78, 79, 82, 86, 94, 129, 131, 135, 142, 143, 146, 150, 158, 257, 259, 263, 270, 271, 274, 278, 286]
def D1 : List Nat := [2, 5, 6, 8, 9, 10, 11, 12, 13, 16, 17, 19, 20, 23, 26, 28, 31, 32, 33, 35, 39, 46, 47, 54, 62, 64, 65, 67, 71, 78, 79, 82, 86, 94, 128, 129, 131, 135, 142, 143, 146, 150, 158, 256, 257, 259, 263, 270, 271, 274, 278, 286]
def mask0 : Nat := 124852537919022627138580971919556285462035923326028414688851311662527477081846895558260
def mask1 : Nat := 124852538034814716375897167343127270470723831179638681721412814165466882441269797928804
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (4::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (4::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 7 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 7 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=4) (mask0:=mask0) (mask1:=mask1) (L:=7) (start:=4)
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
end Snake9.LocalWindow.SplitShare62.E21
