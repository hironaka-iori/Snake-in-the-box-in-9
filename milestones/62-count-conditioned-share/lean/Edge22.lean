import SplitShare
namespace Snake9.LocalWindow.SplitShare62.E22
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3]
def C : List Nat := [15, 14, 30, 62, 63]
def D0 : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 39, 46, 47, 54, 58, 59, 60, 61, 65, 67, 71, 78, 79, 94, 126, 127, 129, 131, 135, 142, 143, 158, 190, 191, 257, 259, 263, 270, 271, 286, 318, 319]
def D1 : List Nat := [2, 5, 6, 8, 9, 10, 11, 12, 13, 16, 17, 19, 22, 23, 26, 28, 31, 32, 33, 35, 39, 46, 47, 54, 58, 59, 60, 61, 64, 65, 67, 71, 78, 79, 94, 126, 127, 128, 129, 131, 135, 142, 143, 158, 190, 191, 256, 257, 259, 263, 270, 271, 286, 318, 319]
def mask0 : Nat := 1601990277065019078290791447481282075807292506321487105592144949755406340350546728573490243976820
def mask1 : Nat := 1601990277065019078406583536718598271230863491330175013445755216787967842853486133932913146412900
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (4::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (4::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 4 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 4 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=4) (mask0:=mask0) (mask1:=mask1) (L:=4) (start:=4)
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
end Snake9.LocalWindow.SplitShare62.E22
