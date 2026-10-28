import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E032
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55, 119, 115]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3, 6, 2]
def C : List Nat := [30, 62, 63, 55, 119]
def D0 : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 39, 46, 47, 51, 53, 54, 58, 59, 60, 61, 65, 67, 71, 78, 79, 87, 94, 103, 117, 118, 126, 127, 129, 131, 135, 142, 143, 158, 183, 190, 191, 247, 257, 259, 263, 270, 271, 286, 311, 318, 319, 375]
def D1 : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 39, 46, 47, 51, 53, 54, 58, 59, 60, 61, 65, 67, 71, 78, 79, 87, 94, 99, 103, 113, 114, 117, 118, 123, 126, 127, 129, 131, 135, 142, 143, 158, 183, 190, 191, 243, 247, 257, 259, 263, 270, 271, 286, 311, 318, 319, 371, 375]
def mask0 : Nat := 76957043352332968817644626940145101508741746438063940998661346191304389049296538056759672290832311503635270483556
def mask1 : Nat := 81766858561853779268362283202369663740821279074746407168506544481008296480868540998529578955845850080230186303076
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (83::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (83::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 6 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 6 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=83) (mask0:=mask0) (mask1:=mask1) (L:=6) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E032
