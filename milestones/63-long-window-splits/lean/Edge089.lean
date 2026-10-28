import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E089
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 2, 1]
def C : List Nat := [27, 25, 57, 56, 60]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 28, 29, 30, 33, 35, 39, 40, 41, 44, 47, 48, 49, 52, 58, 59, 61, 63, 65, 67, 71, 79, 89, 91, 95, 120, 121, 124, 129, 131, 135, 143, 153, 155, 159, 184, 185, 188, 257, 259, 263, 271, 281, 283, 287, 312, 313, 316]
def D1 : List Nat := [2, 4, 5, 6, 9, 11, 13, 14, 16, 17, 19, 23, 24, 26, 28, 29, 30, 32, 33, 35, 39, 40, 41, 44, 47, 48, 49, 52, 58, 59, 61, 63, 64, 65, 67, 71, 79, 89, 91, 95, 120, 121, 124, 128, 129, 131, 135, 143, 153, 155, 159, 184, 185, 188, 256, 257, 259, 263, 271, 281, 283, 287, 312, 313, 316]
def mask0 : Nat := 158530288090347162559394572168383797174613659914816868397489104414667334720732599587509098933092
def mask1 : Nat := 158530288090347162675186661405699992598184644923504776251099371447228837223672004946932001368692
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (8::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (8::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 14 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 14 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    14 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=8) (mask0:=mask0) (mask1:=mask1) (L:=14) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E089
