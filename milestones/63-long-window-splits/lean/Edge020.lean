import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E020
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 29, 21, 53, 37]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 0, 3, 5, 4]
def C : List Nat := [12, 28, 29, 21, 53]
def D0 : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 25, 30, 31, 33, 35, 39, 44, 46, 47, 49, 52, 55, 60, 61, 65, 67, 71, 76, 78, 79, 85, 92, 93, 117, 129, 131, 135, 140, 142, 143, 149, 156, 157, 181, 257, 259, 263, 268, 270, 271, 277, 284, 285, 309]
def D1 : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 25, 30, 31, 33, 35, 39, 44, 45, 46, 47, 49, 52, 55, 60, 61, 65, 67, 71, 76, 78, 79, 85, 92, 93, 101, 117, 129, 131, 135, 140, 142, 143, 149, 156, 157, 165, 181, 257, 259, 263, 268, 270, 271, 277, 284, 285, 293, 309]
def mask0 : Nat := 1042962513380378991008679092873588644948938003727938285988498823357925115329645629377881976692
def mask1 : Nat := 1042978427723944104181228065105529343215821265092816195704350303258401543811065497544799432564
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (36::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (36::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 15 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 15 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    15 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=36) (mask0:=mask0) (mask1:=mask1) (L:=15) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E020
