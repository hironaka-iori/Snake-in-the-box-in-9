import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E186
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 3]
def C : List Nat := [63, 55, 51, 115, 113]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 49, 50, 53, 54, 59, 61, 62, 65, 67, 71, 79, 81, 83, 95, 97, 99, 112, 114, 117, 119, 123, 127, 129, 131, 135, 143, 159, 179, 183, 191, 241, 243, 257, 259, 263, 271, 287, 307, 311, 319, 369, 371]
def D1 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 49, 50, 53, 54, 59, 61, 62, 65, 67, 71, 79, 81, 83, 89, 95, 97, 99, 105, 112, 114, 117, 119, 120, 123, 125, 127, 129, 131, 135, 143, 159, 179, 183, 191, 241, 243, 249, 257, 259, 263, 271, 287, 307, 311, 319, 369, 371, 377]
def mask0 : Nat := 6012269011901014135823178821405014170712170903025678995501447280118704098538574029850940248113367615335230499428
def mask1 : Nat := 313840442421232882981753179603776997023802259650703513865594137821168779718508068251151552672088698490031960648292
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (57::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (57::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 28 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 28 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    28 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=57) (mask0:=mask0) (mask1:=mask1) (L:=28) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E186
