import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E149
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 50, 54, 22]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 0, 2, 5]
def C : List Nat := [63, 59, 51, 50, 54]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 23, 27, 29, 30, 33, 34, 35, 38, 39, 43, 47, 48, 49, 52, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 114, 115, 118, 123, 127, 129, 131, 135, 143, 159, 178, 179, 182, 187, 191, 257, 259, 263, 271, 287, 306, 307, 310, 315, 319]
def D1 : List Nat := [2, 4, 5, 6, 8, 9, 11, 13, 14, 17, 18, 19, 23, 27, 29, 30, 32, 33, 34, 35, 38, 39, 43, 47, 48, 49, 52, 55, 57, 58, 61, 62, 64, 65, 67, 71, 79, 95, 114, 115, 118, 123, 127, 128, 129, 131, 135, 143, 159, 178, 179, 182, 187, 191, 256, 257, 259, 263, 271, 287, 306, 307, 310, 315, 319]
def mask0 : Nat := 1137220148828871644812639475564098096830110468654667506759971819491589997607543931668458831309412
def mask1 : Nat := 1137220148828871644928431564801414292253681453663355414613582086524151500110483337027881733614452
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (16::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (16::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 23 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 23 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    23 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=16) (mask0:=mask0) (mask1:=mask1) (L:=23) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E149
