import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E156
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 114, 82]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 6, 5]
def C : List Nat := [63, 55, 51, 50, 114]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 23, 27, 29, 30, 33, 34, 35, 39, 47, 48, 49, 53, 54, 58, 59, 61, 62, 65, 67, 71, 79, 95, 98, 112, 115, 118, 119, 122, 127, 129, 131, 135, 143, 159, 178, 179, 183, 191, 242, 257, 259, 263, 271, 287, 306, 307, 311, 319, 370]
def D1 : List Nat := [2, 4, 5, 6, 8, 9, 11, 13, 14, 17, 18, 19, 23, 27, 29, 30, 32, 33, 34, 35, 39, 47, 48, 49, 53, 54, 58, 59, 61, 62, 64, 65, 67, 71, 79, 95, 98, 112, 115, 118, 119, 122, 127, 128, 129, 131, 135, 143, 159, 178, 179, 183, 191, 242, 256, 257, 259, 263, 271, 287, 306, 307, 311, 319, 370]
def mask0 : Nat := 2404907604760406297915306927221999606173701949572029570425225663920609917117743143053299379285764452800751692388
def mask1 : Nat := 2404907604760406297915306927221999721965791186888224993996210672608517770728010175614801882225169812223653997428
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (16::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (16::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 8 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 8 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    8 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=16) (mask0:=mask0) (mask1:=mask1) (L:=8) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E156
