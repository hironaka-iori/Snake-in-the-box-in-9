import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E011
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55, 51, 50]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3, 2, 0]
def C : List Nat := [30, 62, 63, 55, 51]
def D0 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 49, 53, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 115, 119, 126, 127, 129, 131, 134, 135, 142, 158, 179, 183, 190, 191, 257, 259, 262, 263, 270, 286, 307, 311, 318, 319]
def D1 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 34, 35, 38, 39, 46, 47, 48, 49, 53, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 114, 115, 119, 126, 127, 129, 131, 134, 135, 142, 158, 178, 179, 183, 190, 191, 257, 259, 262, 263, 270, 286, 306, 307, 311, 318, 319]
def mask0 : Nat := 1606422867349519133150025168110405750220259803628863098458652910583927156293137123820472229600820
def mask1 : Nat := 1606553237652004540259546348634463950422567480729942934850908233928630058412928396457925986131508
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (18::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (18::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 9 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 9 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    9 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=18) (mask0:=mask0) (mask1:=mask1) (L:=9) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E011
