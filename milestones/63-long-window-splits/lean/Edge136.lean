import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E136
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 126, 94, 78, 74]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 6, 5, 4, 2]
def C : List Nat := [63, 62, 126, 94, 78]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 46, 47, 54, 55, 58, 59, 60, 61, 65, 67, 70, 71, 76, 79, 86, 90, 92, 95, 110, 118, 122, 124, 127, 129, 131, 135, 143, 159, 190, 191, 206, 222, 254, 257, 259, 263, 271, 287, 318, 319, 334, 350, 382]
def D1 : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 46, 47, 54, 55, 58, 59, 60, 61, 65, 67, 70, 71, 72, 75, 76, 79, 86, 90, 92, 95, 106, 110, 118, 122, 124, 127, 129, 131, 135, 143, 159, 190, 191, 202, 206, 222, 254, 257, 259, 263, 271, 287, 318, 319, 330, 334, 350, 382]
def mask0 : Nat := 9850501551392153416673418342026862296892251706502423263289943338978502705161715792789965496718465537858184306911844
def mask1 : Nat := 9850501551392155603924143125038786669394478824123788622887126409226900233100170572188744744640234929567853645033060
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (66::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (66::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 4 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 4 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=66) (mask0:=mask0) (mask1:=mask1) (L:=4) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E136
