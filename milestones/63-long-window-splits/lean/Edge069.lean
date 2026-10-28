import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E069
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 126, 127, 111, 107]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 6, 0, 4, 2]
def C : List Nat := [30, 62, 126, 127, 111]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 39, 46, 47, 54, 58, 60, 63, 65, 67, 71, 79, 94, 95, 103, 109, 110, 118, 119, 122, 123, 124, 125, 129, 131, 135, 143, 158, 159, 190, 239, 254, 255, 257, 259, 263, 271, 286, 287, 318, 367, 382, 383]
def D1 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 39, 43, 46, 47, 54, 58, 60, 63, 65, 67, 71, 75, 79, 94, 95, 103, 105, 106, 109, 110, 118, 119, 122, 123, 124, 125, 129, 131, 135, 143, 158, 159, 190, 235, 239, 254, 255, 257, 259, 263, 271, 286, 287, 318, 363, 367, 382, 383]
def mask0 : Nat := 29551805260746454460396446687977323147196737341852516124453707348817657686630589071290490568355893146121469659081316
def mask1 : Nat := 29551824049087116651062269803822097461892956402526878165337183306623476842518993607887970687670547505285976115800676
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (99::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (99::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 4 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 4 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=99) (mask0:=mask0) (mask1:=mask1) (L:=4) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E069
