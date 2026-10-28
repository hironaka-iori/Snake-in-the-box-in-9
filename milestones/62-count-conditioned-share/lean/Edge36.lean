import SplitShare
namespace Snake9.LocalWindow.SplitShare62.E36
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 24, 26]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 0, 1]
def C : List Nat := [15, 31, 29, 25, 24]
def D0 : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 19, 21, 23, 27, 28, 30, 33, 35, 39, 47, 56, 57, 61, 63, 65, 67, 71, 79, 88, 89, 93, 95, 129, 131, 135, 143, 152, 153, 157, 159, 257, 259, 263, 271, 280, 281, 285, 287]
def D1 : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 18, 19, 21, 23, 27, 28, 30, 33, 35, 39, 47, 56, 57, 58, 61, 63, 65, 67, 71, 79, 88, 89, 90, 93, 95, 129, 131, 135, 143, 152, 153, 154, 157, 159, 257, 259, 263, 271, 280, 281, 282, 285, 287]
def mask0 : Nat := 316658839687282281686598898839066277667938711160590001275347233020207851121427742420836
def mask1 : Nat := 324429515256185197970276746466360353294531174479881854718452653174714233795081751456612
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (10::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (10::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 8 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 8 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    8 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=10) (mask0:=mask0) (mask1:=mask1) (L:=8) (start:=4)
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
end Snake9.LocalWindow.SplitShare62.E36
