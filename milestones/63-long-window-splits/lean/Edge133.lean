import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E133
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 46, 38, 102, 98]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 4, 3, 6, 2]
def C : List Nat := [63, 62, 46, 38, 102]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 34, 35, 36, 39, 42, 44, 47, 54, 55, 58, 59, 60, 61, 65, 67, 70, 71, 79, 95, 100, 103, 110, 118, 126, 127, 129, 131, 135, 143, 159, 166, 174, 190, 191, 230, 257, 259, 263, 271, 287, 294, 302, 318, 319, 358]
def D1 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 34, 35, 36, 39, 42, 44, 47, 54, 55, 58, 59, 60, 61, 65, 67, 70, 71, 79, 95, 96, 99, 100, 103, 106, 110, 114, 118, 126, 127, 129, 131, 135, 143, 159, 166, 174, 190, 191, 226, 230, 257, 259, 263, 271, 287, 294, 302, 318, 319, 354, 358]
def mask0 : Nat := 587135645695060305429532089655760595061204873150743765954027263339365660178104506247101586647659393709664868
def mask1 : Nat := 623831623550901449615305223980593986114057752764104866493007352829904504739065841879928517575225640514906724
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (66::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (66::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 6 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 6 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=66) (mask0:=mask0) (mask1:=mask1) (L:=6) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E133
