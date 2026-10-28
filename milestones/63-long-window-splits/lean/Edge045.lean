import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E045
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 22, 54, 50]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 2]
def C : List Nat := [12, 28, 20, 22, 54]
def D0 : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 18, 19, 21, 23, 24, 29, 30, 31, 33, 35, 38, 39, 44, 45, 47, 52, 55, 60, 62, 65, 67, 71, 76, 77, 79, 84, 86, 92, 118, 129, 131, 135, 140, 141, 143, 148, 150, 156, 182, 257, 259, 263, 268, 269, 271, 276, 278, 284, 310]
def D1 : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 18, 19, 21, 23, 24, 29, 30, 31, 33, 35, 38, 39, 44, 45, 47, 48, 51, 52, 55, 58, 60, 62, 65, 67, 71, 76, 77, 79, 84, 86, 92, 114, 118, 129, 131, 135, 140, 141, 143, 148, 150, 156, 178, 182, 257, 259, 263, 268, 269, 271, 276, 278, 284, 306, 310]
def mask0 : Nat := 2085924871461533164452085122440898459077968423282307812480532922454843327747142995743362468724
def mask1 : Nat := 2216295173946940273973265646499098661385645524362144204735856267157745447538706115338724920180
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (34::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (34::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 19 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 19 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    19 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=34) (mask0:=mask0) (mask1:=mask1) (L:=19) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E045
