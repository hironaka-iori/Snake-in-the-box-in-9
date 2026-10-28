import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E008
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 59, 57, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 5, 1, 0]
def C : List Nat := [30, 26, 27, 59, 57]
def D0 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 25, 28, 31, 33, 35, 38, 39, 41, 43, 46, 49, 51, 58, 61, 62, 63, 65, 67, 70, 71, 78, 90, 91, 94, 121, 123, 129, 131, 134, 135, 142, 154, 155, 158, 185, 187, 257, 259, 262, 263, 270, 282, 283, 286, 313, 315]
def D1 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 16, 17, 18, 19, 22, 23, 24, 25, 28, 31, 32, 33, 35, 38, 39, 41, 43, 46, 49, 51, 58, 61, 62, 63, 64, 65, 67, 70, 71, 78, 90, 91, 94, 121, 123, 128, 129, 131, 134, 135, 142, 154, 155, 158, 185, 187, 256, 257, 259, 262, 263, 270, 282, 283, 286, 313, 315]
def mask0 : Nat := 83436993738305306430303034913544529743858135693991754089841158093940853355023825583150145118004
def mask1 : Nat := 83436993738305306546095124150860725167429120702679661943451425126502355857963230942573047553588
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (8::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (8::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 36 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 36 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    36 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=8) (mask0:=mask0) (mask1:=mask1) (L:=36) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E008
