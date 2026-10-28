import SplitShare
namespace Snake9.LocalWindow.SplitShare62.E07
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 25]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 1]
def C : List Nat := [6, 14, 30, 26, 27]
def D0 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 31, 33, 35, 38, 39, 46, 58, 59, 62, 65, 67, 70, 71, 78, 90, 91, 94, 129, 131, 134, 135, 142, 154, 155, 158, 257, 259, 262, 263, 270, 282, 283, 286]
def D1 : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 16, 17, 18, 19, 22, 23, 24, 28, 31, 32, 33, 35, 38, 39, 46, 58, 59, 62, 64, 65, 67, 70, 71, 78, 90, 91, 94, 128, 129, 131, 134, 135, 142, 154, 155, 158, 256, 257, 259, 262, 263, 270, 282, 283, 286]
def mask0 : Nat := 147644756336747499516296400266944791002896463046434217484083496688598562187687326818100
def mask1 : Nat := 147644756452539588753612595690515776011584370900044484516644999191537967547110229253684
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (8::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (8::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 10 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 10 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=8) (mask0:=mask0) (mask1:=mask1) (L:=10) (start:=4)
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
end Snake9.LocalWindow.SplitShare62.E07
