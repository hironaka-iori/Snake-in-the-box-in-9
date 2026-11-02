import Port95M62SplitShare
namespace Snake9.LocalWindow.SplitShare62.E27
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 5, 1]
def C : List Nat := [15, 13, 12, 28, 60]
def D0 : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 47, 52, 56, 61, 65, 67, 71, 76, 77, 79, 92, 124, 129, 131, 135, 140, 141, 143, 156, 188, 257, 259, 263, 268, 269, 271, 284, 316]
def D1 : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 47, 52, 54, 56, 58, 61, 63, 65, 67, 71, 76, 77, 79, 92, 124, 126, 129, 131, 135, 140, 141, 143, 156, 188, 190, 257, 259, 263, 268, 269, 271, 284, 316, 318]
def mask0 : Nat := 133499189776144815532981513038444370539334136653429855009026788332737569127775466511015178029940
def mask1 : Nat := 667495948756372336131736939580832399191579542676439717686831208235824651792836566076172422237044
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (46::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (46::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 6 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 6 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=46) (mask0:=mask0) (mask1:=mask1) (L:=6) (start:=4)
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
end Snake9.LocalWindow.SplitShare62.E27
