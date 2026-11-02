import Port95M62SplitShare
namespace Snake9.LocalWindow.LongWindow63.E057
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 22, 18, 50, 48, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 3, 2, 5, 1, 3]
def C : List Nat := [30, 22, 18, 50, 48]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 16, 17, 19, 20, 23, 26, 27, 28, 29, 32, 33, 34, 35, 39, 47, 49, 51, 52, 54, 58, 62, 63, 65, 67, 71, 79, 82, 86, 94, 95, 112, 114, 129, 131, 135, 143, 146, 150, 158, 159, 176, 178, 257, 259, 263, 271, 274, 278, 286, 287, 304, 306]
def D1 : List Nat := [2, 5, 6, 9, 11, 13, 14, 16, 17, 19, 20, 23, 24, 26, 27, 28, 29, 32, 33, 34, 35, 39, 40, 47, 49, 51, 52, 54, 57, 58, 62, 63, 65, 67, 71, 79, 82, 86, 94, 95, 112, 114, 120, 129, 131, 135, 143, 146, 150, 158, 159, 176, 178, 184, 257, 259, 263, 271, 274, 278, 286, 287, 304, 306, 312]
def mask0 : Nat := 162963251619017873227359682799026458832919546662271483071817561446376097254852769144893041252
def mask1 : Nat := 8506662610685072882582913222523839406524254015771800587412511622432111763895274745470304086628
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (60::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (60::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 22 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 22 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    22 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=60) (mask0:=mask0) (mask1:=mask1) (L:=22) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E057
