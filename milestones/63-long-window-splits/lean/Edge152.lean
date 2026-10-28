import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E152
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 48, 112]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 6]
def C : List Nat := [63, 55, 51, 50, 48]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 16, 17, 18, 19, 23, 27, 29, 30, 32, 33, 34, 35, 39, 47, 49, 52, 53, 54, 56, 58, 59, 61, 62, 65, 67, 71, 79, 95, 114, 115, 119, 127, 129, 131, 135, 143, 159, 176, 178, 179, 183, 191, 257, 259, 263, 271, 287, 304, 306, 307, 311, 319]
def D1 : List Nat := [2, 5, 6, 9, 11, 13, 14, 16, 17, 18, 19, 23, 27, 29, 30, 32, 33, 34, 35, 39, 47, 49, 52, 53, 54, 56, 58, 59, 61, 62, 65, 67, 71, 79, 95, 96, 113, 114, 115, 116, 119, 120, 127, 129, 131, 135, 143, 159, 176, 178, 179, 183, 191, 240, 257, 259, 263, 271, 287, 304, 306, 307, 311, 319, 368]
def mask0 : Nat := 1072589071371731070267514230762245346536079545794338615299395266162829414395119347390045729286756
def mask1 : Nat := 601226901190102378928778404509140546524172341830654807310195580551603728341856097671462454022631863181772810852
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (80::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (80::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 11 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 11 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    11 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=80) (mask0:=mask0) (mask1:=mask1) (L:=11) (start:=6)
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
end Snake9.LocalWindow.LongWindow63.E152
