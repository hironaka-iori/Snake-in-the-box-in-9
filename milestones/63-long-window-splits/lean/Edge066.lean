import SplitShare
namespace Snake9.LocalWindow.LongWindow63.E066
open ForcedShare58 ExtendedShare59 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 46, 38, 102, 98]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 4, 3, 6, 2]
def C : List Nat := [30, 62, 46, 38, 102]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 34, 35, 36, 39, 42, 44, 47, 54, 58, 60, 63, 65, 67, 70, 71, 79, 94, 95, 100, 103, 110, 118, 126, 129, 131, 135, 143, 158, 159, 166, 174, 190, 230, 257, 259, 263, 271, 286, 287, 294, 302, 318, 358]
def D1 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 34, 35, 36, 39, 42, 44, 47, 54, 58, 60, 63, 65, 67, 70, 71, 79, 94, 95, 96, 99, 100, 103, 106, 110, 114, 118, 126, 129, 131, 135, 143, 158, 159, 166, 174, 190, 226, 230, 257, 259, 263, 271, 286, 287, 294, 302, 318, 354, 358]
def mask0 : Nat := 587135645693992311911695965423665530868658942655475980352006723027118720993388018804243587323753888062532196
def mask1 : Nat := 623831623549833456097469099748498921921511822268837080890986812517657565554349354437070518251320134867774052
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
end Snake9.LocalWindow.LongWindow63.E066
