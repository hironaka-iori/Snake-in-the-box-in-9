import SplitShare
namespace Snake9.LocalWindow.SplitShare62.E50
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 4]
def C : List Nat := [15, 31, 27, 25, 57]
def D0 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 91, 95, 121, 129, 131, 135, 143, 153, 155, 159, 185, 257, 259, 263, 271, 281, 283, 287, 313]
def D1 : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 40, 45, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 91, 95, 105, 121, 129, 131, 135, 143, 153, 155, 159, 169, 185, 257, 259, 263, 271, 281, 283, 287, 297, 313]
def mask0 : Nat := 16687398986224227400350161993061977063860973939954873623697305377909828387828055331336452991588
def mask1 : Nat := 16687653615721269211110945548773028236131106121792920179150929056317451243530772687644481186404
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced0 : forceCheckPlus W D0=true := by decide +kernel
theorem forced1 : forceCheckPlus (43::W) D1=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask0 : maskCheck mask0 (43::D0)=true := by decide +kernel
theorem checked_mask1 : maskCheck mask1 D1=true := by decide +kernel
theorem credit0 : 8 ≤ (C.map (shareLocal 12 (allowed mask0))).sum := by decide +kernel
theorem credit1 : 8 ≤ (C.map (shareLocal 12 (allowed mask1))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    8 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  split_in_snake (W:=W) (cs:=ds) (D0:=D0) (D1:=D1) (C:=C)
    (q:=43) (mask0:=mask0) (mask1:=mask1) (L:=8) (start:=4)
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
end Snake9.LocalWindow.SplitShare62.E50
