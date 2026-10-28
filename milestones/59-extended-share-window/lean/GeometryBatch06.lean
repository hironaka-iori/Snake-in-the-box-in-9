import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G098
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 61]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 0]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 56, 62, 65, 67, 71, 76, 78, 79, 92, 124, 129, 131, 135, 140, 142, 143, 156, 188, 257, 259, 263, 268, 270, 271, 284, 316]
def C : List Nat := [15, 14, 12, 28, 60]
def mask : Nat := 133499189776145764101776545132717280432843327824770991784334319076566073207386476676071865069428
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 5 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G098


namespace G099
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 1]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 56, 61, 65, 67, 71, 76, 78, 79, 92, 124, 129, 131, 135, 140, 142, 143, 156, 188, 257, 259, 263, 268, 270, 271, 284, 316]
def C : List Nat := [15, 14, 12, 28, 60]
def mask : Nat := 133499189776145764101776545132717280432843327824770991784334319076566073207384170833062651375476
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 5 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G099


namespace G100
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 56]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 61, 62, 65, 67, 71, 76, 78, 79, 92, 124, 129, 131, 135, 140, 142, 143, 156, 188, 257, 259, 263, 268, 270, 271, 284, 316]
def C : List Nat := [15, 14, 12, 28, 60]
def mask : Nat := 133499189776145764101776545132717280432843327824770991784334319076566073207388710461487040835444
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 5 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G100


namespace G101
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 52]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 3]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 56, 61, 62, 65, 67, 71, 76, 78, 79, 92, 124, 129, 131, 135, 140, 142, 143, 156, 188, 257, 259, 263, 268, 270, 271, 284, 316]
def C : List Nat := [15, 14, 12, 28, 60]
def mask : Nat := 133499189776145764101776545132717280432843327824770991784334319076566073207388778015481451392884
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 5 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G101


namespace G102
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 124]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 6]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 56, 61, 62, 65, 67, 71, 76, 78, 79, 92, 129, 131, 135, 140, 142, 143, 156, 188, 257, 259, 263, 268, 270, 271, 284, 316]
def C : List Nat := [15, 14, 12, 28, 60]
def mask : Nat := 133499189776145764101776545132717280432843327824770991784313051428633514553422321606116593250164
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 5 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G102


namespace G103
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 27, 25]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 0, 1]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 17, 18, 19, 23, 24, 30, 31, 33, 35, 39, 42, 46, 47, 58, 59, 65, 67, 71, 74, 78, 79, 90, 91, 129, 131, 135, 138, 142, 143, 154, 155, 257, 259, 263, 266, 270, 271, 282, 283]
def C : List Nat := [15, 14, 10, 26, 27]
def mask : Nat := 23317852669886635178090084432421954003173136504851036628753193356760402024875133123428
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 5 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G103


namespace G104
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 27, 59]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 0, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 17, 18, 19, 23, 24, 25, 30, 31, 33, 35, 39, 42, 46, 47, 58, 65, 67, 71, 74, 78, 79, 90, 91, 129, 131, 135, 138, 142, 143, 154, 155, 257, 259, 263, 266, 270, 271, 282, 283]
def C : List Nat := [15, 14, 10, 26, 27]
def mask : Nat := 23317852669886635178090084432421954003173136504851036628753193356759825564122863254372
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 10 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G104


namespace G105
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 24, 25]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 1, 0]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 16, 17, 18, 19, 23, 27, 28, 30, 31, 33, 35, 39, 42, 46, 47, 56, 58, 65, 67, 71, 74, 78, 79, 88, 90, 129, 131, 135, 138, 142, 143, 152, 154, 257, 259, 263, 266, 270, 271, 280, 282]
def C : List Nat := [15, 14, 10, 26, 24]
def mask : Nat := 9719170424306531681653851084657321656636325696090293103318708086374232345981003709284
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G105


namespace G106
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 24, 28]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 1, 2]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 16, 17, 18, 19, 23, 25, 27, 30, 31, 33, 35, 39, 42, 46, 47, 56, 58, 65, 67, 71, 74, 78, 79, 88, 90, 129, 131, 135, 138, 142, 143, 152, 154, 257, 259, 263, 266, 270, 271, 280, 282]
def C : List Nat := [15, 14, 10, 26, 24]
def mask : Nat := 9719170424306531681653851084657321656636325696090293103318708086374232345980768828260
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 23 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    23 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=23) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G106


namespace G107
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 1, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 16, 17, 18, 19, 23, 25, 27, 28, 30, 31, 33, 35, 39, 42, 46, 47, 58, 65, 67, 71, 74, 78, 79, 88, 90, 129, 131, 135, 138, 142, 143, 152, 154, 257, 259, 263, 266, 270, 271, 280, 282]
def C : List Nat := [15, 14, 10, 26, 24]
def mask : Nat := 9719170424306531681653851084657321656636325696090293103318708086374160288386999335780
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 24 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    24 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=24) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G107


namespace G108
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 18, 22]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 3, 2]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 16, 17, 19, 23, 24, 27, 30, 31, 33, 35, 39, 42, 46, 47, 50, 58, 65, 67, 71, 74, 78, 79, 82, 90, 129, 131, 135, 138, 142, 143, 146, 154, 257, 259, 263, 266, 270, 271, 274, 282]
def C : List Nat := [15, 14, 10, 26, 18]
def mask : Nat := 7806855733521829627467505770127920232904586676108313545054483595226177234886210567012
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 11 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    11 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=11) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G108


namespace G109
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 18, 50]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 3, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 16, 17, 19, 22, 23, 24, 27, 30, 31, 33, 35, 39, 42, 46, 47, 58, 65, 67, 71, 74, 78, 79, 82, 90, 129, 131, 135, 138, 142, 143, 146, 154, 257, 259, 263, 266, 270, 271, 274, 282]
def C : List Nat := [15, 14, 10, 26, 18]
def mask : Nat := 7806855733521829627467505770127920232904586676108313545054483595226176108986307918692
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 17 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    17 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=17) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G109

end Snake9.LocalWindow.ExtendedShare59
