import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G240
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 28, 20, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 1, 3, 5]
def D : List Nat := [2, 4, 5, 6, 9, 11, 12, 13, 14, 16, 17, 19, 21, 22, 23, 24, 26, 27, 29, 33, 35, 39, 47, 60, 62, 63, 65, 67, 71, 79, 84, 92, 94, 95, 129, 131, 135, 143, 148, 156, 158, 159, 257, 259, 263, 271, 276, 284, 286, 287]
def C : List Nat := [15, 31, 30, 28, 20]
def mask : Nat := 404200356643204197944907151015301098398769430741987287720331731948318813925710840429172
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 22 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    22 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=22) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G240


namespace G241
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 28, 12, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 1, 4, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 13, 14, 17, 19, 20, 22, 23, 24, 26, 27, 29, 33, 35, 39, 47, 60, 62, 63, 65, 67, 71, 76, 79, 92, 94, 95, 129, 131, 135, 140, 143, 156, 158, 159, 257, 259, 263, 268, 271, 284, 286, 287]
def C : List Nat := [15, 31, 30, 28, 12]
def mask : Nat := 404079414121837605925111139592879224052774491890277117882197461798209008378650545515380
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
end G241


namespace G247
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 26, 24, 25]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 2, 1, 0]
def D : List Nat := [2, 5, 6, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 22, 23, 27, 28, 29, 33, 35, 39, 47, 56, 58, 62, 63, 65, 67, 71, 79, 88, 90, 94, 95, 129, 131, 135, 143, 152, 154, 158, 159, 257, 259, 263, 271, 280, 282, 286, 287]
def C : List Nat := [15, 31, 30, 26, 24]
def mask : Nat := 382709582022957070097860603671065920493974649374570755541743304333512103847486282493796
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 22 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    22 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=22) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G247


namespace G248
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 26, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 2, 1, 5]
def D : List Nat := [2, 5, 6, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 22, 23, 25, 27, 28, 29, 33, 35, 39, 47, 58, 62, 63, 65, 67, 71, 79, 88, 90, 94, 95, 129, 131, 135, 143, 152, 154, 158, 159, 257, 259, 263, 271, 280, 282, 286, 287]
def C : List Nat := [15, 31, 30, 26, 24]
def mask : Nat := 382709582022957070097860603671065920493974649374570755541743304333512031789892278120292
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 43 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    43 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=43) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G248


namespace G249
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 26, 18, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 2, 3, 5]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 16, 17, 19, 22, 23, 24, 27, 28, 29, 33, 35, 39, 47, 58, 62, 63, 65, 67, 71, 79, 82, 90, 94, 95, 129, 131, 135, 143, 146, 154, 158, 159, 257, 259, 263, 271, 274, 282, 286, 287]
def C : List Nat := [15, 31, 30, 26, 18]
def mask : Nat := 380797267332172368043674258356536519070242910354588775983479079842364047610491850944100
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
end G249


namespace G250
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 26, 10, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 2, 4, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 17, 18, 19, 22, 23, 24, 27, 28, 29, 33, 35, 39, 47, 58, 62, 63, 65, 67, 71, 74, 79, 90, 94, 95, 129, 131, 135, 138, 143, 154, 158, 159, 257, 259, 263, 266, 271, 282, 286, 287]
def C : List Nat := [15, 31, 30, 26, 10]
def mask : Nat := 380767031701830720038725255500931050483744175641661233523945512304836596223726777690980
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
end G250


namespace G251
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 26, 58, 59]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 2, 5, 0]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 18, 19, 22, 23, 24, 27, 28, 29, 33, 35, 39, 42, 47, 50, 56, 62, 63, 65, 67, 71, 79, 90, 94, 95, 122, 129, 131, 135, 143, 154, 158, 159, 186, 257, 259, 263, 271, 282, 286, 287, 314]
def C : List Nat := [15, 31, 30, 26, 58]
def mask : Nat := 33374797817031133168153555185840393555007739463764649962110568424909891961451016262758291107428
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
end G251


namespace G252
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 26, 58, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 2, 5, 1]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 18, 19, 22, 23, 24, 27, 28, 29, 33, 35, 39, 42, 47, 50, 59, 62, 63, 65, 67, 71, 79, 90, 94, 95, 122, 129, 131, 135, 143, 154, 158, 159, 186, 257, 259, 263, 271, 282, 286, 287, 314]
def C : List Nat := [15, 31, 30, 26, 58]
def mask : Nat := 33374797817031133168153555185840393555007739463764649962110568424909891961451520665916556602980
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
end G252


namespace G253
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 26, 58, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 2, 5, 3]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 18, 19, 22, 23, 24, 27, 28, 29, 33, 35, 39, 42, 47, 56, 59, 62, 63, 65, 67, 71, 79, 90, 94, 95, 122, 129, 131, 135, 143, 154, 158, 159, 186, 257, 259, 263, 271, 282, 286, 287, 314]
def C : List Nat := [15, 31, 30, 26, 58]
def mask : Nat := 33374797817031133168153555185840393555007739463764649962110568424909891961451591597610687688292
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
end G253


namespace G254
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 26, 58, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 2, 5, 4]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 18, 19, 22, 23, 24, 27, 28, 29, 33, 35, 39, 47, 50, 56, 59, 62, 63, 65, 67, 71, 79, 90, 94, 95, 122, 129, 131, 135, 143, 154, 158, 159, 186, 257, 259, 263, 271, 282, 286, 287, 314]
def C : List Nat := [15, 31, 30, 26, 58]
def mask : Nat := 33374797817031133168153555185840393555007739463764649962110568424909891961451592719112548019812
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
end G254


namespace G255
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 26, 58, 122]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 2, 5, 6]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 18, 19, 22, 23, 24, 27, 28, 29, 33, 35, 39, 42, 47, 50, 56, 59, 62, 63, 65, 67, 71, 79, 90, 94, 95, 129, 131, 135, 143, 154, 158, 159, 186, 257, 259, 263, 271, 282, 286, 287, 314]
def C : List Nat := [15, 31, 30, 26, 58]
def mask : Nat := 33374797817031133168153555185840393555007739463764649962105251512926752297959977495269473152612
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
end G255


namespace G256
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 22, 20, 21]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 3, 1, 0]
def D : List Nat := [2, 4, 5, 6, 9, 11, 13, 14, 16, 17, 18, 19, 23, 26, 27, 28, 29, 33, 35, 39, 47, 52, 54, 62, 63, 65, 67, 71, 79, 84, 86, 94, 95, 129, 131, 135, 143, 148, 150, 158, 159, 257, 259, 263, 271, 276, 278, 286, 287]
def C : List Nat := [15, 31, 30, 22, 20]
def mask : Nat := 373603321590648965077925625982830675619061606422275614788104140089949936651798053874292
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 8 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    8 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=8) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G256

end Snake9.LocalWindow.ExtendedShare59
