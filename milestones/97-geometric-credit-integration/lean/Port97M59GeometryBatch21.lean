import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G335
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 125, 117]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 6, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 79, 93, 95, 109, 121, 124, 127, 129, 131, 135, 143, 157, 159, 189, 253, 257, 259, 263, 271, 285, 287, 317, 381]
def C : List Nat := [15, 31, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392318896318959424227707879885366201472616300504928984928295106649328763990034613241801316
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 12 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    12 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=12) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G335


namespace G336
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 125, 109]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 6, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 79, 93, 95, 117, 121, 124, 127, 129, 131, 135, 143, 157, 159, 189, 253, 257, 259, 263, 271, 285, 287, 317, 381]
def C : List Nat := [15, 31, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392318896318959424227707879885366201472616300504928985093799569015126394649444183735691876
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 12 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    12 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=12) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G336


namespace G337
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 125, 253]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 6, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 79, 93, 95, 109, 117, 121, 124, 127, 129, 131, 135, 143, 157, 159, 189, 257, 259, 263, 271, 285, 287, 317, 381]
def C : List Nat := [15, 31, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392318896318944950216553215360938255099490214516447326346365401051938315905009506635639396
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 12 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    12 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=12) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G337


namespace G338
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 24, 28]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 0, 1, 2]
def D : List Nat := [2, 5, 6, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 23, 25, 29, 30, 33, 35, 39, 47, 56, 58, 59, 63, 65, 67, 71, 79, 88, 90, 91, 95, 129, 131, 135, 143, 152, 154, 155, 159, 257, 259, 263, 271, 280, 282, 283, 287]
def C : List Nat := [15, 31, 27, 26, 24]
def mask : Nat := 273920124058316242126370736888948861721680162904484807338267422170422746416330860097380
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 21 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    21 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=21) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G338


namespace G339
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 0, 1, 5]
def D : List Nat := [2, 5, 6, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19, 23, 25, 28, 29, 30, 33, 35, 39, 47, 58, 59, 63, 65, 67, 71, 79, 88, 90, 91, 95, 129, 131, 135, 143, 152, 154, 155, 159, 257, 259, 263, 271, 280, 282, 283, 287]
def C : List Nat := [15, 31, 27, 26, 24]
def mask : Nat := 273920124058316242126370736888948861721680162904484807338267422170422674358737090604900
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
end G339


namespace G340
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 18, 22]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 0, 3, 2]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 16, 17, 19, 23, 24, 25, 29, 30, 33, 35, 39, 47, 50, 58, 59, 63, 65, 67, 71, 79, 82, 90, 91, 95, 129, 131, 135, 143, 146, 154, 155, 159, 257, 259, 263, 271, 274, 282, 283, 287]
def C : List Nat := [15, 31, 27, 26, 18]
def mask : Nat := 272007809367531540072184391574419460297948423884502827780003197679274691305236335390308
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 14 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    14 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=14) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G340


namespace G341
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 18, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 0, 3, 5]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 16, 17, 19, 22, 23, 24, 25, 29, 30, 33, 35, 39, 47, 58, 59, 63, 65, 67, 71, 79, 82, 90, 91, 95, 129, 131, 135, 143, 146, 154, 155, 159, 257, 259, 263, 271, 274, 282, 283, 287]
def C : List Nat := [15, 31, 27, 26, 18]
def mask : Nat := 272007809367531540072184391574419460297948423884502827780003197679274690179336432741988
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 20 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    20 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=20) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G341


namespace G342
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 10, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 0, 4, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 17, 18, 19, 23, 24, 25, 29, 30, 33, 35, 39, 47, 58, 59, 63, 65, 67, 71, 74, 79, 90, 91, 95, 129, 131, 135, 138, 143, 154, 155, 159, 257, 259, 263, 266, 271, 282, 283, 287]
def C : List Nat := [15, 31, 27, 26, 10]
def mask : Nat := 271977573737189892067235388718813991711449689171575285320469630141747238792571355294564
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 9 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    9 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=9) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G342


namespace G343
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 58, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 0, 5, 1]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 18, 19, 23, 24, 25, 29, 30, 33, 35, 39, 42, 47, 50, 59, 62, 63, 65, 67, 71, 79, 90, 91, 95, 122, 129, 131, 135, 143, 154, 155, 159, 186, 257, 259, 263, 271, 282, 283, 287, 314]
def C : List Nat := [15, 31, 27, 26, 58]
def mask : Nat := 33374797708241675203512727214350526772890680691470163492024620221434009798366198460027258170980
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 9 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    9 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=9) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G343


namespace G344
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 58, 62]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 0, 5, 2]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 18, 19, 23, 24, 25, 29, 30, 33, 35, 39, 42, 47, 50, 56, 59, 63, 65, 67, 71, 79, 90, 91, 95, 122, 129, 131, 135, 143, 154, 155, 159, 186, 257, 259, 263, 271, 282, 283, 287, 314]
def C : List Nat := [15, 31, 27, 26, 58]
def mask : Nat := 33374797708241675203512727214350526772890680691470163492024620221434009798361658831602868711012
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 9 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    9 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=9) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G344


namespace G345
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 58, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 0, 5, 3]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 18, 19, 23, 24, 25, 29, 30, 33, 35, 39, 42, 47, 56, 59, 62, 63, 65, 67, 71, 79, 90, 91, 95, 122, 129, 131, 135, 143, 154, 155, 159, 186, 257, 259, 263, 271, 282, 283, 287, 314]
def C : List Nat := [15, 31, 27, 26, 58]
def mask : Nat := 33374797708241675203512727214350526772890680691470163492024620221434009798366269391721389256292
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 9 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    9 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=9) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G345


namespace G346
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 58, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 0, 5, 4]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 18, 19, 23, 24, 25, 29, 30, 33, 35, 39, 47, 50, 56, 59, 62, 63, 65, 67, 71, 79, 90, 91, 95, 122, 129, 131, 135, 143, 154, 155, 159, 186, 257, 259, 263, 271, 282, 283, 287, 314]
def C : List Nat := [15, 31, 27, 26, 58]
def mask : Nat := 33374797708241675203512727214350526772890680691470163492024620221434009798366270513223249587812
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 9 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    9 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=9) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G346

end Snake9.LocalWindow.ExtendedShare59
