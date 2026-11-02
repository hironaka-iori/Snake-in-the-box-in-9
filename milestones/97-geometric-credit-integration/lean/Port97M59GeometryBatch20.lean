import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G323
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 53, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 3, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 37, 39, 45, 47, 49, 55, 57, 60, 63, 65, 67, 71, 79, 93, 95, 117, 125, 129, 131, 135, 143, 157, 159, 181, 189, 257, 259, 263, 271, 285, 287, 309, 317]
def C : List Nat := [15, 31, 29, 61, 53]
def mask : Nat := 268041342220827850186152251937500129063179840768137986148065907902184926195183055793989559675492
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 44 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    44 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=44) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G323


namespace G324
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 53, 55]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 3, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 37, 39, 45, 47, 49, 52, 57, 60, 63, 65, 67, 71, 79, 93, 95, 117, 125, 129, 131, 135, 143, 157, 159, 181, 189, 257, 259, 263, 271, 285, 287, 309, 317]
def C : List Nat := [15, 31, 29, 61, 53]
def mask : Nat := 268041342220827850186152251937500129063179840768137986148065907902184926195183024268792168082020
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 37 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    37 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=37) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G324


namespace G325
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 53, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 3, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 37, 39, 45, 47, 52, 55, 57, 60, 63, 65, 67, 71, 79, 93, 95, 117, 125, 129, 131, 135, 143, 157, 159, 181, 189, 257, 259, 263, 271, 285, 287, 309, 317]
def C : List Nat := [15, 31, 29, 61, 53]
def mask : Nat := 268041342220827850186152251937500129063179840768137986148065907902184926195183059734639233624676
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 38 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    38 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=38) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G325


namespace G326
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 53, 37]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 3, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 45, 47, 49, 52, 55, 57, 60, 63, 65, 67, 71, 79, 93, 95, 117, 125, 129, 131, 135, 143, 157, 159, 181, 189, 257, 259, 263, 271, 285, 287, 309, 317]
def C : List Nat := [15, 31, 29, 61, 53]
def mask : Nat := 268041342220827850186152251937500129063179840768137986148065907902184926195183060297451748092516
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 27 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    27 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=27) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G326


namespace G327
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 53, 117]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 3, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 37, 39, 45, 47, 49, 52, 55, 57, 60, 63, 65, 67, 71, 79, 93, 95, 125, 129, 131, 135, 143, 157, 159, 181, 189, 257, 259, 263, 271, 285, 287, 309, 317]
def C : List Nat := [15, 31, 29, 61, 53]
def mask : Nat := 268041342220827850186152251937500129063179840768137986148065741748685453080698947321706652002916
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 44 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    44 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=44) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G327


namespace G328
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 45, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 4, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 37, 39, 41, 47, 53, 57, 60, 63, 65, 67, 71, 79, 93, 95, 109, 125, 129, 131, 135, 143, 157, 159, 173, 189, 257, 259, 263, 271, 285, 287, 301, 317]
def C : List Nat := [15, 31, 29, 61, 45]
def mask : Nat := 267002453872897262282155344636411346201040538868908039897281299999083674928096326589887491500644
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 25 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    25 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=25) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G328


namespace G329
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 45, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 4, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 37, 39, 44, 47, 53, 57, 60, 63, 65, 67, 71, 79, 93, 95, 109, 125, 129, 131, 135, 143, 157, 159, 173, 189, 257, 259, 263, 271, 285, 287, 301, 317]
def C : List Nat := [15, 31, 29, 61, 45]
def mask : Nat := 267002453872897262282155344636411346201040538868908039897281299999083674928096326605280654289508
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 19 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    19 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=19) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G329


namespace G330
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 45, 37]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 4, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 41, 44, 47, 53, 57, 60, 63, 65, 67, 71, 79, 93, 95, 109, 125, 129, 131, 135, 143, 157, 159, 173, 189, 257, 259, 263, 271, 285, 287, 301, 317]
def C : List Nat := [15, 31, 29, 61, 45]
def mask : Nat := 267002453872897262282155344636411346201040538868908039897281299999083674928096326607342238591588
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 18 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    18 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=18) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G330


namespace G331
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 45, 109]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 4, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 37, 39, 41, 44, 47, 53, 57, 60, 63, 65, 67, 71, 79, 93, 95, 125, 129, 131, 135, 143, 157, 159, 173, 189, 257, 259, 263, 271, 285, 287, 301, 317]
def C : List Nat := [15, 31, 29, 61, 45]
def mask : Nat := 267002453872897262282155344636411346201040538868908039897281299350046567611242873041167636392548
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 25 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    25 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=25) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G331


namespace G332
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 125, 124]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 6, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 79, 93, 95, 109, 117, 121, 127, 129, 131, 135, 143, 157, 159, 189, 253, 257, 259, 263, 271, 285, 287, 317, 381]
def C : List Nat := [15, 31, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392318896318959424227707879885366201472616300504928963826800673563789281642097531291331172
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
end G332


namespace G333
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 125, 127]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 6, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 79, 93, 95, 109, 117, 121, 124, 129, 131, 135, 143, 157, 159, 189, 253, 257, 259, 263, 271, 285, 287, 317, 381]
def C : List Nat := [15, 31, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392318896318959424227707879885366201472616300504928814953265145653211516415706779892738660
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
end G333


namespace G334
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 125, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 6, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 79, 93, 95, 109, 117, 124, 127, 129, 131, 135, 143, 157, 159, 189, 253, 257, 259, 263, 271, 285, 287, 317, 381]
def C : List Nat := [15, 31, 29, 61, 125]
def mask : Nat := 4925250774549309901801878392318896318959424227707879885366201472616300504928982435992614552611502295396375216155236
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
end G334

end Snake9.LocalWindow.ExtendedShare59
