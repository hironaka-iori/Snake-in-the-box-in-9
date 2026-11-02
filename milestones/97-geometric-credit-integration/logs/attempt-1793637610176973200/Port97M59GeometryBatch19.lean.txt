import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G311
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 21, 53, 37]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 3, 5, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 20, 23, 25, 27, 28, 30, 33, 35, 39, 47, 49, 52, 55, 61, 63, 65, 67, 71, 79, 85, 93, 95, 117, 129, 131, 135, 143, 149, 157, 159, 181, 257, 259, 263, 271, 277, 285, 287, 309]
def C : List Nat := [15, 31, 29, 21, 53]
def mask : Nat := 1042962730956923498302754800171047475410077619964069287891568370738429242486599510579102771812
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 16 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    16 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=16) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G311


namespace G312
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 21, 53, 117]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 3, 5, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 20, 23, 25, 27, 28, 30, 33, 35, 37, 39, 47, 49, 52, 55, 61, 63, 65, 67, 71, 79, 85, 93, 95, 129, 131, 135, 143, 149, 157, 159, 181, 257, 259, 263, 271, 277, 285, 287, 309]
def C : List Nat := [15, 31, 29, 21, 53]
def mask : Nat := 1042962730956923498302754800171047475410077619964069287891402217238956128002486534834006682212
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
end G312


namespace G313
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 0, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 44, 45, 47, 52, 53, 56, 57, 63, 65, 67, 71, 79, 93, 95, 124, 125, 129, 131, 135, 143, 157, 159, 188, 189, 257, 259, 263, 271, 285, 287, 316, 317]
def C : List Nat := [15, 31, 29, 61, 60]
def mask : Nat := 400497569546001473459671664380631534607779775465251760679474426120333479903114665523571463973476
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
end G313


namespace G314
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 60, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 0, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 44, 45, 47, 52, 53, 57, 62, 63, 65, 67, 71, 79, 93, 95, 124, 125, 129, 131, 135, 143, 157, 159, 188, 189, 257, 259, 263, 271, 285, 287, 316, 317]
def C : List Nat := [15, 31, 29, 61, 60]
def mask : Nat := 400497569546001473459671664380631534607779775465251760679474426120333479903119205151995853433444
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
end G314


namespace G315
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 60, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 0, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 44, 45, 47, 53, 56, 57, 62, 63, 65, 67, 71, 79, 93, 95, 124, 125, 129, 131, 135, 143, 157, 159, 188, 189, 257, 259, 263, 271, 285, 287, 316, 317]
def C : List Nat := [15, 31, 29, 61, 60]
def mask : Nat := 400497569546001473459671664380631534607779775465251760679474426120333479903119272705990263990884
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
end G315


namespace G316
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 60, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 0, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 45, 47, 52, 53, 56, 57, 62, 63, 65, 67, 71, 79, 93, 95, 124, 125, 129, 131, 135, 143, 157, 159, 188, 189, 257, 259, 263, 271, 285, 287, 316, 317]
def C : List Nat := [15, 31, 29, 61, 60]
def mask : Nat := 400497569546001473459671664380631534607779775465251760679474426120333479903119277191997705316964
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
end G316


namespace G317
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 60, 124]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 0, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 44, 45, 47, 52, 53, 56, 57, 62, 63, 65, 67, 71, 79, 93, 95, 125, 129, 131, 135, 143, 157, 159, 188, 189, 257, 259, 263, 271, 285, 287, 316, 317]
def C : List Nat := [15, 31, 29, 61, 60]
def mask : Nat := 400497569546001473459671664380631534607779775465251760679453158472400921249152816296625405848164
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
end G317


namespace G318
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 57, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 2, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 41, 45, 47, 49, 53, 59, 60, 63, 65, 67, 71, 79, 93, 95, 121, 125, 129, 131, 135, 143, 157, 159, 185, 189, 257, 259, 263, 271, 285, 287, 313, 317]
def C : List Nat := [15, 31, 29, 61, 57]
def mask : Nat := 283685778519076703328693914824484153340101092897718353218704709266533180570136143835409632881252
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 29 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    29 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=29) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G318


namespace G319
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 57, 59]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 2, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 41, 45, 47, 49, 53, 56, 60, 63, 65, 67, 71, 79, 93, 95, 121, 125, 129, 131, 135, 143, 157, 159, 185, 189, 257, 259, 263, 271, 285, 287, 313, 317]
def C : List Nat := [15, 31, 29, 61, 57]
def mask : Nat := 283685778519076703328693914824484153340101092897718353218704709266533180570135639432251367385700
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 29 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    29 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=29) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G319


namespace G320
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 57, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 2, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 41, 45, 47, 53, 56, 59, 60, 63, 65, 67, 71, 79, 93, 95, 121, 125, 129, 131, 135, 143, 157, 159, 185, 189, 257, 259, 263, 271, 285, 287, 313, 317]
def C : List Nat := [15, 31, 29, 61, 57]
def mask : Nat := 283685778519076703328693914824484153340101092897718353218704709266533180570136215330053717387876
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
end G320


namespace G321
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 57, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 2, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 45, 47, 49, 53, 56, 59, 60, 63, 65, 67, 71, 79, 93, 95, 121, 125, 129, 131, 135, 143, 157, 159, 185, 189, 257, 259, 263, 271, 285, 287, 313, 317]
def C : List Nat := [15, 31, 29, 61, 57]
def mask : Nat := 283685778519076703328693914824484153340101092897718353218704709266533180570136215890804647553636
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
end G321


namespace G322
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 61, 57, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 5, 2, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 25, 27, 28, 30, 33, 35, 39, 41, 45, 47, 49, 53, 56, 59, 60, 63, 65, 67, 71, 79, 93, 95, 125, 129, 131, 135, 143, 157, 159, 185, 189, 257, 259, 263, 271, 285, 287, 313, 317]
def C : List Nat := [15, 31, 29, 61, 57]
def mask : Nat := 283685778519076703328693914824484153340101092897718353218702050810541610738390408278883110120036
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 29 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    29 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=29) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G322

end Snake9.LocalWindow.ExtendedShare59
