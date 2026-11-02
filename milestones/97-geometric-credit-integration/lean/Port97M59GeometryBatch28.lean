import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G455
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 53, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 1, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 27, 29, 30, 33, 35, 37, 39, 47, 49, 51, 54, 59, 61, 62, 65, 67, 71, 79, 95, 117, 119, 127, 129, 131, 135, 143, 159, 181, 183, 191, 257, 259, 263, 271, 287, 309, 311, 319]
def C : List Nat := [15, 31, 63, 55, 53]
def mask : Nat := 1073208330308536754037739838251521797497041012024467838162608057242465056790029328449877192632932
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 28 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    28 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=28) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G455


namespace G456
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 53, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 1, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 27, 29, 30, 33, 35, 37, 39, 47, 51, 52, 54, 59, 61, 62, 65, 67, 71, 79, 95, 117, 119, 127, 129, 131, 135, 143, 159, 181, 183, 191, 257, 259, 263, 271, 287, 309, 311, 319]
def C : List Nat := [15, 31, 63, 55, 53]
def mask : Nat := 1073208330308536754037739838251521797497041012024467838162608057242465056790029332390526866582116
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
end G456


namespace G457
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 53, 37]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 1, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 27, 29, 30, 33, 35, 39, 47, 49, 51, 52, 54, 59, 61, 62, 65, 67, 71, 79, 95, 117, 119, 127, 129, 131, 135, 143, 159, 181, 183, 191, 257, 259, 263, 271, 287, 309, 311, 319]
def C : List Nat := [15, 31, 63, 55, 53]
def mask : Nat := 1073208330308536754037739838251521797497041012024467838162608057242465056790029332953339381049956
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
end G457


namespace G458
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 53, 21]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 1, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 37, 39, 47, 49, 51, 52, 54, 59, 61, 62, 65, 67, 71, 79, 95, 117, 119, 127, 129, 131, 135, 143, 159, 181, 183, 191, 257, 259, 263, 271, 287, 309, 311, 319]
def C : List Nat := [15, 31, 63, 55, 53]
def mask : Nat := 1073208330308536754037739838251521797497041012024467838162608057242465056790029332953476817906276
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
end G458


namespace G459
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 53, 117]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 1, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 27, 29, 30, 33, 35, 37, 39, 47, 49, 51, 52, 54, 59, 61, 62, 65, 67, 71, 79, 95, 119, 127, 129, 131, 135, 143, 159, 181, 183, 191, 257, 259, 263, 271, 287, 309, 311, 319]
def C : List Nat := [15, 31, 63, 55, 53]
def mask : Nat := 1073208330308536754037739838251521797497041012024467838162607891088965583675545219977594284960356
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 28 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    28 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=28) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G459


namespace G463
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 119, 118]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 6, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 51, 53, 54, 59, 61, 62, 65, 67, 71, 79, 87, 95, 103, 115, 117, 127, 129, 131, 135, 143, 159, 183, 191, 247, 257, 259, 263, 271, 287, 311, 319, 375]
def C : List Nat := [15, 31, 63, 55, 119]
def mask : Nat := 76957043352332968283647868084246492874842916245975654596102767851091665929546420987078216316910259701843168488036
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
end G463


namespace G464
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 119, 117]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 6, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 51, 53, 54, 59, 61, 62, 65, 67, 71, 79, 87, 95, 103, 115, 118, 127, 129, 131, 135, 143, 159, 183, 191, 247, 257, 259, 263, 271, 287, 311, 319, 375]
def C : List Nat := [15, 31, 63, 55, 119]
def mask : Nat := 76957043352332968283647868084246492874842916245975654596102767851091665929546587140577689431394372677725703531108
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
end G464


namespace G465
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 119, 115]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 6, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 51, 53, 54, 59, 61, 62, 65, 67, 71, 79, 87, 95, 103, 117, 118, 127, 129, 131, 135, 143, 159, 183, 191, 247, 257, 259, 263, 271, 287, 311, 319, 375]
def C : List Nat := [15, 31, 63, 55, 119]
def mask : Nat := 76957043352332968283647868084246492874842916245975654596102767851091665929546711755702294267257457409637604813412
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
end G465


namespace G466
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 119, 103]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 6, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 51, 53, 54, 59, 61, 62, 65, 67, 71, 79, 87, 95, 115, 117, 118, 127, 129, 131, 135, 143, 159, 183, 191, 247, 257, 259, 263, 271, 287, 311, 319, 375]
def C : List Nat := [15, 31, 63, 55, 119]
def mask : Nat := 76957043352332968283647868084246492874842916245975654596102767851091665929546753283935957744052650441634612931172
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
end G466


namespace G467
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 119, 87]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 6, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 51, 53, 54, 59, 61, 62, 65, 67, 71, 79, 95, 103, 115, 117, 118, 127, 129, 131, 135, 143, 159, 183, 191, 247, 257, 259, 263, 271, 287, 311, 319, 375]
def C : List Nat := [15, 31, 63, 55, 119]
def mask : Nat := 76957043352332968283647868084246492874842916245975654596102767851091665929546753294077007803373574981073876183652
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
end G467


namespace G468
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 119, 247]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 6, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 51, 53, 54, 59, 61, 62, 65, 67, 71, 79, 87, 95, 103, 115, 117, 118, 127, 129, 131, 135, 143, 159, 183, 191, 257, 259, 263, 271, 287, 311, 319, 375]
def C : List Nat := [15, 31, 63, 55, 119]
def mask : Nat := 76957043352332968283647868084246492874616759821684021401916105770996572359520835355277083319238920059842783242852
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
end G468


namespace G487
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 119, 118]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 3, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 55, 59, 61, 62, 65, 67, 71, 79, 87, 95, 103, 111, 115, 117, 123, 125, 126, 129, 131, 135, 143, 159, 191, 247, 255, 257, 259, 263, 271, 287, 319, 375, 383]
def C : List Nat := [15, 31, 63, 127, 119]
def mask : Nat := 19777960141549572574418996068476520367967930819327494679808189295243741741052585137734786241690176738273073539213924
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
end G487

end Snake9.LocalWindow.ExtendedShare59
