import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G412
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 57, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 2, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 27, 29, 30, 33, 35, 39, 41, 45, 47, 49, 53, 55, 56, 59, 60, 62, 65, 67, 71, 79, 95, 125, 127, 129, 131, 135, 143, 159, 185, 189, 191, 257, 259, 263, 271, 287, 313, 317, 319]
def C : List Nat := [15, 31, 63, 61, 57]
def mask : Nat := 1351679296417366339974981437639837429626239299930998372019976063071872414832440217112868056361572
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
end G412


namespace G413
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 53, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 3, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 27, 29, 30, 33, 35, 37, 39, 45, 47, 49, 55, 57, 59, 60, 62, 65, 67, 71, 79, 95, 117, 125, 127, 129, 131, 135, 143, 159, 181, 189, 191, 257, 259, 263, 271, 287, 309, 317, 319]
def C : List Nat := [15, 31, 63, 61, 53]
def mask : Nat := 1336034860119117486832439774752853405349318047801418004949339920163515730289233405059929758919268
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
end G413


namespace G414
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 53, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 3, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 27, 29, 30, 33, 35, 37, 39, 45, 47, 52, 55, 57, 59, 60, 62, 65, 67, 71, 79, 95, 117, 125, 127, 129, 131, 135, 143, 159, 181, 189, 191, 257, 259, 263, 271, 287, 309, 317, 319]
def C : List Nat := [15, 31, 63, 61, 53]
def mask : Nat := 1336034860119117486832439774752853405349318047801418004949339920163515730289233409000579432868452
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
end G414


namespace G415
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 53, 37]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 3, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 27, 29, 30, 33, 35, 39, 45, 47, 49, 52, 55, 57, 59, 60, 62, 65, 67, 71, 79, 95, 117, 125, 127, 129, 131, 135, 143, 159, 181, 189, 191, 257, 259, 263, 271, 287, 309, 317, 319]
def C : List Nat := [15, 31, 63, 61, 53]
def mask : Nat := 1336034860119117486832439774752853405349318047801418004949339920163515730289233409563391947336292
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
end G415


namespace G416
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 53, 21]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 3, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 37, 39, 45, 47, 49, 52, 55, 57, 59, 60, 62, 65, 67, 71, 79, 95, 117, 125, 127, 129, 131, 135, 143, 159, 181, 189, 191, 257, 259, 263, 271, 287, 309, 317, 319]
def C : List Nat := [15, 31, 63, 61, 53]
def mask : Nat := 1336034860119117486832439774752853405349318047801418004949339920163515730289233409563529384192612
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 15 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    15 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=15) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G416


namespace G417
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 53, 117]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 3, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 27, 29, 30, 33, 35, 37, 39, 45, 47, 49, 52, 55, 57, 59, 60, 62, 65, 67, 71, 79, 95, 125, 127, 129, 131, 135, 143, 159, 181, 189, 191, 257, 259, 263, 271, 287, 309, 317, 319]
def C : List Nat := [15, 31, 63, 61, 53]
def mask : Nat := 1336034860119117486832439774752853405349318047801418004949339754010016257174749296587646851246692
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
end G417


namespace G418
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 45, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 4, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 37, 39, 41, 47, 53, 55, 57, 59, 60, 62, 65, 67, 71, 79, 95, 109, 125, 127, 129, 131, 135, 143, 159, 173, 189, 191, 257, 259, 263, 271, 287, 301, 317, 319]
def C : List Nat := [15, 31, 63, 61, 45]
def mask : Nat := 1334995971771186898928442867451764622487178745902188058698555312260414479022146711884624707611236
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=7) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G418


namespace G419
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 45, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 4, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 37, 39, 44, 47, 53, 55, 57, 59, 60, 62, 65, 67, 71, 79, 95, 109, 125, 127, 129, 131, 135, 143, 159, 173, 189, 191, 257, 259, 263, 271, 287, 301, 317, 319]
def C : List Nat := [15, 31, 63, 61, 45]
def mask : Nat := 1334995971771186898928442867451764622487178745902188058698555312260414479022146711900017870400100
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=7) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G419


namespace G421
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 45, 109]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 4, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 37, 39, 41, 44, 47, 53, 55, 57, 59, 60, 62, 65, 67, 71, 79, 95, 125, 127, 129, 131, 135, 143, 159, 173, 189, 191, 257, 259, 263, 271, 287, 301, 317, 319]
def C : List Nat := [15, 31, 63, 61, 45]
def mask : Nat := 1334995971771186898928442867451764622487178745902188058698555311611377371705293258335904852503140
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 7 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=7) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G421


namespace G428
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 58, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 0, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 26, 27, 29, 30, 33, 35, 39, 42, 43, 47, 50, 51, 55, 57, 61, 62, 65, 67, 71, 79, 95, 122, 123, 127, 129, 131, 135, 143, 159, 186, 187, 191, 257, 259, 263, 271, 287, 314, 315, 319]
def C : List Nat := [15, 31, 63, 59, 58]
def mask : Nat := 1168117910517913129769159259765891544777029941610588731724483452186177799998075189834763148618340
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
end G428


namespace G429
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 58, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 0, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 26, 27, 29, 30, 33, 35, 39, 42, 43, 47, 51, 55, 56, 57, 61, 62, 65, 67, 71, 79, 95, 122, 123, 127, 129, 131, 135, 143, 159, 186, 187, 191, 257, 259, 263, 271, 287, 314, 315, 319]
def C : List Nat := [15, 31, 63, 59, 58]
def mask : Nat := 1168117910517913129769159259765891544777029941610588731724483452186177799998075260766457279703652
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
end G429


namespace G430
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 58, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 0, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 26, 27, 29, 30, 33, 35, 39, 43, 47, 50, 51, 55, 56, 57, 61, 62, 65, 67, 71, 79, 95, 122, 123, 127, 129, 131, 135, 143, 159, 186, 187, 191, 257, 259, 263, 271, 287, 314, 315, 319]
def C : List Nat := [15, 31, 63, 59, 58]
def mask : Nat := 1168117910517913129769159259765891544777029941610588731724483452186177799998075261887959140035172
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
end G430

end Snake9.LocalWindow.ExtendedShare59
