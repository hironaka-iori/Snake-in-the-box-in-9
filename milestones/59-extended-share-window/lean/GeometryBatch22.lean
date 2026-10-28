import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G347
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 58, 122]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 0, 5, 6]
def D : List Nat := [2, 5, 6, 9, 10, 11, 13, 14, 17, 18, 19, 23, 24, 25, 29, 30, 33, 35, 39, 42, 47, 50, 56, 59, 62, 63, 65, 67, 71, 79, 90, 91, 95, 129, 131, 135, 143, 154, 155, 159, 186, 257, 259, 263, 271, 282, 283, 287, 314]
def C : List Nat := [15, 31, 27, 26, 58]
def mask : Nat := 33374797708241675203512727214350526772890680691470163492019303309450870134874655289380174720612
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
end G347


namespace G355
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 58, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 0, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 42, 43, 47, 50, 51, 57, 62, 63, 65, 67, 71, 79, 91, 95, 122, 123, 129, 131, 135, 143, 155, 159, 186, 187, 257, 259, 263, 271, 283, 287, 314, 315]
def C : List Nat := [15, 31, 27, 59, 58]
def mask : Nat := 100124392572999439709454239248471182727127280817753933007458319266214474976991120184120439368292
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
end G355


namespace G356
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 58, 62]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 0, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 42, 43, 47, 50, 51, 56, 57, 63, 65, 67, 71, 79, 91, 95, 122, 123, 129, 131, 135, 143, 155, 159, 186, 187, 257, 259, 263, 271, 283, 287, 314, 315]
def C : List Nat := [15, 31, 27, 59, 58]
def mask : Nat := 100124392572999439709454239248471182727127280817753933007458319266214474976986580555696049908324
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
end G356


namespace G357
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 58, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 0, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 42, 43, 47, 51, 56, 57, 62, 63, 65, 67, 71, 79, 91, 95, 122, 123, 129, 131, 135, 143, 155, 159, 186, 187, 257, 259, 263, 271, 283, 287, 314, 315]
def C : List Nat := [15, 31, 27, 59, 58]
def mask : Nat := 100124392572999439709454239248471182727127280817753933007458319266214474976991191115814570453604
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
end G357


namespace G358
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 58, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 0, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 50, 51, 56, 57, 62, 63, 65, 67, 71, 79, 91, 95, 122, 123, 129, 131, 135, 143, 155, 159, 186, 187, 257, 259, 263, 271, 283, 287, 314, 315]
def C : List Nat := [15, 31, 27, 59, 58]
def mask : Nat := 100124392572999439709454239248471182727127280817753933007458319266214474976991192237316430785124
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
end G358


namespace G359
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 58, 122]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 0, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 42, 43, 47, 50, 51, 56, 57, 62, 63, 65, 67, 71, 79, 91, 95, 123, 129, 131, 135, 143, 155, 159, 186, 187, 257, 259, 263, 271, 283, 287, 314, 315]
def C : List Nat := [15, 31, 27, 59, 58]
def mask : Nat := 100124392572999439709454239248471182727127280817753933007453002354231335313499577013473355917924
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
end G359


namespace G360
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 57, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 1, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 41, 43, 47, 49, 51, 58, 61, 63, 65, 67, 71, 79, 91, 95, 121, 123, 129, 131, 135, 143, 155, 159, 185, 187, 257, 259, 263, 271, 283, 287, 313, 315]
def C : List Nat := [15, 31, 27, 59, 57]
def mask : Nat := 83436993854867329690743132169021556831744611879534874798776931144243003643706096328065497590372
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 33 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    33 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=33) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G360


namespace G361
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 57, 61]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 1, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 41, 43, 47, 49, 51, 56, 58, 63, 65, 67, 71, 79, 91, 95, 121, 123, 129, 131, 135, 143, 155, 159, 185, 187, 257, 259, 263, 271, 283, 287, 313, 315]
def C : List Nat := [15, 31, 27, 59, 57]
def mask : Nat := 83436993854867329690743132169021556831744611879534874798776931144243003643703862542650321824356
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 32 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    32 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=32) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G361


namespace G362
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 57, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 1, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 41, 43, 47, 51, 56, 58, 61, 63, 65, 67, 71, 79, 91, 95, 121, 123, 129, 131, 135, 143, 155, 159, 185, 187, 257, 259, 263, 271, 283, 287, 313, 315]
def C : List Nat := [15, 31, 27, 59, 57]
def mask : Nat := 83436993854867329690743132169021556831744611879534874798776931144243003643706167822709582096996
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
end G362


namespace G363
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 57, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 1, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 49, 51, 56, 58, 61, 63, 65, 67, 71, 79, 91, 95, 121, 123, 129, 131, 135, 143, 155, 159, 185, 187, 257, 259, 263, 271, 283, 287, 313, 315]
def C : List Nat := [15, 31, 27, 59, 57]
def mask : Nat := 83436993854867329690743132169021556831744611879534874798776931144243003643706168383460512262756
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
end G363


namespace G364
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 57, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 1, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 41, 43, 47, 49, 51, 56, 58, 61, 63, 65, 67, 71, 79, 91, 95, 123, 129, 131, 135, 143, 155, 159, 185, 187, 257, 259, 263, 271, 283, 287, 313, 315]
def C : List Nat := [15, 31, 27, 59, 57]
def mask : Nat := 83436993854867329690743132169021556831744611879534874798774272688251433811960360771538974829156
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 33 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    33 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=33) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G364


namespace G365
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 51, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 3, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 49, 55, 57, 58, 63, 65, 67, 71, 79, 91, 95, 115, 123, 129, 131, 135, 143, 155, 159, 179, 187, 257, 259, 263, 271, 283, 287, 307, 315]
def C : List Nat := [15, 31, 27, 59, 51]
def mask : Nat := 67010335741706033891074386137688331340977297143475489374606189711677336550003651523880914938468
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
end G365

end Snake9.LocalWindow.ExtendedShare59
