import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G366
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 51, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 3, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 50, 55, 57, 58, 63, 65, 67, 71, 79, 91, 95, 115, 123, 129, 131, 135, 143, 155, 159, 179, 187, 257, 259, 263, 271, 283, 287, 307, 315]
def C : List Nat := [15, 31, 27, 59, 51]
def mask : Nat := 67010335741706033891074386137688331340977297143475489374606189711677336550003652086830868359780
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
end G366


namespace G367
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 51, 55]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 3, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 49, 50, 57, 58, 63, 65, 67, 71, 79, 91, 95, 115, 123, 129, 131, 135, 143, 155, 159, 179, 187, 257, 259, 263, 271, 283, 287, 307, 315]
def C : List Nat := [15, 31, 27, 59, 51]
def mask : Nat := 67010335741706033891074386137688331340977297143475489374606189711677336550003616620983802817124
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
end G367


namespace G368
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 51, 115]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 3, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 49, 50, 55, 57, 58, 63, 65, 67, 71, 79, 91, 95, 123, 129, 131, 135, 143, 155, 159, 179, 187, 257, 259, 263, 271, 283, 287, 307, 315]
def C : List Nat := [15, 31, 27, 59, 51]
def mask : Nat := 67010335741706033891074386137688331340977297143475489374606148173302468271382624405810188020324
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
end G368


namespace G369
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 43, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 4, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 41, 47, 51, 57, 58, 63, 65, 67, 71, 79, 91, 95, 107, 123, 129, 131, 135, 143, 155, 159, 171, 187, 257, 259, 263, 271, 283, 287, 299, 315]
def C : List Nat := [15, 31, 27, 59, 43]
def mask : Nat := 66750613654723386915075159312416135625442471668668002811910037735902023733231941780694436047460
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
end G369


namespace G370
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 43, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 4, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 42, 47, 51, 57, 58, 63, 65, 67, 71, 79, 91, 95, 107, 123, 129, 131, 135, 143, 155, 159, 171, 187, 257, 259, 263, 271, 283, 287, 299, 315]
def C : List Nat := [15, 31, 27, 59, 43]
def mask : Nat := 66750613654723386915075159312416135625442471668668002811910037735902023733231941782893459303012
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
end G370


namespace G371
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 43, 107]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 4, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 41, 42, 47, 51, 57, 58, 63, 65, 67, 71, 79, 91, 95, 123, 129, 131, 135, 143, 155, 159, 171, 187, 257, 259, 263, 271, 283, 287, 299, 315]
def C : List Nat := [15, 31, 27, 59, 43]
def mask : Nat := 66750613654723386915075159312416135625442471668668002811910037573642746904018578393514472270436
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
end G371


namespace G372
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 123, 122]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 6, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 51, 57, 58, 63, 65, 67, 71, 79, 91, 95, 107, 115, 121, 127, 129, 131, 135, 143, 155, 159, 187, 251, 257, 259, 263, 271, 283, 287, 315, 379]
def C : List Nat := [15, 31, 27, 59, 123]
def mask : Nat := 1231312693637327475450469598266223151084392380080283270416732705105516119069960269165888525246136391844367811897956
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
end G372


namespace G373
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 123, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 6, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 51, 57, 58, 63, 65, 67, 71, 79, 91, 95, 107, 115, 122, 127, 129, 131, 135, 143, 155, 159, 187, 251, 257, 259, 263, 271, 283, 287, 315, 379]
def C : List Nat := [15, 31, 27, 59, 123]
def mask : Nat := 1231312693637327475450469598266223151084392380080283270416732705105516119069962927621880095077882199458488372587108
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
end G373


namespace G374
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 123, 127]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 6, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 51, 57, 58, 63, 65, 67, 71, 79, 91, 95, 107, 115, 121, 122, 129, 131, 135, 143, 155, 159, 187, 251, 257, 259, 263, 271, 283, 287, 315, 379]
def C : List Nat := [15, 31, 27, 59, 123]
def mask : Nat := 1231312693637327475450469598266223151084392380080283270416732705105516119069795444894411195677896319768893049170532
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
end G374


namespace G375
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 123, 115]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 6, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 51, 57, 58, 63, 65, 67, 71, 79, 91, 95, 107, 121, 122, 127, 129, 131, 135, 143, 155, 159, 187, 251, 257, 259, 263, 271, 283, 287, 315, 379]
def C : List Nat := [15, 31, 27, 59, 123]
def mask : Nat := 1231312693637327475450469598266223151084392380080283270416732705105516119069965544539496796631006978828638299515492
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
end G375


namespace G376
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 123, 107]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 6, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 51, 57, 58, 63, 65, 67, 71, 79, 91, 95, 115, 121, 122, 127, 129, 131, 135, 143, 155, 159, 187, 251, 257, 259, 263, 271, 283, 287, 315, 379]
def C : List Nat := [15, 31, 27, 59, 123]
def mask : Nat := 1231312693637327475450469598266223151084392380080283270416732705105516119069965585915612388080414643681030922988132
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
end G376


namespace G377
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 123, 251]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 6, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 26, 29, 30, 33, 35, 39, 43, 47, 51, 57, 58, 63, 65, 67, 71, 79, 91, 95, 107, 115, 121, 122, 127, 129, 131, 135, 143, 155, 159, 187, 257, 259, 263, 271, 283, 287, 315, 379]
def C : List Nat := [15, 31, 27, 59, 123]
def mask : Nat := 1231312693637327475450469598266223151080773877291617139309746111823994621949550899057070397283394957572361647975012
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
end G377

end Snake9.LocalWindow.ExtendedShare59
