import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G388
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 54, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 3, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 27, 29, 30, 33, 35, 38, 39, 46, 47, 50, 55, 58, 59, 60, 61, 65, 67, 71, 79, 95, 118, 126, 127, 129, 131, 135, 143, 159, 182, 190, 191, 257, 259, 263, 271, 287, 310, 318, 319]
def C : List Nat := [15, 31, 63, 62, 54]
def mask : Nat := 1604076202029114504007986932216513021293902167621561627426284716872682488580087207787430425553508
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
end G388


namespace G389
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 54, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 3, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 27, 29, 30, 33, 35, 38, 39, 46, 47, 52, 55, 58, 59, 60, 61, 65, 67, 71, 79, 95, 118, 126, 127, 129, 131, 135, 143, 159, 182, 190, 191, 257, 259, 263, 271, 287, 310, 318, 319]
def C : List Nat := [15, 31, 63, 62, 54]
def mask : Nat := 1604076202029114504007986932216513021293902167621561627426284716872682488580087211165130146081380
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
end G389


namespace G390
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 54, 38]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 3, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 27, 29, 30, 33, 35, 39, 46, 47, 50, 52, 55, 58, 59, 60, 61, 65, 67, 71, 79, 95, 118, 126, 127, 129, 131, 135, 143, 159, 182, 190, 191, 257, 259, 263, 271, 287, 310, 318, 319]
def C : List Nat := [15, 31, 63, 62, 54]
def mask : Nat := 1604076202029114504007986932216513021293902167621561627426284716872682488580087212290755175017060
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 6 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G390


namespace G391
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 54, 22]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 3, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 38, 39, 46, 47, 50, 52, 55, 58, 59, 60, 61, 65, 67, 71, 79, 95, 118, 126, 127, 129, 131, 135, 143, 159, 182, 190, 191, 257, 259, 263, 271, 287, 310, 318, 319]
def C : List Nat := [15, 31, 63, 62, 54]
def mask : Nat := 1604076202029114504007986932216513021293902167621561627426284716872682488580087212291030048729700
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
end G391


namespace G392
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 54, 118]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 3, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 27, 29, 30, 33, 35, 38, 39, 46, 47, 50, 52, 55, 58, 59, 60, 61, 65, 67, 71, 79, 95, 126, 127, 129, 131, 135, 143, 159, 182, 190, 191, 257, 259, 263, 271, 287, 310, 318, 319]
def C : List Nat := [15, 31, 63, 62, 54]
def mask : Nat := 1604076202029114504007986932216513021293902167621561627426284384565683542351118986339264982837860
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
end G392


namespace G393
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 46, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 4, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 38, 39, 42, 47, 54, 55, 58, 59, 60, 61, 65, 67, 71, 79, 95, 110, 126, 127, 129, 131, 135, 143, 159, 174, 190, 191, 257, 259, 263, 271, 287, 302, 318, 319]
def C : List Nat := [15, 31, 63, 62, 46]
def mask : Nat := 1601998425333253328199993117614335455569623563823101734924715501066479986045913821436820322937444
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
end G393


namespace G394
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 46, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 4, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 38, 39, 44, 47, 54, 55, 58, 59, 60, 61, 65, 67, 71, 79, 95, 110, 126, 127, 129, 131, 135, 143, 159, 174, 190, 191, 257, 259, 263, 271, 287, 302, 318, 319]
def C : List Nat := [15, 31, 63, 62, 46]
def mask : Nat := 1601998425333253328199993117614335455569623563823101734924715501066479986045913821450014462470756
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
end G394


namespace G396
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 46, 110]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 4, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 38, 39, 42, 44, 47, 54, 55, 58, 59, 60, 61, 65, 67, 71, 79, 95, 126, 127, 129, 131, 135, 143, 159, 174, 190, 191, 257, 259, 263, 271, 287, 302, 318, 319]
def C : List Nat := [15, 31, 63, 62, 46]
def mask : Nat := 1601998425333253328199993117614335455569623563823101734924715499768405771412206914321788426676836
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
end G396


namespace G408
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 57, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 2, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 27, 29, 30, 33, 35, 39, 41, 45, 47, 49, 53, 55, 59, 60, 62, 65, 67, 71, 79, 95, 121, 125, 127, 129, 131, 135, 143, 159, 185, 189, 191, 257, 259, 263, 271, 287, 313, 317, 319]
def C : List Nat := [15, 31, 63, 61, 57]
def mask : Nat := 1351679296417366339974981437639837429626239299930998372019978721527863984664185952669394579122788
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
end G408


namespace G409
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 57, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 2, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 27, 29, 30, 33, 35, 39, 41, 45, 47, 53, 55, 56, 59, 60, 62, 65, 67, 71, 79, 95, 121, 125, 127, 129, 131, 135, 143, 159, 185, 189, 191, 257, 259, 263, 271, 287, 313, 317, 319]
def C : List Nat := [15, 31, 63, 61, 57]
def mask : Nat := 1351679296417366339974981437639837429626239299930998372019978721527863984664186024164038663629412
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
end G409


namespace G410
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 57, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 2, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 27, 29, 30, 33, 35, 39, 45, 47, 49, 53, 55, 56, 59, 60, 62, 65, 67, 71, 79, 95, 121, 125, 127, 129, 131, 135, 143, 159, 185, 189, 191, 257, 259, 263, 271, 287, 313, 317, 319]
def C : List Nat := [15, 31, 63, 61, 57]
def mask : Nat := 1351679296417366339974981437639837429626239299930998372019978721527863984664186024724789593795172
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
end G410


namespace G411
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 57, 25]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 2, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 41, 45, 47, 49, 53, 55, 56, 59, 60, 62, 65, 67, 71, 79, 95, 121, 125, 127, 129, 131, 135, 143, 159, 185, 189, 191, 257, 259, 263, 271, 287, 313, 317, 319]
def C : List Nat := [15, 31, 63, 61, 57]
def mask : Nat := 1351679296417366339974981437639837429626239299930998372019978721527863984664186024726988583496292
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 6 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G411

end Snake9.LocalWindow.ExtendedShare59
