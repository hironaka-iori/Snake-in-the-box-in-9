import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G203
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 25, 57, 41]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 2, 5, 4]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 24, 27, 28, 31, 33, 35, 39, 45, 47, 49, 56, 59, 61, 65, 67, 71, 77, 79, 89, 93, 121, 129, 131, 135, 141, 143, 153, 157, 185, 257, 259, 263, 269, 271, 281, 285, 313]
def C : List Nat := [15, 13, 29, 25, 57]
def mask : Nat := 16687398784187611177669370711710848647724198819891964097416646600997408450269080817696313596516
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
end G203


namespace G204
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 25, 57, 121]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 2, 5, 6]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 24, 27, 28, 31, 33, 35, 39, 41, 45, 47, 49, 56, 59, 61, 65, 67, 71, 77, 79, 89, 93, 129, 131, 135, 141, 143, 153, 157, 185, 257, 259, 263, 269, 271, 281, 285, 313]
def C : List Nat := [15, 13, 29, 25, 57]
def mask : Nat := 16687398784187611177669370711710848647724198819891964097413988145005838618523273205774776162916
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
end G204


namespace G205
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 21, 20, 22]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 3, 0, 1]
def D : List Nat := [2, 4, 5, 6, 9, 11, 12, 14, 16, 17, 19, 23, 25, 28, 31, 33, 35, 39, 45, 47, 52, 53, 61, 65, 67, 71, 77, 79, 84, 85, 93, 129, 131, 135, 141, 143, 148, 149, 157, 257, 259, 263, 269, 271, 276, 277, 285]
def C : List Nat := [15, 13, 29, 21, 20]
def mask : Nat := 62534413791799129691219698046223901863373195947181137387618793609475009639503675218548
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
end G205


namespace G206
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 21, 20, 52]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 3, 0, 5]
def D : List Nat := [2, 4, 5, 6, 9, 11, 12, 14, 16, 17, 19, 22, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 61, 65, 67, 71, 77, 79, 84, 85, 93, 129, 131, 135, 141, 143, 148, 149, 157, 257, 259, 263, 269, 271, 276, 277, 285]
def C : List Nat := [15, 13, 29, 21, 20]
def mask : Nat := 62534413791799129691219698046223901863373195947181137387618793609475005135904052042356
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
end G206


namespace G207
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 21, 53, 52]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 3, 5, 0]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 23, 25, 28, 31, 33, 35, 37, 39, 45, 47, 49, 55, 61, 65, 67, 71, 77, 79, 85, 93, 117, 129, 131, 135, 141, 143, 149, 157, 181, 257, 259, 263, 269, 271, 277, 285, 309]
def C : List Nat := [15, 13, 29, 21, 53]
def mask : Nat := 1042962482296253862204465816752833295508848740346379845859788935193488377891053842605790616164
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
end G207


namespace G208
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 21, 53, 55]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 3, 5, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 23, 25, 28, 31, 33, 35, 37, 39, 45, 47, 49, 52, 61, 65, 67, 71, 77, 79, 85, 93, 117, 129, 131, 135, 141, 143, 149, 157, 181, 257, 259, 263, 269, 271, 277, 285, 309]
def C : List Nat := [15, 13, 29, 21, 53]
def mask : Nat := 1042962482296253862204465816752833295508848740346379845859788935193488377891022317408399022692
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
end G208


namespace G209
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 21, 53, 49]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 3, 5, 2]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 23, 25, 28, 31, 33, 35, 37, 39, 45, 47, 52, 55, 61, 65, 67, 71, 77, 79, 85, 93, 117, 129, 131, 135, 141, 143, 149, 157, 181, 257, 259, 263, 269, 271, 277, 285, 309]
def C : List Nat := [15, 13, 29, 21, 53]
def mask : Nat := 1042962482296253862204465816752833295508848740346379845859788935193488377891057783255464565348
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
end G209


namespace G211
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 21, 53, 117]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 3, 5, 6]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 23, 25, 28, 31, 33, 35, 37, 39, 45, 47, 49, 52, 55, 61, 65, 67, 71, 77, 79, 85, 93, 129, 131, 135, 141, 143, 149, 157, 181, 257, 259, 263, 269, 271, 277, 285, 309]
def C : List Nat := [15, 13, 29, 21, 53]
def mask : Nat := 1042962482296253862204465816752833295508848740346379845859622781694015263406945370322882943588
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
end G211


namespace G212
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 0, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 44, 45, 47, 52, 53, 56, 57, 63, 65, 67, 71, 77, 79, 93, 124, 125, 129, 131, 135, 141, 143, 157, 188, 189, 257, 259, 263, 269, 271, 285, 316, 317]
def C : List Nat := [15, 13, 29, 61, 60]
def mask : Nat := 400497569297340803823573375397213320427878546585634071237442646684788539038528347695912822921828
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 2 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G212


namespace G213
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 60, 56]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 0, 2]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 44, 45, 47, 52, 53, 57, 62, 63, 65, 67, 71, 77, 79, 93, 124, 125, 129, 131, 135, 141, 143, 157, 188, 189, 257, 259, 263, 269, 271, 285, 316, 317]
def C : List Nat := [15, 13, 29, 61, 60]
def mask : Nat := 400497569297340803823573375397213320427878546585634071237442646684788539038532887324337212381796
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 2 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G213


namespace G214
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 60, 52]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 0, 3]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 44, 45, 47, 53, 56, 57, 62, 63, 65, 67, 71, 77, 79, 93, 124, 125, 129, 131, 135, 141, 143, 157, 188, 189, 257, 259, 263, 269, 271, 285, 316, 317]
def C : List Nat := [15, 13, 29, 61, 60]
def mask : Nat := 400497569297340803823573375397213320427878546585634071237442646684788539038532954878331622939236
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 2 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G214


namespace G215
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 60, 44]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 0, 4]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 52, 53, 56, 57, 62, 63, 65, 67, 71, 77, 79, 93, 124, 125, 129, 131, 135, 141, 143, 157, 188, 189, 257, 259, 263, 269, 271, 285, 316, 317]
def C : List Nat := [15, 13, 29, 61, 60]
def mask : Nat := 400497569297340803823573375397213320427878546585634071237442646684788539038532959364339064265316
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 2 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G215

end Snake9.LocalWindow.ExtendedShare59
