import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G216
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 60, 124]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 0, 6]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 44, 45, 47, 52, 53, 56, 57, 62, 63, 65, 67, 71, 77, 79, 93, 125, 129, 131, 135, 141, 143, 157, 188, 189, 257, 259, 263, 269, 271, 285, 316, 317]
def C : List Nat := [15, 13, 29, 61, 60]
def mask : Nat := 400497569297340803823573375397213320427878546585634071237421379036855980384566498468966764796516
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
end G216


namespace G217
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 63, 62]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 1, 0]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 55, 57, 59, 60, 65, 67, 71, 77, 79, 93, 125, 127, 129, 131, 135, 141, 143, 157, 189, 191, 257, 259, 263, 269, 271, 285, 317, 319]
def C : List Nat := [15, 13, 29, 61, 63]
def mask : Nat := 1334991897512738964871395371846392370569308007125901330923600381515190933702361060688894372764260
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
end G217


namespace G218
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 63, 59]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 1, 2]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 55, 57, 60, 62, 65, 67, 71, 77, 79, 93, 125, 127, 129, 131, 135, 141, 143, 157, 189, 191, 257, 259, 263, 269, 271, 285, 317, 319]
def C : List Nat := [15, 13, 29, 61, 63]
def mask : Nat := 1334991897512738964871395371846392370569308007125901330923600381515190933702365095914160496728676
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
end G218


namespace G219
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 63, 55]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 1, 3]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 57, 59, 60, 62, 65, 67, 71, 77, 79, 93, 125, 127, 129, 131, 135, 141, 143, 157, 189, 191, 257, 259, 263, 269, 271, 285, 317, 319]
def C : List Nat := [15, 13, 29, 61, 63]
def mask : Nat := 1334991897512738964871395371846392370569308007125901330923600381515190933702365636346115781188196
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
end G219


namespace G220
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 63, 127]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 1, 6]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 55, 57, 59, 60, 62, 65, 67, 71, 77, 79, 93, 125, 129, 131, 135, 141, 143, 157, 189, 191, 257, 259, 263, 269, 271, 285, 317, 319]
def C : List Nat := [15, 13, 29, 61, 63]
def mask : Nat := 1334991897512738964871395371846392370569308007125901330923430240331730464470633985071196916046436
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
end G220


namespace G221
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 57, 56]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 2, 0]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 41, 45, 47, 49, 53, 59, 60, 63, 65, 67, 71, 77, 79, 93, 121, 125, 129, 131, 135, 141, 143, 157, 185, 189, 257, 259, 263, 269, 271, 285, 313, 317]
def C : List Nat := [15, 13, 29, 61, 57]
def mask : Nat := 283685778270416033692595625841065939160199864018100663776672929830988239705549826007750991829604
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
end G221


namespace G222
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 57, 59]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 2, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 41, 45, 47, 49, 53, 56, 60, 63, 65, 67, 71, 77, 79, 93, 121, 125, 129, 131, 135, 141, 143, 157, 185, 189, 257, 259, 263, 269, 271, 285, 313, 317]
def C : List Nat := [15, 13, 29, 61, 57]
def mask : Nat := 283685778270416033692595625841065939160199864018100663776672929830988239705549321604592726334052
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
end G222


namespace G223
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 57, 49]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 2, 3]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 41, 45, 47, 53, 56, 59, 60, 63, 65, 67, 71, 77, 79, 93, 121, 125, 129, 131, 135, 141, 143, 157, 185, 189, 257, 259, 263, 269, 271, 285, 313, 317]
def C : List Nat := [15, 13, 29, 61, 57]
def mask : Nat := 283685778270416033692595625841065939160199864018100663776672929830988239705549897502395076336228
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
end G223


namespace G224
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 57, 41]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 2, 4]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 49, 53, 56, 59, 60, 63, 65, 67, 71, 77, 79, 93, 121, 125, 129, 131, 135, 141, 143, 157, 185, 189, 257, 259, 263, 269, 271, 285, 313, 317]
def C : List Nat := [15, 13, 29, 61, 57]
def mask : Nat := 283685778270416033692595625841065939160199864018100663776672929830988239705549898063146006501988
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
end G224


namespace G225
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 57, 121]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 2, 6]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 41, 45, 47, 49, 53, 56, 59, 60, 63, 65, 67, 71, 77, 79, 93, 125, 129, 131, 135, 141, 143, 157, 185, 189, 257, 259, 263, 269, 271, 285, 313, 317]
def C : List Nat := [15, 13, 29, 61, 57]
def mask : Nat := 283685778270416033692595625841065939160199864018100663776670271374996669873804090451224469068388
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
end G225


namespace G226
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 53, 52]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 3, 0]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 37, 39, 45, 47, 49, 55, 57, 60, 63, 65, 67, 71, 77, 79, 93, 117, 125, 129, 131, 135, 141, 143, 157, 181, 189, 257, 259, 263, 269, 271, 285, 309, 317]
def C : List Nat := [15, 13, 29, 61, 53]
def mask : Nat := 268041341972167180550053962954081914883278611888520296706034128466639985330596737966330918623844
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
end G226


namespace G227
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 53, 55]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 3, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 37, 39, 45, 47, 49, 52, 57, 60, 63, 65, 67, 71, 77, 79, 93, 117, 125, 129, 131, 135, 141, 143, 157, 181, 189, 257, 259, 263, 269, 271, 285, 309, 317]
def C : List Nat := [15, 13, 29, 61, 53]
def mask : Nat := 268041341972167180550053962954081914883278611888520296706034128466639985330596706441133527030372
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
end G227

end Snake9.LocalWindow.ExtendedShare59
