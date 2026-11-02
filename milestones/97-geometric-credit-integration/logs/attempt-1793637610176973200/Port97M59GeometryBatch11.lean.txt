import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G191
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 5, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 21, 23, 24, 25, 30, 31, 33, 35, 39, 44, 45, 47, 52, 56, 61, 65, 67, 71, 77, 79, 92, 93, 124, 129, 131, 135, 141, 143, 156, 157, 188, 257, 259, 263, 269, 271, 284, 285, 316]
def C : List Nat := [15, 13, 29, 28, 60]
def mask : Nat := 133499189838309745799807327260730696610932146080498993175707850505666678324019869808252866419300
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
end G191


namespace G192
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 60, 56]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 5, 2]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 21, 23, 24, 25, 30, 31, 33, 35, 39, 44, 45, 47, 52, 61, 62, 65, 67, 71, 77, 79, 92, 93, 124, 129, 131, 135, 141, 143, 156, 157, 188, 257, 259, 263, 269, 271, 284, 285, 316]
def C : List Nat := [15, 13, 29, 28, 60]
def mask : Nat := 133499189838309745799807327260730696610932146080498993175707850505666678324024409436677255879268
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
end G192


namespace G193
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 60, 52]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 5, 3]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 21, 23, 24, 25, 30, 31, 33, 35, 39, 44, 45, 47, 56, 61, 62, 65, 67, 71, 77, 79, 92, 93, 124, 129, 131, 135, 141, 143, 156, 157, 188, 257, 259, 263, 269, 271, 284, 285, 316]
def C : List Nat := [15, 13, 29, 28, 60]
def mask : Nat := 133499189838309745799807327260730696610932146080498993175707850505666678324024476990671666436708
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
end G193


namespace G194
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 60, 44]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 5, 4]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 21, 23, 24, 25, 30, 31, 33, 35, 39, 45, 47, 52, 56, 61, 62, 65, 67, 71, 77, 79, 92, 93, 124, 129, 131, 135, 141, 143, 156, 157, 188, 257, 259, 263, 269, 271, 284, 285, 316]
def C : List Nat := [15, 13, 29, 28, 60]
def mask : Nat := 133499189838309745799807327260730696610932146080498993175707850505666678324024481476679107762788
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
end G194


namespace G195
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 28, 60, 124]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 0, 5, 6]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 20, 21, 23, 24, 25, 30, 31, 33, 35, 39, 44, 45, 47, 52, 56, 61, 62, 65, 67, 71, 77, 79, 92, 93, 129, 131, 135, 141, 143, 156, 157, 188, 257, 259, 263, 269, 271, 284, 285, 316]
def C : List Nat := [15, 13, 29, 28, 60]
def mask : Nat := 133499189838309745799807327260730696610932146080498993175686582857734119670058020581306808293988
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
end G195


namespace G196
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 25, 24, 26]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 2, 0, 1]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 14, 16, 17, 19, 21, 23, 27, 28, 31, 33, 35, 39, 45, 47, 56, 57, 61, 65, 67, 71, 77, 79, 88, 89, 93, 129, 131, 135, 141, 143, 152, 153, 157, 257, 259, 263, 269, 271, 280, 281, 285]
def C : List Nat := [15, 13, 29, 25, 24]
def mask : Nat := 67998170051183992703180684659165048788321021718558221839802292155612309956916752898916
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
end G196


namespace G197
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 25, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 2, 0, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 14, 16, 17, 19, 21, 23, 26, 27, 28, 31, 33, 35, 39, 45, 47, 57, 61, 65, 67, 71, 77, 79, 88, 89, 93, 129, 131, 135, 141, 143, 152, 153, 157, 257, 259, 263, 269, 271, 280, 281, 285]
def C : List Nat := [15, 13, 29, 25, 24]
def mask : Nat := 67998170051183992703180684659165048788321021718558221839802292155612237899322782079844
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
end G197


namespace G198
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 25, 27, 26]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 2, 1, 0]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 24, 28, 31, 33, 35, 39, 45, 47, 57, 59, 61, 65, 67, 71, 77, 79, 89, 91, 93, 129, 131, 135, 141, 143, 153, 155, 157, 257, 259, 263, 269, 271, 281, 283, 285]
def C : List Nat := [15, 13, 29, 25, 27]
def mask : Nat := 81596852296764096199616918006929681134857832527318965365236777425998479635811150748260
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 4 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=4) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G198


namespace G199
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 25, 27, 59]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 2, 1, 5]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 24, 26, 28, 31, 33, 35, 39, 45, 47, 57, 61, 65, 67, 71, 77, 79, 89, 91, 93, 129, 131, 135, 141, 143, 153, 155, 157, 257, 259, 263, 269, 271, 281, 283, 285]
def C : List Nat := [15, 13, 29, 25, 27]
def mask : Nat := 81596852296764096199616918006929681134857832527318965365236777425997903175058914433636
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 4 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=4) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G199


namespace G200
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 25, 57, 56]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 2, 5, 0]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 24, 27, 28, 31, 33, 35, 39, 41, 45, 47, 49, 59, 61, 65, 67, 71, 77, 79, 89, 93, 121, 129, 131, 135, 141, 143, 153, 157, 185, 257, 259, 263, 269, 271, 281, 285, 313]
def C : List Nat := [15, 13, 29, 25, 57]
def mask : Nat := 16687398784187611177669370711710848647724198819891964097416646600997408450269008762301298924132
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
end G200


namespace G201
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 25, 57, 59]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 2, 5, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 24, 27, 28, 31, 33, 35, 39, 41, 45, 47, 49, 56, 61, 65, 67, 71, 77, 79, 89, 93, 121, 129, 131, 135, 141, 143, 153, 157, 185, 257, 259, 263, 269, 271, 281, 285, 313]
def C : List Nat := [15, 13, 29, 25, 57]
def mask : Nat := 16687398784187611177669370711710848647724198819891964097416646600997408450268504359143033428580
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
end G201


namespace G202
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 25, 57, 49]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 2, 5, 3]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 24, 27, 28, 31, 33, 35, 39, 41, 45, 47, 56, 59, 61, 65, 67, 71, 77, 79, 89, 93, 121, 129, 131, 135, 141, 143, 153, 157, 185, 257, 259, 263, 269, 271, 281, 285, 313]
def C : List Nat := [15, 13, 29, 25, 57]
def mask : Nat := 16687398784187611177669370711710848647724198819891964097416646600997408450269080256945383430756
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
end G202

end Snake9.LocalWindow.ExtendedShare59
