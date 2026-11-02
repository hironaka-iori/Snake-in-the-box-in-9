import Port95M59MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G280
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 46, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 4, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 44, 47, 54, 58, 60, 63, 65, 67, 71, 79, 94, 95, 110, 126, 129, 131, 135, 143, 158, 159, 174, 190, 257, 259, 263, 271, 286, 287, 302, 318]
def C : List Nat := [15, 31, 30, 62, 46]
def mask : Nat := 534004907497129096104928925068404960301837961802561422677776316349992543187914497544508815338084
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
end G280


namespace G282
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 46, 110]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 4, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 42, 44, 47, 54, 58, 60, 63, 65, 67, 71, 79, 94, 95, 126, 129, 131, 135, 143, 158, 159, 174, 190, 257, 259, 263, 271, 286, 287, 302, 318]
def C : List Nat := [15, 31, 30, 62, 46]
def mask : Nat := 534004907497129096104928925068404960301837961802561422677776315051918328554207590416282779544164
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
end G282


namespace G289
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 28, 24, 26]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 0, 2, 1]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 23, 25, 27, 30, 33, 35, 39, 47, 56, 60, 61, 63, 65, 67, 71, 79, 88, 92, 93, 95, 129, 131, 135, 143, 152, 156, 157, 159, 257, 259, 263, 271, 280, 284, 285, 287]
def C : List Nat := [15, 31, 29, 28, 24]
def mask : Nat := 343856204178442488679471365534595542361012332778111488326216203560980190479216539302756
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
end G289


namespace G290
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 28, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 0, 2, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 23, 25, 26, 27, 30, 33, 35, 39, 47, 60, 61, 63, 65, 67, 71, 79, 88, 92, 93, 95, 129, 131, 135, 143, 152, 156, 157, 159, 257, 259, 263, 271, 280, 284, 285, 287]
def C : List Nat := [15, 31, 29, 28, 24]
def mask : Nat := 343856204178442488679471365534595542361012332778111488326216203560980118421622568483684
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
end G290


namespace G291
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 28, 20, 22]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 0, 3, 1]
def D : List Nat := [2, 4, 5, 6, 9, 11, 12, 13, 14, 16, 17, 19, 21, 23, 24, 25, 27, 30, 33, 35, 39, 47, 52, 60, 61, 63, 65, 67, 71, 79, 84, 92, 93, 95, 129, 131, 135, 143, 148, 156, 157, 159, 257, 259, 263, 271, 276, 284, 285, 287]
def C : List Nat := [15, 31, 29, 28, 20]
def mask : Nat := 342034952091980867675484369996948493386029724187652460175488370712267757040078896724596
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
end G291


namespace G292
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 28, 20, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 0, 3, 5]
def D : List Nat := [2, 4, 5, 6, 9, 11, 12, 13, 14, 16, 17, 19, 21, 22, 23, 24, 25, 27, 30, 33, 35, 39, 47, 60, 61, 63, 65, 67, 71, 79, 84, 92, 93, 95, 129, 131, 135, 143, 148, 156, 157, 159, 257, 259, 263, 271, 276, 284, 285, 287]
def C : List Nat := [15, 31, 29, 28, 20]
def mask : Nat := 342034952091980867675484369996948493386029724187652460175488370712267752536479273548404
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 40 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    40 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=40) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G292


namespace G293
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 28, 12, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 0, 4, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 13, 14, 17, 19, 20, 21, 23, 24, 25, 27, 30, 33, 35, 39, 47, 60, 61, 63, 65, 67, 71, 76, 79, 92, 93, 95, 129, 131, 135, 140, 143, 156, 157, 159, 257, 259, 263, 268, 271, 284, 285, 287]
def C : List Nat := [15, 31, 29, 28, 12]
def mask : Nat := 341914009570614275655688358574526619040034785335942290337354100562157946989418976537460
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
end G293


namespace G294
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 28, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 0, 5, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 13, 14, 17, 19, 20, 21, 23, 24, 25, 27, 30, 33, 35, 39, 44, 47, 52, 56, 61, 63, 65, 67, 71, 79, 92, 93, 95, 124, 129, 131, 135, 143, 156, 157, 159, 188, 257, 259, 263, 271, 284, 285, 287, 316]
def C : List Nat := [15, 31, 29, 28, 60]
def mask : Nat := 133499190086970415435905616244148910790833374960116682617739629941211619188615410972762916420196
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
end G294


namespace G295
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 28, 60, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 0, 5, 2]
def D : List Nat := [2, 5, 6, 9, 11, 12, 13, 14, 17, 19, 20, 21, 23, 24, 25, 27, 30, 33, 35, 39, 44, 47, 52, 61, 62, 63, 65, 67, 71, 79, 92, 93, 95, 124, 129, 131, 135, 143, 156, 157, 159, 188, 257, 259, 263, 271, 284, 285, 287, 316]
def C : List Nat := [15, 31, 29, 28, 60]
def mask : Nat := 133499190086970415435905616244148910790833374960116682617739629941211619188619950601187305880164
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
end G295


namespace G296
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 28, 60, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 0, 5, 3]
def D : List Nat := [2, 5, 6, 9, 11, 12, 13, 14, 17, 19, 20, 21, 23, 24, 25, 27, 30, 33, 35, 39, 44, 47, 56, 61, 62, 63, 65, 67, 71, 79, 92, 93, 95, 124, 129, 131, 135, 143, 156, 157, 159, 188, 257, 259, 263, 271, 284, 285, 287, 316]
def C : List Nat := [15, 31, 29, 28, 60]
def mask : Nat := 133499190086970415435905616244148910790833374960116682617739629941211619188620018155181716437604
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
end G296


namespace G297
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 28, 60, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 0, 5, 4]
def D : List Nat := [2, 5, 6, 9, 11, 12, 13, 14, 17, 19, 20, 21, 23, 24, 25, 27, 30, 33, 35, 39, 47, 52, 56, 61, 62, 63, 65, 67, 71, 79, 92, 93, 95, 124, 129, 131, 135, 143, 156, 157, 159, 188, 257, 259, 263, 271, 284, 285, 287, 316]
def C : List Nat := [15, 31, 29, 28, 60]
def mask : Nat := 133499190086970415435905616244148910790833374960116682617739629941211619188620022641189157763684
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
end G297


namespace G298
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 28, 60, 124]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 0, 5, 6]
def D : List Nat := [2, 5, 6, 9, 11, 12, 13, 14, 17, 19, 20, 21, 23, 24, 25, 27, 30, 33, 35, 39, 44, 47, 52, 56, 61, 62, 63, 65, 67, 71, 79, 92, 93, 95, 129, 131, 135, 143, 156, 157, 159, 188, 257, 259, 263, 271, 284, 285, 287, 316]
def C : List Nat := [15, 31, 29, 28, 60]
def mask : Nat := 133499190086970415435905616244148910790833374960116682617718362293279060534653561745816858294884
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
end G298

end Snake9.LocalWindow.ExtendedShare59
