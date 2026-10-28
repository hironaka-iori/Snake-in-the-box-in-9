import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G257
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 22, 20, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 3, 1, 5]
def D : List Nat := [2, 4, 5, 6, 9, 11, 13, 14, 16, 17, 18, 19, 21, 23, 26, 27, 28, 29, 33, 35, 39, 47, 54, 62, 63, 65, 67, 71, 79, 84, 86, 94, 95, 129, 131, 135, 143, 148, 150, 158, 159, 257, 259, 263, 271, 276, 278, 286, 287]
def C : List Nat := [15, 31, 30, 22, 20]
def mask : Nat := 373603321590648965077925625982830675619061606422275614788104140089949932148198428600948
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
end G257


namespace G259
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 22, 54, 55]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 3, 5, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 20, 23, 26, 27, 28, 29, 33, 35, 38, 39, 47, 50, 52, 62, 63, 65, 67, 71, 79, 86, 94, 95, 118, 129, 131, 135, 143, 150, 158, 159, 182, 257, 259, 263, 271, 278, 286, 287, 310]
def C : List Nat := [15, 31, 30, 22, 54]
def mask : Nat := 2085925213248418537223745395924362850577039304673481458996853093302051816696119733283717016164
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
end G259


namespace G260
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 22, 54, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 3, 5, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 20, 23, 26, 27, 28, 29, 33, 35, 38, 39, 47, 50, 55, 62, 63, 65, 67, 71, 79, 86, 94, 95, 118, 129, 131, 135, 143, 150, 158, 159, 182, 257, 259, 263, 271, 278, 286, 287, 310]
def C : List Nat := [15, 31, 30, 22, 54]
def mask : Nat := 2085925213248418537223745395924362850577039304673481458996853093302051816696151258481108609636
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
end G260


namespace G261
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 22, 54, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 3, 5, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 20, 23, 26, 27, 28, 29, 33, 35, 38, 39, 47, 52, 55, 62, 63, 65, 67, 71, 79, 86, 94, 95, 118, 129, 131, 135, 143, 150, 158, 159, 182, 257, 259, 263, 271, 278, 286, 287, 310]
def C : List Nat := [15, 31, 30, 22, 54]
def mask : Nat := 2085925213248418537223745395924362850577039304673481458996853093302051816696154636180829137508
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
end G261


namespace G262
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 22, 54, 38]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 3, 5, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 20, 23, 26, 27, 28, 29, 33, 35, 39, 47, 50, 52, 55, 62, 63, 65, 67, 71, 79, 86, 94, 95, 118, 129, 131, 135, 143, 150, 158, 159, 182, 257, 259, 263, 271, 278, 286, 287, 310]
def C : List Nat := [15, 31, 30, 22, 54]
def mask : Nat := 2085925213248418537223745395924362850577039304673481458996853093302051816696155761805858073188
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
end G262


namespace G263
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 22, 54, 118]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 3, 5, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 20, 23, 26, 27, 28, 29, 33, 35, 38, 39, 47, 50, 52, 55, 62, 63, 65, 67, 71, 79, 86, 94, 95, 129, 131, 135, 143, 150, 158, 159, 182, 257, 259, 263, 271, 278, 286, 287, 310]
def C : List Nat := [15, 31, 30, 22, 54]
def mask : Nat := 2085925213248418537223745395924362850577039304673481458996520786303105587727929810315665893988
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
end G263


namespace G274
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 54, 55]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 3, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 46, 47, 50, 52, 58, 60, 63, 65, 67, 71, 79, 94, 95, 118, 126, 129, 131, 135, 143, 158, 159, 182, 190, 257, 259, 263, 271, 286, 287, 310, 318]
def C : List Nat := [15, 31, 30, 62, 54]
def mask : Nat := 536082684192990271912922739670582526026116565601021315179345532156195045722087888385524401597028
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
end G274


namespace G275
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 54, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 3, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 46, 47, 50, 55, 58, 60, 63, 65, 67, 71, 79, 94, 95, 118, 126, 129, 131, 135, 143, 158, 159, 182, 190, 257, 259, 263, 271, 286, 287, 310, 318]
def C : List Nat := [15, 31, 30, 62, 54]
def mask : Nat := 536082684192990271912922739670582526026116565601021315179345532156195045722087919910721793190500
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
end G275


namespace G276
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 54, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 3, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 46, 47, 52, 55, 58, 60, 63, 65, 67, 71, 79, 94, 95, 118, 126, 129, 131, 135, 143, 158, 159, 182, 190, 257, 259, 263, 271, 286, 287, 310, 318]
def C : List Nat := [15, 31, 30, 62, 54]
def mask : Nat := 536082684192990271912922739670582526026116565601021315179345532156195045722087923288421513718372
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
end G276


namespace G277
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 54, 38]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 3, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 39, 46, 47, 50, 52, 55, 58, 60, 63, 65, 67, 71, 79, 94, 95, 118, 126, 129, 131, 135, 143, 158, 159, 182, 190, 257, 259, 263, 271, 286, 287, 310, 318]
def C : List Nat := [15, 31, 30, 62, 54]
def mask : Nat := 536082684192990271912922739670582526026116565601021315179345532156195045722087924414046542654052
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
end G277


namespace G278
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 54, 118]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 3, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 46, 47, 50, 52, 55, 58, 60, 63, 65, 67, 71, 79, 94, 95, 126, 129, 131, 135, 143, 158, 159, 182, 190, 257, 259, 263, 271, 286, 287, 310, 318]
def C : List Nat := [15, 31, 30, 62, 54]
def mask : Nat := 536082684192990271912922739670582526026116565601021315179345199849196099493119698462556350474852
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
end G278


namespace G279
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 46, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 4, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 22, 23, 26, 27, 28, 29, 33, 35, 38, 39, 42, 47, 54, 58, 60, 63, 65, 67, 71, 79, 94, 95, 110, 126, 129, 131, 135, 143, 158, 159, 174, 190, 257, 259, 263, 271, 286, 287, 302, 318]
def C : List Nat := [15, 31, 30, 62, 46]
def mask : Nat := 534004907497129096104928925068404960301837961802561422677776316349992543187914497531314675804772
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
end G279

end Snake9.LocalWindow.ExtendedShare59
