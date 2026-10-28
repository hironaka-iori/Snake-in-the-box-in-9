import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G141
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 54, 52]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 5, 1]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 20, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 50, 55, 62, 65, 67, 71, 78, 79, 86, 94, 118, 129, 131, 135, 142, 143, 150, 158, 182, 257, 259, 263, 270, 271, 278, 286, 310]
def C : List Nat := [15, 14, 30, 22, 54]
def mask : Nat := 2085924964588697469920488506779058564185001596396928792272604401585615031709314486386739265124
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
end G141


namespace G142
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 54, 50]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 5, 2]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 20, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 52, 55, 62, 65, 67, 71, 78, 79, 86, 94, 118, 129, 131, 135, 142, 143, 150, 158, 182, 257, 259, 263, 270, 271, 278, 286, 310]
def C : List Nat := [15, 14, 30, 22, 54]
def mask : Nat := 2085924964588697469920488506779058564185001596396928792272604401585615031709317864086459792996
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
end G142


namespace G143
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 54, 38]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 5, 4]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 20, 23, 26, 28, 31, 33, 35, 39, 46, 47, 50, 52, 55, 62, 65, 67, 71, 78, 79, 86, 94, 118, 129, 131, 135, 142, 143, 150, 158, 182, 257, 259, 263, 270, 271, 278, 286, 310]
def C : List Nat := [15, 14, 30, 22, 54]
def mask : Nat := 2085924964588697469920488506779058564185001596396928792272604401585615031709318989711488728676
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
end G143


namespace G144
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 54, 118]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 5, 6]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 20, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 50, 52, 55, 62, 65, 67, 71, 78, 79, 86, 94, 129, 131, 135, 142, 143, 150, 158, 182, 257, 259, 263, 270, 271, 278, 286, 310]
def C : List Nat := [15, 14, 30, 22, 54]
def mask : Nat := 2085924964588697469920488506779058564185001596396928792272272094586668802741093038221296549476
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
end G144


namespace G145
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 61]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 1]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 39, 46, 47, 54, 55, 58, 59, 60, 65, 67, 71, 78, 79, 94, 126, 127, 129, 131, 135, 142, 143, 158, 190, 191, 257, 259, 263, 270, 271, 286, 318, 319]
def C : List Nat := [15, 14, 30, 62, 63]
def mask : Nat := 1601990277065019078290791447481282075807292506321487105592144949755406340350544458759278049246820
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
end G145


namespace G146
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 59]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 2]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 39, 46, 47, 54, 55, 58, 60, 61, 65, 67, 71, 78, 79, 94, 126, 127, 129, 131, 135, 142, 143, 158, 190, 191, 257, 259, 263, 270, 271, 286, 318, 319]
def C : List Nat := [15, 14, 30, 62, 63]
def mask : Nat := 1601990277065019078290791447481282075807292506321487105592144949755406340350546188141534959517284
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
end G146


namespace G148
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 127]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 6]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 39, 46, 47, 54, 55, 58, 59, 60, 61, 65, 67, 71, 78, 79, 94, 126, 129, 131, 135, 142, 143, 158, 190, 191, 257, 259, 263, 270, 271, 286, 318, 319]
def C : List Nat := [15, 14, 30, 62, 63]
def mask : Nat := 1601990277065019078290791447481282075807292506321487105591974808571945871118815077298571378835044
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
end G148


namespace G159
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 54, 55]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 3, 0]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 50, 52, 58, 60, 63, 65, 67, 71, 78, 79, 94, 118, 126, 129, 131, 135, 142, 143, 158, 182, 190, 257, 259, 263, 270, 271, 286, 310, 318]
def C : List Nat := [15, 14, 30, 62, 54]
def mask : Nat := 536082683944330550845619482781437221739724527892744762512621283464478608937110274915098142850660
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
end G159


namespace G160
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 54, 52]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 3, 1]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 50, 55, 58, 60, 63, 65, 67, 71, 78, 79, 94, 118, 126, 129, 131, 135, 142, 143, 158, 182, 190, 257, 259, 263, 270, 271, 286, 310, 318]
def C : List Nat := [15, 14, 30, 62, 54]
def mask : Nat := 536082683944330550845619482781437221739724527892744762512621283464478608937110306440295534444132
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
end G160


namespace G161
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 54, 50]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 3, 2]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 52, 55, 58, 60, 63, 65, 67, 71, 78, 79, 94, 118, 126, 129, 131, 135, 142, 143, 158, 182, 190, 257, 259, 263, 270, 271, 286, 310, 318]
def C : List Nat := [15, 14, 30, 62, 54]
def mask : Nat := 536082683944330550845619482781437221739724527892744762512621283464478608937110309817995254972004
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
end G161


namespace G162
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 54, 38]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 3, 4]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 39, 46, 47, 50, 52, 55, 58, 60, 63, 65, 67, 71, 78, 79, 94, 118, 126, 129, 131, 135, 142, 143, 158, 182, 190, 257, 259, 263, 270, 271, 286, 310, 318]
def C : List Nat := [15, 14, 30, 62, 54]
def mask : Nat := 536082683944330550845619482781437221739724527892744762512621283464478608937110310943620283907684
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
end G162


namespace G163
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 54, 118]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 3, 6]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 50, 52, 55, 58, 60, 63, 65, 67, 71, 78, 79, 94, 126, 129, 131, 135, 142, 143, 158, 182, 190, 257, 259, 263, 270, 271, 286, 310, 318]
def C : List Nat := [15, 14, 30, 62, 54]
def mask : Nat := 536082683944330550845619482781437221739724527892744762512620951157479662708142084992130091728484
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
end G163

end Snake9.LocalWindow.ExtendedShare59
