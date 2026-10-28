import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G110
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 58, 59]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 5, 0]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 17, 18, 19, 23, 24, 27, 30, 31, 33, 35, 39, 42, 46, 47, 50, 56, 62, 65, 67, 71, 74, 78, 79, 90, 122, 129, 131, 135, 138, 142, 143, 154, 186, 257, 259, 263, 266, 270, 271, 282, 314]
def C : List Nat := [15, 14, 10, 26, 58]
def mask : Nat := 33374797444040721569503016769633640968599140626426326283630105986485295714317756442873124764516
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
end G110


namespace G111
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 58, 56]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 5, 1]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 17, 18, 19, 23, 24, 27, 30, 31, 33, 35, 39, 42, 46, 47, 50, 59, 62, 65, 67, 71, 74, 78, 79, 90, 122, 129, 131, 135, 138, 142, 143, 154, 186, 257, 259, 263, 266, 270, 271, 282, 314]
def C : List Nat := [15, 14, 10, 26, 58]
def mask : Nat := 33374797444040721569503016769633640968599140626426326283630105986485295714318260846031390260068
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
end G111


namespace G112
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 58, 62]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 5, 2]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 17, 18, 19, 23, 24, 27, 30, 31, 33, 35, 39, 42, 46, 47, 50, 56, 59, 65, 67, 71, 74, 78, 79, 90, 122, 129, 131, 135, 138, 142, 143, 154, 186, 257, 259, 263, 266, 270, 271, 282, 314]
def C : List Nat := [15, 14, 10, 26, 58]
def mask : Nat := 33374797444040721569503016769633640968599140626426326283630105986485295714313721217607000800100
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
end G112


namespace G113
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 58, 50]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 5, 3]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 17, 18, 19, 23, 24, 27, 30, 31, 33, 35, 39, 42, 46, 47, 56, 59, 62, 65, 67, 71, 74, 78, 79, 90, 122, 129, 131, 135, 138, 142, 143, 154, 186, 257, 259, 263, 266, 270, 271, 282, 314]
def C : List Nat := [15, 14, 10, 26, 58]
def mask : Nat := 33374797444040721569503016769633640968599140626426326283630105986485295714318331777725521345380
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
end G113


namespace G114
def W : List Nat := [0, 1, 3, 7, 15, 14, 10, 26, 58, 122]
def ds : List Nat := [0, 1, 2, 3, 0, 2, 4, 5, 6]
def D : List Nat := [2, 5, 6, 8, 9, 11, 12, 13, 17, 18, 19, 23, 24, 27, 30, 31, 33, 35, 39, 42, 46, 47, 50, 56, 59, 62, 65, 67, 71, 74, 78, 79, 90, 129, 131, 135, 138, 142, 143, 154, 186, 257, 259, 263, 266, 270, 271, 282, 314]
def C : List Nat := [15, 14, 10, 26, 58]
def mask : Nat := 33374797444040721569503016769633640968599140626426326283624789074502156050826717675384306809700
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
end G114


namespace G115
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 28, 29, 25]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 1, 0, 2]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 20, 21, 22, 23, 24, 26, 31, 33, 35, 39, 46, 47, 60, 61, 62, 65, 67, 71, 78, 79, 92, 93, 94, 129, 131, 135, 142, 143, 156, 157, 158, 257, 259, 263, 270, 271, 284, 285, 286]
def C : List Nat := [15, 14, 30, 28, 29]
def mask : Nat := 217584623321360163258252161378085195771567077390233931363410134209468880817172325744228
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
end G115


namespace G117
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 28, 29, 61]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 1, 0, 5]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 20, 21, 22, 23, 24, 25, 26, 31, 33, 35, 39, 46, 47, 60, 62, 65, 67, 71, 78, 79, 92, 93, 94, 129, 131, 135, 142, 143, 156, 157, 158, 257, 259, 263, 270, 271, 284, 285, 286]
def C : List Nat := [15, 14, 30, 28, 29]
def mask : Nat := 217584623321360163258252161378085195771567077390233931363410134209466574974163145604708
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
end G117


namespace G118
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 28, 24, 25]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 1, 2, 0]
def D : List Nat := [2, 5, 6, 8, 9, 10, 11, 12, 13, 16, 17, 19, 20, 22, 23, 26, 29, 31, 33, 35, 39, 46, 47, 56, 60, 62, 65, 67, 71, 78, 79, 88, 92, 94, 129, 131, 135, 142, 143, 152, 156, 158, 257, 259, 263, 270, 271, 280, 284, 286]
def C : List Nat := [15, 14, 30, 28, 24]
def mask : Nat := 157361887662362562059748842266556109665475486665722067179343128012044415096354275802980
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 11 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    11 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=11) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G118


namespace G119
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 28, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 1, 2, 5]
def D : List Nat := [2, 5, 6, 8, 9, 10, 11, 12, 13, 16, 17, 19, 20, 22, 23, 25, 26, 29, 31, 33, 35, 39, 46, 47, 60, 62, 65, 67, 71, 78, 79, 88, 92, 94, 129, 131, 135, 142, 143, 152, 156, 158, 257, 259, 263, 270, 271, 280, 284, 286]
def C : List Nat := [15, 14, 30, 28, 24]
def mask : Nat := 157361887662362562059748842266556109665475486665722067179343128012044343038760271429476
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
end G119


namespace G120
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 28, 20, 21]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 1, 3, 0]
def D : List Nat := [2, 4, 5, 6, 9, 10, 11, 12, 13, 16, 17, 19, 22, 23, 24, 26, 29, 31, 33, 35, 39, 46, 47, 52, 60, 62, 65, 67, 71, 78, 79, 84, 92, 94, 129, 131, 135, 142, 143, 148, 156, 158, 257, 259, 263, 270, 271, 276, 284, 286]
def C : List Nat := [15, 14, 30, 28, 20]
def mask : Nat := 155540635575900941055761846728909060690492878075263039028615295163331981657216633224820
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
end G120


namespace G121
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 28, 20, 52]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 1, 3, 5]
def D : List Nat := [2, 4, 5, 6, 9, 10, 11, 12, 13, 16, 17, 19, 21, 22, 23, 24, 26, 29, 31, 33, 35, 39, 46, 47, 60, 62, 65, 67, 71, 78, 79, 84, 92, 94, 129, 131, 135, 142, 143, 148, 156, 158, 257, 259, 263, 270, 271, 276, 284, 286]
def C : List Nat := [15, 14, 30, 28, 20]
def mask : Nat := 155540635575900941055761846728909060690492878075263039028615295163331977153617007951476
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 21 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    21 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=21) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G121


namespace G127
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 26, 27, 25]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 2, 0, 1]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 18, 19, 22, 23, 24, 28, 31, 33, 35, 39, 46, 47, 58, 59, 62, 65, 67, 71, 78, 79, 90, 91, 94, 129, 131, 135, 142, 143, 154, 155, 158, 257, 259, 263, 270, 271, 282, 283, 286]
def C : List Nat := [15, 14, 30, 26, 27]
def mask : Nat := 147648543201233916705151532732438515132234907516607250375461352818911436754286445215332
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 11 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    11 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=11) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G127

end Snake9.LocalWindow.ExtendedShare59
