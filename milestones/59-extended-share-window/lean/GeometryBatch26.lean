import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G431
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 58, 26]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 0, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 42, 43, 47, 50, 51, 55, 56, 57, 61, 62, 65, 67, 71, 79, 95, 122, 123, 127, 129, 131, 135, 143, 159, 186, 187, 191, 257, 259, 263, 271, 287, 314, 315, 319]
def C : List Nat := [15, 31, 63, 59, 58]
def mask : Nat := 1168117910517913129769159259765891544777029941610588731724483452186177799998075261892357119437412
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G431


namespace G432
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 58, 122]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 0, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 26, 27, 29, 30, 33, 35, 39, 42, 43, 47, 50, 51, 55, 56, 57, 61, 62, 65, 67, 71, 79, 95, 123, 127, 129, 131, 135, 143, 159, 186, 187, 191, 257, 259, 263, 271, 287, 314, 315, 319]
def C : List Nat := [15, 31, 63, 59, 58]
def mask : Nat := 1168117910517913129769159259765891544777029941610588731724478135274194660334583646664116065167972
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 13 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G432


namespace G433
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 57, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 1, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 27, 29, 30, 33, 35, 39, 41, 43, 47, 49, 51, 55, 58, 61, 62, 65, 67, 71, 79, 95, 121, 123, 127, 129, 131, 135, 143, 159, 185, 187, 191, 257, 259, 263, 271, 287, 313, 315, 319]
def C : List Nat := [15, 31, 63, 59, 57]
def mask : Nat := 1151430511799781019750448152686441918881647272672369673515802064064206328664792471821717386979940
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 54 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    54 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=54) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G433


namespace G434
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 57, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 1, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 27, 29, 30, 33, 35, 39, 41, 43, 47, 51, 55, 56, 58, 61, 62, 65, 67, 71, 79, 95, 121, 123, 127, 129, 131, 135, 143, 159, 185, 187, 191, 257, 259, 263, 271, 287, 313, 315, 319]
def C : List Nat := [15, 31, 63, 59, 57]
def mask : Nat := 1151430511799781019750448152686441918881647272672369673515802064064206328664792543316361471486564
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 45 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    45 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=45) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G434


namespace G435
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 57, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 1, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 27, 29, 30, 33, 35, 39, 43, 47, 49, 51, 55, 56, 58, 61, 62, 65, 67, 71, 79, 95, 121, 123, 127, 129, 131, 135, 143, 159, 185, 187, 191, 257, 259, 263, 271, 287, 313, 315, 319]
def C : List Nat := [15, 31, 63, 59, 57]
def mask : Nat := 1151430511799781019750448152686441918881647272672369673515802064064206328664792543877112401652324
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 43 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    43 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=43) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G435


namespace G436
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 57, 25]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 1, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 41, 43, 47, 49, 51, 55, 56, 58, 61, 62, 65, 67, 71, 79, 95, 121, 123, 127, 129, 131, 135, 143, 159, 185, 187, 191, 257, 259, 263, 271, 287, 313, 315, 319]
def C : List Nat := [15, 31, 63, 59, 57]
def mask : Nat := 1151430511799781019750448152686441918881647272672369673515802064064206328664792543879311391353444
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
end G436


namespace G437
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 57, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 1, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 25, 27, 29, 30, 33, 35, 39, 41, 43, 47, 49, 51, 55, 56, 58, 61, 62, 65, 67, 71, 79, 95, 123, 127, 129, 131, 135, 143, 159, 185, 187, 191, 257, 259, 263, 271, 287, 313, 315, 319]
def C : List Nat := [15, 31, 63, 59, 57]
def mask : Nat := 1151430511799781019750448152686441918881647272672369673515799405608214758833046736265190864218724
theorem canonical : Canon W ds := ⟨rfl, rfl, by decide +kernel⟩
theorem forced : forceCheck W D = true := by decide +kernel
theorem supported : supportCheck W C = true := by decide +kernel
theorem mask_checked : maskCheck mask D = true := by decide +kernel
theorem credit : 54 ≤
    (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0) :
    54 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+4)))).sum :=
  mask_credit_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=54) (mask:=mask) (start:=4)
    canonical rfl (by decide) rfl forced supported mask_checked credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms mask_checked
#print axioms credit
#print axioms in_snake
end G437


namespace G438
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 50]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 49, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 115, 123, 127, 129, 131, 135, 143, 159, 179, 187, 191, 257, 259, 263, 271, 287, 307, 315, 319]
def C : List Nat := [15, 31, 63, 59, 51]
def mask : Nat := 1135003853686619723950779406655108693390879957936310288091631322631640661571092296831744965503588
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
end G438


namespace G439
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 50, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 115, 123, 127, 129, 131, 135, 143, 159, 179, 187, 191, 257, 259, 263, 271, 287, 307, 315, 319]
def C : List Nat := [15, 31, 63, 59, 51]
def mask : Nat := 1135003853686619723950779406655108693390879957936310288091631322631640661571092297394694918924900
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
end G439


namespace G440
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 115]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 49, 50, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 123, 127, 129, 131, 135, 143, 159, 179, 187, 191, 257, 259, 263, 271, 287, 307, 315, 319]
def C : List Nat := [15, 31, 63, 59, 51]
def mask : Nat := 1135003853686619723950779406655108693390879957936310288091631281093265793292471269713674238585444
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
end G440


namespace G441
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 43, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 4, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 41, 47, 51, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 107, 123, 127, 129, 131, 135, 143, 159, 171, 187, 191, 257, 259, 263, 271, 287, 299, 315, 319]
def C : List Nat := [15, 31, 63, 59, 43]
def mask : Nat := 1134744131599637076974780179829836497675345132461502801528935170655865348754320623117355505576548
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
end G441


namespace G442
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 43, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 4, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 42, 47, 51, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 107, 123, 127, 129, 131, 135, 143, 159, 171, 187, 191, 257, 259, 263, 271, 287, 299, 315, 319]
def C : List Nat := [15, 31, 63, 59, 43]
def mask : Nat := 1134744131599637076974780179829836497675345132461502801528935170655865348754320623119554528832100
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
end G442

end Snake9.LocalWindow.ExtendedShare59
