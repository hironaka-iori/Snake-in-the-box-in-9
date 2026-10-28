import MaskShareBridge
namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G299
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 24, 26]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 0, 1]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 19, 21, 23, 27, 28, 30, 33, 35, 39, 47, 56, 57, 61, 63, 65, 67, 71, 79, 88, 89, 93, 95, 129, 131, 135, 143, 152, 153, 157, 159, 257, 259, 263, 271, 280, 281, 285, 287]
def C : List Nat := [15, 31, 29, 25, 24]
def mask : Nat := 316658839687282281686598898839066277667938711160590001275347233020207851121427742419812
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
end G299


namespace G300
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 24, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 0, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 19, 21, 23, 26, 27, 28, 30, 33, 35, 39, 47, 57, 61, 63, 65, 67, 71, 79, 88, 89, 93, 95, 129, 131, 135, 143, 152, 153, 157, 159, 257, 259, 263, 271, 280, 281, 285, 287]
def C : List Nat := [15, 31, 29, 25, 24]
def mask : Nat := 316658839687282281686598898839066277667938711160590001275347233020207779063833771600740
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
end G300


namespace G301
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 41, 47, 49, 59, 61, 63, 65, 67, 71, 79, 89, 93, 95, 121, 129, 131, 135, 143, 153, 157, 159, 185, 257, 259, 263, 271, 281, 285, 287, 313]
def C : List Nat := [15, 31, 29, 25, 57]
def mask : Nat := 16687399032848280813767659695129062827625427699509653539448426036542349314864549926812288445028
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
end G301


namespace G302
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 59]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 41, 47, 49, 56, 61, 63, 65, 67, 71, 79, 89, 93, 95, 121, 129, 131, 135, 143, 153, 157, 159, 185, 257, 259, 263, 271, 281, 285, 287, 313]
def C : List Nat := [15, 31, 29, 25, 57]
def mask : Nat := 16687399032848280813767659695129062827625427699509653539448426036542349314864045523654022949476
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
end G302


namespace G303
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 41, 47, 56, 59, 61, 63, 65, 67, 71, 79, 89, 93, 95, 121, 129, 131, 135, 143, 153, 157, 159, 185, 257, 259, 263, 271, 281, 285, 287, 313]
def C : List Nat := [15, 31, 29, 25, 57]
def mask : Nat := 16687399032848280813767659695129062827625427699509653539448426036542349314864621421456372951652
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
end G303


namespace G304
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 41]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 93, 95, 121, 129, 131, 135, 143, 153, 157, 159, 185, 257, 259, 263, 271, 281, 285, 287, 313]
def C : List Nat := [15, 31, 29, 25, 57]
def mask : Nat := 16687399032848280813767659695129062827625427699509653539448426036542349314864621982207303117412
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
end G304


namespace G305
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 41, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 93, 95, 129, 131, 135, 143, 153, 157, 159, 185, 257, 259, 263, 271, 281, 285, 287, 313]
def C : List Nat := [15, 31, 29, 25, 57]
def mask : Nat := 16687399032848280813767659695129062827625427699509653539445767580550779483118814370285765683812
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
end G305


namespace G306
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 21, 20, 22]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 3, 0, 1]
def D : List Nat := [2, 4, 5, 6, 9, 11, 13, 14, 16, 17, 19, 23, 25, 27, 28, 30, 33, 35, 39, 47, 52, 53, 61, 63, 65, 67, 71, 79, 84, 85, 93, 95, 129, 131, 135, 143, 148, 149, 157, 159, 257, 259, 263, 271, 276, 277, 285, 287]
def C : List Nat := [15, 31, 29, 21, 20]
def mask : Nat := 311195083427897418674637912226125130742990885389212916823163734474070550804014798957172
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
end G306


namespace G307
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 21, 20, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 3, 0, 5]
def D : List Nat := [2, 4, 5, 6, 9, 11, 13, 14, 16, 17, 19, 22, 23, 25, 27, 28, 30, 33, 35, 39, 47, 53, 61, 63, 65, 67, 71, 79, 84, 85, 93, 95, 129, 131, 135, 143, 148, 149, 157, 159, 257, 259, 263, 271, 276, 277, 285, 287]
def C : List Nat := [15, 31, 29, 21, 20]
def mask : Nat := 311195083427897418674637912226125130742990885389212916823163734474070546300415175780980
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
end G307


namespace G308
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 21, 53, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 3, 5, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 20, 23, 25, 27, 28, 30, 33, 35, 37, 39, 47, 49, 55, 61, 63, 65, 67, 71, 79, 85, 93, 95, 117, 129, 131, 135, 143, 149, 157, 159, 181, 257, 259, 263, 271, 277, 285, 287, 309]
def C : List Nat := [15, 31, 29, 21, 53]
def mask : Nat := 1042962730956923498302754800171047475410077619964069287891568370738429242486595007116914354788
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
end G308


namespace G309
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 21, 53, 55]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 3, 5, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 20, 23, 25, 27, 28, 30, 33, 35, 37, 39, 47, 49, 52, 61, 63, 65, 67, 71, 79, 85, 93, 95, 117, 129, 131, 135, 143, 149, 157, 159, 181, 257, 259, 263, 271, 277, 285, 287, 309]
def C : List Nat := [15, 31, 29, 21, 53]
def mask : Nat := 1042962730956923498302754800171047475410077619964069287891568370738429242486563481919522761316
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
end G309


namespace G310
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 21, 53, 49]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 3, 5, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 20, 23, 25, 27, 28, 30, 33, 35, 37, 39, 47, 52, 55, 61, 63, 65, 67, 71, 79, 85, 93, 95, 117, 129, 131, 135, 143, 149, 157, 159, 181, 257, 259, 263, 271, 277, 285, 287, 309]
def C : List Nat := [15, 31, 29, 21, 53]
def mask : Nat := 1042962730956923498302754800171047475410077619964069287891568370738429242486598947766588303972
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
end G310

end Snake9.LocalWindow.ExtendedShare59
