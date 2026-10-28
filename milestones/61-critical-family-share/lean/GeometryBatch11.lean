import GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G282
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 99, 227]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 4, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 49, 50, 53, 54, 59, 61, 62, 65, 67, 71, 79, 83, 95, 97, 98, 103, 107, 113, 114, 119, 123, 127, 129, 131, 135, 143, 159, 179, 183, 191, 243, 257, 259, 263, 271, 287, 307, 311, 319, 355, 371]
def C : List Nat := [63, 55, 51, 115, 99]
def mask : Nat := 4809888601476523205432136302117523279474393233934715838036107310535587622180113581398585347091695814347093338724
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 5 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G282


namespace G292
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 49, 50, 53, 54, 59, 61, 62, 65, 67, 71, 79, 81, 83, 95, 97, 99, 112, 114, 117, 119, 123, 127, 129, 131, 135, 143, 159, 179, 183, 191, 241, 243, 257, 259, 263, 271, 287, 307, 311, 319, 369, 371]
def C : List Nat := [63, 55, 51, 115, 113]
def mask : Nat := 6012269011901014135823178821405014170712170903025678995501447280118704098538574029850940248113223500147154643556
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 20 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    20 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=20) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G292


namespace G299
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 125, 93, 77, 73]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 55, 59, 61, 62, 65, 67, 69, 71, 76, 79, 85, 89, 92, 95, 109, 111, 117, 119, 121, 123, 124, 126, 129, 131, 135, 143, 159, 191, 205, 221, 253, 255, 257, 259, 263, 271, 287, 319, 333, 349, 381, 383]
def C : List Nat := [63, 127, 125, 93, 77]
def mask : Nat := 24626253873893316314743227600699684525572960128475995943707148125095588452153372945772783341477288811648326287649380
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G299


namespace G301
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 125, 93, 77, 76]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 55, 59, 61, 62, 65, 67, 69, 71, 73, 79, 85, 89, 92, 95, 109, 111, 117, 119, 121, 123, 124, 126, 129, 131, 135, 143, 159, 191, 205, 221, 253, 255, 257, 259, 263, 271, 287, 319, 333, 349, 381, 383]
def C : List Nat := [63, 127, 125, 93, 77]
def mask : Nat := 24626253873893316314743227600699684525572960128475995943707148125095588452153372945772783341411175680888151254657636
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G301


namespace G302
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 125, 93, 77, 205]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 55, 59, 61, 62, 65, 67, 69, 71, 73, 76, 79, 85, 89, 92, 95, 109, 111, 117, 119, 121, 123, 124, 126, 129, 131, 135, 143, 159, 191, 221, 253, 255, 257, 259, 263, 271, 287, 319, 333, 349, 381, 383]
def C : List Nat := [63, 127, 125, 93, 77]
def mask : Nat := 24626253873893316314743227600699684525572960128475995892285130708807899634810585990855580060776237743564694848432740
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G302


namespace G306
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 111, 103, 101, 97]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 37, 39, 47, 55, 59, 61, 62, 65, 67, 69, 71, 79, 95, 99, 100, 102, 107, 109, 110, 117, 119, 123, 125, 126, 129, 131, 135, 143, 159, 191, 229, 231, 239, 255, 257, 259, 263, 271, 287, 319, 357, 359, 367, 383]
def C : List Nat := [63, 127, 111, 103, 101]
def mask : Nat := 19701305179486948891506450852722689400729805382045552409670303006705165337915858540941175649833293115591508907158116
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 8 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    8 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=8) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G306


namespace G307
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 111, 103, 101, 100]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 37, 39, 47, 55, 59, 61, 62, 65, 67, 69, 71, 79, 95, 97, 99, 102, 107, 109, 110, 117, 119, 123, 125, 126, 129, 131, 135, 143, 159, 191, 229, 231, 239, 255, 257, 259, 263, 271, 287, 319, 357, 359, 367, 383]
def C : List Nat := [63, 127, 111, 103, 101]
def mask : Nat := 19701305179486948891506450852722689400729805382045552409670303006705165337915858540940066455558093414865199291853412
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 16 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    16 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=16) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G307


namespace G308
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 111, 103, 101, 229]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 37, 39, 47, 55, 59, 61, 62, 65, 67, 69, 71, 79, 95, 97, 99, 100, 102, 107, 109, 110, 117, 119, 123, 125, 126, 129, 131, 135, 143, 159, 191, 231, 239, 255, 257, 259, 263, 271, 287, 319, 357, 359, 367, 383]
def C : List Nat := [63, 127, 111, 103, 101]
def mask : Nat := 19701305179486948891506450852722689400729805381182834116321482533275820855131230359384945484637023324871380467083876
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 16 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    16 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=16) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G308

end Snake9.LocalWindow.FamilyShare61