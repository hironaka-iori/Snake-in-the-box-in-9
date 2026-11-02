import Port95M60GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G258
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 48, 112]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 16, 17, 18, 19, 23, 27, 29, 30, 32, 33, 34, 35, 39, 47, 49, 52, 53, 54, 56, 58, 59, 61, 62, 65, 67, 71, 79, 95, 114, 115, 119, 127, 129, 131, 135, 143, 159, 176, 178, 179, 183, 191, 257, 259, 263, 271, 287, 304, 306, 307, 311, 319]
def C : List Nat := [63, 55, 51, 50, 48]
def mask : Nat := 1072589071371731070267514230762245346536079545794338615299395266162829413186193527775416554580580
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 10 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G258


namespace G260
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 34, 98]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 4, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 23, 27, 29, 30, 32, 33, 35, 38, 39, 42, 47, 48, 49, 53, 54, 58, 59, 61, 62, 65, 67, 71, 79, 95, 114, 115, 119, 127, 129, 131, 135, 143, 159, 162, 178, 179, 183, 191, 257, 259, 263, 271, 287, 290, 306, 307, 311, 319]
def C : List Nat := [63, 55, 51, 50, 34]
def mask : Nat := 1072556480785402664129280504252759789072785986926739265940045921953621193094576382070616771947108
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 4 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=4) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G260


namespace G265
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 48, 56]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 16, 17, 18, 19, 23, 27, 29, 30, 32, 33, 34, 35, 39, 47, 49, 52, 53, 54, 58, 59, 61, 62, 65, 67, 71, 79, 95, 112, 114, 115, 119, 127, 129, 131, 135, 143, 159, 176, 178, 179, 183, 191, 257, 259, 263, 271, 287, 304, 306, 307, 311, 319]
def C : List Nat := [63, 55, 51, 50, 48]
def mask : Nat := 1072589071371731070267514230762245346536079545794338615299395271355126271721021084248318845872740
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 10 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G265


namespace G275
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 97]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 49, 50, 53, 54, 59, 61, 62, 65, 67, 71, 79, 81, 83, 95, 99, 112, 114, 117, 119, 121, 123, 127, 129, 131, 135, 143, 159, 179, 183, 191, 241, 243, 257, 259, 263, 271, 287, 307, 311, 319, 369, 371]
def C : List Nat := [63, 55, 51, 115, 113]
def mask : Nat := 6012269011901014135823178821405014170712170903025678995501447280118704098541232485684053754830502439080627432036
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 10 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G275


namespace G276
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 81]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 49, 50, 53, 54, 59, 61, 62, 65, 67, 71, 79, 83, 95, 97, 99, 112, 114, 117, 119, 121, 123, 127, 129, 131, 135, 143, 159, 179, 183, 191, 241, 243, 257, 259, 263, 271, 287, 307, 311, 319, 369, 371]
def C : List Nat := [63, 55, 51, 115, 113]
def mask : Nat := 6012269011901014135823178821405014170712170903025678995501447280118704098541232485842507662007391885009365920356
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 10 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G276


namespace G277
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 112]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 49, 50, 53, 54, 59, 61, 62, 65, 67, 71, 79, 81, 83, 95, 97, 99, 114, 117, 119, 121, 123, 127, 129, 131, 135, 143, 159, 179, 183, 191, 241, 243, 257, 259, 263, 271, 287, 307, 311, 319, 369, 371]
def C : List Nat := [63, 55, 51, 115, 113]
def mask : Nat := 6012269011901014135823178821405014170712170903025678995501447280118704098541227293545651545031402583771386112612
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
end G277


namespace G278
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 241]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 49, 50, 53, 54, 59, 61, 62, 65, 67, 71, 79, 81, 83, 95, 97, 99, 112, 114, 117, 119, 121, 123, 127, 129, 131, 135, 143, 159, 179, 183, 191, 243, 257, 259, 263, 271, 287, 307, 311, 319, 369, 371]
def C : List Nat := [63, 55, 51, 115, 113]
def mask : Nat := 6012269011901014135823178821405014170708637208896122226842280685117218261509577518048758841942787901865130093156
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
end G278


namespace G281
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 99, 98]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 4, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 47, 49, 50, 53, 54, 59, 61, 62, 65, 67, 71, 79, 83, 95, 97, 103, 107, 113, 114, 119, 123, 127, 129, 131, 135, 143, 159, 179, 183, 191, 227, 243, 257, 259, 263, 271, 287, 307, 311, 319, 355, 371]
def C : List Nat := [63, 55, 51, 115, 99]
def mask : Nat := 4809888601476523205432136302117523279474393449614289175241225667871708318337158970178828077359218312801799531108
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
end G281

end Snake9.LocalWindow.FamilyShare61