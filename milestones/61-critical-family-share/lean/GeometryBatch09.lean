import GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G249
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 45, 37, 101, 100]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 4, 3, 6, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 36, 39, 41, 44, 47, 53, 55, 57, 59, 60, 62, 65, 67, 69, 71, 79, 95, 97, 103, 109, 117, 125, 127, 129, 131, 135, 143, 159, 165, 173, 189, 191, 229, 257, 259, 263, 271, 287, 293, 301, 317, 319, 357]
def C : List Nat := [63, 61, 45, 37, 101]
def mask : Nat := 293567822848064149473870605062708743839247033470074249941004268860919027650784022842975773563097011393817188
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
end G249


namespace G250
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 45, 37, 101, 229]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 4, 3, 6, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 36, 39, 41, 44, 47, 53, 55, 57, 59, 60, 62, 65, 67, 69, 71, 79, 95, 97, 100, 103, 109, 117, 125, 127, 129, 131, 135, 143, 159, 165, 173, 189, 191, 257, 259, 263, 271, 287, 293, 301, 317, 319, 357]
def C : List Nat := [63, 61, 45, 37, 101]
def mask : Nat := 293567822848064149473870605062708743838384315176725429467574924378134399469228901872054703473103192569047652
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
end G250


namespace G251
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 125, 93, 77, 73]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 45, 47, 53, 55, 57, 59, 60, 62, 65, 67, 69, 71, 76, 79, 85, 89, 92, 95, 109, 117, 121, 124, 127, 129, 131, 135, 143, 159, 189, 191, 205, 221, 253, 257, 259, 263, 271, 287, 317, 319, 333, 349, 381]
def C : List Nat := [63, 61, 125, 93, 77]
def mask : Nat := 4925250775696076708870705930117991383274572161895808526347338633479888543817066091946125989603226409687148483209828
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
end G251


namespace G253
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 125, 93, 77, 76]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 45, 47, 53, 55, 57, 59, 60, 62, 65, 67, 69, 71, 73, 79, 85, 89, 92, 95, 109, 117, 121, 124, 127, 129, 131, 135, 143, 159, 189, 191, 205, 221, 253, 257, 259, 263, 271, 287, 317, 319, 333, 349, 381]
def C : List Nat := [63, 61, 125, 93, 77]
def mask : Nat := 4925250775696076708870705930117991383274572161895808526347338633479888543817066091946125989537113278926973450218084
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
end G253


namespace G254
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 125, 93, 77, 205]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 45, 47, 53, 55, 57, 59, 60, 62, 65, 67, 69, 71, 73, 76, 79, 85, 89, 92, 95, 109, 117, 121, 124, 127, 129, 131, 135, 143, 159, 189, 191, 221, 253, 257, 259, 263, 271, 287, 317, 319, 333, 349, 381]
def C : List Nat := [63, 61, 125, 93, 77]
def mask : Nat := 4925250775696076708870705930117991383274572161895808474925321217192199726474279137028922708902175341603517043993188
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
end G254


namespace G255
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 50, 54, 22]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 0, 2, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 23, 27, 29, 30, 33, 34, 35, 38, 39, 43, 47, 48, 49, 52, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 114, 115, 118, 123, 127, 129, 131, 135, 143, 159, 178, 179, 182, 187, 191, 257, 259, 263, 271, 287, 306, 307, 310, 315, 319]
def C : List Nat := [63, 59, 51, 50, 54]
def mask : Nat := 1137220148828871644812639475564098096830110468654667506759971819491589997607543931668458831243876
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 15 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    15 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=15) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G255


namespace G256
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 49, 53, 21]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 1, 2, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 37, 39, 43, 47, 48, 50, 52, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 113, 115, 117, 123, 127, 129, 131, 135, 143, 159, 177, 179, 181, 187, 191, 257, 259, 263, 271, 287, 305, 307, 309, 315, 319]
def C : List Nat := [63, 59, 51, 49, 53]
def mask : Nat := 1136112001257745684381709441109603395110495213295488897425801571061615329589318117205580563769956
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
end G256


namespace G257
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 115, 119, 87]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 6, 2, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 49, 50, 55, 57, 58, 61, 62, 65, 67, 71, 79, 83, 95, 99, 103, 113, 114, 117, 118, 123, 127, 129, 131, 135, 143, 159, 179, 187, 191, 243, 247, 257, 259, 263, 271, 287, 307, 315, 319, 371, 375]
def C : List Nat := [63, 59, 51, 115, 119]
def mask : Nat := 81766858561853778797204010144437281896131461478710618278248328861276714428174556095927632124304532262190838344292
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 15 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    15 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=15) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G257

end Snake9.LocalWindow.FamilyShare61