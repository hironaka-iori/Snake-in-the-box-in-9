import GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G071
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 41, 45]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 4, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 40, 43, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 91, 95, 105, 121, 129, 131, 135, 143, 153, 155, 159, 169, 185, 257, 259, 263, 271, 281, 283, 287, 297, 313]
def C : List Nat := [31, 27, 25, 57, 41]
def mask : Nat := 16687653615721269211110945548773028236131106121792920179150929056317451243530772661256202119780
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 8 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    8 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=8) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G071


namespace G087
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 50, 54]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 0, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 23, 27, 29, 30, 33, 34, 35, 39, 43, 47, 48, 49, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 114, 115, 123, 127, 129, 131, 135, 143, 159, 178, 179, 187, 191, 257, 259, 263, 271, 287, 306, 307, 315, 319]
def C : List Nat := [31, 63, 59, 51, 50]
def mask : Nat := 1135134223989105131060300587179166893593187635037390124483886645976343563690883569469198722558564
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 5 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G087


namespace G088
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 49, 53]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 1, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 48, 50, 55, 57, 58, 61, 62, 65, 67, 71, 79, 95, 113, 115, 123, 127, 129, 131, 135, 143, 159, 177, 179, 187, 191, 257, 259, 263, 271, 287, 305, 307, 315, 319]
def C : List Nat := [31, 63, 59, 51, 49]
def mask : Nat := 1135069038837862427505539996917137793492033796486850206287758984303992112630987933854150695742052
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 5 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G088


namespace G089
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 115, 119]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 6, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 39, 43, 47, 49, 50, 55, 57, 58, 61, 62, 65, 67, 71, 79, 83, 95, 99, 113, 114, 123, 127, 129, 131, 135, 143, 159, 179, 187, 191, 243, 257, 259, 263, 271, 287, 307, 315, 319, 371]
def C : List Nat := [31, 63, 59, 51, 115]
def mask : Nat := 4809815209520811585721509948844286182858939291791159560725156226014195523192650211069439973314691667853706947172
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 5 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G089


namespace G112
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 27, 59, 57, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 2, 5, 1, 0]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 25, 26, 28, 29, 33, 35, 38, 39, 41, 43, 46, 49, 51, 58, 61, 62, 63, 65, 67, 70, 71, 78, 91, 94, 95, 121, 123, 129, 131, 134, 135, 142, 155, 158, 159, 185, 187, 257, 259, 262, 263, 270, 283, 286, 287, 313, 315]
def C : List Nat := [30, 31, 27, 59, 57]
def mask : Nat := 83436993979196249066293439707557806189974480118358116987888614830208878144712753324762153524788
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
end G112


namespace G117
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 25, 57, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 1, 5, 0]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 29, 31, 33, 35, 38, 39, 41, 46, 49, 58, 59, 61, 62, 65, 67, 70, 71, 78, 89, 90, 91, 94, 121, 129, 131, 134, 135, 142, 153, 154, 155, 158, 185, 257, 259, 262, 263, 270, 281, 282, 283, 286, 313]
def C : List Nat := [30, 26, 27, 25, 57]
def mask : Nat := 16687398869662204139910064737584949975974497754411752914761532327607678099136777380569809854004
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
end G117


namespace G118
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 59, 57, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 5, 1, 0]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 25, 28, 31, 33, 35, 38, 39, 41, 43, 46, 49, 51, 58, 61, 62, 63, 65, 67, 70, 71, 78, 90, 91, 94, 121, 123, 129, 131, 134, 135, 142, 154, 155, 158, 185, 187, 257, 259, 262, 263, 270, 282, 283, 286, 313, 315]
def C : List Nat := [30, 26, 27, 59, 57]
def mask : Nat := 83436993738305306430303034913544529743858135693991754089841158093940853355023825583150145117748
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 25 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    25 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=25) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G118


namespace G119
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 59, 123, 122]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 5, 6, 0]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 25, 28, 31, 33, 35, 38, 39, 43, 46, 51, 57, 58, 62, 63, 65, 67, 70, 71, 78, 90, 91, 94, 107, 115, 121, 127, 129, 131, 134, 135, 142, 154, 155, 158, 187, 251, 257, 259, 262, 263, 270, 282, 283, 286, 315, 379]
def C : List Nat := [30, 26, 27, 59, 123]
def mask : Nat := 1231312693637327475450469598149661127823952282824806243328846228919972998361024496115586374957454121099452459425332
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
end G119

end Snake9.LocalWindow.FamilyShare61