import Port95M60GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G218
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 125, 127]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 2, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 41, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 91, 93, 95, 105, 109, 113, 117, 120, 123, 124, 129, 131, 135, 143, 153, 155, 159, 185, 249, 253, 257, 259, 263, 271, 281, 283, 287, 313, 377, 381]
def C : List Nat := [27, 25, 57, 121, 125]
def mask : Nat := 5233078947958641770397497412286547935902881670703585169855436713137806159162463759016380526069908609301088003844708
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G218


namespace G219
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 113, 117]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 41, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 81, 89, 91, 95, 97, 105, 112, 115, 120, 123, 125, 129, 131, 135, 143, 153, 155, 159, 185, 241, 249, 257, 259, 263, 271, 281, 283, 287, 313, 369, 377]
def C : List Nat := [27, 25, 57, 121, 113]
def mask : Nat := 309030627211712071475296813834152350811460133899910428476414964053430926101565156188861882018439379934115757976164
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
end G219


namespace G221
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 113, 112]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 41, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 81, 89, 91, 95, 97, 105, 115, 117, 120, 123, 125, 129, 131, 135, 143, 153, 155, 159, 185, 241, 249, 257, 259, 263, 271, 281, 283, 287, 313, 369, 377]
def C : List Nat := [27, 25, 57, 121, 113]
def mask : Nat := 309030627211712071475296813834152350811460133899910428476414964053430926101565317150064496598095864379501963799140
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
end G221


namespace G222
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 113, 241]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 41, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 81, 89, 91, 95, 97, 105, 112, 115, 117, 120, 123, 125, 129, 131, 135, 143, 153, 155, 159, 185, 249, 257, 259, 263, 271, 281, 283, 287, 313, 369, 377]
def C : List Nat := [27, 25, 57, 121, 113]
def mask : Nat := 309030627211712071475296813834152350811456600205780871707755797458429440264533667374567603895007249697595707779684
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
end G222


namespace G224
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 105, 104]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 41, 47, 49, 56, 59, 61, 63, 65, 67, 71, 73, 79, 89, 91, 95, 97, 107, 109, 113, 120, 123, 125, 129, 131, 135, 143, 153, 155, 159, 185, 233, 249, 257, 259, 263, 271, 281, 283, 287, 313, 361, 377]
def C : List Nat := [27, 25, 57, 121, 105]
def mask : Nat := 307832870494497416529073178729789788927495015909330322154822653932459738215775920241773141418683185141217518840420
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
end G224


namespace G225
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 105, 233]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 7]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 41, 47, 49, 56, 59, 61, 63, 65, 67, 71, 73, 79, 89, 91, 95, 97, 104, 107, 109, 113, 120, 123, 125, 129, 131, 135, 143, 153, 155, 159, 185, 249, 257, 259, 263, 271, 281, 283, 287, 313, 361, 377]
def C : List Nat := [27, 25, 57, 121, 105]
def mask : Nat := 307832870494497416529073178729789788927495002105837628573695079062948013661725015359837606681561745240116322527844
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
end G225


namespace G237
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 46, 38, 36, 100]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 4, 3, 1, 6]
def D : List Nat := [2, 4, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 32, 33, 34, 35, 37, 39, 42, 44, 47, 52, 54, 55, 58, 59, 60, 61, 65, 67, 71, 79, 95, 102, 110, 126, 127, 129, 131, 135, 143, 159, 164, 166, 174, 190, 191, 257, 259, 263, 271, 287, 292, 294, 302, 318, 319]
def C : List Nat := [63, 62, 46, 38, 36]
def mask : Nat := 1601998465119112240982924490044915307315290771976513929699005129764963526516889146139027631139444
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 7 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=7) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G237


namespace G248
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 45, 37, 101, 97]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 4, 3, 6, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 27, 29, 30, 33, 35, 36, 39, 41, 44, 47, 53, 55, 57, 59, 60, 62, 65, 67, 69, 71, 79, 95, 100, 103, 109, 117, 125, 127, 129, 131, 135, 143, 159, 165, 173, 189, 191, 229, 257, 259, 263, 271, 287, 293, 301, 317, 319, 357]
def C : List Nat := [63, 61, 45, 37, 101]
def mask : Nat := 293567822848064149473870605062708743839247033470074249941004268860919027650785132037250973263823321009121892
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
end G248

end Snake9.LocalWindow.FamilyShare61