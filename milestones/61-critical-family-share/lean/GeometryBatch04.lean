import GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G134
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 22, 18, 50, 34, 42]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 3, 2, 5, 4, 3]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 16, 17, 19, 20, 23, 26, 28, 31, 32, 33, 35, 38, 39, 46, 47, 48, 51, 54, 58, 62, 65, 67, 71, 78, 79, 82, 86, 94, 98, 114, 129, 131, 135, 142, 143, 146, 150, 158, 162, 178, 257, 259, 263, 270, 271, 274, 278, 286, 290, 306]
def C : List Nat := [30, 22, 18, 50, 34]
def mask : Nat := 130372416630890667690376284168164709147322970786369456998219468541773335879217680870018858596
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
end G134


namespace G135
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55, 53, 49]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 2]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 21, 22, 23, 26, 28, 31, 33, 35, 37, 39, 46, 47, 51, 52, 54, 58, 59, 60, 61, 65, 67, 71, 78, 79, 94, 117, 119, 126, 127, 129, 131, 135, 142, 143, 158, 181, 183, 190, 191, 257, 259, 263, 270, 271, 286, 309, 311, 318, 319]
def C : List Nat := [30, 62, 63, 55, 53]
def mask : Nat := 1607205089164435362671638668443610083899599590364680561282357883543522425142197629567491134602852
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
end G135


namespace G136
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55, 53, 52]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 0]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 21, 22, 23, 26, 28, 31, 33, 35, 37, 39, 46, 47, 49, 51, 54, 58, 59, 60, 61, 65, 67, 71, 78, 79, 94, 117, 119, 126, 127, 129, 131, 135, 142, 143, 158, 181, 183, 190, 191, 257, 259, 263, 270, 271, 286, 309, 311, 318, 319]
def C : List Nat := [30, 62, 63, 55, 53]
def mask : Nat := 1607205089164435362671638668443610083899599590364680561282357883543522425142197625626841460653668
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
end G136


namespace G137
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55, 53, 37]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 4]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 21, 22, 23, 26, 28, 31, 33, 35, 39, 46, 47, 49, 51, 52, 54, 58, 59, 60, 61, 65, 67, 71, 78, 79, 94, 117, 119, 126, 127, 129, 131, 135, 142, 143, 158, 181, 183, 190, 191, 257, 259, 263, 270, 271, 286, 309, 311, 318, 319]
def C : List Nat := [30, 62, 63, 55, 53]
def mask : Nat := 1607205089164435362671638668443610083899599590364680561282357883543522425142197630130303649070692
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 12 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    12 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=12) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G137


namespace G138
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55, 53, 117]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 6]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 21, 22, 23, 26, 28, 31, 33, 35, 37, 39, 46, 47, 49, 51, 52, 54, 58, 59, 60, 61, 65, 67, 71, 78, 79, 94, 119, 126, 127, 129, 131, 135, 142, 143, 158, 181, 183, 190, 191, 257, 259, 263, 270, 271, 286, 309, 311, 318, 319]
def C : List Nat := [30, 62, 63, 55, 53]
def mask : Nat := 1607205089164435362671638668443610083899599590364680561282357717390022952027713517154558552981092
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
end G138


namespace G152
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 24, 56, 48, 52]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 2, 5, 3, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 19, 20, 23, 25, 26, 29, 30, 31, 32, 33, 35, 39, 40, 44, 45, 47, 49, 50, 57, 58, 60, 65, 67, 71, 76, 77, 79, 88, 92, 112, 120, 129, 131, 135, 140, 141, 143, 152, 156, 176, 184, 257, 259, 263, 268, 269, 271, 280, 284, 304, 312]
def C : List Nat := [12, 28, 24, 56, 48]
def mask : Nat := 8376291967718011062254234144506188281364557798704993371803171614903614696727550970139799931764
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
end G152


namespace G154
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 22, 18, 50]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 1, 2, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 19, 21, 23, 24, 26, 29, 30, 31, 33, 35, 39, 44, 45, 47, 52, 54, 60, 65, 67, 71, 76, 77, 79, 82, 84, 86, 92, 129, 131, 135, 140, 141, 143, 146, 148, 150, 156, 257, 259, 263, 268, 269, 271, 274, 276, 278, 284]
def C : List Nat := [12, 28, 20, 22, 18]
def mask : Nat := 31725373613554223754242811814449252288921302346236343209720539958560695031067885390708
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
end G154


namespace G155
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 22, 54, 50]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 18, 19, 21, 23, 24, 29, 30, 31, 33, 35, 38, 39, 44, 45, 47, 52, 55, 60, 62, 65, 67, 71, 76, 77, 79, 84, 86, 92, 118, 129, 131, 135, 140, 141, 143, 148, 150, 156, 182, 257, 259, 263, 268, 269, 271, 276, 278, 284, 310]
def C : List Nat := [12, 28, 20, 22, 54]
def mask : Nat := 2085924871461533164452085122440898459077968423282307812480532922454843327747142995726182599540
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 13 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    13 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=13) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G155

end Snake9.LocalWindow.FamilyShare61