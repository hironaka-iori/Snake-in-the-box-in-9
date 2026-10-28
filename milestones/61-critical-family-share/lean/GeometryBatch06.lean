import GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G183
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 24, 26, 10, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 0, 1, 4, 5]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 18, 19, 21, 23, 27, 28, 30, 33, 35, 39, 47, 56, 57, 58, 61, 63, 65, 67, 71, 74, 79, 88, 89, 90, 93, 95, 129, 131, 135, 138, 143, 152, 153, 154, 157, 159, 257, 259, 263, 266, 271, 280, 281, 282, 285, 287]
def C : List Nat := [29, 25, 24, 26, 10]
def mask : Nat := 324429633827284576982060860203049002190948816576795296061431216184665321839735732136804
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 9 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    9 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=9) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G183


namespace G184
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 24, 56, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 0, 5, 2, 1]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 19, 21, 23, 26, 27, 28, 30, 33, 35, 39, 40, 44, 47, 48, 52, 57, 58, 61, 63, 65, 67, 71, 79, 88, 89, 93, 95, 120, 124, 129, 131, 135, 143, 152, 153, 157, 159, 184, 188, 257, 259, 263, 271, 280, 281, 285, 287, 312, 316]
def C : List Nat := [29, 25, 24, 56, 60]
def mask : Nat := 141842889420781774846326691861920718949818963642800705934381800312104739353112395384197256801124
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
end G184


namespace G185
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 56, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 0, 2, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 40, 41, 44, 47, 48, 49, 52, 58, 59, 61, 63, 65, 67, 71, 79, 89, 93, 95, 120, 121, 124, 129, 131, 135, 143, 153, 157, 159, 184, 185, 188, 257, 259, 263, 271, 281, 285, 287, 312, 313, 316]
def C : List Nat := [29, 25, 57, 56, 60]
def mask : Nat := 158530288136971215972812069870450882938378113674371648313240225073299855647769166247175773645412
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
end G185


namespace G186
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 59, 43, 42]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 1, 4, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 41, 47, 49, 51, 56, 58, 61, 63, 65, 67, 71, 79, 89, 93, 95, 107, 121, 123, 129, 131, 135, 143, 153, 157, 159, 171, 185, 187, 257, 259, 263, 271, 281, 285, 287, 299, 313, 315]
def C : List Nat := [29, 25, 57, 59, 43]
def mask : Nat := 83438012423364888131655222235771771098236632179738072595988473238058726070806651573450247400036
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
end G186


namespace G187
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 59, 43, 107]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 1, 4, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 41, 42, 47, 49, 51, 56, 58, 61, 63, 65, 67, 71, 79, 89, 93, 95, 121, 123, 129, 131, 135, 143, 153, 157, 159, 171, 185, 187, 257, 259, 263, 271, 281, 285, 287, 299, 313, 315]
def C : List Nat := [29, 25, 57, 59, 43]
def mask : Nat := 83438012423364888131655222235771771098236632179738072595988473075799449241593288186270283623012
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
end G187


namespace G188
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 121, 125, 127]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 6, 2, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 41, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 93, 95, 105, 109, 113, 117, 120, 123, 124, 129, 131, 135, 143, 153, 157, 159, 185, 249, 253, 257, 259, 263, 271, 281, 285, 287, 313, 377, 381]
def C : List Nat := [29, 25, 57, 121, 125]
def mask : Nat := 5233078947958641770397497412333171989316299168405652255619201166897360939078214879675003143476630892918555753998948
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
end G188


namespace G190
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 24, 56, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 0, 5, 2, 1]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 19, 23, 26, 28, 29, 30, 33, 35, 39, 40, 44, 47, 48, 52, 57, 58, 59, 61, 63, 65, 67, 71, 79, 88, 89, 91, 95, 120, 124, 129, 131, 135, 143, 152, 153, 155, 159, 184, 188, 257, 259, 263, 271, 280, 281, 283, 287, 312, 316]
def C : List Nat := [27, 25, 24, 56, 60]
def mask : Nat := 141842889374157721432909194159853633186054509883245926018630679653472218426076405185282818403172
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
end G190


namespace G198
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 60, 62]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 2, 1]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 28, 29, 30, 33, 35, 39, 40, 41, 44, 47, 48, 49, 52, 58, 59, 61, 63, 65, 67, 71, 79, 89, 91, 95, 120, 121, 124, 129, 131, 135, 143, 153, 155, 159, 184, 185, 188, 257, 259, 263, 271, 281, 283, 287, 312, 313, 316]
def C : List Nat := [27, 25, 57, 56, 60]
def mask : Nat := 158530288090347162559394572168383797174613659914816868397489104414667334720732599587509098932836
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
end G198

end Snake9.LocalWindow.FamilyShare61