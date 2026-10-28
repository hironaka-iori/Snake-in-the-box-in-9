import GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G008
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 25, 57]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 1, 5]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 28, 29, 31, 33, 35, 38, 39, 46, 58, 59, 62, 65, 67, 70, 71, 78, 89, 90, 91, 94, 129, 131, 134, 135, 142, 153, 154, 155, 158, 257, 259, 262, 263, 270, 281, 282, 283, 286]
def C : List Nat := [14, 30, 26, 27, 25]
def mask : Nat := 151530094121198957658135324080591828816192694706080144205636206765851609409326792220212
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
end G008


namespace G009
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 59, 57]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 5, 1]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 25, 28, 31, 33, 35, 38, 39, 43, 46, 51, 58, 62, 63, 65, 67, 70, 71, 78, 90, 91, 94, 123, 129, 131, 134, 135, 142, 154, 155, 158, 187, 257, 259, 262, 263, 270, 282, 283, 286, 315]
def C : List Nat := [14, 30, 26, 27, 59]
def mask : Nat := 66749595020173196411591927834094903848475466755772695881159769971969382021738657611907127483956
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
end G009


namespace G010
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 26, 27, 59, 123]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 2, 0, 5, 6]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 18, 19, 22, 23, 24, 25, 28, 31, 33, 35, 38, 39, 43, 46, 51, 57, 58, 62, 63, 65, 67, 70, 71, 78, 90, 91, 94, 129, 131, 134, 135, 142, 154, 155, 158, 187, 257, 259, 262, 263, 270, 282, 283, 286, 315]
def C : List Nat := [14, 30, 26, 27, 59]
def mask : Nat := 66749595020173196411591927834094903848475466755772695881149136148003102694755571270612960583220
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
end G010


namespace G011
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55, 53]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3, 1]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 51, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 119, 126, 127, 129, 131, 134, 135, 142, 158, 183, 190, 191, 257, 259, 262, 263, 270, 286, 311, 318, 319]
def C : List Nat := [14, 30, 62, 63, 55]
def mask : Nat := 1606162126744548318930982807062289349815644449426703425674142263894521352053554571790199634435636
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G011


namespace G012
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55, 51]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3, 2]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 53, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 119, 126, 127, 129, 131, 134, 135, 142, 158, 183, 190, 191, 257, 259, 262, 263, 270, 286, 311, 318, 319]
def C : List Nat := [14, 30, 62, 63, 55]
def mask : Nat := 1606162126744548318930982807062289349815644449426703425674142263894521352053554578545599075491380
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G012


namespace G013
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55, 119]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3, 6]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 51, 53, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 126, 127, 129, 131, 134, 135, 142, 158, 183, 190, 191, 257, 259, 262, 263, 270, 286, 311, 318, 319]
def C : List Nat := [14, 30, 62, 63, 55]
def mask : Nat := 1606162126744548318930982807062289349815644449426703425674141599280523459595618128893868749004340
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G013


namespace G023
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 29, 21, 53]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 0, 3, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 25, 30, 31, 33, 35, 39, 44, 46, 47, 60, 61, 65, 67, 71, 76, 78, 79, 85, 92, 93, 129, 131, 135, 140, 142, 143, 149, 156, 157, 257, 259, 263, 268, 270, 271, 277, 284, 285]
def C : List Nat := [14, 12, 28, 29, 21]
def mask : Nat := 93497122114839234900407987026487521195089247147945912065734708156999425686269761040244
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 9 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    9 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=9) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G023


namespace G024
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 62, 63]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 1, 0]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 54, 56, 58, 61, 65, 67, 71, 76, 78, 79, 92, 124, 126, 129, 131, 135, 140, 142, 143, 156, 188, 190, 257, 259, 263, 268, 270, 271, 284, 316, 318]
def C : List Nat := [14, 12, 28, 60, 62]
def mask : Nat := 667495948756373284700531971675105309085088733847780854462138738979653155872436047096551784984436
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 4 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=4) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G024

end Snake9.LocalWindow.FamilyShare61