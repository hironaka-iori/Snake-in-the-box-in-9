import GenericWindow
namespace Snake9.LocalWindow.CriticalExtension60
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace T10
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
end T10


namespace T11
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55, 53]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3, 1]
def D : List Nat := [2, 5, 6, 9, 10, 11, 12, 13, 17, 19, 22, 23, 26, 28, 31, 33, 35, 39, 46, 47, 51, 54, 58, 59, 60, 61, 65, 67, 71, 78, 79, 94, 119, 126, 127, 129, 131, 135, 142, 143, 158, 183, 190, 191, 257, 259, 263, 270, 271, 286, 311, 318, 319]
def C : List Nat := [14, 30, 62, 63, 55]
def mask : Nat := 1606162126744552105795469224251144482281138173556041870144315296785899208183867446216061264477796
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 0 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    0 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=0) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T11


namespace T12
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 58]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 18, 19, 23, 27, 29, 30, 33, 34, 35, 39, 47, 48, 49, 53, 54, 59, 61, 62, 65, 67, 71, 79, 95, 114, 115, 119, 127, 129, 131, 135, 143, 159, 178, 179, 183, 191, 257, 259, 263, 271, 287, 306, 307, 311, 319]
def C : List Nat := [31, 63, 55, 51, 50]
def mask : Nat := 1072556478796109718490133935631230796485502626519068656201331440518950546191072973706823348415076
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 0 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    0 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=0) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T12


namespace T13
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 61, 45]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 2, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 41, 47, 49, 53, 56, 59, 60, 63, 65, 67, 71, 79, 89, 91, 95, 121, 125, 129, 131, 135, 143, 153, 155, 159, 185, 189, 257, 259, 263, 271, 281, 283, 287, 313, 317]
def C : List Nat := [31, 27, 25, 57, 61]
def mask : Nat := 283685778476337987699727875264255991389983676951459804962599515329453369720352696419791267326564
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 0 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    0 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=0) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T13


namespace T14
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 30, 22, 18]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 1, 3, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 23, 24, 26, 29, 31, 33, 35, 39, 44, 45, 47, 54, 60, 62, 65, 67, 71, 76, 77, 79, 86, 92, 94, 129, 131, 135, 140, 141, 143, 150, 156, 158, 257, 259, 263, 268, 269, 271, 278, 284, 286]
def C : List Nat := [13, 12, 28, 30, 22]
def mask : Nat := 155904411708795749209422790889683874899818831405701079286846609693270116148836052913012
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 0 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    0 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=0) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T14


namespace T15
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 27, 25, 24]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 2, 1, 0]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 29, 33, 35, 38, 39, 46, 57, 59, 62, 63, 65, 67, 70, 71, 78, 89, 91, 94, 95, 129, 131, 134, 135, 142, 153, 155, 158, 159, 257, 259, 262, 263, 270, 281, 283, 286, 287]
def C : List Nat := [14, 30, 31, 27, 25]
def mask : Nat := 392421036757189362452148600526708173240559057604127600941904231555549616407787042676276
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 0 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    0 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=0) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T15


namespace T16
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 24, 28, 12]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 0, 2, 4]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 19, 20, 23, 26, 29, 30, 33, 35, 39, 47, 56, 57, 59, 60, 63, 65, 67, 71, 79, 88, 89, 91, 92, 95, 129, 131, 135, 143, 152, 153, 155, 156, 159, 257, 259, 263, 271, 280, 281, 283, 284, 287]
def C : List Nat := [31, 27, 25, 24, 28]
def mask : Nat := 301117488549476449119243203584478126414753784522006294389136392711195085774119925148516
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 0 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    0 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=0) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T16


namespace T17
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 30, 22, 18]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 1, 3, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 23, 24, 26, 29, 31, 33, 35, 39, 44, 45, 47, 54, 60, 62, 65, 67, 71, 76, 77, 79, 86, 92, 94, 129, 131, 135, 140, 141, 143, 150, 156, 158, 257, 259, 263, 268, 269, 271, 278, 284, 286]
def C : List Nat := [13, 12, 28, 30, 22]
def mask : Nat := 155904411708795749209422790889683874899818831405701079286846609693270116148836052913012
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 0 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    0 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=0) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T17


namespace T18
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 27, 25, 57]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 2, 1, 5]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 24, 26, 28, 29, 33, 35, 38, 39, 46, 59, 62, 63, 65, 67, 70, 71, 78, 89, 91, 94, 95, 129, 131, 134, 135, 142, 153, 155, 158, 159, 257, 259, 262, 263, 270, 281, 283, 286, 287]
def C : List Nat := [14, 30, 31, 27, 25]
def mask : Nat := 392421036757189362452148600526708173240559057604127600941904231555549472292598983597620
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 0 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    0 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=0) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T18


namespace T19
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 24, 56, 60]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 0, 5, 2]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 19, 23, 26, 28, 29, 30, 33, 35, 39, 40, 47, 48, 57, 58, 59, 63, 65, 67, 71, 79, 88, 89, 91, 95, 120, 129, 131, 135, 143, 152, 153, 155, 159, 184, 257, 259, 263, 271, 280, 281, 283, 287, 312]
def C : List Nat := [31, 27, 25, 24, 56]
def mask : Nat := 8343699629100841283220337524256626022993158377493460349179574677700447759811202316403173190500
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 0 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    0 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=0) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end T19

end Snake9.LocalWindow.CriticalExtension60