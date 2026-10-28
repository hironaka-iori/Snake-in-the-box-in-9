import GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G199
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 48, 52]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 3, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 16, 17, 19, 23, 24, 26, 29, 30, 32, 33, 35, 39, 40, 41, 47, 49, 50, 58, 59, 60, 61, 63, 65, 67, 71, 79, 89, 91, 95, 112, 120, 121, 129, 131, 135, 143, 153, 155, 159, 176, 184, 185, 257, 259, 263, 271, 281, 283, 287, 304, 312, 313]
def C : List Nat := [27, 25, 57, 56, 48]
def mask : Nat := 25063690920911634187086010663801340062129227684334361826101830275071289584418674416562631043684
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
end G199


namespace G200
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 48, 112]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 3, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 16, 17, 19, 23, 24, 26, 29, 30, 32, 33, 35, 39, 40, 41, 47, 49, 50, 52, 58, 59, 60, 61, 63, 65, 67, 71, 79, 89, 91, 95, 120, 121, 129, 131, 135, 143, 153, 155, 159, 176, 184, 185, 257, 259, 263, 271, 281, 283, 287, 304, 312, 313]
def C : List Nat := [27, 25, 57, 56, 48]
def mask : Nat := 25063690920911634187086010663801340062129227684334361826101825082774431049591050389665929194084
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
end G200


namespace G201
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 40, 104]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 4, 6]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 32, 33, 35, 39, 41, 42, 44, 47, 48, 49, 58, 59, 60, 61, 63, 65, 67, 71, 79, 89, 91, 95, 120, 121, 129, 131, 135, 143, 153, 155, 159, 168, 184, 185, 257, 259, 263, 271, 281, 283, 287, 296, 312, 313]
def C : List Nat := [27, 25, 57, 56, 40]
def mask : Nat := 25031225660038803315086107310642315597687374499983426005764811257816965878670543744500889185124
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
end G201


namespace G207
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 61, 45, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 37, 39, 41, 47, 49, 53, 56, 59, 60, 63, 65, 67, 71, 79, 89, 91, 95, 109, 121, 125, 129, 131, 135, 143, 153, 155, 159, 173, 185, 189, 257, 259, 263, 271, 281, 283, 287, 301, 313, 317]
def C : List Nat := [27, 25, 57, 61, 45]
def mask : Nat := 283689852548290656671900412155632810146305791860868549849857494183975335411596173681052506286692
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
end G207


namespace G208
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 61, 45, 109]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 37, 39, 41, 44, 47, 49, 53, 56, 59, 60, 63, 65, 67, 71, 79, 89, 91, 95, 121, 125, 129, 131, 135, 143, 153, 155, 159, 173, 185, 189, 257, 259, 263, 271, 281, 283, 287, 301, 313, 317]
def C : List Nat := [27, 25, 57, 61, 45]
def mask : Nat := 283689852548290656671900412155632810146305791860868549849857493534938228094742720132332651178596
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
end G208


namespace G215
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 41, 45, 37]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 3]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 40, 43, 44, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 91, 95, 105, 109, 121, 129, 131, 135, 143, 153, 155, 159, 169, 173, 185, 257, 259, 263, 271, 281, 283, 287, 297, 301, 313]
def C : List Nat := [27, 25, 57, 41, 45]
def mask : Nat := 16691727687673938183283482440149846992453221031201665066408907910839416934774249939972188170852
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
end G215


namespace G216
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 41, 45, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 0]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 37, 39, 40, 43, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 91, 95, 105, 109, 121, 129, 131, 135, 143, 153, 155, 159, 169, 173, 185, 257, 259, 263, 271, 281, 283, 287, 297, 301, 313]
def C : List Nat := [27, 25, 57, 41, 45]
def mask : Nat := 16691727687673938183283482440149846992453221031201665066408907910839416934774249922517441079908
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 14 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    14 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=14) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G216


namespace G217
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 41, 45, 109]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 6]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 37, 39, 40, 43, 44, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 91, 95, 105, 121, 129, 131, 135, 143, 153, 155, 159, 169, 173, 185, 257, 259, 263, 271, 281, 283, 287, 297, 301, 313]
def C : List Nat := [27, 25, 57, 41, 45]
def mask : Nat := 16691727687673938183283482440149846992453221031201665066408907261802309617920796373797585971812
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 14 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    14 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=14) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G217

end Snake9.LocalWindow.FamilyShare61