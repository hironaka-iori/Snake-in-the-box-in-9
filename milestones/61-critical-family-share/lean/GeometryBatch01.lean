import GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G034
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 22, 18]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 1, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 19, 21, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 47, 52, 54, 60, 65, 67, 71, 76, 77, 79, 84, 86, 92, 129, 131, 135, 140, 141, 143, 148, 150, 156, 257, 259, 263, 268, 269, 271, 276, 278, 284]
def C : List Nat := [13, 12, 28, 20, 22]
def mask : Nat := 31695019412113196737509695222155134806004925536395359407208409411082155599648764152692
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 10 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G034


namespace G035
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 22, 54]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 1, 5]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 16, 17, 18, 19, 21, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 47, 52, 60, 65, 67, 71, 76, 77, 79, 84, 86, 92, 129, 131, 135, 140, 141, 143, 148, 150, 156, 257, 259, 263, 268, 269, 271, 276, 278, 284]
def C : List Nat := [13, 12, 28, 20, 22]
def mask : Nat := 31695019412113196737509695222155134806004925536395359407208409411082137585250254932852
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 14 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    14 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=14) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G035


namespace G036
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 60, 62, 63]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 5, 1, 0]
def D : List Nat := [2, 4, 5, 6, 8, 9, 11, 14, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 45, 46, 47, 52, 54, 56, 58, 61, 65, 67, 71, 76, 77, 79, 92, 124, 126, 129, 131, 135, 140, 141, 143, 156, 188, 190, 257, 259, 263, 268, 269, 271, 284, 316, 318]
def C : List Nat := [13, 12, 28, 60, 62]
def mask : Nat := 667495948756372336131736939580832399191579542676439717686831208235824651792827342774504311638900
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
end G036


namespace G054
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 24, 26, 10]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 0, 1, 4]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 18, 19, 21, 23, 27, 28, 30, 33, 35, 39, 47, 56, 57, 58, 61, 63, 65, 67, 71, 79, 88, 89, 90, 93, 95, 129, 131, 135, 143, 152, 153, 154, 157, 159, 257, 259, 263, 271, 280, 281, 282, 285, 287]
def C : List Nat := [31, 29, 25, 24, 26]
def mask : Nat := 324429515256185197970276746466360353294531174479881854718452653174714233795081751456612
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 10 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=10) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G054


namespace G055
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 24, 56, 60]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 0, 5, 2]
def D : List Nat := [2, 5, 6, 8, 9, 11, 13, 14, 16, 17, 19, 21, 23, 26, 27, 28, 30, 33, 35, 39, 40, 47, 48, 57, 58, 61, 63, 65, 67, 71, 79, 88, 89, 93, 95, 120, 129, 131, 135, 143, 152, 153, 157, 159, 184, 257, 259, 263, 271, 280, 281, 285, 287, 312]
def C : List Nat := [31, 29, 25, 24, 56]
def mask : Nat := 8343699675724894696637835226323711786757612137048240264930695336332968686849498358326825282404
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
end G055


namespace G056
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 56, 60]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 0, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 40, 41, 47, 48, 49, 58, 59, 61, 63, 65, 67, 71, 79, 89, 93, 95, 120, 121, 129, 131, 135, 143, 153, 157, 159, 184, 185, 257, 259, 263, 271, 281, 285, 287, 312, 313]
def C : List Nat := [31, 29, 25, 57, 56]
def mask : Nat := 25031098391914335823123213234853875775316762168619182643789120097528084981506269221305342126692
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
end G056


namespace G057
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 59, 43]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 1, 4]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 41, 47, 49, 51, 56, 58, 61, 63, 65, 67, 71, 79, 89, 93, 95, 121, 123, 129, 131, 135, 143, 153, 157, 159, 185, 187, 257, 259, 263, 271, 281, 285, 287, 313, 315]
def C : List Nat := [31, 29, 25, 57, 59]
def mask : Nat := 83436993905376720888612088012927566409156103452385886374173978524428234647995782258169297398372
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 15 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    15 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+5)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=15) (mask:=mask) (start:=5)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G057


namespace G058
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 121, 125]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 6, 2]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 21, 23, 24, 27, 28, 30, 33, 35, 39, 41, 47, 49, 56, 59, 61, 63, 65, 67, 71, 79, 89, 93, 95, 105, 113, 120, 123, 129, 131, 135, 143, 153, 157, 159, 185, 249, 257, 259, 263, 271, 281, 285, 287, 313, 377]
def C : List Nat := [31, 29, 25, 57, 121]
def mask : Nat := 307828173409331868862617399815220263666857748442806897697718118240559729159383370714545652025780212361579052296804
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
end G058

end Snake9.LocalWindow.FamilyShare61