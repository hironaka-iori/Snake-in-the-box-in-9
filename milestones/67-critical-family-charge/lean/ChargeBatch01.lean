import GenericWindow
import GeometryBatch02
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G005
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 27, 59, 58, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 2, 5, 0, 1]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 25, 26, 28, 29, 33, 35, 38, 39, 42, 43, 46, 50, 51, 57, 62, 63, 65, 67, 70, 71, 78, 91, 94, 95, 122, 123, 129, 131, 134, 135, 142, 155, 158, 159, 186, 187, 257, 259, 262, 263, 270, 283, 286, 287, 314, 315]
def C : List Nat := [30, 31, 27, 59, 58]
def mask : Nat := 100124392697328359085004546787007432085357149056577175196570002952180349477993165494798667914804
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G005
namespace G006
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 27, 59, 58, 122]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 2, 5, 0, 6]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 25, 26, 28, 29, 33, 35, 38, 39, 42, 43, 46, 50, 51, 56, 57, 62, 63, 65, 67, 70, 71, 78, 91, 94, 95, 123, 129, 131, 134, 135, 142, 155, 158, 159, 186, 187, 257, 259, 262, 263, 270, 283, 286, 287, 314, 315]
def C : List Nat := [30, 31, 27, 59, 58]
def mask : Nat := 100124392697328359085004546787007432085357149056577175196564686040197209814501622324151584464436
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 6≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    6≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=6) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G006
namespace G007
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 27, 59, 57, 56]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 2, 5, 1, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    20≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G112.in_snake p P r hr hP
  exact (by decide : 20≤20).trans h
#print axioms in_snake
end G007
namespace G008
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 29, 21, 53, 49]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 0, 3, 5, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 25, 30, 31, 33, 35, 37, 39, 44, 46, 47, 52, 55, 60, 61, 65, 67, 71, 76, 78, 79, 85, 92, 93, 117, 129, 131, 135, 140, 142, 143, 149, 156, 157, 181, 257, 259, 263, 268, 270, 271, 277, 284, 285, 309]
def C : List Nat := [12, 28, 29, 21, 53]
def mask : Nat := 1042962513380378991008679092873588644948938003727938285988498823357925115329645066496648032116
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 9≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    9≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=9) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G008
namespace G009
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 29, 21, 53, 117]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 0, 3, 5, 6]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 25, 30, 31, 33, 35, 37, 39, 44, 46, 47, 49, 52, 55, 60, 61, 65, 67, 71, 76, 78, 79, 85, 92, 93, 129, 131, 135, 140, 142, 143, 149, 156, 157, 181, 257, 259, 263, 268, 270, 271, 277, 284, 285, 309]
def C : List Nat := [12, 28, 29, 21, 53]
def mask : Nat := 1042962513380378991008679092873588644948938003727938285988332669858452000845532653564066410356
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 9≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    9≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=9) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G009
end Snake9.LocalWindow.FamilyCharge67
