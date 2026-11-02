import Port95M60GenericWindow
import Port95M61GeometryBatch06
import Port95M61GeometryBatch07
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G030
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 59, 43, 107]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 1, 4, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    16≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G187.in_snake p P r hr hP
  exact (by decide : 16≤16).trans h
#print axioms in_snake
end G030
namespace G031
def W : List Nat := [0, 1, 3, 7, 15, 31, 29, 25, 57, 121, 125, 127]
def ds : List Nat := [0, 1, 2, 3, 4, 1, 2, 5, 6, 2, 1]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G188.in_snake p P r hr hP
  exact (by decide : 4≤4).trans h
#print axioms in_snake
end G031
namespace G032
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 40, 104]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 4, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G201.in_snake p P r hr hP
  exact (by decide : 4≤4).trans h
#print axioms in_snake
end G032
namespace G033
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 61, 60, 28]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 2, 0, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 41, 44, 45, 47, 49, 52, 53, 56, 59, 62, 63, 65, 67, 71, 79, 89, 91, 95, 121, 124, 125, 129, 131, 135, 143, 153, 155, 159, 185, 188, 189, 257, 259, 263, 271, 281, 283, 287, 313, 316, 317]
def C : List Nat := [27, 25, 57, 61, 60]
def mask : Nat := 417184968221394867849416731899852998553045028457212270632050620305225140386619052245359891475044
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
end G033
namespace G034
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 61, 45, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    7≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G207.in_snake p P r hr hP
  exact (by decide : 7≤7).trans h
#print axioms in_snake
end G034
end Snake9.LocalWindow.FamilyCharge67
