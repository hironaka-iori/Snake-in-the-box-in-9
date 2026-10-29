import GenericWindow
import GeometryBatch07
import GeometryBatch08
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G035
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 61, 45, 109]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 2, 4, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    7≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G208.in_snake p P r hr hP
  exact (by decide : 7≤7).trans h
#print axioms in_snake
end G035
namespace G036
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 61, 125, 93]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 2, 6, 5]
def D : List Nat := [2, 5, 6, 9, 11, 13, 14, 17, 19, 23, 24, 26, 29, 30, 33, 35, 39, 41, 45, 47, 49, 53, 56, 59, 60, 63, 65, 67, 71, 79, 89, 91, 95, 109, 117, 121, 124, 127, 129, 131, 135, 143, 153, 155, 159, 185, 189, 253, 257, 259, 263, 271, 281, 283, 287, 313, 317, 381]
def C : List Nat := [27, 25, 57, 61, 125]
def mask : Nat := 4925250774549309901818565790994289713349169295227101349311466725608261014881558630177506213095002142489739254196836
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
end G036
namespace G037
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 41, 45, 44]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    14≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G216.in_snake p P r hr hP
  exact (by decide : 14≤14).trans h
#print axioms in_snake
end G037
namespace G038
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 41, 45, 109]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 4, 2, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    14≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G217.in_snake p P r hr hP
  exact (by decide : 14≤14).trans h
#print axioms in_snake
end G038
namespace G039
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 113, 112]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G221.in_snake p P r hr hP
  exact (by decide : 5≤5).trans h
#print axioms in_snake
end G039
end Snake9.LocalWindow.FamilyCharge67
