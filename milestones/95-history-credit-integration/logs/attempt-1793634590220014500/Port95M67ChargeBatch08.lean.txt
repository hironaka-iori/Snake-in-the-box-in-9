import Port95M60GenericWindow
import Port95M61GeometryBatch08
import Port95M61GeometryBatch09
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G040
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 113, 241]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 3, 7]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G222.in_snake p P r hr hP
  exact (by decide : 5≤5).trans h
#print axioms in_snake
end G040
namespace G041
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 105, 104]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G224.in_snake p P r hr hP
  exact (by decide : 5≤5).trans h
#print axioms in_snake
end G041
namespace G042
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 121, 105, 233]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 6, 4, 7]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G225.in_snake p P r hr hP
  exact (by decide : 5≤5).trans h
#print axioms in_snake
end G042
namespace G043
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 46, 38, 36, 100]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 4, 3, 1, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    7≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G237.in_snake p P r hr hP
  exact (by decide : 7≤7).trans h
#print axioms in_snake
end G043
namespace G044
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 125, 93, 77, 76]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G253.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G044
end Snake9.LocalWindow.FamilyCharge67
