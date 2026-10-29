import GenericWindow
import GeometryBatch09
import GeometryBatch10
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G045
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 125, 93, 77, 73]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 2]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G251.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G045
namespace G046
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 125, 93, 77, 205]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 6, 5, 4, 7]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G254.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G046
namespace G047
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 59, 51, 115, 119, 87]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 2, 3, 6, 2, 5]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    15≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G257.in_snake p P r hr hP
  exact (by decide : 15≤15).trans h
#print axioms in_snake
end G047
namespace G048
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 48, 112]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G258.in_snake p P r hr hP
  exact (by decide : 10≤10).trans h
#print axioms in_snake
end G048
namespace G049
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 34, 98]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 4, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G260.in_snake p P r hr hP
  exact (by decide : 4≤4).trans h
#print axioms in_snake
end G049
end Snake9.LocalWindow.FamilyCharge67
