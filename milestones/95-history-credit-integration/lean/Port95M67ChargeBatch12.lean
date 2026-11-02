import Port95M60GenericWindow
import Port95M61GeometryBatch11
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G060
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 125, 93, 77, 205]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 1, 5, 4, 7]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G302.in_snake p P r hr hP
  exact (by decide : 2≤2).trans h
#print axioms in_snake
end G060
namespace G061
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 111, 103, 101, 100]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    16≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G307.in_snake p P r hr hP
  exact (by decide : 16≤16).trans h
#print axioms in_snake
end G061
namespace G062
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 127, 111, 103, 101, 229]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 6, 4, 3, 1, 7]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    16≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G308.in_snake p P r hr hP
  exact (by decide : 16≤16).trans h
#print axioms in_snake
end G062
end Snake9.LocalWindow.FamilyCharge67
