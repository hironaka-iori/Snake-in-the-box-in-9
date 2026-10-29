import GenericWindow
import GeometryBatch04
import GeometryBatch05
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G015
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55, 53, 49]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 2]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    8≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G135.in_snake p P r hr hP
  exact (by decide : 8≤8).trans h
#print axioms in_snake
end G015
namespace G016
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55, 53, 37]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 4]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    12≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G137.in_snake p P r hr hP
  exact (by decide : 12≤12).trans h
#print axioms in_snake
end G016
namespace G017
def W : List Nat := [0, 1, 3, 7, 15, 14, 30, 62, 63, 55, 53, 117]
def ds : List Nat := [0, 1, 2, 3, 0, 4, 5, 0, 3, 1, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    16≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G138.in_snake p P r hr hP
  exact (by decide : 16≤16).trans h
#print axioms in_snake
end G017
namespace G018
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 24, 56, 48, 52]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 2, 5, 3, 2]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G152.in_snake p P r hr hP
  exact (by decide : 5≤5).trans h
#print axioms in_snake
end G018
namespace G019
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 20, 22, 54, 118]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 3, 1, 5, 6]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    13≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G156.in_snake p P r hr hP
  exact (by decide : 13≤13).trans h
#print axioms in_snake
end G019
end Snake9.LocalWindow.FamilyCharge67
