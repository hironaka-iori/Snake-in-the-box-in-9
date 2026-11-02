import Port95M60GenericWindow
import Port95M61GeometryBatch10
import Port95M61GeometryBatch11
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G050
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 112]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 0]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    20≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G277.in_snake p P r hr hP
  exact (by decide : 20≤20).trans h
#print axioms in_snake
end G050
namespace G051
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 121]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 3]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    20≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G292.in_snake p P r hr hP
  exact (by decide : 20≤20).trans h
#print axioms in_snake
end G051
namespace G052
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 97]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 4]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G275.in_snake p P r hr hP
  exact (by decide : 10≤10).trans h
#print axioms in_snake
end G052
namespace G053
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 81]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 5]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    10≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G276.in_snake p P r hr hP
  exact (by decide : 10≤10).trans h
#print axioms in_snake
end G053
namespace G054
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 115, 113, 241]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 6, 1, 7]
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    20≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  have h := Snake9.LocalWindow.FamilyShare61.G278.in_snake p P r hr hP
  exact (by decide : 20≤20).trans h
#print axioms in_snake
end G054
end Snake9.LocalWindow.FamilyCharge67
