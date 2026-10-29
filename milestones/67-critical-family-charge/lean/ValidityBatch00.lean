import GenericWindow
namespace Snake9.LocalWindow.FamilyCharge67
open CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Rejected00
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 27, 25, 24, 8]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 2, 1, 0, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected00
namespace Rejected01
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 60, 56, 24, 8]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 1, 2, 5, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected01
namespace Rejected02
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 58, 56, 24, 8]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 2, 1, 5, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected02
namespace Rejected03
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 30, 22, 18, 16]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 1, 3, 2, 1]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected03
namespace Rejected04
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 60, 56, 48, 16]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 5, 2, 3, 5]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected04
namespace Rejected05
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 60, 52, 48, 16]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 5, 3, 2, 5]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected05
namespace Rejected06
def W : List Nat := [0, 1, 3, 7, 15, 31, 30, 62, 46, 38, 34, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 0, 5, 4, 3, 2, 1]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected06
namespace Rejected07
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 24, 28, 12, 4]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 0, 2, 4, 3]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected07
end Snake9.LocalWindow.FamilyCharge67
