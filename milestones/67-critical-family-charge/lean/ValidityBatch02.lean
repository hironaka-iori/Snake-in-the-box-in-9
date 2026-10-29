import GenericWindow
namespace Snake9.LocalWindow.FamilyCharge67
open CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Rejected16
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 46, 38, 34, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 4, 3, 2, 1]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected16
namespace Rejected17
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 60, 28, 12, 8]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 0, 5, 4, 2]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected17
namespace Rejected18
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 60, 28, 12, 4]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 0, 5, 4, 3]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected18
namespace Rejected19
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 54, 22, 18, 16]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 0, 5, 2, 1]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected19
namespace Rejected20
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 48, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected20
namespace Rejected21
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 48, 16]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 5]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected21
namespace Rejected22
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 34, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 4, 1]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected22
namespace Rejected23
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 49, 48, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 1, 0, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected23
end Snake9.LocalWindow.FamilyCharge67
