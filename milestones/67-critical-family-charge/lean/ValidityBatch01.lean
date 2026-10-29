import GenericWindow
namespace Snake9.LocalWindow.FamilyCharge67
open CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Rejected08
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 24, 56, 48, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 0, 5, 3, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected08
namespace Rejected09
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 24, 56, 40, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 0, 5, 4, 3]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected09
namespace Rejected10
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 48, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 3, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected10
namespace Rejected11
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 40, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 4, 3]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected11
namespace Rejected12
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 49, 48, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 3, 0, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected12
namespace Rejected13
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 59, 43, 41, 40, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 5, 4, 1, 0, 3]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected13
namespace Rejected14
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 60, 28, 12, 8]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 1, 5, 4, 2]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected14
namespace Rejected15
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 60, 28, 12, 4]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 1, 5, 4, 3]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v) := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False :=
  cycle_window_forbidden (W:=W) (cs:=ds) canonical (by decide) (by decide) cycle p P r hr hP
#print axioms canonical
#print axioms cycle
#print axioms impossible
end Rejected15
end Snake9.LocalWindow.FamilyCharge67
