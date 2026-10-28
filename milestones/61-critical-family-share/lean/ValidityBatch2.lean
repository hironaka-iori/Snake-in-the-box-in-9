import GenericWindow
namespace Snake9.LocalWindow.FamilyValidity61
open CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace F18
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 46, 38, 34, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 4, 3, 2, 1]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2≤cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F18


namespace F19
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 60, 28, 12, 8]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 0, 5, 4, 2]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2≤cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F19


namespace F20
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 60, 28, 12, 4]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 0, 5, 4, 3]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2≤cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F20


namespace F21
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 61, 45, 37, 36, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 1, 4, 3, 0, 2]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2≤cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F21


namespace F22
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 48, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2≤cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F22


namespace F23
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 48, 16]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 5]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2≤cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F23


namespace F24
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 34, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 4, 1]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2≤cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F24


namespace F25
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 49, 48, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 1, 0, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2≤cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F25


namespace F26
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 49, 48, 16]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 1, 0, 5]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2≤cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F26

end Snake9.LocalWindow.FamilyValidity61