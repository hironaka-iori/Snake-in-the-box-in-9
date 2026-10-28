import GenericWindow
namespace Snake9.LocalWindow.FamilyValidity61
open CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace F09
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 24, 56, 48, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 0, 5, 3, 4]
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
end F09


namespace F10
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 24, 56, 40, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 0, 5, 4, 3]
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
end F10


namespace F11
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 48, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 3, 4]
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
end F11


namespace F12
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 56, 40, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 0, 4, 3]
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
end F12


namespace F13
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 57, 49, 48, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 5, 3, 0, 4]
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
end F13


namespace F14
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 60, 28, 12, 8]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 1, 5, 4, 2]
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
end F14


namespace F15
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 60, 28, 12, 4]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 1, 5, 4, 3]
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
end F15


namespace F16
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 58, 26, 10, 8]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 2, 5, 4, 1]
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
end F16


namespace F17
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 62, 46, 38, 36, 32]
def ds : List Nat := [0, 1, 2, 3, 4, 5, 0, 4, 3, 1, 2]
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
end F17

end Snake9.LocalWindow.FamilyValidity61