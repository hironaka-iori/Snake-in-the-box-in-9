import GenericWindow
namespace Snake9.LocalWindow.CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace F14
def W : List Nat := [0, 1, 3, 7, 15, 13, 12, 28, 30, 22, 18, 16]
def ds : List Nat := [0, 1, 2, 3, 1, 0, 4, 1, 3, 2, 1]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2 ≤ cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
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
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 31, 27, 25, 24, 8]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 0, 2, 1, 0, 4]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2 ≤ cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
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
def W : List Nat := [0, 1, 3, 7, 15, 31, 27, 25, 24, 28, 12, 4]
def ds : List Nat := [0, 1, 2, 3, 4, 2, 1, 0, 2, 4, 3]
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem cycle_checked : W.all (fun v => decide (2 ≤ cnt (fun x => W.contains x) (nbrs v)))=true := by decide +kernel
theorem impossible {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) : False := by
  apply cycle_window_forbidden canonical (by decide) (by decide) ?_ p P r hr hP
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp cycle_checked v hv)
#print axioms canonical
#print axioms cycle_checked
#print axioms impossible
end F16

end Snake9.LocalWindow.CriticalExtension60