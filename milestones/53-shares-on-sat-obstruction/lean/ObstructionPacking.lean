import Mathlib.Tactic
namespace Snake9.ObstructionPacking

def firstArc : Finset (Fin 16) := {13,14,15,0,1}
def secondArc : Finset (Fin 16) := {6,7,8,9,10}

theorem disjoint_arcs : Disjoint firstArc secondArc := by decide

theorem one_window (s : Fin 16 → Nat) (h : 96 ≤ ∑ i ∈ firstArc, s i) :
    96 ≤ ∑ i : Fin 16, s i := by
  exact h.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ firstArc))

theorem two_windows (s : Fin 16 → Nat)
    (h1 : 96 ≤ ∑ i ∈ firstArc, s i) (h2 : 96 ≤ ∑ i ∈ secondArc, s i) :
    192 ≤ ∑ i : Fin 16, s i := by
  have h := Finset.sum_le_sum_of_subset (f := s) (Finset.subset_univ (firstArc ∪ secondArc))
  rw [Finset.sum_union disjoint_arcs] at h
  omega

/-- Conditional cyclic charge arithmetic; boundary and all-cycle coverage are separate. -/
theorem one_window_charge (s : Fin 16 → Nat) (h : 96 ≤ ∑ i ∈ firstArc, s i) :
    24*69 ≤ 24*65 + ∑ i : Fin 16, s i := by
  have := one_window s h
  omega

theorem two_window_charge (s : Fin 16 → Nat)
    (h1 : 96 ≤ ∑ i ∈ firstArc, s i) (h2 : 96 ≤ ∑ i ∈ secondArc, s i) :
    24*73 ≤ 24*65 + ∑ i : Fin 16, s i := by
  have := two_windows s h1 h2
  omega

#print axioms disjoint_arcs
#print axioms one_window
#print axioms two_windows
#print axioms one_window_charge
#print axioms two_window_charge
end Snake9.ObstructionPacking
