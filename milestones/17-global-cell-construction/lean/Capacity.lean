import CycleCuts
namespace Snake9.GlobalCells.Capacity
open Finset
def profiles : List (Nat × Nat) := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0),(6,1),(6,2),(7,0),(7,1),(7,2),(8,0),(8,1),(8,2),(9,1),(9,2),(10,0),(10,1),(10,2),(11,1),(11,2),(12,1),(12,2),(13,1),(13,2),(14,1),(14,2)]
theorem profiles_checked : profiles.all (fun r => decide (r.1 ≤ 10+4*r.2)) = true := by decide
theorem profile_bound (c e : Nat) (h : (c,e) ∈ profiles) : c ≤ 10+4*e := by
  exact of_decide_eq_true (List.all_eq_true.mp profiles_checked (c,e) h)
/-- The geometric application requires the separate local census premise. -/
theorem conditional_total (c e : Fin 16 → Nat)
    (h : ∀ i, c i ≤ 10+4*e i) (he : (∑ i, e i) ≤ 2) :
    (∑ i, c i) ≤ 168 := by
  calc
    (∑ i, c i) ≤ ∑ i, (10+4*e i) := Finset.sum_le_sum (fun i _ => h i)
    _ = 160+4*(∑ i, e i) := by simp [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 168 := by omega
theorem table_total (c e : Fin 16 → Nat)
    (h : ∀ i, (c i,e i) ∈ profiles) (he : (∑ i, e i) ≤ 2) :
    (∑ i, c i) ≤ 168 :=
  conditional_total c e (fun i => profile_bound _ _ (h i)) he
#print axioms profiles_checked
#print axioms profile_bound
#print axioms conditional_total
#print axioms table_total
end Snake9.GlobalCells.Capacity
