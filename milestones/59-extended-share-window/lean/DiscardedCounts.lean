import Mathlib.Tactic
namespace Snake9.ExtendedBudget59

/-- Seven omitted internal positions and both endpoints contribute fifteen. -/
theorem discarded_counts (alpha b : Nat → Nat) (m : Nat) (hm : 8 ≤ m)
    (h0 : 4 ≤ alpha 0) (hend : 4 ≤ alpha m)
    (hpos : ∀ i, 0 < i → i < m → 1 ≤ alpha i)
    (htrunc : ∀ i < m-8, b i ≤ alpha (8+i)) :
    (∑ i ∈ Finset.range (m-8), b i)+15 ≤ ∑ i ∈ Finset.range (m+1), alpha i := by
  have hpref : 11 ≤ ∑ i ∈ Finset.range 8, alpha i := by
    have h := Finset.sum_le_sum (s:=Finset.range 8)
      (f:=fun i => if i=0 then 4 else 1) (g:=alpha) (by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        by_cases hz : i=0
        · simpa [hz] using h0
        · simpa [hz] using hpos i (by omega) (by omega))
    norm_num [Finset.sum_range_succ] at h ⊢
    exact h
  have htail : (∑ i ∈ Finset.range (m-8), b i) ≤
      ∑ i ∈ Finset.range (m-8), alpha (8+i) :=
    Finset.sum_le_sum (by intro i hi; exact htrunc i (Finset.mem_range.mp hi))
  have hsplit := Finset.sum_range_add alpha 8 (m-8)
  have he : 8+(m-8)=m := by omega
  rw [he] at hsplit
  rw [Finset.sum_range_succ,hsplit]
  omega

#print axioms discarded_counts
end Snake9.ExtendedBudget59
