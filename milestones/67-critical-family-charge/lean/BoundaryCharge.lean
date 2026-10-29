import Aggregate247
import ExtendedBudget

namespace Snake9.BoundaryCharge67
open SquareIncidence

/-- Three disjoint internal pairs and the seventh positive count. -/
theorem seven_internal_counts {m : Nat} (p : Snake m) (hm : 8 ≤ m) :
    13 ≤ localAlpha p ⟨1,by omega⟩ + localAlpha p ⟨2,by omega⟩ +
      localAlpha p ⟨3,by omega⟩ + localAlpha p ⟨4,by omega⟩ +
      localAlpha p ⟨5,by omega⟩ + localAlpha p ⟨6,by omega⟩ +
      localAlpha p ⟨7,by omega⟩ := by
  have h12 := adjacent_internal_alpha_sum_ge_four p ⟨1,by omega⟩ (by dsimp; omega) (by dsimp; omega)
  have h34 := adjacent_internal_alpha_sum_ge_four p ⟨3,by omega⟩ (by dsimp; omega) (by dsimp; omega)
  have h56 := adjacent_internal_alpha_sum_ge_four p ⟨5,by omega⟩ (by dsimp; omega) (by dsimp; omega)
  have h7 := localAlpha_positive p ⟨7,by omega⟩
  change 4 ≤ localAlpha p ⟨1,by omega⟩ + localAlpha p ⟨2,by omega⟩ at h12
  change 4 ≤ localAlpha p ⟨3,by omega⟩ + localAlpha p ⟨4,by omega⟩ at h34
  change 4 ≤ localAlpha p ⟨5,by omega⟩ + localAlpha p ⟨6,by omega⟩ at h56
  omega

theorem discarded_counts (alpha b : Nat → Nat) (m : Nat) (hm : 8 ≤ m)
    (h0 : 4 ≤ alpha 0) (hend : 4 ≤ alpha m)
    (hpos : ∀ i, 0 < i → i < m → 1 ≤ alpha i)
    (hpair : ∀ i, 0 < i → i+1 < m → 4 ≤ alpha i+alpha (i+1))
    (htrunc : ∀ i < m-8, b i ≤ alpha (8+i)) :
    (∑ i ∈ Finset.range (m-8), b i)+21 ≤ ∑ i ∈ Finset.range (m+1), alpha i := by
  have hpref : 17 ≤ ∑ i ∈ Finset.range 8, alpha i := by
    have h12 := hpair 1 (by omega) (by omega)
    have h34 := hpair 3 (by omega) (by omega)
    have h56 := hpair 5 (by omega) (by omega)
    have h7 := hpos 7 (by omega) (by omega)
    norm_num at h12 h34 h56
    norm_num [Finset.sum_range_succ]
    omega
  have htail : (∑ i ∈ Finset.range (m-8), b i) ≤
      ∑ i ∈ Finset.range (m-8), alpha (8+i) :=
    Finset.sum_le_sum (by intro i hi; exact htrunc i (Finset.mem_range.mp hi))
  have hsplit := Finset.sum_range_add alpha 8 (m-8)
  have he : 8+(m-8)=m := by omega
  rw [he] at hsplit
  rw [Finset.sum_range_succ,hsplit]
  omega

theorem aggregate_charge (B T S L G : Nat)
    (ht : B+21 ≤ T) (hl : L ≤ 5*S) (hg : G=24*T+S) :
    120*B+L+2520 ≤ 5*G := by omega

theorem global_charge (m G W : Nat)
    (hg : G+840*(m+1) ≤ 221136) (hw : W+2520 ≤ 5*G) :
    W+4200*m ≤ 1098960 := by omega

/-- Conditional on the full-model path inequality, not a global snake theorem. -/
theorem conditional_bound (m W : ℤ)
    (hb : W+4200*m ≤ 1098960)
    (hp : 2482*(m-8) ≤ 5*W+3238) : 23482*m ≤ 5517894 := by omega

theorem conditional_integer_bound (m : ℤ) (h : 23482*m ≤ 5517894) : m ≤ 234 := by omega

theorem old_boundary_allows_235 : (23482:ℤ)*235 ≤ 5521494 := by norm_num
theorem improved_boundary_excludes_235 : (5517894:ℤ) < 23482*235 := by norm_num
theorem mean_improvement : (2482:ℚ)/5-18823/38=201/190 := by norm_num

#print axioms seven_internal_counts
#print axioms discarded_counts
#print axioms aggregate_charge
#print axioms global_charge
#print axioms conditional_bound
#print axioms conditional_integer_bound
#print axioms old_boundary_allows_235
#print axioms improved_boundary_excludes_235
#print axioms mean_improvement
end Snake9.BoundaryCharge67
