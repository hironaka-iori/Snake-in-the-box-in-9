import SixPrefixBoundary175
import ShareLoss172

open scoped BigOperators
namespace Snake9.Boundary175
open SquareIncidence Count171 Integration172
noncomputable section

theorem discarded_counts_twenty_two (a b : Nat → Nat) (m : Nat) (hm : 7 ≤ m)
    (h0 : 4≤a 0) (hend : 4≤a m)
    (hsix : 14≤a 1+a 2+a 3+a 4+a 5+a 6)
    (htrunc : ∀ i<m-7, b i≤a (7+i)) :
    (∑ i ∈ Finset.range (m-7), b i)+22 ≤ ∑ i ∈ Finset.range (m+1), a i := by
  have hpref : 18 ≤ ∑ i ∈ Finset.range 7, a i := by
    norm_num [Finset.sum_range_succ]
    omega
  have htail : (∑ i ∈ Finset.range (m-7), b i) ≤
      ∑ i ∈ Finset.range (m-7), a (7+i) :=
    Finset.sum_le_sum (by intro i hi; exact htrunc i (Finset.mem_range.mp hi))
  have hsplit := Finset.sum_range_add a 7 (m-7)
  have he : 7+(m-7)=m := by omega
  rw [he] at hsplit
  rw [Finset.sum_range_succ,hsplit]
  omega

theorem actual_six_discarded_counts {m : Nat} (p : Snake m) (hm : 7≤m)
    (b : Nat → Nat)
    (htrunc : ∀ i, ∀ hi : i<m-7, b i ≤ localAlpha p ⟨7+i,by omega⟩) :
    (∑ i ∈ Finset.range (m-7), b i)+22 ≤ totalSingleton p := by
  let a : Nat → Nat := fun k => if hk : k<m+1 then localAlpha p ⟨k,hk⟩ else 0
  have ha (k : Nat) (hk : k≤m) : a k=localAlpha p ⟨k,by omega⟩ := by
    simp [a,show k<m+1 by omega]
  have h0 : 4≤a 0 := by
    rw [ha 0 (by omega)]
    exact endpoint_alpha_ge_four p _ (by omega) (Or.inl rfl)
  have hend : 4≤a m := by
    rw [ha m (by omega)]
    exact endpoint_alpha_ge_four p _ (by omega) (Or.inr rfl)
  have hsix : 14≤a 1+a 2+a 3+a 4+a 5+a 6 := by
    simpa only [ha 1 (by omega),ha 2 (by omega),ha 3 (by omega),ha 4 (by omega),
      ha 5 (by omega),ha 6 (by omega)] using six_internal_at_least_fourteen p hm
  have ht : ∀ i<m-7, b i≤a (7+i) := by
    intro i hi
    rw [ha (7+i) (by omega)]
    exact htrunc i hi
  have hs : (∑ i ∈ Finset.range (m+1), a i)=totalSingleton p := by
    rw [totalSingleton_eq_path_sum]
    exact (Finset.sum_fin_eq_sum_range (localAlpha p)).symm
  rw [←hs]
  exact discarded_counts_twenty_two a b m hm h0 hend hsix ht

theorem actual_retained_census {m : Nat} (p : Snake m) (hm : 7≤m)
    (b : Nat → Nat)
    (htrunc : ∀ i, ∀ hi : i<m-7,b i≤localAlpha p ⟨7+i,by omega⟩)
    (hwalk : 4*(m-7)≤(∑ i ∈ Finset.range (m-7),b i)+7) :
    4*m≤totalSingleton p+13 ∧ 78*m+totalEmptyAnchored p≤18384 := by
  have hb := actual_six_discarded_counts p hm b htrunc
  have hi := incidence_bound_with_empty p (by omega)
  omega

#print axioms discarded_counts_twenty_two
#print axioms actual_six_discarded_counts
#print axioms actual_retained_census
end
end Snake9.Boundary175
