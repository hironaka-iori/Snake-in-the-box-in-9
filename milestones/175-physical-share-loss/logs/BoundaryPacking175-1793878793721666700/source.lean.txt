import PrefixBoundary175
import ShareLoss172

open scoped BigOperators
namespace Snake9.Boundary175
open SquareIncidence Count171 Integration172
noncomputable section

theorem discarded_counts_twenty_four (a b : Nat → Nat) (m : Nat) (hm : 8 ≤ m)
    (h0 : 4≤a 0) (hend : 4≤a m)
    (hseven : 16≤a 1+a 2+a 3+a 4+a 5+a 6+a 7)
    (htrunc : ∀ i<m-8, b i≤a (8+i)) :
    (∑ i ∈ Finset.range (m-8), b i)+24 ≤ ∑ i ∈ Finset.range (m+1), a i := by
  have hpref : 20 ≤ ∑ i ∈ Finset.range 8, a i := by
    norm_num [Finset.sum_range_succ]
    omega
  have htail : (∑ i ∈ Finset.range (m-8), b i) ≤
      ∑ i ∈ Finset.range (m-8), a (8+i) :=
    Finset.sum_le_sum (by intro i hi; exact htrunc i (Finset.mem_range.mp hi))
  have hsplit := Finset.sum_range_add a 8 (m-8)
  have he : 8+(m-8)=m := by omega
  rw [he] at hsplit
  rw [Finset.sum_range_succ,hsplit]
  omega

theorem actual_discarded_counts {m : Nat} (p : Snake m) (hm : 8≤m)
    (b : Nat → Nat)
    (htrunc : ∀ i, ∀ hi : i<m-8, b i ≤ localAlpha p ⟨8+i,by omega⟩) :
    (∑ i ∈ Finset.range (m-8), b i)+24 ≤ totalSingleton p := by
  let a : Nat → Nat := fun k => if hk : k<m+1 then localAlpha p ⟨k,hk⟩ else 0
  have ha (k : Nat) (hk : k≤m) : a k=localAlpha p ⟨k,by omega⟩ := by
    simp [a,show k<m+1 by omega]
  have h0 : 4≤a 0 := by
    rw [ha 0 (by omega)]
    exact endpoint_alpha_ge_four p _ (by omega) (Or.inl rfl)
  have hend : 4≤a m := by
    rw [ha m (by omega)]
    exact endpoint_alpha_ge_four p _ (by omega) (Or.inr rfl)
  have hseven : 16≤a 1+a 2+a 3+a 4+a 5+a 6+a 7 := by
    simpa only [ha 1 (by omega),ha 2 (by omega),ha 3 (by omega),ha 4 (by omega),
      ha 5 (by omega),ha 6 (by omega),ha 7 (by omega)] using seven_internal_at_least_sixteen p hm
  have ht : ∀ i<m-8, b i≤a (8+i) := by
    intro i hi
    rw [ha (8+i) (by omega)]
    exact htrunc i hi
  have hs : (∑ i ∈ Finset.range (m+1), a i)=totalSingleton p := by
    rw [totalSingleton_eq_path_sum]
    exact (Finset.sum_fin_eq_sum_range (localAlpha p)).symm
  rw [←hs]
  exact discarded_counts_twenty_four a b m hm h0 hend hseven ht

theorem sum_selected_share {m : Nat} (p : Snake m) (f : Vertex → Nat) :
    (∑ x,selected p x*f x)=∑ i : Fin (m+1), f (p.vertex i) := by
  classical
  let s : Finset Vertex := Finset.univ.image p.vertex
  have hs (v : Vertex) : selected p v*f v=if v∈s then f v else 0 := by
    have hv : InPath p v ↔ v∈s := by simp [s,InPath]
    unfold selected
    rw [hv]
    split <;> simp
  simp only [hs]
  rw [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_image]
  intro i _ j _ h
  exact p.distinct i j h

private theorem shifted_sum_le (f : Nat → Nat) (a n N : Nat) (h : a+n≤N) :
    (∑ r ∈ Finset.range n,f (r+a))≤∑ k ∈ Finset.range N,f k := by
  calc
    _ ≤ (∑ k ∈ Finset.range a,f k)+∑ r ∈ Finset.range n,f (r+a) := Nat.le_add_left _ _
    _ = ∑ k ∈ Finset.range (a+n),f k := by
      rw [Finset.sum_range_add]
      simp only [Nat.add_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
      (by intro i _ _; exact Nat.zero_le _)

theorem five_share_capacity (share demand : Nat → Nat) (m : Nat) (hm : 8≤m)
    (hl : ∀ r<m-8,demand r≤∑ k ∈ Finset.range 5,share (r+k+4)) :
    (∑ r ∈ Finset.range (m-8),demand r)≤5*∑ i ∈ Finset.range (m+1),share i := by
  calc
    _ ≤ ∑ r ∈ Finset.range (m-8), ∑ k ∈ Finset.range 5,share (r+k+4) :=
      Finset.sum_le_sum (by intro r hr; exact hl r (Finset.mem_range.mp hr))
    _ = ∑ k ∈ Finset.range 5, ∑ r ∈ Finset.range (m-8),share (r+k+4) := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range 5, ∑ i ∈ Finset.range (m+1),share i := by
      apply Finset.sum_le_sum
      intro k hk
      have hk5 := Finset.mem_range.mp hk
      simpa only [Nat.add_assoc] using shifted_sum_le share (k+4) (m-8) (m+1) (by omega)
    _ = _ := by simp [Nat.mul_comm]

theorem actual_charge_packing {m : Nat} (p : Snake m) (hm : 8≤m)
    (b share demand : Nat → Nat)
    (htrunc : ∀ i, ∀ hi : i<m-8,b i≤localAlpha p ⟨8+i,by omega⟩)
    (hshare : ∀ i,∀ hi : i<m+1,share i=shareN 12 p (p.vertex ⟨i,hi⟩))
    (hlocal : ∀ r<m-8,demand r≤∑ k ∈ Finset.range 5,share (r+k+4)) :
    (∑ r ∈ Finset.range (m-8),(120*b r+demand r))+2880 ≤
      5*(24*totalSingleton p+∑ x,selected p x*shareN 12 p x) := by
  have hc := actual_discarded_counts p hm b htrunc
  have hs := five_share_capacity share demand m hm hlocal
  have he : (∑ i ∈ Finset.range (m+1),share i)=∑ x,selected p x*shareN 12 p x := by
    rw [sum_selected_share,Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [dif_pos (Finset.mem_range.mp hi)] using hshare i (Finset.mem_range.mp hi)
  rw [he] at hs
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  omega

#print axioms discarded_counts_twenty_four
#print axioms actual_discarded_counts
#print axioms sum_selected_share
#print axioms five_share_capacity
#print axioms actual_charge_packing
end
end Snake9.Boundary175
