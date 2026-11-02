import Mathlib.Tactic

/-!
Arithmetic for alternative outer-four and total-five deficits on suffix centres.
The shifted-sum argument is reused from milestone41 JointExcess.shifted_sum_le;
the boundary argument is adapted from milestone98 GlobalCharge98.discarded_counts.
Local count inequalities remain hypotheses. No geometric statement is asserted.
-/
namespace Snake9.SumBudget112
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem weighted_max (a b d4 d5 e4 e1 : Nat)
    (h4 : d4 ≤ e4) (h5 : d5 ≤ e4+e1) :
    max (a*d4) (min a b*d5) ≤ a*e4+b*e1 := by
  apply max_le
  · exact (Nat.mul_le_mul_left a h4).trans (Nat.le_add_right _ _)
  · have hd := Nat.mul_le_mul_left (min a b) h5
    have houter := Nat.mul_le_mul_right e4 (Nat.min_le_left a b)
    have hmiddle := Nat.mul_le_mul_right e1 (Nat.min_le_right a b)
    nlinarith

theorem local_deficits (alpha : Nat → Nat) (r a b l4 l5 : Nat)
    (h4 : l4 ≤ alpha (r+4)+alpha (r+5)+alpha (r+7)+alpha (r+8))
    (h5 : l5 ≤ alpha (r+4)+alpha (r+5)+alpha (r+7)+alpha (r+8)+alpha (r+6)) :
    max
      (a*(l4-(min 6 (alpha (r+4))+min 6 (alpha (r+5))+
        min 6 (alpha (r+7))+min 6 (alpha (r+8)))))
      (min a b*(l5-(min 6 (alpha (r+4))+min 6 (alpha (r+5))+
        min 6 (alpha (r+7))+min 6 (alpha (r+8))+min 6 (alpha (r+6))))) ≤
      a*((alpha (r+4)-min 6 (alpha (r+4)))+
        (alpha (r+5)-min 6 (alpha (r+5)))+
        (alpha (r+7)-min 6 (alpha (r+7)))+
        (alpha (r+8)-min 6 (alpha (r+8))))+
      b*(alpha (r+6)-min 6 (alpha (r+6))) := by
  have h4c := Nat.min_le_right 6 (alpha (r+4))
  have h5c := Nat.min_le_right 6 (alpha (r+5))
  have h6c := Nat.min_le_right 6 (alpha (r+6))
  have h7c := Nat.min_le_right 6 (alpha (r+7))
  have h8c := Nat.min_le_right 6 (alpha (r+8))
  apply weighted_max <;> omega

theorem shifted_sum_le (delta : Nat → Nat) (J : Finset Nat) (N k : Nat)
    (hJ : ∀ r ∈ J, r+k < N) :
    (∑ r ∈ J, delta (r+k)) ≤ ∑ j ∈ Finset.range N, delta j := by
  have hinj : Set.InjOn (fun r : Nat => r+k) (↑J : Set Nat) := by
    intro a ha b hb h
    exact Nat.add_right_cancel h
  have hsub : J.image (fun r => r+k) ⊆ Finset.range N := by
    intro j hj
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hJ r hr)
  calc
    _ = ∑ j ∈ J.image (fun r => r+k), delta j := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (by intros; exact Nat.zero_le _)

theorem weighted_window_budget (delta credit : Nat → Nat) (m a b : Nat)
    (hcapacity : 4*a+b ≤ 120)
    (hlocal : ∀ r < m-8, credit r ≤
      a*(delta (r+4)+delta (r+5)+delta (r+7)+delta (r+8))+b*delta (r+6)) :
    (∑ r ∈ Finset.range (m-8), credit r) ≤
      120 * ∑ i ∈ Finset.range (m+1), delta i := by
  have hs (k : Nat) (hk : k ≤ 8) :
      (∑ r ∈ Finset.range (m-8), delta (r+k)) ≤
        ∑ i ∈ Finset.range (m+1), delta i :=
    shifted_sum_le delta (Finset.range (m-8)) (m+1) k
      (by intro r hr; have := Finset.mem_range.mp hr; omega)
  have hsum := Finset.sum_le_sum (s := Finset.range (m-8))
    (fun r hr => hlocal r (Finset.mem_range.mp hr))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hfour :
      (∑ r ∈ Finset.range (m-8), delta (r+4))+
      (∑ r ∈ Finset.range (m-8), delta (r+5))+
      (∑ r ∈ Finset.range (m-8), delta (r+7))+
      (∑ r ∈ Finset.range (m-8), delta (r+8)) ≤
        4*(∑ i ∈ Finset.range (m+1), delta i) := by
    have h4 := hs 4 (by omega)
    have h5 := hs 5 (by omega)
    have h7 := hs 7 (by omega)
    have h8 := hs 8 (by omega)
    omega
  have ha := Nat.mul_le_mul_left a hfour
  have hb := Nat.mul_le_mul_left b (hs 6 (by omega))
  have hc := Nat.mul_le_mul_right (∑ i ∈ Finset.range (m+1), delta i) hcapacity
  nlinarith

theorem combined_deficit_budget (alpha lower4 lower5 : Nat → Nat) (m a b : Nat)
    (hcapacity : 4*a+b ≤ 120)
    (h4 : ∀ r < m-8, lower4 r ≤
      alpha (r+4)+alpha (r+5)+alpha (r+7)+alpha (r+8))
    (h5 : ∀ r < m-8, lower5 r ≤
      alpha (r+4)+alpha (r+5)+alpha (r+7)+alpha (r+8)+alpha (r+6)) :
    (∑ r ∈ Finset.range (m-8), max
      (a*(lower4 r-(min 6 (alpha (r+4))+min 6 (alpha (r+5))+
        min 6 (alpha (r+7))+min 6 (alpha (r+8)))))
      (min a b*(lower5 r-(min 6 (alpha (r+4))+min 6 (alpha (r+5))+
        min 6 (alpha (r+7))+min 6 (alpha (r+8))+min 6 (alpha (r+6)))))) ≤
      120 * ∑ i ∈ Finset.range (m+1), (alpha i-min 6 (alpha i)) := by
  apply weighted_window_budget (fun i => alpha i-min 6 (alpha i)) _ m a b hcapacity
  intro r hr
  exact local_deficits alpha r a b (lower4 r) (lower5 r) (h4 r hr) (h5 r hr)

theorem clipped_boundary (alpha : Nat → Nat) (m : Nat) (hm : 8 ≤ m)
    (h0 : 4 ≤ alpha 0) (hend : 4 ≤ alpha m)
    (hpos : ∀ i, 0 < i → i < m → 1 ≤ alpha i)
    (hpair : ∀ i, 0 < i → i+1 < m → 4 ≤ alpha i+alpha (i+1)) :
    (∑ r ∈ Finset.range (m-8), min 6 (alpha (r+8)))+21 ≤
      ∑ i ∈ Finset.range (m+1), min 6 (alpha i) := by
  have hpref : 17 ≤ ∑ i ∈ Finset.range 8, min 6 (alpha i) := by
    have h12 := hpair 1 (by omega) (by omega)
    have h34 := hpair 3 (by omega) (by omega)
    have h56 := hpair 5 (by omega) (by omega)
    have h7 := hpos 7 (by omega) (by omega)
    norm_num at h12 h34 h56
    norm_num [Finset.sum_range_succ]
    omega
  have hsplit := Finset.sum_range_add (fun i => min 6 (alpha i)) 8 (m-8)
  have he : 8+(m-8)=m := by omega
  rw [he] at hsplit
  rw [Finset.sum_range_succ, hsplit]
  simp only [Nat.add_comm 8] at *
  omega

theorem clipped_charge_budget (alpha credit : Nat → Nat) (m : Nat) (hm : 8 ≤ m)
    (h0 : 4 ≤ alpha 0) (hend : 4 ≤ alpha m)
    (hpos : ∀ i, 0 < i → i < m → 1 ≤ alpha i)
    (hpair : ∀ i, 0 < i → i+1 < m → 4 ≤ alpha i+alpha (i+1))
    (hcredit : (∑ r ∈ Finset.range (m-8), credit r) ≤
      120 * ∑ i ∈ Finset.range (m+1), (alpha i-min 6 (alpha i))) :
    120*(∑ r ∈ Finset.range (m-8), min 6 (alpha (r+8)))+
      (∑ r ∈ Finset.range (m-8), credit r)+2520 ≤
      120*(∑ i ∈ Finset.range (m+1), alpha i) := by
  have hboundary := clipped_boundary alpha m hm h0 hend hpos hpair
  have hdecomp : (∑ i ∈ Finset.range (m+1), min 6 (alpha i))+
      (∑ i ∈ Finset.range (m+1), (alpha i-min 6 (alpha i))) =
      ∑ i ∈ Finset.range (m+1), alpha i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.add_sub_of_le (Nat.min_le_right 6 (alpha i))
  omega

#print axioms weighted_max
#print axioms local_deficits
#print axioms shifted_sum_le
#print axioms weighted_window_budget
#print axioms combined_deficit_budget
#print axioms clipped_boundary
#print axioms clipped_charge_budget
end Snake9.SumBudget112
