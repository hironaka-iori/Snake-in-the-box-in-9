import AggregateSingletonBound
import UpperBound251

/- Conditional aggregate bridge for the proposed next strengthening.
   Its additional geometric premise is NOT discharged in this module. -/
namespace Snake9.SquareIncidence
open scoped BigOperators
open Finset Classical
noncomputable section

theorem internal_pair_four_bound_sum {m : Nat} (f : Fin (m+1) → Nat)
    (hpos : ∀ i, 1 ≤ f i)
    (hpair : ∀ i : Fin m, 0 < i.val → i.val+1 < m →
      4 ≤ f i.castSucc + f i.succ) :
    4*m ≤ 2 * (∑ i, f i) + 2 := by
  have hlocal (i : Fin m) :
      4 ≤ f i.castSucc + f i.succ + 2*(if i.val=0 then 1 else 0) +
        2*(if i.val=m-1 then 1 else 0) := by
    by_cases h0 : i.val=0
    · rw [if_pos h0]
      have hl := hpos i.castSucc
      have hr := hpos i.succ
      omega
    · rw [if_neg h0]
      by_cases hm : i.val=m-1
      · rw [if_pos hm]
        have hl := hpos i.castSucc
        have hr := hpos i.succ
        omega
      · rw [if_neg hm]
        have hi := i.isLt
        have hp := hpair i (by omega) (by omega)
        omega
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hlocal i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at hs
  have he0 := index_indicator_sum_le_one m 0
  have hem := index_indicator_sum_le_one m (m-1)
  have hfirst := hpos 0
  have hlast := hpos (Fin.last m)
  have hleft := Fin.sum_univ_castSucc f
  have hright := Fin.sum_univ_succ f
  omega

theorem upper_248_of_no_adjacent_one_two {m : Nat} (p : Snake m)
    (h12 : ∀ i j : Fin (m+1), 0 < i.val → i.val < m →
      0 < j.val → j.val < m → Adj (p.vertex i) (p.vertex j) →
      ¬ (localAlpha p i = 1 ∧ localAlpha p j = 2)) : m ≤ 248 := by
  have hsum : 4*m ≤ 2 * totalSingleton p + 2 := by
    rw [totalSingleton_eq_path_sum]
    apply internal_pair_four_bound_sum _ (localAlpha_positive p)
    intro i hi hm
    have hp := localAlpha_positive p i.castSucc
    have hq := localAlpha_positive p i.succ
    have hleft : i.castSucc.val < m := by change i.val < m; exact i.isLt
    have hright : 0 < i.succ.val := by change 0 < i.val+1; omega
    have hadj : Adj (p.vertex i.castSucc) (p.vertex i.succ) :=
      (path_adj_iff p _ _).mpr (Or.inl rfl)
    have h11 := adjacent_internal_alpha_one_impossible p i.castSucc i.succ hi hleft hright hm hadj
    have hf := h12 i.castSucc i.succ hi hleft hright hm hadj
    have hr := h12 i.succ i.castSucc hright hm hi hleft
      ((path_adj_iff p _ _).mpr (Or.inr rfl))
    omega
  have hidentity := global_identity p
  rw [selected_total p] at hidentity
  have hw := wedge_total_upper p
  omega

#print axioms internal_pair_four_bound_sum
#print axioms upper_248_of_no_adjacent_one_two
end
end Snake9.SquareIncidence
