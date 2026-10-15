import UpperBound248

/- Conditional endpoint bridge. The additional endpoint premise is discharged
   only once the separate endpoint geometry is integrated. -/
namespace Snake9.SquareIncidence
open scoped BigOperators
open Finset Classical
noncomputable section

theorem index_indicator_sum_eq_one (n t : Nat) (ht : t<n) :
    (∑ i : Fin n, if i.val=t then 1 else 0) = 1 := by
  have heq (i : Fin n) : (i.val=t) ↔ i=(⟨t,ht⟩ : Fin n) := by
    constructor
    · intro h
      exact Fin.ext h
    · intro h
      exact congrArg Fin.val h
  simp only [heq]
  simp

theorem internal_pair_four_endpoint_sum {m : Nat} (hm : 1≤m)
    (f : Fin (m+1) → Nat) (hpos : ∀ i, 1≤f i)
    (hpair : ∀ i : Fin m, 0 < i.val → i.val + 1 < m → 4 ≤ f i.castSucc+f i.succ)
    (hfirst : 4≤f 0) (hlast : 4≤f (Fin.last m)) :
    4*m+10 ≤ 2*(∑ i, f i) := by
  have hlocal (i : Fin m) :
      4+(if i.val=0 then 1 else 0)+(if i.val=m-1 then 1 else 0) ≤
        f i.castSucc+f i.succ := by
    have hb0 (h : i.val=0) : 4≤f i.castSucc := by
      have he : i.castSucc=(0 : Fin (m+1)) := Fin.ext h
      simpa only [he] using hfirst
    have hbm (h : i.val=m-1) : 4≤f i.succ := by
      have he : i.succ=Fin.last m := by apply Fin.ext; dsimp; omega
      simpa only [he] using hlast
    have hp := hpos i.castSucc
    have hq := hpos i.succ
    by_cases h0 : i.val=0
    · rw [if_pos h0]
      have hf := hb0 h0
      by_cases hl : i.val=m-1
      · rw [if_pos hl]
        have he := hbm hl
        omega
      · rw [if_neg hl]
        omega
    · rw [if_neg h0]
      by_cases hl : i.val=m-1
      · rw [if_pos hl]
        have he := hbm hl
        omega
      · rw [if_neg hl]
        have hi := i.isLt
        have hpairi := hpair i (by omega) (by omega)
        omega
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin m))) => hlocal i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul] at hs
  have he0 := index_indicator_sum_eq_one m 0 (by omega)
  have hem := index_indicator_sum_eq_one m (m-1) (by omega)
  have hleft := Fin.sum_univ_castSucc f
  have hright := Fin.sum_univ_succ f
  omega

theorem adjacent_internal_alpha_sum_ge_four {m : Nat} (p : Snake m)
    (i : Fin m) (hi : 0 < i.val) (hm : i.val + 1 < m) :
    4 ≤ localAlpha p i.castSucc + localAlpha p i.succ := by
  have hp := localAlpha_positive p i.castSucc
  have hq := localAlpha_positive p i.succ
  have hleft : i.castSucc.val < m := by change i.val < m; exact i.isLt
  have hright : 0 < i.succ.val := by change 0 < i.val+1; omega
  have hadj : Adj (p.vertex i.castSucc) (p.vertex i.succ) :=
    (path_adj_iff p _ _).mpr (Or.inl rfl)
  have h11 := adjacent_internal_alpha_one_impossible p i.castSucc i.succ hi hleft hright hm hadj
  have h12 := adjacent_internal_one_two_impossible p i.castSucc i.succ hi hleft hright hm hadj
  have h21 := adjacent_internal_one_two_impossible p i.succ i.castSucc hright hm hi hleft
    ((path_adj_iff p _ _).mpr (Or.inr rfl))
  omega

theorem upper_247_of_endpoint_alpha {m : Nat} (p : Snake m)
    (hfirst : 4≤localAlpha p 0) (hlast : 4≤localAlpha p (Fin.last m)) : m≤247 := by
  by_cases hm : m=0
  · omega
  have hsum : 4*m+10 ≤ 2*totalSingleton p := by
    rw [totalSingleton_eq_path_sum]
    exact internal_pair_four_endpoint_sum (by omega) _ (localAlpha_positive p)
      (adjacent_internal_alpha_sum_ge_four p) hfirst hlast
  have hidentity := global_identity p
  rw [selected_total p] at hidentity
  have hw := wedge_total_upper p
  omega

#print axioms internal_pair_four_endpoint_sum
#print axioms adjacent_internal_alpha_sum_ge_four
#print axioms upper_247_of_endpoint_alpha
end
end Snake9.SquareIncidence
