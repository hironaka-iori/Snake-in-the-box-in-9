import SquareIncidence
import Mathlib.Algebra.BigOperators.Fin

namespace Snake9.SquareIncidence
open scoped BigOperators
open Finset Classical
noncomputable section
set_option maxHeartbeats 400000

def localAlpha {m : Nat} (p : Snake m) (i : Fin (m+1)) : Nat :=
  ∑ ab : AxisPair, singleton p ab (p.vertex i)

theorem localAlpha_positive {m : Nat} (p : Snake m) (i : Fin (m+1)) :
    1 ≤ localAlpha p i := singleton_at_vertex p i

theorem totalSingleton_eq_path_sum {m : Nat} (p : Snake m) :
    totalSingleton p = ∑ i, localAlpha p i := by
  let f : Vertex → Nat := fun v => ∑ ab : AxisPair, singleton p ab v
  let s : Finset Vertex := Finset.univ.image p.vertex
  have hout (v : Vertex) (hv : v ∉ s) : f v = 0 := by
    have hn : ¬ InPath p v := by
      rintro ⟨i, hi⟩
      exact hv (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hi⟩)
    simp [f,singleton,hn]
  calc
    totalSingleton p = ∑ v, f v := by unfold totalSingleton f; rw [Finset.sum_comm]
    _ = ∑ v ∈ s, f v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro v _ hv
      exact hout v hv
    _ = ∑ i : Fin (m+1), f (p.vertex i) := by
      dsimp [s]
      rw [Finset.sum_image]
      intro i _ j _ h
      exact p.distinct i j h
    _ = ∑ i, localAlpha p i := rfl

theorem index_indicator_sum_le_one (n t : Nat) :
    (∑ i : Fin n, if i.val = t then 1 else 0) ≤ 1 := by
  rw [← Finset.card_filter]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply Fin.ext
  exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm

theorem internal_pair_bound_sum {m : Nat} (f : Fin (m+1) → Nat)
    (hpos : ∀ i, 1 ≤ f i)
    (hpair : ∀ i : Fin m, 0 < i.val → i.val+1 < m →
      3 ≤ f i.castSucc + f i.succ) :
    3*m ≤ 2 * (∑ i, f i) := by
  have hlocal (i : Fin m) :
      3 ≤ f i.castSucc + f i.succ + (if i.val=0 then 1 else 0) +
        (if i.val=m-1 then 1 else 0) := by
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
    smul_eq_mul] at hs
  have he0 := index_indicator_sum_le_one m 0
  have hem := index_indicator_sum_le_one m (m-1)
  have hfirst := hpos 0
  have hlast := hpos (Fin.last m)
  have hleft := Fin.sum_univ_castSucc f
  have hright := Fin.sum_univ_succ f
  omega

/- This is explicitly a conditional bridge. Its local geometric premise is not
   discharged by this file and must not be advertised as an unconditional bound. -/
theorem upper_251_of_no_adjacent_internal_singletons {m : Nat} (p : Snake m)
    (hlocal : ∀ i : Fin m, 0 < i.val → i.val+1 < m →
      ¬ (localAlpha p i.castSucc = 1 ∧ localAlpha p i.succ = 1)) : m ≤ 251 := by
  have hsum : 3*m ≤ 2 * totalSingleton p := by
    rw [totalSingleton_eq_path_sum]
    apply internal_pair_bound_sum _ (localAlpha_positive p)
    intro i hi hm
    have hp := localAlpha_positive p i.castSucc
    have hq := localAlpha_positive p i.succ
    have hn := hlocal i hi hm
    omega
  have hidentity := global_identity p
  rw [selected_total p] at hidentity
  have hw := wedge_total_upper p
  omega

#print axioms totalSingleton_eq_path_sum
#print axioms internal_pair_bound_sum
#print axioms upper_251_of_no_adjacent_internal_singletons
end
end Snake9.SquareIncidence
