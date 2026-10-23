import ThreeSquareBonus
import WeightedExcess

namespace Snake9.LocalWindow.PairShareCert
open Finset

/-- Each index can be the first or second charged position of at most one start. -/
theorem pair_share_packing (m : Nat) (J : Finset Nat) (s : Nat → Nat)
    (hr : ∀ r ∈ J, r+7 ≤ m)
    (hs : ∀ r ∈ J, 12 ≤ s (r+1)+s (r+6)) :
    6*J.card ≤ ∑ k ∈ range (m+1), s k := by
  have h := Snake9.JointExcess.weighted_overlap J (range (m+1))
    (fun r => {r+1,r+6}) s (fun _ => 12) 2
    (by
      intro r hJ k hk
      have := hr r hJ
      simp only [mem_insert, mem_singleton] at hk
      simp only [mem_range]
      rcases hk with rfl | rfl <;> omega)
    (by
      intro r hJ
      have hne : r+1 ≠ r+6 := by omega
      simpa [hne] using hs r hJ)
    (by
      intro k hk
      have hsub : J.filter (fun r => k ∈ ({r+1,r+6} : Finset Nat)) ⊆ {k-1,k-6} := by
        intro r h
        simp only [mem_filter, mem_insert, mem_singleton] at h ⊢
        rcases h.2 with h | h
        · left; omega
        · right; omega
      exact (card_le_card hsub).trans ((card_insert_le _ _).trans (by simp)))
  simp only [sum_const, smul_eq_mul] at h
  omega

theorem snake_occurrence_bonus {m : Nat} (p : Snake m) (J : Finset Nat)
    (hr : ∀ r ∈ J, r+7 ≤ m)
    (hp : ∀ r ∈ J, ∃ P : CPerm,
      ∀ j, j < 7 → P.fwd (dir p (r+j)) = directions.getD j 0) :
    6*J.card ≤ ∑ k ∈ range (m+1), coreShare 12 p k := by
  apply pair_share_packing m J (coreShare 12 p) hr
  intro r hJ
  obtain ⟨P,hP⟩ := hp r hJ
  exact share_in_snake p P r (hr r hJ) hP

theorem occurrence_charge (T share N : Nat) (h : 6*N ≤ share) :
    24*T+6*N ≤ 24*T+share := by omega

#print axioms pair_share_packing
#print axioms snake_occurrence_bonus
#print axioms occurrence_charge
end Snake9.LocalWindow.PairShareCert
