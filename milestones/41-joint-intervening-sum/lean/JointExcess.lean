import Mathlib.Tactic

namespace JointInterveningAccounting

theorem forced_excess (A B : Nat) (hs : 12 ≤ A+B)
    (hc : min 6 A + min 6 B ≤ 11) :
    1 ≤ (A-min 6 A)+(B-min 6 B) := by
  have ha := Nat.min_le_right 6 A
  have hb := Nat.min_le_right 6 B
  omega

theorem shifted_sum_le (delta : Nat → Nat) (J : Finset Nat) (N k : Nat)
    (hJ : ∀ r ∈ J, r+k < N) :
    ∑ r ∈ J, delta (r+k) ≤ ∑ j ∈ Finset.range N, delta j := by
  have hinj : Set.InjOn (fun r : Nat => r+k) (↑J : Set Nat) := by
    intro a ha b hb h
    exact Nat.add_right_cancel h
  have hsub : J.image (fun r => r+k) ⊆ Finset.range N := by
    intro j hj
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hJ r hr)
  calc
    _ = ∑ j ∈ J.image (fun r => r+k), delta j := (Finset.sum_image hinj).symm
    _ ≤ ∑ j ∈ Finset.range N, delta j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)

theorem occurrence_excess (delta : Nat → Nat) (J : Finset Nat) (N : Nat)
    (h3 : ∀ r ∈ J, r+3 < N) (h6 : ∀ r ∈ J, r+6 < N)
    (hd : ∀ r ∈ J, 1 ≤ delta (r+3)+delta (r+6)) :
    J.card ≤ 2 * ∑ j ∈ Finset.range N, delta j := by
  have hsum : J.card ≤ ∑ r ∈ J, (delta (r+3)+delta (r+6)) := by
    calc
      _ = ∑ r ∈ J, (1 : Nat) := by simp
      _ ≤ _ := Finset.sum_le_sum hd
  rw [Finset.sum_add_distrib] at hsum
  have ha := shifted_sum_le delta J N 3 h3
  have hb := shifted_sum_le delta J N 6 h6
  omega

theorem charge_bonus (J D B S G : Nat) (hc : J ≤ 2*D)
    (hG : G = 24*(B+D)+S) : 24*B+12*J+S ≤ G := by omega

#print axioms forced_excess
#print axioms shifted_sum_le
#print axioms occurrence_excess
#print axioms charge_bonus
end JointInterveningAccounting
