import Mathlib.Tactic

namespace Snake9.JointExcess
open Finset

/-- A joint high-count bound gives the corresponding excess beyond three
coarse sixes. Natural subtraction is justified by the three lower bounds. -/
theorem excess_of_sum (a b c q : Nat) (ha : 6 ≤ a) (hb : 6 ≤ b) (hc : 6 ≤ c)
    (h : 18+q ≤ a+b+c) : q ≤ (a-6)+(b-6)+(c-6) := by omega

/-- Weighted version of the overlap budget, allowing different certified
excess lower bounds at different windows. -/
theorem weighted_overlap {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (J : Finset ι) (S : Finset κ) (F : ι → Finset κ) (δ : κ → Nat) (q : ι → Nat) (K : Nat)
    (hsub : ∀ j ∈ J, F j ⊆ S)
    (hlocal : ∀ j ∈ J, q j ≤ ∑ x ∈ F j, δ x)
    (hcap : ∀ x ∈ S, (J.filter (fun j => x ∈ F j)).card ≤ K) :
    (∑ j ∈ J, q j) ≤ K * ∑ x ∈ S, δ x := by
  have hexpand (j : ι) (hj : j ∈ J) :
      (∑ x ∈ F j, δ x) = ∑ x ∈ S, if x ∈ F j then δ x else 0 := by
    calc
      _ = ∑ x ∈ F j, if x ∈ F j then δ x else 0 := by
        apply sum_congr rfl
        intro x hx
        simp only [hx, if_true]
      _ = _ := sum_subset (hsub j hj) (by intro x hx hnot; simp only [hnot, if_false])
  calc
    (∑ j ∈ J, q j) ≤ ∑ j ∈ J, ∑ x ∈ F j, δ x := sum_le_sum hlocal
    _ = ∑ j ∈ J, ∑ x ∈ S, if x ∈ F j then δ x else 0 := sum_congr rfl hexpand
    _ = ∑ x ∈ S, ∑ j ∈ J, if x ∈ F j then δ x else 0 := sum_comm
    _ = ∑ x ∈ S, (J.filter (fun j => x ∈ F j)).card * δ x := by
      apply sum_congr rfl
      intro x hx
      rw [← sum_filter]
      simp
    _ ≤ ∑ x ∈ S, K * δ x := sum_le_sum (by intro x hx; exact Nat.mul_le_mul_right (δ x) (hcap x hx))
    _ = K * ∑ x ∈ S, δ x := (mul_sum S δ K).symm

theorem weighted_charge (T B D Q share : Nat) (hT : T = B+D) (hQ : Q ≤ 3*D) :
    24*B+8*Q+share ≤ 24*T+share := by omega

#print axioms excess_of_sum
#print axioms weighted_overlap
#print axioms weighted_charge
end Snake9.JointExcess
