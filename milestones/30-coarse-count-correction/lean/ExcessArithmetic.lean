import Mathlib.Tactic

namespace Snake9.CoarseCorrection
open Finset

/-- The high entries of a 6,3,3,6,3,3,6 window must all equal six
if their total does not exceed eighteen. -/
theorem high_equal_six (a b c : Nat) (ha : 6 ≤ a) (hb : 6 ≤ b) (hc : 6 ≤ c)
    (h : a + b + c ≤ 18) : a = 6 ∧ b = 6 ∧ c = 6 := by omega

theorem seven_count_total (a b c : Nat) (h : 19 ≤ a+b+c) :
    31 ≤ a+3+3+b+3+3+c := by omega

theorem high_excess (a b c : Nat) (ha : 6 ≤ a) (hb : 6 ≤ b) (hc : 6 ≤ c)
    (h : 19 ≤ a+b+c) : 1 ≤ (a-6)+(b-6)+(c-6) := by omega

/-- A general overlap budget. Each marked set consumes at least one unit;
if a position occurs in at most K sets, their number is at most K times
the total available excess. -/
theorem overlap_budget {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (J : Finset ι) (S : Finset κ) (F : ι → Finset κ) (δ : κ → Nat) (K : Nat)
    (hsub : ∀ j ∈ J, F j ⊆ S)
    (hone : ∀ j ∈ J, 1 ≤ ∑ x ∈ F j, δ x)
    (hcap : ∀ x ∈ S, (J.filter (fun j => x ∈ F j)).card ≤ K) :
    J.card ≤ K * ∑ x ∈ S, δ x := by
  have hexpand (j : ι) (hj : j ∈ J) :
      (∑ x ∈ F j, δ x) = ∑ x ∈ S, if x ∈ F j then δ x else 0 := by
    calc
      _ = ∑ x ∈ F j, if x ∈ F j then δ x else 0 := by
        apply sum_congr rfl
        intro x hx
        simp only [hx, if_true]
      _ = _ := sum_subset (hsub j hj) (by intro x hx hnot; simp only [hnot, if_false])
  calc
    J.card = ∑ j ∈ J, (1 : Nat) := by simp
    _ ≤ ∑ j ∈ J, ∑ x ∈ F j, δ x := sum_le_sum hone
    _ = ∑ j ∈ J, ∑ x ∈ S, if x ∈ F j then δ x else 0 := sum_congr rfl hexpand
    _ = ∑ x ∈ S, ∑ j ∈ J, if x ∈ F j then δ x else 0 := sum_comm
    _ = ∑ x ∈ S, (J.filter (fun j => x ∈ F j)).card * δ x := by
      apply sum_congr rfl
      intro x hx
      rw [← sum_filter]
      simp
    _ ≤ ∑ x ∈ S, K * δ x := sum_le_sum (by intro x hx; exact Nat.mul_le_mul_right (δ x) (hcap x hx))
    _ = K * ∑ x ∈ S, δ x := (mul_sum S δ K).symm

/-- Only offsets zero, three and six can pay for one of these windows.
Thus any position is charged by at most three distinct starting positions. -/
theorem triple_multiplicity (J : Finset Nat) (x : Nat) :
    (J.filter (fun r => x ∈ ({r,r+3,r+6} : Finset Nat))).card ≤ 3 := by
  have hsub : J.filter (fun r => x ∈ ({r,r+3,r+6} : Finset Nat)) ⊆
      ({x,x-3,x-6} : Finset Nat) := by
    intro r hr
    have hx := (mem_filter.mp hr).2
    simp only [mem_insert, mem_singleton] at hx ⊢
    omega
  have h1 := card_insert_le x ({x-3,x-6} : Finset Nat)
  have h2 := card_insert_le (x-3) ({x-6} : Finset Nat)
  simp only [card_singleton] at h2
  exact le_trans (card_le_card hsub) (by omega)

theorem triple_overlap_budget (J S : Finset Nat) (δ : Nat → Nat)
    (hsub : ∀ r ∈ J, ({r,r+3,r+6} : Finset Nat) ⊆ S)
    (hone : ∀ r ∈ J, 1 ≤ ∑ x ∈ ({r,r+3,r+6} : Finset Nat), δ x) :
    J.card ≤ 3 * ∑ x ∈ S, δ x :=
  overlap_budget J S (fun r => {r,r+3,r+6}) δ 3 hsub hone
    (by intro x hx; exact triple_multiplicity J x)

theorem coarse_decomposition {κ : Type*} (S : Finset κ) (α : κ → Nat) :
    (∑ x ∈ S, α x) = (∑ x ∈ S, min 6 (α x)) + ∑ x ∈ S, (α x-6) := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  omega

/-- Each qualifying distinct window contributes eight integer charge units
at M=12, after paying the maximum overlap multiplicity of three. -/
theorem corrected_charge (J S : Finset Nat) (α : Nat → Nat) (share : Nat)
    (hsub : ∀ r ∈ J, ({r,r+3,r+6} : Finset Nat) ⊆ S)
    (hone : ∀ r ∈ J, 1 ≤ ∑ x ∈ ({r,r+3,r+6} : Finset Nat), (α x-6)) :
    24 * (∑ x ∈ S, min 6 (α x)) + 8 * J.card + share ≤
      24 * (∑ x ∈ S, α x) + share := by
  have hbudget := triple_overlap_budget J S (fun x => α x-6) hsub hone
  change J.card ≤ 3 * ∑ x ∈ S, (α x-6) at hbudget
  have hdecomp := coarse_decomposition S α
  omega

#print axioms high_equal_six
#print axioms seven_count_total
#print axioms high_excess
#print axioms overlap_budget
#print axioms triple_multiplicity
#print axioms triple_overlap_budget
#print axioms coarse_decomposition
#print axioms corrected_charge
end Snake9.CoarseCorrection
