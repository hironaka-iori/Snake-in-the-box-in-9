import ReferenceInterface

namespace Snake9.SixCharge123
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

-- The translated-image argument follows SumBudget112.shifted_sum_le.
-- Here the terms are integers with an explicit nonnegativity hypothesis.
theorem six_window_sum_le (e : Nat → Int) (N : Nat)
    (he : ∀ k, 0 ≤ e k) :
    (∑ r ∈ range N, ∑ j ∈ range 6, e (r+j)) ≤
      6 * ∑ k ∈ range (N+5), e k := by
  have hs (j : Nat) (hj : j < 6) :
      (∑ r ∈ range N, e (r+j)) ≤ ∑ k ∈ range (N+5), e k := by
    have hinj : Set.InjOn (fun r : Nat => r+j) (↑(range N) : Set Nat) := by
      intro r hr s hs h
      exact Nat.add_right_cancel h
    have hsub : (range N).image (fun r => r+j) ⊆ range (N+5) := by
      intro k hk
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hk
      apply Finset.mem_range.mpr
      have h := Finset.mem_range.mp hr
      omega
    calc
      _ = ∑ k ∈ (range N).image (fun r => r+j), e k :=
        (Finset.sum_image hinj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (by intro k _ _; exact he k)
  calc
    _ = ∑ j ∈ range 6, ∑ r ∈ range N, e (r+j) := Finset.sum_comm
    _ ≤ ∑ _j ∈ range 6, ∑ k ∈ range (N+5), e k :=
      Finset.sum_le_sum (fun j hj => hs j (Finset.mem_range.mp hj))
    _ = _ := by simp [nsmul_eq_mul]

theorem credit_budget (e b : Nat → Int) (N : Nat) (C : Int)
    (he : ∀ k, 0 ≤ e k) (hC0 : 0 ≤ C) (hC20 : C ≤ 20)
    (hlocal : ∀ r < N, b r ≤ C * ∑ j ∈ range 6, e (r+j)) :
    (∑ r ∈ range N, b r) ≤ 120 * ∑ k ∈ range (N+5), e k := by
  have htotal : 0 ≤ ∑ k ∈ range (N+5), e k :=
    Finset.sum_nonneg (fun k _ => he k)
  have hcoef : C*6 ≤ 120 := by omega
  calc
    _ ≤ ∑ r ∈ range N, C * ∑ j ∈ range 6, e (r+j) :=
      Finset.sum_le_sum (fun r hr => hlocal r (Finset.mem_range.mp hr))
    _ = C * (∑ r ∈ range N, ∑ j ∈ range 6, e (r+j)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * (6 * ∑ k ∈ range (N+5), e k) :=
      mul_le_mul_of_nonneg_left (six_window_sum_le e N he) hC0
    _ = (C*6) * ∑ k ∈ range (N+5), e k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef htotal

-- A and B denote the total actual and clipped counts, respectively.
-- The proposed local lower bound L ≤ A remains an explicit premise.
theorem deficit_le (A B L C : Int)
    (hexcess : 0 ≤ A-B) (hlocal : L ≤ A) (hC : 0 ≤ C) :
    C * max 0 (L-B) ≤ C * (A-B) := by
  apply mul_le_mul_of_nonneg_left _ hC
  exact max_le hexcess (by omega)

-- The old five-centre window is the last five positions of the new six-centre window.
theorem max_credit_le (e : Nat → Int) (r : Nat) (b5 b6 : Int)
    (he : ∀ k, 0 ≤ e k)
    (h5 : b5 ≤ 20 * ∑ j ∈ range 5, e (r+j+1))
    (h6 : b6 ≤ 20 * ∑ j ∈ range 6, e (r+j)) :
    max b5 b6 ≤ 20 * ∑ j ∈ range 6, e (r+j) := by
  have hsplit : (∑ j ∈ range 6, e (r+j)) =
      (∑ j ∈ range 5, e (r+j+1)) + e r := by
    simpa only [Nat.add_assoc, Nat.add_zero] using
      (Finset.sum_range_succ' (fun j => e (r+j)) 5)
  have htail : (∑ j ∈ range 5, e (r+j+1)) ≤
      ∑ j ∈ range 6, e (r+j) := by
    have h := he r
    omega
  exact max_le
    (h5.trans (mul_le_mul_of_nonneg_left htail (by norm_num : (0:Int) ≤ 20))) h6

#print axioms six_window_sum_le
#print axioms credit_budget
#print axioms deficit_le
#print axioms max_credit_le
end Snake9.SixCharge123
