import Mathlib.Tactic

namespace Snake9.RemainderComparison163

theorem exact_budget (T sigma empty v loss : ℝ)
    (hsquare : T + 2 * empty + 35 * v = 9214)
    (hshare : sigma + loss = 48 * empty) :
    24 * T + sigma + 840 * v + loss = 221136 := by
  linarith

theorem retained_comparison (m W G mu C R loss : ℝ)
    (hpack : W + 2520 ≤ 5 * G)
    (hbudget : G + 840 * (m + 1) + loss = 221136)
    (hpotential : mu * (m - 8) ≤ W + R + 24 * C) :
    (4200 + mu) * m ≤ 1098960 + 8 * mu + 24 * C + R - 5 * loss := by
  nlinarith

theorem saved_witness_equalities :
    0 ≤ (4462 / 9 : ℚ) ∧
    9 * (4462 / 9 : ℚ) = 4462 ∧
    9 * (4462 / 9 : ℚ) - 3861 = 601 := by
  norm_num

theorem integer_loss_threshold (loss : ℤ) :
    ((1098960 + 8 * (4462 / 9 : ℚ) + 601 - 5 * (loss : ℚ)) /
      (4200 + (4462 / 9 : ℚ)) < 235) ↔ 4 ≤ loss := by
  have hden : (0 : ℚ) < 4200 + 4462 / 9 := by norm_num
  constructor
  · intro h
    rw [div_lt_iff₀ hden] at h
    have hq : (3 : ℚ) < (loss : ℚ) := by linarith
    have hi : (3 : ℤ) < loss := by exact_mod_cast hq
    omega
  · intro h
    have hq : (4 : ℚ) ≤ (loss : ℚ) := by exact_mod_cast h
    apply (div_lt_iff₀ hden).2
    linarith

theorem loss_three_and_four :
    (1098960 + 8 * (4462 / 9 : ℚ) + 601 - 5 * 3) /
      (4200 + (4462 / 9 : ℚ)) = 235 + 40 / 42262 ∧
    (1098960 + 8 * (4462 / 9 : ℚ) + 601 - 5 * 4) /
      (4200 + (4462 / 9 : ℚ)) = 235 - 5 / 42262 := by
  norm_num

theorem conditional_edge_bound (m : ℕ) (W G loss : ℝ)
    (hpack : W + 2520 ≤ 5 * G)
    (hbudget : G + 840 * ((m : ℝ) + 1) + loss = 221136)
    (hpotential : (4462 / 9 : ℝ) * ((m : ℝ) - 8) ≤ W + 601)
    (hloss : 4 ≤ loss) : m ≤ 234 := by
  have h := retained_comparison (m : ℝ) W G (4462 / 9) 0 601 loss
    hpack hbudget (by simpa using hpotential)
  by_contra hm
  have hi : 235 ≤ m := by omega
  have hr : (235 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi
  nlinarith

theorem aggregate_rounding_example :
    (12 * 6 : ℕ) % 5 = 2 ∧
    6 * (12 % 5 : ℕ) = 12 ∧
    (12 * 6 : ℕ) % 5 ≠ 6 * (12 % 5 : ℕ) := by
  norm_num

#print axioms exact_budget
#print axioms retained_comparison
#print axioms saved_witness_equalities
#print axioms integer_loss_threshold
#print axioms loss_three_and_four
#print axioms conditional_edge_bound
#print axioms aggregate_rounding_example

end Snake9.RemainderComparison163
