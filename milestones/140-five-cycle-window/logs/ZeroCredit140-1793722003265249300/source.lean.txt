import Mathlib.Tactic

namespace Snake9.Credit140

theorem zero_credit_comparison {R : ℚ} (hR : R < 632) :
    (1098960 + 8 * 496 + R) / (4200 + 496) < 235 := by
  apply (div_lt_iff₀ (by norm_num : (0 : ℚ) < 4200 + 496)).2
  linarith

theorem old_range_zero_credit_arithmetic :
    ((1098960 + 8 * 496 + 602 : ℚ) / (4200 + 496) = 551765 / 2348) ∧
    (551765 / 2348 : ℚ) < 235 := by
  norm_num

#print axioms zero_credit_comparison
#print axioms old_range_zero_credit_arithmetic
end Snake9.Credit140
