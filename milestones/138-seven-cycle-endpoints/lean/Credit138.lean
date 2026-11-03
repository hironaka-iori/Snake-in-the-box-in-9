import Mathlib.Tactic

namespace Snake9.Credit138

theorem balanced_cycle_means : (488 : ℚ) + (83 / 3) / 2 = 3011 / 6 := by
  norm_num

theorem comparison_lt_235_iff (R : ℚ) :
    (1098960 + 8 * (3011 / 6 : ℚ) + 24 * (83 / 3 : ℚ) + R) /
      (4200 + 3011 / 6) < 235 ↔ R < 7753 / 6 := by
  norm_num
  constructor <;> intro h <;> linarith

theorem sufficient_target {μ R : ℚ} (hμ : 3011 / 6 ≤ μ) (hR : R < 7753 / 6) :
    (1098960 + 8 * μ + 24 * (83 / 3 : ℚ) + R) / (4200 + μ) < 235 := by
  have hpos : (0 : ℚ) < 4200 + μ := by linarith
  apply (div_lt_iff₀ hpos).2
  nlinarith

#print axioms balanced_cycle_means
#print axioms comparison_lt_235_iff
#print axioms sufficient_target

end Snake9.Credit138
