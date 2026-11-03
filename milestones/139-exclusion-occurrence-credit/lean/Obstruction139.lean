import Mathlib.Tactic

namespace Snake9.Obstruction139

theorem completed_profile_obstruction {μ C B R : ℚ}
    (hμ : 0 ≤ μ) (hcap : μ ≤ 2446 / 5)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    235 < (1098960 + 8*μ + B*C + R)/(4200+μ) := by
  have hp : (0 : ℚ) < 4200+μ := by linarith
  apply (lt_div_iff₀ hp).2
  have hBC := mul_nonneg hB hC
  nlinarith

theorem conditional_profile_obstruction {μ C B R : ℚ}
    (hμ : 0 ≤ μ) (hcap : μ ≤ 496)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    234 < (1098960 + 8*μ + B*C + R)/(4200+μ) := by
  have hp : (0 : ℚ) < 4200+μ := by linarith
  apply (lt_div_iff₀ hp).2
  have hBC := mul_nonneg hB hC
  nlinarith

#print axioms completed_profile_obstruction
#print axioms conditional_profile_obstruction
end Snake9.Obstruction139
