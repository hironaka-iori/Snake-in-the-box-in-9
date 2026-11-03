import Mathlib.Tactic

namespace Snake9.CreditLimitation132

/-- The two saved cycle caps prevent this comparison from reaching 234,
even with zero range and an allowance of only two equality windows. -/
theorem comparison_above_235 (C mu R : ℚ)
    (hC : 0 ≤ C) (hmu : 0 ≤ mu) (hR : 0 ≤ R)
    (hfour : mu ≤ 488 + C / 2)
    (hseven : mu ≤ 3453 / 7) :
    235 < (1098960 + 8 * mu + 2 * C + R) / (4200 + mu) := by
  have hden : (0 : ℚ) < 4200 + mu := by linarith
  apply (lt_div_iff₀ hden).2
  linarith

/-- Any larger occurrence allowance preserves the same obstruction. -/
theorem comparison_above_235_of_allowance (C mu R allowance : ℚ)
    (hC : 0 ≤ C) (hmu : 0 ≤ mu) (hR : 0 ≤ R)
    (hallowance : 2 ≤ allowance)
    (hfour : mu ≤ 488 + C / 2)
    (hseven : mu ≤ 3453 / 7) :
    235 < (1098960 + 8 * mu + allowance * C + R) / (4200 + mu) := by
  have hden : (0 : ℚ) < 4200 + mu := by linarith
  have h := comparison_above_235 C mu R hC hmu hR hfour hseven
  apply (lt_div_iff₀ hden).2
  have hbase := (lt_div_iff₀ hden).1 h
  nlinarith

#print axioms comparison_above_235
#print axioms comparison_above_235_of_allowance

end Snake9.CreditLimitation132
