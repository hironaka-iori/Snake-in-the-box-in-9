import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Snake9.RangeRestriction155

theorem both16_lower_bound {mu C R : ℚ}
    (hmu : 0 ≤ mu) (hcap : mu ≤ 496)
    (hrange : 2 * mu ≤ 512 + R) (hC : 0 ≤ C) :
    137926 / 587 ≤ (1098960 + 8 * mu + 24 * C + R) / (4200 + mu) := by
  have hp : (0 : ℚ) < 4200 + mu := by linarith
  apply (le_div_iff₀ hp).2
  linarith

theorem exact_gap : (137926 / 587 : ℚ) = 234 + 568 / 587 := by
  norm_num

theorem necessary_below234 {mu F G C R : ℚ}
    (hmu : 0 ≤ mu) (hcap : 7 * mu ≤ 3424 + 2 * F + G)
    (hrange : 2 * mu ≤ 496 + F + R)
    (hgood : (1098960 + 8 * mu + 24 * C + R) / (4200 + mu) < 234) :
    42672 + 168 * C < 455 * F + 224 * G := by
  have hp : (0 : ℚ) < 4200 + mu := by linarith
  have hn := (div_lt_iff₀ hp).mp hgood
  linarith

#print axioms both16_lower_bound
#print axioms exact_gap
#print axioms necessary_below234

end Snake9.RangeRestriction155
