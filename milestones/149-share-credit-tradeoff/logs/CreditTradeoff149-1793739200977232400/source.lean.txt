import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Snake9.CreditTradeoff149

theorem three_cycle_cap {mu p0 p1 p2 : ℚ}
    (h0 : mu + p1 ≤ 616 + p0)
    (h1 : mu + p2 ≤ 496 + p1)
    (h2 : mu + p0 ≤ 376 + p2) : mu ≤ 496 := by
  linarith

theorem necessary_credit_below_one {mu C R : ℚ}
    (hmu : 0 ≤ mu) (h3 : mu ≤ 496) (h28 : 28 * mu ≤ 13280 + R)
    (hgood : (1098960 + 8 * mu + 24 * C + R) / (4200 + mu) < 235) : C < 1 := by
  have hp : (0 : ℚ) < 4200 + mu := by linarith
  have hn := (div_lt_iff₀ hp).mp hgood
  linarith

theorem necessary_credit_above_one {mu C R : ℚ}
    (hmu : 0 ≤ mu) (h11 : 11 * mu ≤ 5452 + 4 * C)
    (h28 : 28 * mu ≤ 13280 + R)
    (hgood : (1098960 + 8 * mu + 24 * C + R) / (4200 + mu) < 235) : 1 < C := by
  have hp : (0 : ℚ) < 4200 + mu := by linarith
  have hn := (div_lt_iff₀ hp).mp hgood
  linarith

theorem comparison_at_least_235 {mu C R : ℚ}
    (hmu : 0 ≤ mu) (h3 : mu ≤ 496)
    (h11 : 11 * mu ≤ 5452 + 4 * C)
    (h28 : 28 * mu ≤ 13280 + R) :
    235 ≤ (1098960 + 8 * mu + 24 * C + R) / (4200 + mu) := by
  have hp : (0 : ℚ) < 4200 + mu := by linarith
  apply (le_div_iff₀ hp).2
  linarith

theorem arithmetic_relaxation_attains :
    (1098960 + 8 * (496 : ℚ) + 24 * 1 + 608) / (4200 + 496) = 235 ∧
    11 * (496 : ℚ) = 5452 + 4 * 1 ∧
    28 * (496 : ℚ) = 13280 + 608 := by
  norm_num

#print axioms three_cycle_cap
#print axioms necessary_credit_below_one
#print axioms necessary_credit_above_one
#print axioms comparison_at_least_235
#print axioms arithmetic_relaxation_attains

end Snake9.CreditTradeoff149
