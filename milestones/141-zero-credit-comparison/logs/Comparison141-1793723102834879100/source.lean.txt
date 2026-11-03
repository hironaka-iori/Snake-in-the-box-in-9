import Mathlib.Tactic

namespace Snake9.Comparison141

theorem completed_arithmetic :
    ((1098960 + 8 * (3424 / 7) + 4159 / 7 : ℚ) / (4200 + 3424 / 7) =
      7724271 / 32824) ∧ (235 : ℚ) < 7724271 / 32824 ∧
      (7724271 / 32824 : ℚ) < 236 := by
  norm_num

theorem conditional_arithmetic :
    ((1098960 + 8 * 496 + 602 : ℚ) / (4200 + 496) = 551765 / 2348) ∧
      (234 : ℚ) < 551765 / 2348 ∧ (551765 / 2348 : ℚ) < 235 := by
  norm_num

theorem conditional_integer_bound {m : Nat}
    (h : (m : ℚ) ≤ 551765 / 2348) : m ≤ 234 := by
  have hx : (m : ℚ) < 235 := lt_of_le_of_lt h (by norm_num)
  have hn : m < 235 := by exact_mod_cast hx
  omega

theorem completed_integer_bound {m : Nat}
    (h : (m : ℚ) ≤ 7724271 / 32824) : m ≤ 235 := by
  have hx : (m : ℚ) < 236 := lt_of_le_of_lt h (by norm_num)
  have hn : m < 236 := by exact_mod_cast hx
  omega

theorem next_credit_intersection :
    ((3424 + 2 * (533 / 12) : ℚ) / 7 = 3011 / 6) := by
  norm_num

theorem next_credit_range {R : ℚ} :
    ((1098960 + 8 * (3011 / 6) + 24 * (533 / 12) + R) /
      (4200 + 3011 / 6) < 235) ↔ R < 5341 / 6 := by
  rw [div_lt_iff₀ (by norm_num : (0 : ℚ) < 4200 + 3011 / 6)]
  constructor <;> intro h <;> linarith

theorem two_cycle_relaxation {mu C R : ℚ}
    (hm : 0 ≤ mu) (hc : 0 ≤ C) (hr : 0 ≤ R)
    (hseven : mu ≤ (3424 + 2*C) / 7)
    (heighteen : mu ≤ 3011 / 6) :
    6624244 / 28211 ≤ (1098960 + 8*mu + 24*C + R) / (4200 + mu) := by
  apply (le_div_iff₀ (by linarith : (0 : ℚ) < 4200 + mu)).2
  linarith

theorem two_cycle_relaxation_equality :
    ((1098960 + 8*(3011/6) + 24*(533/12) : ℚ) / (4200 + 3011/6) =
      6624244 / 28211) ∧ (6624244 / 28211 : ℚ) < 235 := by
  norm_num

#print axioms completed_arithmetic
#print axioms conditional_arithmetic
#print axioms conditional_integer_bound
#print axioms completed_integer_bound
#print axioms next_credit_intersection
#print axioms next_credit_range
#print axioms two_cycle_relaxation
#print axioms two_cycle_relaxation_equality
end Snake9.Comparison141
