import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Snake9.RangeObstruction156

theorem fourteen_cycle_cap
    {mu p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : ℚ}
    (h0 : mu + p1 ≤ 256 + p0) (h1 : mu + p2 ≤ 256 + p1)
    (h2 : mu + p3 ≤ 736 + p2) (h3 : mu + p4 ≤ 496 + p3)
    (h4 : mu + p5 ≤ 376 + p4) (h5 : mu + p6 ≤ 736 + p5)
    (h6 : mu + p7 ≤ 376 + p6) (h7 : mu + p8 ≤ 496 + p7)
    (h8 : mu + p9 ≤ 496 + p8) (h9 : mu + p10 ≤ 376 + p9)
    (h10 : mu + p11 ≤ 736 + p10) (h11 : mu + p12 ≤ 376 + p11)
    (h12 : mu + p13 ≤ 496 + p12) (h13 : mu + p0 ≤ 736 + p13) :
    mu ≤ 496 := by linarith

theorem nine_edge_range
    {mu R p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : ℚ}
    (h0 : mu + p1 ≤ 252 + p0) (h1 : mu + p2 ≤ 378 + p1)
    (h2 : mu + p3 ≤ 496 + p2) (h3 : mu + p4 ≤ 496 + p3)
    (h4 : mu + p5 ≤ 616 + p4) (h5 : mu + p6 ≤ 496 + p5)
    (h6 : mu + p7 ≤ 496 + p6) (h7 : mu + p8 ≤ 376 + p7)
    (h8 : mu + p9 ≤ 256 + p8) (hr : p0 - p9 ≤ R) :
    9 * mu ≤ 3862 + R := by linarith

theorem comparison_lower_bound
    {mu C R : ℚ} (hmu : 0 ≤ mu) (hC : 0 ≤ C)
    (hcap : mu ≤ 496) (hwalk : 9 * mu ≤ 3862 + R) :
    551765 / 2348 ≤ (1098960 + 8 * mu + 24 * C + R) / (4200 + mu) := by
  have hp : (0 : ℚ) < 4200 + mu := by linarith
  apply (le_div_iff₀ hp).2
  linarith

theorem equality_parameters
    {mu C R : ℚ} (hmu : 0 ≤ mu) (hC : 0 ≤ C)
    (hcap : mu ≤ 496) (hwalk : 9 * mu ≤ 3862 + R)
    (heq : (1098960 + 8 * mu + 24 * C + R) / (4200 + mu) = 551765 / 2348) :
    mu = 496 ∧ C = 0 ∧ R = 602 := by
  have hp : (0 : ℚ) < 4200 + mu := by linarith
  have hn := (div_eq_iff hp.ne').mp heq
  have hm : mu = 496 := by linarith
  have hc : C = 0 := by linarith
  exact ⟨hm, hc, by linarith⟩

theorem exact_gap : (551765 / 2348 : ℚ) = 235 - 15 / 2348 := by
  norm_num

theorem strict_above234 : (234 : ℚ) < 551765 / 2348 := by
  norm_num

theorem arithmetic_attainment :
    (1098960 + 8 * (496 : ℚ) + 24 * 0 + 602) / (4200 + 496) = 551765 / 2348 ∧
    9 * (496 : ℚ) = 3862 + 602 ∧ 14 * (496 : ℚ) = 6944 := by
  norm_num

#print axioms fourteen_cycle_cap
#print axioms nine_edge_range
#print axioms comparison_lower_bound
#print axioms equality_parameters
#print axioms exact_gap
#print axioms strict_above234
#print axioms arithmetic_attainment

end Snake9.RangeObstruction156
