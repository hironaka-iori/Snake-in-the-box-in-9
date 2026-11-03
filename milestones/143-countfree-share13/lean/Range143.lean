import Mathlib.Tactic

namespace Snake9.Range143

theorem five_edge_range {μ R p0 p1 p2 p3 p4 p5 : ℚ}
    (h01 : μ + p1 ≤ 374 + p0) (h12 : μ + p2 ≤ 492 + p1)
    (h23 : μ + p3 ≤ 614 + p2) (h34 : μ + p4 ≤ 374 + p3)
    (h45 : μ + p5 ≤ 376 + p4) (hspread : p0 - p5 ≤ R) :
    5 * μ - 2230 ≤ R := by
  linarith

theorem cycle_mean_cap {μ p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℚ}
    (h0 : μ + p1 ≤ 614 + p0) (h1 : μ + p2 ≤ 494 + p1)
    (h2 : μ + p3 ≤ 376 + p2) (h3 : μ + p4 ≤ 734 + p3)
    (h4 : μ + p5 ≤ 374 + p4) (h5 : μ + p6 ≤ 492 + p5)
    (h6 : μ + p7 ≤ 614 + p6) (h7 : μ + p8 ≤ 374 + p7)
    (h8 : μ + p0 ≤ 376 + p8) :
    μ ≤ 4448 / 9 := by
  linarith

theorem comparison_lower_bound {μ C B R : ℚ}
    (hμ : 0 ≤ μ) (hcap : μ ≤ 4448 / 9)
    (hrange : 5 * μ - 2230 ≤ R) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    4964197 / 21124 ≤ (1098960 + 8 * μ + B * C + R) / (4200 + μ) := by
  have hp : (0 : ℚ) < 4200 + μ := by linarith
  apply (le_div_iff₀ hp).2
  have hBC := mul_nonneg hB hC
  nlinarith

theorem comparison_obstruction {μ C B R : ℚ}
    (hμ : 0 ≤ μ) (hcap : μ ≤ 4448 / 9)
    (hrange : 5 * μ - 2230 ≤ R) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    235 < (1098960 + 8 * μ + B * C + R) / (4200 + μ) := by
  have h := comparison_lower_bound hμ hcap hrange hC hB
  have hstrict : (235 : ℚ) < 4964197 / 21124 := by norm_num
  exact lt_of_lt_of_le hstrict h

theorem floor14_relaxation_value :
    (1098960 + 8 * (4448 / 9 : ℚ) + 2170 / 9) / (4200 + 4448 / 9) =
      235 + 57 / 21124 := by norm_num

theorem floor15_relaxation_value :
    (1098960 + 8 * (4454 / 9 : ℚ) + 2173 / 9) / (4200 + 4454 / 9) =
      235 - 1245 / 42254 := by norm_num

theorem floor18_relaxation_value :
    (1098960 + 8 * (4472 / 9 : ℚ) + 2182 / 9) / (4200 + 4472 / 9) =
      235 - 2661 / 21136 := by norm_num

#print axioms five_edge_range
#print axioms cycle_mean_cap
#print axioms comparison_lower_bound
#print axioms comparison_obstruction
#print axioms floor14_relaxation_value
#print axioms floor15_relaxation_value
#print axioms floor18_relaxation_value
end Snake9.Range143
