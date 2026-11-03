import Mathlib.Tactic

namespace Snake9.Obstruction144

theorem cycle_mean_cap {μ C p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : ℚ}
    (h0 : μ + p1 ≤ 360 + C + p0) (h1 : μ + p2 ≤ 496 + p1)
    (h2 : μ + p3 ≤ 480 + C + p2) (h3 : μ + p4 ≤ 496 + p3)
    (h4 : μ + p5 ≤ 496 + p4) (h5 : μ + p6 ≤ 376 + p5)
    (h6 : μ + p7 ≤ 616 + p6) (h7 : μ + p8 ≤ 487 + C + p7)
    (h8 : μ + p9 ≤ 496 + p8) (h9 : μ + p10 ≤ 480 + C + p9)
    (h10 : μ + p0 ≤ 616 + p10) : 11 * μ ≤ 5399 + 4 * C := by
  linarith

theorem six_edge_range {μ C R p0 p1 p2 p3 p4 p5 p6 : ℚ}
    (h0 : μ + p1 ≤ 360 + C + p0) (h1 : μ + p2 ≤ 496 + p1)
    (h2 : μ + p3 ≤ 480 + C + p2) (h3 : μ + p4 ≤ 496 + p3)
    (h4 : μ + p5 ≤ 496 + p4) (h5 : μ + p6 ≤ 376 + p5)
    (hr : p0 - p6 ≤ R) : 6 * μ - 2704 - 2 * C ≤ R := by
  linarith

theorem zero_credit_comparison {μ R : ℚ}
    (hμ : 0 ≤ μ) (hcap : 11 * μ ≤ 5399) (hR : 0 ≤ R) :
    12131752 / 51599 ≤ (1098960 + 8 * μ + R) / (4200 + μ) := by
  have hp : (0 : ℚ) < 4200 + μ := by linarith
  apply (le_div_iff₀ hp).2
  nlinarith

theorem zero_credit_obstruction {μ R : ℚ}
    (hμ : 0 ≤ μ) (hcap : 11 * μ ≤ 5399) (hR : 0 ≤ R) :
    235 < (1098960 + 8 * μ + R) / (4200 + μ) := by
  have h := zero_credit_comparison hμ hcap hR
  have hs : (235 : ℚ) < 12131752 / 51599 := by norm_num
  exact lt_of_lt_of_le hs h

theorem computed_comparison :
    (1098960 + 8 * (5399 / 11 : ℚ) + 593) / (4200 + 5399 / 11) =
      235 + 12510 / 51599 := by norm_num

theorem zero_range_gap : (12131752 / 51599 : ℚ) = 235 + 5987 / 51599 := by
  norm_num

theorem candidate_cycle_equality :
    11 * (4472 / 9 : ℚ) = 5399 + 4 * (601 / 36) := by norm_num

theorem candidate_path_equality :
    6 * (4472 / 9 : ℚ) - 2704 - 2 * (601 / 36) = 4391 / 18 := by norm_num

theorem candidate_comparison :
    (1098960 + 8 * (4472 / 9 : ℚ) + 24 * (601 / 36) + 4391 / 18) /
      (4200 + 4472 / 9) = 235 - 3405 / 84544 := by norm_num

#print axioms cycle_mean_cap
#print axioms six_edge_range
#print axioms zero_credit_comparison
#print axioms zero_credit_obstruction
#print axioms computed_comparison
#print axioms zero_range_gap
#print axioms candidate_cycle_equality
#print axioms candidate_path_equality
#print axioms candidate_comparison
end Snake9.Obstruction144
