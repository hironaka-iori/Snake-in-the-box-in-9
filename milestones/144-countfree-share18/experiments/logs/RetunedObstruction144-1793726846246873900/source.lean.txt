import Mathlib.Tactic

namespace Snake9.RetunedObstruction144

theorem cycle_mean_cap {μ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : ℚ}
    (h0 : μ + p1 ≤ 256 + p0) (h1 : μ + p2 ≤ 246 + p1)
    (h2 : μ + p3 ≤ 736 + p2) (h3 : μ + p4 ≤ 496 + p3)
    (h4 : μ + p5 ≤ 371 + p4) (h5 : μ + p6 ≤ 736 + p5)
    (h6 : μ + p7 ≤ 364 + p6) (h7 : μ + p8 ≤ 496 + p7)
    (h8 : μ + p9 ≤ 486 + p8) (h9 : μ + p10 ≤ 376 + p9)
    (h10 : μ + p11 ≤ 736 + p10) (h11 : μ + p12 ≤ 371 + p11)
    (h12 : μ + p13 ≤ 496 + p12) (h13 : μ + p0 ≤ 724 + p13) :
    7 * μ ≤ 3445 := by linarith

theorem comparison_lower_bound {μ C B R : ℚ}
    (hμ : 0 ≤ μ) (hcap : 7 * μ ≤ 3445)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    1544056 / 6569 ≤ (1098960 + 8 * μ + B * C + R) / (4200 + μ) := by
  have hp : (0 : ℚ) < 4200 + μ := by linarith
  have hBC := mul_nonneg hB hC
  apply (le_div_iff₀ hp).2
  nlinarith

theorem comparison_obstruction {μ C B R : ℚ}
    (hμ : 0 ≤ μ) (hcap : 7 * μ ≤ 3445)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    235 < (1098960 + 8 * μ + B * C + R) / (4200 + μ) := by
  have h := comparison_lower_bound hμ hcap hC hB hR
  have hs : (235 : ℚ) < 1544056 / 6569 := by norm_num
  exact lt_of_lt_of_le hs h

theorem obstruction_gap : (1544056 / 6569 : ℚ) = 235 + 341 / 6569 := by norm_num

theorem computed_comparison :
    (1098960 + 8 * (3445 / 7 : ℚ) + 24 * (601 / 36) + 608) /
      (4200 + 3445 / 7) = 235 + 26297 / 98535 := by norm_num

#print axioms cycle_mean_cap
#print axioms comparison_lower_bound
#print axioms comparison_obstruction
#print axioms obstruction_gap
#print axioms computed_comparison
end Snake9.RetunedObstruction144
