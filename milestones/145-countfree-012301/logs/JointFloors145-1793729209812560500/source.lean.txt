import Mathlib.Tactic

namespace Snake9.JointFloors145

theorem cycle_mean_cap {μ F G p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 : ℚ}
    (h0 : μ + p1 ≤ 256 + p0) (h1 : μ + p2 ≤ 240 + F + p1)
    (h2 : μ + p3 ≤ 736 + p2) (h3 : μ + p4 ≤ 496 + p3)
    (h4 : μ + p5 ≤ 360 + F + p4) (h5 : μ + p6 ≤ 736 + p5)
    (h6 : μ + p7 ≤ 360 + G + p6) (h7 : μ + p8 ≤ 496 + p7)
    (h8 : μ + p9 ≤ 480 + F + p8) (h9 : μ + p10 ≤ 376 + p9)
    (h10 : μ + p11 ≤ 736 + p10) (h11 : μ + p12 ≤ 360 + F + p11)
    (h12 : μ + p13 ≤ 496 + p12) (h13 : μ + p0 ≤ 720 + G + p13) :
    7 * μ ≤ 3424 + 2 * F + G := by linarith

theorem two_edge_range {μ F R p0 p1 p2 : ℚ}
    (h0 : μ + p1 ≤ 256 + p0) (h1 : μ + p2 ≤ 240 + F + p1)
    (hr : p0 - p2 ≤ R) : 2 * μ ≤ 496 + F + R := by linarith

theorem necessary_tradeoff {μ F G B C R : ℚ}
    (hμ : 0 ≤ μ) (hcap : 7 * μ ≤ 3424 + 2 * F + G)
    (hrange : 2 * μ ≤ 496 + F + R)
    (hgood : (1098960 + 8 * μ + B * C + R) / (4200 + μ) < 235) :
    9848 + 7 * B * C < 457 * F + 225 * G := by
  have hp : (0 : ℚ) < 4200 + μ := by linarith
  have hnum := (div_lt_iff₀ hp).mp hgood
  nlinarith

theorem floor19_lower_bound {μ B C R : ℚ}
    (hμ : 0 ≤ μ) (hcap : 7 * μ ≤ 3466)
    (hrange : 2 * μ ≤ 515 + R) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    7723775 / 32866 ≤ (1098960 + 8 * μ + B * C + R) / (4200 + μ) := by
  have hp : (0 : ℚ) < 4200 + μ := by linarith
  have hBC := mul_nonneg hB hC
  apply (le_div_iff₀ hp).2
  nlinarith

theorem floor19_gap : (7723775 / 32866 : ℚ) = 235 + 265 / 32866 := by norm_num

theorem floor16_needs_second_floor12 {μ B C R : ℚ} {G : Nat}
    (hμ : 0 ≤ μ) (hcap : 7 * μ ≤ 3456 + G)
    (hrange : 2 * μ ≤ 512 + R) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hgood : (1098960 + 8 * μ + B * C + R) / (4200 + μ) < 235) : 12 ≤ G := by
  have hc : 7 * μ ≤ 3424 + 2 * (16 : ℚ) + G := by linarith
  have hr : 2 * μ ≤ 496 + (16 : ℚ) + R := by linarith
  have hn := necessary_tradeoff hμ hc hr hgood
  have hBC := mul_nonneg hB hC
  by_contra h
  have hg : G ≤ 11 := by omega
  have hgr : (G : ℚ) ≤ 11 := by exact_mod_cast hg
  nlinarith

theorem both16_credit_limit {μ C R : ℚ}
    (hμ : 0 ≤ μ) (hcap : 7 * μ ≤ 3472) (hrange : 2 * μ ≤ 512 + R)
    (hgood : (1098960 + 8 * μ + 24 * C + R) / (4200 + μ) < 235) : C < 19 / 3 := by
  have hc : 7 * μ ≤ 3424 + 2 * (16 : ℚ) + 16 := by linarith
  have hr : 2 * μ ≤ 496 + (16 : ℚ) + R := by linarith
  have hn := necessary_tradeoff hμ hc hr hgood
  nlinarith

#print axioms cycle_mean_cap
#print axioms two_edge_range
#print axioms necessary_tradeoff
#print axioms floor19_lower_bound
#print axioms floor19_gap
#print axioms floor16_needs_second_floor12
#print axioms both16_credit_limit

end Snake9.JointFloors145
