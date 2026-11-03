import JointFloors145

namespace Snake9.TwoCycles145

theorem eleven_cycle_mean_cap {μ C p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : ℚ}
    (h0 : μ + p1 ≤ 360 + C + p0) (h1 : μ + p2 ≤ 496 + p1)
    (h2 : μ + p3 ≤ 480 + C + p2) (h3 : μ + p4 ≤ 496 + p3)
    (h4 : μ + p5 ≤ 496 + p4) (h5 : μ + p6 ≤ 376 + p5)
    (h6 : μ + p7 ≤ 616 + p6) (h7 : μ + p8 ≤ 487 + C + p7)
    (h8 : μ + p9 ≤ 496 + p8) (h9 : μ + p10 ≤ 480 + C + p9)
    (h10 : μ + p0 ≤ 616 + p10) : 11 * μ ≤ 5399 + 4 * C := by linarith

theorem necessary_credit {μ F C R : ℚ}
    (hμ : 0 ≤ μ) (h11 : 11 * μ ≤ 5399 + 4 * C)
    (hrange : 2 * μ ≤ 496 + F + R)
    (hgood : (1098960 + 8 * μ + 24 * C + R) / (4200 + μ) < 235) :
    11329 - 11 * F < 636 * C := by
  have hp : (0 : ℚ) < 4200 + μ := by linarith
  have hn := (div_lt_iff₀ hp).mp hgood
  linarith

theorem necessary_joint_floors {μ F G C R : ℚ}
    (hμ : 0 ≤ μ) (h11 : 11 * μ ≤ 5399 + 4 * C)
    (h14 : 7 * μ ≤ 3424 + 2 * F + G)
    (hrange : 2 * μ ≤ 496 + F + R)
    (hgood : (1098960 + 8 * μ + 24 * C + R) / (4200 + μ) < 235) :
    9074 < 325 * F + 159 * G := by
  have ha := necessary_credit hμ h11 hrange hgood
  have hb := Snake9.JointFloors145.necessary_tradeoff hμ h14 hrange hgood
  linarith

theorem both16_lower_bound {μ C R : ℚ}
    (hμ : 0 ≤ μ) (h11 : 11 * μ ≤ 5399 + 4 * C)
    (h14 : 7 * μ ≤ 3472) (hrange : 2 * μ ≤ 512 + R) :
    551875 / 2348 ≤ (1098960 + 8 * μ + 24 * C + R) / (4200 + μ) := by
  have hp : (0 : ℚ) < 4200 + μ := by linarith
  apply (le_div_iff₀ hp).2
  linarith

theorem both16_gap : (551875 / 2348 : ℚ) = 235 + 95 / 2348 := by norm_num

theorem both16_cycle_relaxation_attains :
    (1098960 + 8 * (496 : ℚ) + 24 * (57 / 4) + 480) / (4200 + 496) =
      551875 / 2348 := by norm_num

theorem floor16_needs25_if_eleven_cycle_unchanged {μ C R : ℚ} {G : Nat}
    (hμ : 0 ≤ μ) (h11 : 11 * μ ≤ 5399 + 4 * C)
    (h14 : 7 * μ ≤ 3456 + G) (hrange : 2 * μ ≤ 512 + R)
    (hgood : (1098960 + 8 * μ + 24 * C + R) / (4200 + μ) < 235) : 25 ≤ G := by
  have hc : 7 * μ ≤ 3424 + 2 * (16 : ℚ) + G := by linarith
  have hr : 2 * μ ≤ 496 + (16 : ℚ) + R := by linarith
  have hn := necessary_joint_floors hμ h11 hc hr hgood
  by_contra h
  have hg : G ≤ 24 := by omega
  have hgr : (G : ℚ) ≤ 24 := by exact_mod_cast hg
  linarith

#print axioms eleven_cycle_mean_cap
#print axioms necessary_credit
#print axioms necessary_joint_floors
#print axioms both16_lower_bound
#print axioms both16_gap
#print axioms both16_cycle_relaxation_attains
#print axioms floor16_needs25_if_eleven_cycle_unchanged

end Snake9.TwoCycles145
