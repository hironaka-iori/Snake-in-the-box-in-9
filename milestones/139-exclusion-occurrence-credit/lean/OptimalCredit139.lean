import Mathlib.Tactic

namespace Snake9.OptimalCredit139

theorem comparison_relaxation_minimum {μ C R : ℚ}
    (hμ : 0 ≤ μ) (hfour : μ ≤ 488+C/2) (hfive : μ ≤ 2446/5)
    (hR : 0 ≤ R) :
    2757328/11723 ≤ (1098960+8*μ+24*C+R)/(4200+μ) := by
  have hp : (0 : ℚ) < 4200+μ := by linarith
  apply (le_div_iff₀ hp).2
  nlinarith

theorem comparison_relaxation_attained :
    (1098960+8*(2446/5 : ℚ)+24*(12/5 : ℚ))/(4200+2446/5) =
      2757328/11723 := by
  norm_num

#print axioms comparison_relaxation_minimum
#print axioms comparison_relaxation_attained
end Snake9.OptimalCredit139
