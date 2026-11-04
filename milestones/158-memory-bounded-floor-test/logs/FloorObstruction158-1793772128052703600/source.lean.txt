import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Snake9.FloorObstruction158

theorem cycle_cap
    {mu p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℚ}
    (h0 : mu + p1 ≤ 376 + p0) (h1 : mu + p2 ≤ 736 + p1)
    (h2 : mu + p3 ≤ 497 + p2) (h3 : mu + p4 ≤ 372 + p3)
    (h4 : mu + p5 ≤ 737 + p4) (h5 : mu + p6 ≤ 256 + p5)
    (h6 : mu + p7 ≤ 376 + p6) (h7 : mu + p8 ≤ 736 + p7)
    (h8 : mu + p0 ≤ 376 + p8) : 9 * mu ≤ 4462 := by
  linarith

theorem walk_range
    {mu R p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : ℚ}
    (h0 : mu + p1 ≤ 252 + p0) (h1 : mu + p2 ≤ 377 + p1)
    (h2 : mu + p3 ≤ 496 + p2) (h3 : mu + p4 ≤ 496 + p3)
    (h4 : mu + p5 ≤ 616 + p4) (h5 : mu + p6 ≤ 496 + p5)
    (h6 : mu + p7 ≤ 496 + p6) (h7 : mu + p8 ≤ 376 + p7)
    (h8 : mu + p9 ≤ 256 + p8) (hr : p0 - p9 ≤ R) :
    9 * mu ≤ 3861 + R := by linarith

theorem comparison_lower_bound
    {mu C R : ℚ} (hm : 0 ≤ mu) (hc : 0 ≤ C)
    (hcap : 9 * mu ≤ 4462) (hw : 9 * mu ≤ 3861 + R) :
    235 + 175 / 42262 ≤ (1098960 + 8 * mu + 24 * C + R) / (4200 + mu) := by
  have hp : (0 : ℚ) < 4200 + mu := by linarith
  apply (le_div_iff₀ hp).2
  linarith

theorem strict_above235 : (235 : ℚ) < 235 + 175 / 42262 := by norm_num

theorem necessary_floor
    {mu C R F : ℚ} (hm : 0 ≤ mu) (hc : 0 ≤ C)
    (hcap : 9 * mu ≤ 4428 + 2 * F)
    (hw : 9 * mu ≤ 3844 + F + R)
    (ht : (1098960 + 8 * mu + 24 * C + R) / (4200 + mu) < 235) :
    1548 / 89 < F := by
  have hp : (0 : ℚ) < 4200 + mu := by linarith
  have hn := (div_lt_iff₀ hp).mp ht
  linarith

theorem integer_floor_requirement
    {F : ℕ} (hf : (1548 / 89 : ℚ) < (F : ℚ)) : 18 ≤ F := by
  have hq : (17 : ℚ) < (F : ℚ) := by linarith
  have hn : 17 < F := by exact_mod_cast hq
  exact Nat.succ_le_of_lt hn

#print axioms cycle_cap
#print axioms walk_range
#print axioms comparison_lower_bound
#print axioms strict_above235
#print axioms necessary_floor
#print axioms integer_floor_requirement

end Snake9.FloorObstruction158
