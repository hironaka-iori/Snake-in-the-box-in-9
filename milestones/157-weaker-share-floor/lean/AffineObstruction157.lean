import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Snake9.AffineObstruction157

theorem affine_margin
    {mu t R : ℚ}
    (h1 : mu ≤ 377 + 118 * t) (h2 : mu ≤ 616 - 120 * t)
    (hr : 602 * t ≤ R) :
    227 * mu - 111960 - R ≤ -(10351 / 119) := by
  linarith

theorem affine_comparison
    {mu t R C : ℚ} (hm : 0 ≤ mu) (hc : 0 ≤ C)
    (h1 : mu ≤ 377 + 118 * t) (h2 : mu ≤ 616 - 120 * t)
    (hr : 602 * t ≤ R) :
    235 < (1098960 + 8 * mu + 24 * C + R) / (4200 + mu) := by
  have hp : (0 : ℚ) < 4200 + mu := by linarith
  have ha := affine_margin h1 h2 hr
  apply (lt_div_iff₀ hp).2
  linarith

theorem weaker_walk_range
    {mu R : ℚ} (hm : mu = 496) (hw : 9 * mu ≤ 3861 + R) :
    603 ≤ R := by linarith

theorem target_range
    {R C : ℚ} (hc : 0 ≤ C) :
    ((1098960 + 8 * 496 + 24 * C + R) / (4200 + 496) < 235) ↔
    24 * C + R < 632 := by
  constructor <;> intro h <;> norm_num at * <;> linarith

theorem transferred_comparison :
    (1098960 + 8 * (495 : ℚ) + 602) / (4200 + 495) = 235 + 197 / 4695 := by
  norm_num

#print axioms affine_margin
#print axioms affine_comparison
#print axioms weaker_walk_range
#print axioms target_range
#print axioms transferred_comparison

end Snake9.AffineObstruction157
