import Mathlib.Tactic

namespace Snake9.Paper76

theorem scaled_window_bound (m W p d R : ℚ) (hd : 0 ≤ d)
    (hb : W + 4200*m ≤ 1098960)
    (hp : p*(m-8) ≤ d*W+R) :
    (p+4200*d)*m ≤ 1098960*d+8*p+R := by
  nlinarith

theorem strict_234_criterion (m p d R : ℚ)
    (hpos : 0 < p+4200*d)
    (hbound : (p+4200*d)*m ≤ 1098960*d+8*p+R)
    (hstrict : 111960*d+R < 227*p) : m < 235 := by
  by_contra h
  have hm : 235 ≤ m := le_of_not_gt h
  nlinarith

theorem completed_comparison (m W : ℤ)
    (hb : W+4200*m ≤ 1098960)
    (hp : 480*(m-8) ≤ W+536) : 45*m ≤ 10609 := by omega

theorem one_pending_comparison (m W : ℤ)
    (hb : W+4200*m ≤ 1098960)
    (hp : 483*(m-8) ≤ W+551) : 669*m ≤ 157625 := by omega

theorem mixed_comparison (m W : ℤ)
    (hb : W+4200*m ≤ 1098960)
    (hp : 496*(m-8) ≤ W+600) : 587*m ≤ 137941 ∧ m ≤ 234 := by omega

theorem mixed_margin : (227:ℤ)*496-111960-600=32 := by norm_num

#print axioms scaled_window_bound
#print axioms strict_234_criterion
#print axioms completed_comparison
#print axioms one_pending_comparison
#print axioms mixed_comparison
#print axioms mixed_margin

end Snake9.Paper76
