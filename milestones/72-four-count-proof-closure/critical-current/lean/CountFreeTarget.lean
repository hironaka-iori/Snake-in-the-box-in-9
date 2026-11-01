import Mathlib.Tactic

namespace Snake9.CountFreeTarget

/-- Conditional arithmetic only: the walk and square-counting bounds are inputs. -/
theorem upper234_of_weight_bounds (m W : Int)
    (hLower : 496 * (m - 8) - 600 ≤ W)
    (hUpper : W + 4200 * m ≤ 1098960) : m ≤ 234 := by
  omega

/-- The strict margin is 32 in the certificate's integer scaling. -/
theorem strict_margin : 227 * (496 : Int) - 111960 - 600 = 32 := by
  norm_num

#print axioms upper234_of_weight_bounds
#print axioms strict_margin
end Snake9.CountFreeTarget
