import Mathlib.Tactic

namespace Snake9.Numeric137

set_option maxHeartbeats 2000000

theorem exceptional_parameters (W a k t : Nat)
    (ha : 1 ≤ a) (ha7 : a ≤ 7) (hak : a ≤ k)
    (hfirst : W + 2*k + t ≤ 7*a - a*(a-1)/2 + 1)
    (hsecond : W + 3*k + t ≤ k*(8-a+t) + 2)
    (hlarge : 13 ≤ W) :
    a = 5 ∧ k = 5 ∧ t = 3 := by
  have hkhi : k ≤ 8 := by
    interval_cases a <;> norm_num at hfirst <;> omega
  have hklo : 1 ≤ k := by omega
  interval_cases a <;> interval_cases k <;> norm_num at * <;> omega

theorem eight_coordinates (W k t : Nat)
    (hfirst : W + 2*k + t ≤ 29)
    (hk : 8 ≤ k) (hlarge : 13 ≤ W) :
    k = 8 ∧ t = 0 := by
  omega

#print axioms exceptional_parameters
#print axioms eight_coordinates

end Snake9.Numeric137
