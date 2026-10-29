import Mathlib.Tactic

namespace Snake9.Paper66

theorem current_budget (m W : ℤ)
    (hbudget : W+4200*m≤1099680)
    (hpotential : 18823*(m-8)≤38*W+23459) :
    178423*m≤41961883 := by omega

theorem current_integer_bound (m : ℤ) (h : 178423*m≤41961883) : m≤235 := by omega

theorem current_does_not_exclude_235 : (178423:ℤ)*235≤41961883 := by norm_num

theorem mean_improvement : (18823:ℚ)/38-9891/20=301/380 := by norm_num

theorem normalized_mean : ((18823:ℚ)/38)/120=18823/4560 := by norm_num

theorem share_only_improvement : (9961:ℚ)/2400-1991/480=1/400 := by norm_num

#print axioms current_budget
#print axioms current_integer_bound
#print axioms current_does_not_exclude_235
#print axioms mean_improvement
#print axioms normalized_mean
#print axioms share_only_improvement

end Snake9.Paper66
