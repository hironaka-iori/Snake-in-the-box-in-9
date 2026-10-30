import CheckedShareBudget

namespace Snake9.ExclusionSelection69

theorem relaxed_potential_consequence (m W : ℤ)
    (hb : W+4200*m ≤ 1098960)
    (hp : 14387*(m-8) ≤ 29*W+18984) : 136187*m ≤ 32003920 := by omega

theorem relaxed_integer_bound (m : ℤ) (h : 136187*m ≤ 32003920) : m ≤ 234 := by omega

theorem relaxed_margin : (136187:ℤ)*235-32003920=25 := by norm_num

/-- With this denominator, boundary budget and potential range, decreasing the
    integer numerator further cannot exclude 235 by this inequality alone. -/
theorem smaller_numerator_insufficient (p : ℤ) (hp : p ≤ 14386) :
    (p+4200*29)*235 ≤ 1098960*29+8*p+18984 := by omega

#print axioms relaxed_potential_consequence
#print axioms relaxed_integer_bound
#print axioms relaxed_margin
#print axioms smaller_numerator_insufficient
end Snake9.ExclusionSelection69
