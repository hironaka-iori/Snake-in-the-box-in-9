import BoundaryCharge

namespace Snake9.CheckedShareBudget68

/-- The graph interpretation remains an explicit hypothesis. -/
theorem potential_consequence (m W : ℤ)
    (hb : W+4200*m ≤ 1098960)
    (hp : 14392*(m-8) ≤ 29*W+18984) : 136192*m ≤ 32003960 := by omega

theorem integer_bound (m : ℤ) (h : 136192*m ≤ 32003960) : m ≤ 234 := by omega

theorem conditional_charge_bound (m G W : Nat)
    (hg : G+840*(m+1) ≤ 221136) (hw : W+2520 ≤ 5*G)
    (hp : 14392*(m-8) ≤ 29*W+18984) : m ≤ 234 := by
  have hb := BoundaryCharge67.global_charge m G W hg hw
  omega

theorem exclusion_margin : (136192:ℤ)*235-32003960=1160 := by norm_num

theorem normalized_mean : ((14392:ℚ)/29)/120=1799/435 := by norm_num

theorem previous_mean_difference : (2482:ℚ)/5-14392/29=18/145 := by norm_num

theorem old_boundary_insufficient : (136192:ℤ)*235 ≤ 32024840 := by norm_num

#print axioms potential_consequence
#print axioms integer_bound
#print axioms conditional_charge_bound
#print axioms exclusion_margin
#print axioms normalized_mean
#print axioms previous_mean_difference
#print axioms old_boundary_insufficient
end Snake9.CheckedShareBudget68
