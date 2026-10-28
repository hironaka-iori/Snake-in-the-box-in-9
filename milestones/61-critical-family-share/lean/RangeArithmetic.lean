import Mathlib.Tactic
namespace Snake9.CriticalFamily61

theorem normalized_gain : (4961:ℚ)/1200-3297/800=31/2400 := by norm_num

/-- The restricted graph already supplies a ceiling below the zero-range target. -/
theorem still_below_234_target (mu rho : ℚ) (hm : mu≤4961/10) (hr : 0≤rho) :
    235*(4200+mu)≤1099440+10*mu+rho := by linarith

#print axioms normalized_gain
#print axioms still_below_234_target
end Snake9.CriticalFamily61
