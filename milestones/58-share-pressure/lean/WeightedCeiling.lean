import Mathlib.Tactic

namespace Snake9.LocalWindow.ForcedShare58

/-- The six vertices of the fixed-centre-weight simplex, on the saved cycle.
    The finite cycle and its coefficients are checked separately. -/
theorem weighted_cycle_ceiling (a b c d e f : ℚ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hs : a+b+c+d+e+f=1) :
    4936*a+4935*b+4930*c+4935*d+4945*e+4935*f ≤ 4945 := by
  linarith

/-- This ceiling cannot exclude 235 even with zero potential-range loss,
    when the seven omitted windows are accounted for. -/
theorem weighted_ceiling_insufficient (mu rho : ℚ)
    (hm : mu ≤ 989/2) (hr : 0 ≤ rho) :
    235*(4200+mu) ≤ 1099800+7*mu+rho := by
  linarith

#print axioms weighted_cycle_ceiling
#print axioms weighted_ceiling_insufficient
end Snake9.LocalWindow.ForcedShare58
