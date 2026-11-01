import Mathlib.Tactic

namespace Snake9.GraphInterpretation74

/-- Conditional algebra for a path of length at most 227 with deficit at
least 632 relative to slope 496. Actual graph/path certificates are separate. -/
theorem path_deficit_obstruction (p R L W : ℚ)
    (hL : L ≤ 227) (hp : p ≤ 496)
    (hpath : p*L-W ≤ R) (hdeficit : 632 ≤ 496*L-W) :
    227*p-R ≤ 111960 := by
  have hmul := mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hp)
  nlinarith

#print axioms path_deficit_obstruction
end Snake9.GraphInterpretation74
