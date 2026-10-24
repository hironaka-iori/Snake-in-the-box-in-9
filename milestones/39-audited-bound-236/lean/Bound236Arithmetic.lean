import Mathlib.Tactic

/- These are the arithmetic steps in the revised exposition, conditional on the
   stated inputs. They do not independently replay the 732 window proofs. -/
namespace Bound236Revision

theorem internal_boundary (m tail total initial final : ℤ)
    (telescoped : 42*(m-7) + final ≤ 11*tail + initial)
    (initial_bound : initial ≤ 63) (final_nonnegative : 0 ≤ final)
    (first_six : 6 + tail ≤ total) : 42*m ≤ 11*total + 291 := by
  omega

theorem endpoint_bound (m total internal : ℤ)
    (window : 42*m ≤ 11*internal + 291)
    (endpoints : internal + 8 ≤ total) : 42*m ≤ 11*total + 203 := by
  omega

theorem incidence_bound (m total s0 : ℤ)
    (window : 42*m ≤ 11*total + 203)
    (census : total + 2*s0 + 35*(m+1) = 9214)
    (empty_nonnegative : 0 ≤ s0) : 427*m ≤ 101172 := by
  omega

theorem integer_bound (m : ℤ) (bound : 427*m ≤ 101172) : m ≤ 236 := by
  omega

end Bound236Revision
#print axioms Bound236Revision.internal_boundary
#print axioms Bound236Revision.endpoint_bound
#print axioms Bound236Revision.incidence_bound
#print axioms Bound236Revision.integer_bound
