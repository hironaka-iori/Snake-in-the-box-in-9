import Mathlib.Tactic

/- Arithmetic steps of the revised exposition. These lemmas do not replay the
175 window certificates or assert a new bound on snakes independently of them. -/
namespace PaperRevision

theorem square_identity (s0 s1 s2 s3 v : ℤ)
    (squares : s0 + s1 + s2 + s3 = 4608)
    (incidences : s1 + 2*s2 + 3*s3 = 36*v)
    (corners : s3 = v - 2) : s1 + 2*s0 + 35*v = 9214 := by
  omega

theorem internal_boundary (m tail total initial final : ℤ)
    (telescoped : 7*(m-7) + final ≤ 2*tail + initial)
    (initial_bound : initial ≤ 15) (final_nonnegative : 0 ≤ final)
    (first_six : 6 + tail ≤ total) : 7*m ≤ 2*total + 52 := by
  omega

theorem endpoint_and_incidence (m total internal s0 : ℤ)
    (window : 7*m ≤ 2*internal + 52)
    (endpoints : internal + 8 ≤ total)
    (census : total + 2*s0 + 35*(m+1) = 9214)
    (empty_nonnegative : 0 ≤ s0) : m ≤ 238 := by
  omega

theorem charge_target_230 (v charge : ℤ)
    (census : charge + 840*v ≤ 221136)
    (target : 114*v - 191 ≤ charge) : v - 1 ≤ 230 := by
  omega

theorem charge_target_231 (v charge : ℤ)
    (census : charge + 840*v ≤ 221136)
    (target : 114*v - 1145 ≤ charge) : v - 1 ≤ 231 := by
  omega

end PaperRevision

#print axioms PaperRevision.square_identity
#print axioms PaperRevision.internal_boundary
#print axioms PaperRevision.endpoint_and_incidence
#print axioms PaperRevision.charge_target_230
#print axioms PaperRevision.charge_target_231
