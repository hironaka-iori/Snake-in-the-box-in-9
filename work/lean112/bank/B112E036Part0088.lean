import B112E036Part0087
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c7277 : List Lit := [(70, true)]
theorem step7277 (p : Nat → Bool) (h : Constraints p) : clause p c7277 = true :=
  Snake9.LocalRup.prove_clause [c7274, c1283] c7277 (by decide) p (sat_cons (step7274 p h) (sat_cons (step1283 p h) (sat_nil p)))
def c7278 : List Lit := [(112, true)]
theorem step7278 (p : Nat → Bool) (h : Constraints p) : clause p c7278 = true :=
  Snake9.LocalRup.prove_clause [c7275, c7276, c7254, c7243, c6564] c7278 (by decide) p (sat_cons (step7275 p h) (sat_cons (step7276 p h) (sat_cons (step7254 p h) (sat_cons (step7243 p h) (sat_cons (step6564 p h) (sat_nil p))))))
def c7279 : List Lit := []
theorem step7279 (p : Nat → Bool) (h : Constraints p) : clause p c7279 = true :=
  Snake9.LocalRup.prove_clause [c7277, c7278, c7272, c7256, c437] c7279 (by decide) p (sat_cons (step7277 p h) (sat_cons (step7278 p h) (sat_cons (step7272 p h) (sat_cons (step7256 p h) (sat_cons (step437 p h) (sat_nil p))))))
end B112E036
