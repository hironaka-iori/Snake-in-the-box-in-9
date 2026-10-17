import B112E152Part0016
namespace B112E152
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2035 : List Lit := [(1589, true)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c2033, c694] c2035 (by decide) p (sat_cons (step2033 p h) (sat_cons (step694 p h) (sat_nil p)))
def c2036 : List Lit := [(1716, false)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c2034, c1285] c2036 (by decide) p (sat_cons (step2034 p h) (sat_cons (step1285 p h) (sat_nil p)))
def c2037 : List Lit := [(1591, true)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c2035, c696] c2037 (by decide) p (sat_cons (step2035 p h) (sat_cons (step696 p h) (sat_nil p)))
def c2038 : List Lit := [(1636, false)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c2036, c2027, c895] c2038 (by decide) p (sat_cons (step2036 p h) (sat_cons (step2027 p h) (sat_cons (step895 p h) (sat_nil p))))
def c2039 : List Lit := []
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c2037, c2038, c2031, c1831] c2039 (by decide) p (sat_cons (step2037 p h) (sat_cons (step2038 p h) (sat_cons (step2031 p h) (sat_cons (step1831 p h) (sat_nil p)))))
end B112E152
