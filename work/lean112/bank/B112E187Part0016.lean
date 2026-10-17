import B112E187Part0015
namespace B112E187
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2041 : List Lit := []
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c2039, c2040, c535] c2041 (by decide) p (sat_cons (step2039 p h) (sat_cons (step2040 p h) (sat_cons (step535 p h) (sat_nil p))))
end B112E187
