import B112E190Part0001
namespace B112E190
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c546 : List Lit := []
theorem step546 (p : Nat → Bool) (h : Constraints p) : clause p c546 = true :=
  Snake9.LocalRup.prove_clause [c544, c545, c515, c514, c119] c546 (by decide) p (sat_cons (step544 p h) (sat_cons (step545 p h) (sat_cons (step515 p h) (sat_cons (step514 p h) (sat_cons (step119 p h) (sat_nil p))))))
end B112E190
