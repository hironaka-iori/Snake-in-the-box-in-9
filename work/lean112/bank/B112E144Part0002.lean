import B112E144Part0001
namespace B112E144
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c491 : List Lit := []
theorem step491 (p : Nat → Bool) (h : Constraints p) : clause p c491 = true :=
  Snake9.LocalRup.prove_clause [c490, c489, c483, c212] c491 (by decide) p (sat_cons (step490 p h) (sat_cons (step489 p h) (sat_cons (step483 p h) (sat_cons (step212 p h) (sat_nil p)))))
end B112E144
