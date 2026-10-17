import B112E104Part0020
namespace B112E104
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2500 : List Lit := [(22, false)]
theorem step2500 (p : Nat → Bool) (h : Constraints p) : clause p c2500 = true :=
  Snake9.LocalRup.prove_clause [c2498, c2493, c2492, c2445] c2500 (by decide) p (sat_cons (step2498 p h) (sat_cons (step2493 p h) (sat_cons (step2492 p h) (sat_cons (step2445 p h) (sat_nil p)))))
def c2501 : List Lit := []
theorem step2501 (p : Nat → Bool) (h : Constraints p) : clause p c2501 = true :=
  Snake9.LocalRup.prove_clause [c2500, c2499, c2492, c2493, c2497, c2397] c2501 (by decide) p (sat_cons (step2500 p h) (sat_cons (step2499 p h) (sat_cons (step2492 p h) (sat_cons (step2493 p h) (sat_cons (step2497 p h) (sat_cons (step2397 p h) (sat_nil p)))))))
end B112E104
