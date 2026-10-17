import B112E159Part0020
namespace B112E159
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2349 : List Lit := [(16, true)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c2345, c2332, c1064] c2349 (by decide) p (sat_cons (step2345 p h) (sat_cons (step2332 p h) (sat_cons (step1064 p h) (sat_nil p))))
def c2350 : List Lit := [(817, true)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c2346, c1382] c2350 (by decide) p (sat_cons (step2346 p h) (sat_cons (step1382 p h) (sat_nil p)))
def c2351 : List Lit := [(870, true)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c2347, c2304, c672] c2351 (by decide) p (sat_cons (step2347 p h) (sat_cons (step2304 p h) (sat_cons (step672 p h) (sat_nil p))))
def c2352 : List Lit := []
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c2349, c2348, c2303, c2350, c2345, c2351, c2339, c2341, c1245] c2352 (by decide) p (sat_cons (step2349 p h) (sat_cons (step2348 p h) (sat_cons (step2303 p h) (sat_cons (step2350 p h) (sat_cons (step2345 p h) (sat_cons (step2351 p h) (sat_cons (step2339 p h) (sat_cons (step2341 p h) (sat_cons (step1245 p h) (sat_nil p))))))))))
end B112E159
