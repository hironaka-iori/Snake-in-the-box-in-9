import B112E058Part0009
namespace B112E058
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1323 : List Lit := [(1428, false)]
theorem step1323 (p : Nat → Bool) (h : Constraints p) : clause p c1323 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1295, c824] c1323 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1295 p h) (sat_cons (step824 p h) (sat_nil p))))
def c1324 : List Lit := [(1470, false)]
theorem step1324 (p : Nat → Bool) (h : Constraints p) : clause p c1324 = true :=
  Snake9.LocalRup.prove_clause [c1322, c1241, c461] c1324 (by decide) p (sat_cons (step1322 p h) (sat_cons (step1241 p h) (sat_cons (step461 p h) (sat_nil p))))
def c1325 : List Lit := []
theorem step1325 (p : Nat → Bool) (h : Constraints p) : clause p c1325 = true :=
  Snake9.LocalRup.prove_clause [c1323, c1324, c1256] c1325 (by decide) p (sat_cons (step1323 p h) (sat_cons (step1324 p h) (sat_cons (step1256 p h) (sat_nil p))))
end B112E058
