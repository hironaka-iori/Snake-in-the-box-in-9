import B112E098Part0000
namespace B112E098
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c287 : List Lit := [(1301, false)]
theorem step287 (p : Nat → Bool) (h : Constraints p) : clause p c287 = true :=
  Snake9.LocalRup.prove_clause [c285, c233, c161] c287 (by decide) p (sat_cons (step285 p h) (sat_cons (step233 p h) (sat_cons (step161 p h) (sat_nil p))))
def c288 : List Lit := [(1328, false)]
theorem step288 (p : Nat → Bool) (h : Constraints p) : clause p c288 = true :=
  Snake9.LocalRup.prove_clause [c286, c281, c204] c288 (by decide) p (sat_cons (step286 p h) (sat_cons (step281 p h) (sat_cons (step204 p h) (sat_nil p))))
def c289 : List Lit := [(1296, false)]
theorem step289 (p : Nat → Bool) (h : Constraints p) : clause p c289 = true :=
  Snake9.LocalRup.prove_clause [c287, c280, c158] c289 (by decide) p (sat_cons (step287 p h) (sat_cons (step280 p h) (sat_cons (step158 p h) (sat_nil p))))
def c290 : List Lit := []
theorem step290 (p : Nat → Bool) (h : Constraints p) : clause p c290 = true :=
  Snake9.LocalRup.prove_clause [c288, c289, c242] c290 (by decide) p (sat_cons (step288 p h) (sat_cons (step289 p h) (sat_cons (step242 p h) (sat_nil p))))
end B112E098
