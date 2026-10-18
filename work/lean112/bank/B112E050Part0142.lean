import B112E050Part0141
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c10904 : List Lit := [(88, false)]
theorem step10904 (p : Nat → Bool) (h : Constraints p) : clause p c10904 = true :=
  Snake9.LocalRup.prove_clause [c10902, c10307, c10886, c10784, c4214] c10904 (by decide) p (sat_cons (step10902 p h) (sat_cons (step10307 p h) (sat_cons (step10886 p h) (sat_cons (step10784 p h) (sat_cons (step4214 p h) (sat_nil p))))))
def c10905 : List Lit := [(1739, false)]
theorem step10905 (p : Nat → Bool) (h : Constraints p) : clause p c10905 = true :=
  Snake9.LocalRup.prove_clause [c10903, c10856, c1442] c10905 (by decide) p (sat_cons (step10903 p h) (sat_cons (step10856 p h) (sat_cons (step1442 p h) (sat_nil p))))
def c10906 : List Lit := []
theorem step10906 (p : Nat → Bool) (h : Constraints p) : clause p c10906 = true :=
  Snake9.LocalRup.prove_clause [c10904, c10905, c1434] c10906 (by decide) p (sat_cons (step10904 p h) (sat_cons (step10905 p h) (sat_cons (step1434 p h) (sat_nil p))))
end B112E050
