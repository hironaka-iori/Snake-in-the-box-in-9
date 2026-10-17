import B112E257Part0055
namespace B112E257
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5102 : List Lit := [(89, false)]
theorem step5102 (p : Nat → Bool) (h : Constraints p) : clause p c5102 = true :=
  Snake9.LocalRup.prove_clause [c5100, c5060, c5061, c122] c5102 (by decide) p (sat_cons (step5100 p h) (sat_cons (step5060 p h) (sat_cons (step5061 p h) (sat_cons (step122 p h) (sat_nil p)))))
def c5103 : List Lit := [(73, false)]
theorem step5103 (p : Nat → Bool) (h : Constraints p) : clause p c5103 = true :=
  Snake9.LocalRup.prove_clause [c5100, c5099, c4876, c435] c5103 (by decide) p (sat_cons (step5100 p h) (sat_cons (step5099 p h) (sat_cons (step4876 p h) (sat_cons (step435 p h) (sat_nil p)))))
def c5104 : List Lit := [(959, true)]
theorem step5104 (p : Nat → Bool) (h : Constraints p) : clause p c5104 = true :=
  Snake9.LocalRup.prove_clause [c5101, c4877, c2193] c5104 (by decide) p (sat_cons (step5101 p h) (sat_cons (step4877 p h) (sat_cons (step2193 p h) (sat_nil p))))
def c5105 : List Lit := [(974, true)]
theorem step5105 (p : Nat → Bool) (h : Constraints p) : clause p c5105 = true :=
  Snake9.LocalRup.prove_clause [c5102, c1206] c5105 (by decide) p (sat_cons (step5102 p h) (sat_cons (step1206 p h) (sat_nil p)))
def c5106 : List Lit := [(1020, false)]
theorem step5106 (p : Nat → Bool) (h : Constraints p) : clause p c5106 = true :=
  Snake9.LocalRup.prove_clause [c5104, c5097, c1279] c5106 (by decide) p (sat_cons (step5104 p h) (sat_cons (step5097 p h) (sat_cons (step1279 p h) (sat_nil p))))
def c5107 : List Lit := [(985, true)]
theorem step5107 (p : Nat → Bool) (h : Constraints p) : clause p c5107 = true :=
  Snake9.LocalRup.prove_clause [c5105, c1217] c5107 (by decide) p (sat_cons (step5105 p h) (sat_cons (step1217 p h) (sat_nil p)))
def c5108 : List Lit := []
theorem step5108 (p : Nat → Bool) (h : Constraints p) : clause p c5108 = true :=
  Snake9.LocalRup.prove_clause [c5107, c5106, c5103, c5010] c5108 (by decide) p (sat_cons (step5107 p h) (sat_cons (step5106 p h) (sat_cons (step5103 p h) (sat_cons (step5010 p h) (sat_nil p)))))
end B112E257
