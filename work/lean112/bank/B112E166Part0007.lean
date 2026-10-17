import B112E166Part0006
namespace B112E166
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1090 : List Lit := [(1438, true)]
theorem step1090 (p : Nat → Bool) (h : Constraints p) : clause p c1090 = true :=
  Snake9.LocalRup.prove_clause [c1089, c505] c1090 (by decide) p (sat_cons (step1089 p h) (sat_cons (step505 p h) (sat_nil p)))
def c1091 : List Lit := [(1436, false)]
theorem step1091 (p : Nat → Bool) (h : Constraints p) : clause p c1091 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1084, c506] c1091 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1084 p h) (sat_cons (step506 p h) (sat_nil p))))
def c1092 : List Lit := [(1443, true)]
theorem step1092 (p : Nat → Bool) (h : Constraints p) : clause p c1092 = true :=
  Snake9.LocalRup.prove_clause [c1090, c1082, c513] c1092 (by decide) p (sat_cons (step1090 p h) (sat_cons (step1082 p h) (sat_cons (step513 p h) (sat_nil p))))
def c1093 : List Lit := [(1452, false)]
theorem step1093 (p : Nat → Bool) (h : Constraints p) : clause p c1093 = true :=
  Snake9.LocalRup.prove_clause [c1091, c1087] c1093 (by decide) p (sat_cons (step1091 p h) (sat_cons (step1087 p h) (sat_nil p)))
def c1094 : List Lit := []
theorem step1094 (p : Nat → Bool) (h : Constraints p) : clause p c1094 = true :=
  Snake9.LocalRup.prove_clause [c1092, c1093, c1064, c527] c1094 (by decide) p (sat_cons (step1092 p h) (sat_cons (step1093 p h) (sat_cons (step1064 p h) (sat_cons (step527 p h) (sat_nil p)))))
end B112E166
