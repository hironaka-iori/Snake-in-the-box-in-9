import B112E105Part0274
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c19529 : List Lit := [(1700, false)]
theorem step19529 (p : Nat → Bool) (h : Constraints p) : clause p c19529 = true :=
  Snake9.LocalRup.prove_clause [c19526, c19525, c19527, c19349] c19529 (by decide) p (sat_cons (step19526 p h) (sat_cons (step19525 p h) (sat_cons (step19527 p h) (sat_cons (step19349 p h) (sat_nil p)))))
def c19530 : List Lit := []
theorem step19530 (p : Nat → Bool) (h : Constraints p) : clause p c19530 = true :=
  Snake9.LocalRup.prove_clause [c19528, c19529, c19489, c19075, c19512, c19511, c19440, c10313] c19530 (by decide) p (sat_cons (step19528 p h) (sat_cons (step19529 p h) (sat_cons (step19489 p h) (sat_cons (step19075 p h) (sat_cons (step19512 p h) (sat_cons (step19511 p h) (sat_cons (step19440 p h) (sat_cons (step10313 p h) (sat_nil p)))))))))
end B112E105
