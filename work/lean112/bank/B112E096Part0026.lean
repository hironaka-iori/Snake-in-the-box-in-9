import B112E096Part0025
namespace B112E096
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2700 : List Lit := [(86, false)]
theorem step2700 (p : Nat → Bool) (h : Constraints p) : clause p c2700 = true :=
  Snake9.LocalRup.prove_clause [c2698, c2695, c2688, c213] c2700 (by decide) p (sat_cons (step2698 p h) (sat_cons (step2695 p h) (sat_cons (step2688 p h) (sat_cons (step213 p h) (sat_nil p)))))
def c2701 : List Lit := [(1581, false)]
theorem step2701 (p : Nat → Bool) (h : Constraints p) : clause p c2701 = true :=
  Snake9.LocalRup.prove_clause [c2699, c2696, c802] c2701 (by decide) p (sat_cons (step2699 p h) (sat_cons (step2696 p h) (sat_cons (step802 p h) (sat_nil p))))
def c2702 : List Lit := []
theorem step2702 (p : Nat → Bool) (h : Constraints p) : clause p c2702 = true :=
  Snake9.LocalRup.prove_clause [c2700, c2701, c796] c2702 (by decide) p (sat_cons (step2700 p h) (sat_cons (step2701 p h) (sat_cons (step796 p h) (sat_nil p))))
end B112E096
