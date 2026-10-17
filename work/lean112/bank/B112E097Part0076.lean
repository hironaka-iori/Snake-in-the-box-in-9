import B112E097Part0075
namespace B112E097
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c6459 : List Lit := [(113, false)]
theorem step6459 (p : Nat → Bool) (h : Constraints p) : clause p c6459 = true :=
  Snake9.LocalRup.prove_clause [c6457, c6440, c6427, c565] c6459 (by decide) p (sat_cons (step6457 p h) (sat_cons (step6440 p h) (sat_cons (step6427 p h) (sat_cons (step565 p h) (sat_nil p)))))
def c6460 : List Lit := [(109, false)]
theorem step6460 (p : Nat → Bool) (h : Constraints p) : clause p c6460 = true :=
  Snake9.LocalRup.prove_clause [c6457, c6440, c6427, c563] c6460 (by decide) p (sat_cons (step6457 p h) (sat_cons (step6440 p h) (sat_cons (step6427 p h) (sat_cons (step563 p h) (sat_nil p)))))
def c6461 : List Lit := [(111, false)]
theorem step6461 (p : Nat → Bool) (h : Constraints p) : clause p c6461 = true :=
  Snake9.LocalRup.prove_clause [c6457, c6440, c6427, c564] c6461 (by decide) p (sat_cons (step6457 p h) (sat_cons (step6440 p h) (sat_cons (step6427 p h) (sat_cons (step564 p h) (sat_nil p)))))
def c6462 : List Lit := [(1011, false)]
theorem step6462 (p : Nat → Bool) (h : Constraints p) : clause p c6462 = true :=
  Snake9.LocalRup.prove_clause [c6458, c6417, c1240] c6462 (by decide) p (sat_cons (step6458 p h) (sat_cons (step6417 p h) (sat_cons (step1240 p h) (sat_nil p))))
def c6463 : List Lit := [(1056, true)]
theorem step6463 (p : Nat → Bool) (h : Constraints p) : clause p c6463 = true :=
  Snake9.LocalRup.prove_clause [c6460, c6461, c1309] c6463 (by decide) p (sat_cons (step6460 p h) (sat_cons (step6461 p h) (sat_cons (step1309 p h) (sat_nil p))))
def c6464 : List Lit := [(1007, false)]
theorem step6464 (p : Nat → Bool) (h : Constraints p) : clause p c6464 = true :=
  Snake9.LocalRup.prove_clause [c6462, c1199] c6464 (by decide) p (sat_cons (step6462 p h) (sat_cons (step1199 p h) (sat_nil p)))
def c6465 : List Lit := []
theorem step6465 (p : Nat → Bool) (h : Constraints p) : clause p c6465 = true :=
  Snake9.LocalRup.prove_clause [c6463, c6464, c6452, c6435, c6416, c6459, c5520] c6465 (by decide) p (sat_cons (step6463 p h) (sat_cons (step6464 p h) (sat_cons (step6452 p h) (sat_cons (step6435 p h) (sat_cons (step6416 p h) (sat_cons (step6459 p h) (sat_cons (step5520 p h) (sat_nil p))))))))
end B112E097
