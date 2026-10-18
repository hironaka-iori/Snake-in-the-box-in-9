import B112E246Part0001
namespace B112E246
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c499 : List Lit := [(1418, true)]
theorem step499 (p : Nat → Bool) (h : Constraints p) : clause p c499 = true :=
  Snake9.LocalRup.prove_clause [c498, c485, c304] c499 (by decide) p (sat_cons (step498 p h) (sat_cons (step485 p h) (sat_cons (step304 p h) (sat_nil p))))
def c500 : List Lit := [(1422, true)]
theorem step500 (p : Nat → Bool) (h : Constraints p) : clause p c500 = true :=
  Snake9.LocalRup.prove_clause [c499, c312] c500 (by decide) p (sat_cons (step499 p h) (sat_cons (step312 p h) (sat_nil p)))
def c501 : List Lit := [(1419, false)]
theorem step501 (p : Nat → Bool) (h : Constraints p) : clause p c501 = true :=
  Snake9.LocalRup.prove_clause [c499, c496, c313] c501 (by decide) p (sat_cons (step499 p h) (sat_cons (step496 p h) (sat_cons (step313 p h) (sat_nil p))))
def c502 : List Lit := [(1414, false)]
theorem step502 (p : Nat → Bool) (h : Constraints p) : clause p c502 = true :=
  Snake9.LocalRup.prove_clause [c500, c495, c317] c502 (by decide) p (sat_cons (step500 p h) (sat_cons (step495 p h) (sat_cons (step317 p h) (sat_nil p))))
def c503 : List Lit := [(93, true)]
theorem step503 (p : Nat → Bool) (h : Constraints p) : clause p c503 = true :=
  Snake9.LocalRup.prove_clause [c501, c305] c503 (by decide) p (sat_cons (step501 p h) (sat_cons (step305 p h) (sat_nil p)))
def c504 : List Lit := [(1412, false)]
theorem step504 (p : Nat → Bool) (h : Constraints p) : clause p c504 = true :=
  Snake9.LocalRup.prove_clause [c502, c297] c504 (by decide) p (sat_cons (step502 p h) (sat_cons (step297 p h) (sat_nil p)))
def c505 : List Lit := [(81, true)]
theorem step505 (p : Nat → Bool) (h : Constraints p) : clause p c505 = true :=
  Snake9.LocalRup.prove_clause [c502, c299] c505 (by decide) p (sat_cons (step502 p h) (sat_cons (step299 p h) (sat_nil p)))
def c506 : List Lit := [(78, true)]
theorem step506 (p : Nat → Bool) (h : Constraints p) : clause p c506 = true :=
  Snake9.LocalRup.prove_clause [c503, c137, c91] c506 (by decide) p (sat_cons (step503 p h) (sat_cons (step137 p h) (sat_cons (step91 p h) (sat_nil p))))
def c507 : List Lit := [(82, true)]
theorem step507 (p : Nat → Bool) (h : Constraints p) : clause p c507 = true :=
  Snake9.LocalRup.prove_clause [c504, c295] c507 (by decide) p (sat_cons (step504 p h) (sat_cons (step295 p h) (sat_nil p)))
def c508 : List Lit := []
theorem step508 (p : Nat → Bool) (h : Constraints p) : clause p c508 = true :=
  Snake9.LocalRup.prove_clause [c505, c507, c506, c503, c70] c508 (by decide) p (sat_cons (step505 p h) (sat_cons (step507 p h) (sat_cons (step506 p h) (sat_cons (step503 p h) (sat_cons (step70 p h) (sat_nil p))))))
end B112E246
