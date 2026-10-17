import B112E110Part0048
namespace B112E110
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4437 : List Lit := [(7, true)]
theorem step4437 (p : Nat → Bool) (h : Constraints p) : clause p c4437 = true :=
  Snake9.LocalRup.prove_clause [c4433, c4403, c4394] c4437 (by decide) p (sat_cons (step4433 p h) (sat_cons (step4403 p h) (sat_cons (step4394 p h) (sat_nil p))))
def c4438 : List Lit := [(1682, false)]
theorem step4438 (p : Nat → Bool) (h : Constraints p) : clause p c4438 = true :=
  Snake9.LocalRup.prove_clause [c4434, c1710] c4438 (by decide) p (sat_cons (step4434 p h) (sat_cons (step1710 p h) (sat_nil p)))
def c4439 : List Lit := [(1566, true)]
theorem step4439 (p : Nat → Bool) (h : Constraints p) : clause p c4439 = true :=
  Snake9.LocalRup.prove_clause [c4435, c4401, c1372] c4439 (by decide) p (sat_cons (step4435 p h) (sat_cons (step4401 p h) (sat_cons (step1372 p h) (sat_nil p))))
def c4440 : List Lit := [(13, true)]
theorem step4440 (p : Nat → Bool) (h : Constraints p) : clause p c4440 = true :=
  Snake9.LocalRup.prove_clause [c4436, c785] c4440 (by decide) p (sat_cons (step4436 p h) (sat_cons (step785 p h) (sat_nil p)))
def c4441 : List Lit := [(1428, true)]
theorem step4441 (p : Nat → Bool) (h : Constraints p) : clause p c4441 = true :=
  Snake9.LocalRup.prove_clause [c4437, c3282] c4441 (by decide) p (sat_cons (step4437 p h) (sat_cons (step3282 p h) (sat_nil p)))
def c4442 : List Lit := [(1603, true)]
theorem step4442 (p : Nat → Bool) (h : Constraints p) : clause p c4442 = true :=
  Snake9.LocalRup.prove_clause [c4439, c4429, c1087] c4442 (by decide) p (sat_cons (step4439 p h) (sat_cons (step4429 p h) (sat_cons (step1087 p h) (sat_nil p))))
def c4443 : List Lit := [(1433, true)]
theorem step4443 (p : Nat → Bool) (h : Constraints p) : clause p c4443 = true :=
  Snake9.LocalRup.prove_clause [c4440, c1720] c4443 (by decide) p (sat_cons (step4440 p h) (sat_cons (step1720 p h) (sat_nil p)))
def c4444 : List Lit := [(1681, true)]
theorem step4444 (p : Nat → Bool) (h : Constraints p) : clause p c4444 = true :=
  Snake9.LocalRup.prove_clause [c4442, c4247, c1246] c4444 (by decide) p (sat_cons (step4442 p h) (sat_cons (step4247 p h) (sat_cons (step1246 p h) (sat_nil p))))
def c4445 : List Lit := [(1658, false)]
theorem step4445 (p : Nat → Bool) (h : Constraints p) : clause p c4445 = true :=
  Snake9.LocalRup.prove_clause [c4442, c4438, c1247] c4445 (by decide) p (sat_cons (step4442 p h) (sat_cons (step4438 p h) (sat_cons (step1247 p h) (sat_nil p))))
def c4446 : List Lit := [(1437, true)]
theorem step4446 (p : Nat → Bool) (h : Constraints p) : clause p c4446 = true :=
  Snake9.LocalRup.prove_clause [c4443, c811] c4446 (by decide) p (sat_cons (step4443 p h) (sat_cons (step811 p h) (sat_nil p)))
def c4447 : List Lit := [(1537, false)]
theorem step4447 (p : Nat → Bool) (h : Constraints p) : clause p c4447 = true :=
  Snake9.LocalRup.prove_clause [c4444, c1711] c4447 (by decide) p (sat_cons (step4444 p h) (sat_cons (step1711 p h) (sat_nil p)))
def c4448 : List Lit := [(1624, false)]
theorem step4448 (p : Nat → Bool) (h : Constraints p) : clause p c4448 = true :=
  Snake9.LocalRup.prove_clause [c4445, c4246, c1187] c4448 (by decide) p (sat_cons (step4445 p h) (sat_cons (step4246 p h) (sat_cons (step1187 p h) (sat_nil p))))
def c4449 : List Lit := [(1449, true)]
theorem step4449 (p : Nat → Bool) (h : Constraints p) : clause p c4449 = true :=
  Snake9.LocalRup.prove_clause [c4446, c833] c4449 (by decide) p (sat_cons (step4446 p h) (sat_cons (step833 p h) (sat_nil p)))
def c4450 : List Lit := [(96, true)]
theorem step4450 (p : Nat → Bool) (h : Constraints p) : clause p c4450 = true :=
  Snake9.LocalRup.prove_clause [c4448, c2258] c4450 (by decide) p (sat_cons (step4448 p h) (sat_cons (step2258 p h) (sat_nil p)))
def c4451 : List Lit := [(1460, true)]
theorem step4451 (p : Nat → Bool) (h : Constraints p) : clause p c4451 = true :=
  Snake9.LocalRup.prove_clause [c4449, c4441, c855] c4451 (by decide) p (sat_cons (step4449 p h) (sat_cons (step4441 p h) (sat_cons (step855 p h) (sat_nil p))))
def c4452 : List Lit := [(1518, true)]
theorem step4452 (p : Nat → Bool) (h : Constraints p) : clause p c4452 = true :=
  Snake9.LocalRup.prove_clause [c4450, c4437, c4432, c4400, c3475] c4452 (by decide) p (sat_cons (step4450 p h) (sat_cons (step4437 p h) (sat_cons (step4432 p h) (sat_cons (step4400 p h) (sat_cons (step3475 p h) (sat_nil p))))))
def c4453 : List Lit := []
theorem step4453 (p : Nat → Bool) (h : Constraints p) : clause p c4453 = true :=
  Snake9.LocalRup.prove_clause [c4452, c4451, c4447, c966] c4453 (by decide) p (sat_cons (step4452 p h) (sat_cons (step4451 p h) (sat_cons (step4447 p h) (sat_cons (step966 p h) (sat_nil p)))))
end B112E110
