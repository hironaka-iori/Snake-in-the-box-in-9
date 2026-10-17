import B112E120Part0009
namespace B112E120
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1478 : List Lit := [(1608, false)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c1476, c760] c1478 (by decide) p (sat_cons (step1476 p h) (sat_cons (step760 p h) (sat_nil p)))
def c1479 : List Lit := [(88, false)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1446] c1479 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1446 p h) (sat_nil p)))
def c1480 : List Lit := [(115, true)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c1477, c755] c1480 (by decide) p (sat_cons (step1477 p h) (sat_cons (step755 p h) (sat_nil p)))
def c1481 : List Lit := [(113, true)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c1477, c756] c1481 (by decide) p (sat_cons (step1477 p h) (sat_cons (step756 p h) (sat_nil p)))
def c1482 : List Lit := [(1583, true)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1453] c1482 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1453 p h) (sat_nil p)))
def c1483 : List Lit := [(92, false)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c1479, c1478, c1465] c1483 (by decide) p (sat_cons (step1479 p h) (sat_cons (step1478 p h) (sat_cons (step1465 p h) (sat_nil p))))
def c1484 : List Lit := [(1589, false)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c1482, c1462, c733] c1484 (by decide) p (sat_cons (step1482 p h) (sat_cons (step1462 p h) (sat_cons (step733 p h) (sat_nil p))))
def c1485 : List Lit := [(93, false)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c1483, c1462, c1482, c1461] c1485 (by decide) p (sat_cons (step1483 p h) (sat_cons (step1462 p h) (sat_cons (step1482 p h) (sat_cons (step1461 p h) (sat_nil p)))))
def c1486 : List Lit := [(1585, false)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c1484, c717] c1486 (by decide) p (sat_cons (step1484 p h) (sat_cons (step717 p h) (sat_nil p)))
def c1487 : List Lit := [(114, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c1485, c1481, c1147] c1487 (by decide) p (sat_cons (step1485 p h) (sat_cons (step1481 p h) (sat_cons (step1147 p h) (sat_nil p))))
def c1488 : List Lit := [(94, true)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c1486, c710] c1488 (by decide) p (sat_cons (step1486 p h) (sat_cons (step710 p h) (sat_nil p)))
def c1489 : List Lit := []
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c1487, c1488, c1480, c1481, c323] c1489 (by decide) p (sat_cons (step1487 p h) (sat_cons (step1488 p h) (sat_cons (step1480 p h) (sat_cons (step1481 p h) (sat_cons (step323 p h) (sat_nil p))))))
end B112E120
