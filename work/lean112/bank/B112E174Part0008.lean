import B112E174Part0007
namespace B112E174
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1533 : List Lit := [(708, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1532, c1527, c1525, c1447, c1432] c1533 (by decide) p (sat_cons (step1532 p h) (sat_cons (step1527 p h) (sat_cons (step1525 p h) (sat_cons (step1447 p h) (sat_cons (step1432 p h) (sat_nil p))))))
def c1534 : List Lit := [(705, false)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1533, c518] c1534 (by decide) p (sat_cons (step1533 p h) (sat_cons (step518 p h) (sat_nil p)))
def c1535 : List Lit := [(703, false)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1534, c513] c1535 (by decide) p (sat_cons (step1534 p h) (sat_cons (step513 p h) (sat_nil p)))
def c1536 : List Lit := [(16, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1535, c1508, c1522, c1527, c1525, c1524, c1440] c1536 (by decide) p (sat_cons (step1535 p h) (sat_cons (step1508 p h) (sat_cons (step1522 p h) (sat_cons (step1527 p h) (sat_cons (step1525 p h) (sat_cons (step1524 p h) (sat_cons (step1440 p h) (sat_nil p))))))))
def c1537 : List Lit := [(13, false)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1536, c1325] c1537 (by decide) p (sat_cons (step1536 p h) (sat_cons (step1325 p h) (sat_nil p)))
def c1538 : List Lit := [(1226, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1537, c788] c1538 (by decide) p (sat_cons (step1537 p h) (sat_cons (step788 p h) (sat_nil p)))
def c1539 : List Lit := [(15, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1537, c1516, c789] c1539 (by decide) p (sat_cons (step1537 p h) (sat_cons (step1516 p h) (sat_cons (step789 p h) (sat_nil p))))
def c1540 : List Lit := [(1229, true)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1059] c1540 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1059 p h) (sat_nil p)))
def c1541 : List Lit := [(8, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1539, c1529, c1526, c29] c1541 (by decide) p (sat_cons (step1539 p h) (sat_cons (step1529 p h) (sat_cons (step1526 p h) (sat_cons (step29 p h) (sat_nil p)))))
def c1542 : List Lit := [(1240, true)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1540, c808] c1542 (by decide) p (sat_cons (step1540 p h) (sat_cons (step808 p h) (sat_nil p)))
def c1543 : List Lit := [(1216, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1541, c1051] c1543 (by decide) p (sat_cons (step1541 p h) (sat_cons (step1051 p h) (sat_nil p)))
def c1544 : List Lit := [(1222, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1542, c1510, c819] c1544 (by decide) p (sat_cons (step1542 p h) (sat_cons (step1510 p h) (sat_cons (step819 p h) (sat_nil p))))
def c1545 : List Lit := [(1219, true)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1543, c1525, c776] c1545 (by decide) p (sat_cons (step1543 p h) (sat_cons (step1525 p h) (sat_cons (step776 p h) (sat_nil p))))
def c1546 : List Lit := []
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1545, c1544, c779] c1546 (by decide) p (sat_cons (step1545 p h) (sat_cons (step1544 p h) (sat_cons (step779 p h) (sat_nil p))))
end B112E174
