import B112E146Part0010
namespace B112E146
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1521 : List Lit := [(1365, true), (1451, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c1506, c1466, c1484, c1422, c1518, c651, c1159, c1152, c902, c1520, c1308, c65, c465, c467, c81, c75, c477, c479, c88, c496, c492, c470, c482, c1233, c472] c1521 (by decide) p (sat_cons (step1506 p h) (sat_cons (step1466 p h) (sat_cons (step1484 p h) (sat_cons (step1422 p h) (sat_cons (step1518 p h) (sat_cons (step651 p h) (sat_cons (step1159 p h) (sat_cons (step1152 p h) (sat_cons (step902 p h) (sat_cons (step1520 p h) (sat_cons (step1308 p h) (sat_cons (step65 p h) (sat_cons (step465 p h) (sat_cons (step467 p h) (sat_cons (step81 p h) (sat_cons (step75 p h) (sat_cons (step477 p h) (sat_cons (step479 p h) (sat_cons (step88 p h) (sat_cons (step496 p h) (sat_cons (step492 p h) (sat_cons (step470 p h) (sat_cons (step482 p h) (sat_cons (step1233 p h) (sat_cons (step472 p h) (sat_nil p))))))))))))))))))))))))))
def c1522 : List Lit := [(1395, false), (1451, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c1422, c1506, c1466, c1484, c651, c1159, c1152, c902, c1519, c1520, c1308, c88, c75, c81, c65, c680, c477, c465, c479, c467, c491, c1202, c1521, c1229, c541, c507, c1135] c1522 (by decide) p (sat_cons (step1422 p h) (sat_cons (step1506 p h) (sat_cons (step1466 p h) (sat_cons (step1484 p h) (sat_cons (step651 p h) (sat_cons (step1159 p h) (sat_cons (step1152 p h) (sat_cons (step902 p h) (sat_cons (step1519 p h) (sat_cons (step1520 p h) (sat_cons (step1308 p h) (sat_cons (step88 p h) (sat_cons (step75 p h) (sat_cons (step81 p h) (sat_cons (step65 p h) (sat_cons (step680 p h) (sat_cons (step477 p h) (sat_cons (step465 p h) (sat_cons (step479 p h) (sat_cons (step467 p h) (sat_cons (step491 p h) (sat_cons (step1202 p h) (sat_cons (step1521 p h) (sat_cons (step1229 p h) (sat_cons (step541 p h) (sat_cons (step507 p h) (sat_cons (step1135 p h) (sat_nil p))))))))))))))))))))))))))))
def c1523 : List Lit := [(1451, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c1518, c1522] c1523 (by decide) p (sat_cons (step1518 p h) (sat_cons (step1522 p h) (sat_nil p)))
def c1524 : List Lit := [(1419, false)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c1523, c1500, c628] c1524 (by decide) p (sat_cons (step1523 p h) (sat_cons (step1500 p h) (sat_cons (step628 p h) (sat_nil p))))
def c1525 : List Lit := [(1440, false)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c1523, c1486, c624] c1525 (by decide) p (sat_cons (step1523 p h) (sat_cons (step1486 p h) (sat_cons (step624 p h) (sat_nil p))))
def c1526 : List Lit := [(33, false)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1523, c1366, c1506, c1466, c1261] c1526 (by decide) p (sat_cons (step1523 p h) (sat_cons (step1366 p h) (sat_cons (step1506 p h) (sat_cons (step1466 p h) (sat_cons (step1261 p h) (sat_nil p))))))
def c1527 : List Lit := [(1414, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c1524, c1469, c571] c1527 (by decide) p (sat_cons (step1524 p h) (sat_cons (step1469 p h) (sat_cons (step571 p h) (sat_nil p))))
def c1528 : List Lit := [(1428, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c1525, c614] c1528 (by decide) p (sat_cons (step1525 p h) (sat_cons (step614 p h) (sat_nil p)))
def c1529 : List Lit := [(1435, false)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1498, c611] c1529 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1498 p h) (sat_cons (step611 p h) (sat_nil p))))
def c1530 : List Lit := [(1409, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c1526, c1366, c553] c1530 (by decide) p (sat_cons (step1526 p h) (sat_cons (step1366 p h) (sat_cons (step553 p h) (sat_nil p))))
def c1531 : List Lit := [(1410, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1530, c563] c1531 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1530 p h) (sat_cons (step563 p h) (sat_nil p))))
def c1532 : List Lit := [(1425, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c1528, c1497, c591] c1532 (by decide) p (sat_cons (step1528 p h) (sat_cons (step1497 p h) (sat_cons (step591 p h) (sat_nil p))))
def c1533 : List Lit := [(1433, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1529, c601] c1533 (by decide) p (sat_cons (step1529 p h) (sat_cons (step601 p h) (sat_nil p)))
def c1534 : List Lit := [(1431, false)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1529, c603] c1534 (by decide) p (sat_cons (step1529 p h) (sat_cons (step603 p h) (sat_nil p)))
def c1535 : List Lit := [(39, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1531, c554] c1535 (by decide) p (sat_cons (step1531 p h) (sat_cons (step554 p h) (sat_nil p)))
def c1536 : List Lit := [(37, true)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1531, c555] c1536 (by decide) p (sat_cons (step1531 p h) (sat_cons (step555 p h) (sat_nil p)))
def c1537 : List Lit := [(46, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1532, c585] c1537 (by decide) p (sat_cons (step1532 p h) (sat_cons (step585 p h) (sat_nil p)))
def c1538 : List Lit := [(43, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1532, c586] c1538 (by decide) p (sat_cons (step1532 p h) (sat_cons (step586 p h) (sat_nil p)))
def c1539 : List Lit := [(48, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1534, c596] c1539 (by decide) p (sat_cons (step1534 p h) (sat_cons (step596 p h) (sat_nil p)))
def c1540 : List Lit := [(59, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1535, c1533, c1003] c1540 (by decide) p (sat_cons (step1535 p h) (sat_cons (step1533 p h) (sat_cons (step1003 p h) (sat_nil p))))
def c1541 : List Lit := [(44, true)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1082] c1541 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c1542 : List Lit := [(15, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1539, c1537, c1490] c1542 (by decide) p (sat_cons (step1539 p h) (sat_cons (step1537 p h) (sat_cons (step1490 p h) (sat_nil p))))
def c1543 : List Lit := [(56, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1539, c1537, c976] c1543 (by decide) p (sat_cons (step1539 p h) (sat_cons (step1537 p h) (sat_cons (step976 p h) (sat_nil p))))
def c1544 : List Lit := [(1481, true)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1540, c660] c1544 (by decide) p (sat_cons (step1540 p h) (sat_cons (step660 p h) (sat_nil p)))
def c1545 : List Lit := [(1484, true)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1544, c1543, c665] c1545 (by decide) p (sat_cons (step1544 p h) (sat_cons (step1543 p h) (sat_cons (step665 p h) (sat_nil p))))
def c1546 : List Lit := [(1495, true)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1545, c677] c1546 (by decide) p (sat_cons (step1545 p h) (sat_cons (step677 p h) (sat_nil p)))
def c1547 : List Lit := [(34, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1506, c1541, c1536, c1483, c1466, c146, c186, c545, c1069] c1547 (by decide) p (sat_cons (step1506 p h) (sat_cons (step1541 p h) (sat_cons (step1536 p h) (sat_cons (step1483 p h) (sat_cons (step1466 p h) (sat_cons (step146 p h) (sat_cons (step186 p h) (sat_cons (step545 p h) (sat_cons (step1069 p h) (sat_nil p))))))))))
def c1548 : List Lit := [(14, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1547, c1537, c1506, c1284] c1548 (by decide) p (sat_cons (step1547 p h) (sat_cons (step1537 p h) (sat_cons (step1506 p h) (sat_cons (step1284 p h) (sat_nil p)))))
def c1549 : List Lit := [(1395, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1548, c1506, c1542, c1466, c1282] c1549 (by decide) p (sat_cons (step1548 p h) (sat_cons (step1506 p h) (sat_cons (step1542 p h) (sat_cons (step1466 p h) (sat_cons (step1282 p h) (sat_nil p))))))
def c1550 : List Lit := [(1472, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1502, c650] c1550 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1502 p h) (sat_cons (step650 p h) (sat_nil p))))
def c1551 : List Lit := [(1606, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1158] c1551 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1158 p h) (sat_nil p)))
def c1552 : List Lit := [(1528, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1551, c1154] c1552 (by decide) p (sat_cons (step1551 p h) (sat_cons (step1154 p h) (sat_nil p)))
def c1553 : List Lit := [(1496, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1146] c1553 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1146 p h) (sat_nil p)))
def c1554 : List Lit := [(1518, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1546, c721] c1554 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1546 p h) (sat_cons (step721 p h) (sat_nil p))))
def c1555 : List Lit := [(1485, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1553, c679] c1555 (by decide) p (sat_cons (step1553 p h) (sat_cons (step679 p h) (sat_nil p)))
def c1556 : List Lit := [(1490, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1553, c1545, c678] c1556 (by decide) p (sat_cons (step1553 p h) (sat_cons (step1545 p h) (sat_cons (step678 p h) (sat_nil p))))
def c1557 : List Lit := [(1509, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1554, c900] c1557 (by decide) p (sat_cons (step1554 p h) (sat_cons (step900 p h) (sat_nil p)))
def c1558 : List Lit := [(1501, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1228] c1558 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1228 p h) (sat_nil p)))
def c1559 : List Lit := [(1482, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1555, c1543, c666] c1559 (by decide) p (sat_cons (step1555 p h) (sat_cons (step1543 p h) (sat_cons (step666 p h) (sat_nil p))))
def c1560 : List Lit := [(1488, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1556, c670] c1560 (by decide) p (sat_cons (step1556 p h) (sat_cons (step670 p h) (sat_nil p)))
def c1561 : List Lit := [(81, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1557, c693] c1561 (by decide) p (sat_cons (step1557 p h) (sat_cons (step693 p h) (sat_nil p)))
def c1562 : List Lit := [(72, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1558, c681] c1562 (by decide) p (sat_cons (step1558 p h) (sat_cons (step681 p h) (sat_nil p)))
def c1563 : List Lit := [(60, true)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1559, c1540, c661] c1563 (by decide) p (sat_cons (step1559 p h) (sat_cons (step1540 p h) (sat_cons (step661 p h) (sat_nil p))))
def c1564 : List Lit := [(67, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1560, c669] c1564 (by decide) p (sat_cons (step1560 p h) (sat_cons (step669 p h) (sat_nil p)))
def c1565 : List Lit := [(24, true)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1562, c1564, c906] c1565 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1562 p h) (sat_cons (step1564 p h) (sat_cons (step906 p h) (sat_nil p)))))
def c1566 : List Lit := []
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1565, c1484, c1563, c113] c1566 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1565 p h) (sat_cons (step1484 p h) (sat_cons (step1563 p h) (sat_cons (step113 p h) (sat_nil p))))))
end B112E146
