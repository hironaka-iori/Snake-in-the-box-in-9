import B112E186Part0001
namespace B112E186
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1528 : List Lit := [(1598, true), (53, false), (51, true), (62, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1509, c963, c948, c184] c1528 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1509 p h) (sat_cons (step963 p h) (sat_cons (step948 p h) (sat_cons (step184 p h) (sat_nil p))))))
def c1529 : List Lit := [(1575, true), (1558, false), (32, false), (15, false)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c1429, c1452, c915, c943, c940, c918, c931, c1451, c921, c922, c929, c923, c924, c1428] c1529 (by decide) p (sat_cons (step1429 p h) (sat_cons (step1452 p h) (sat_cons (step915 p h) (sat_cons (step943 p h) (sat_cons (step940 p h) (sat_cons (step918 p h) (sat_cons (step931 p h) (sat_cons (step1451 p h) (sat_cons (step921 p h) (sat_cons (step922 p h) (sat_cons (step929 p h) (sat_cons (step923 p h) (sat_cons (step924 p h) (sat_cons (step1428 p h) (sat_nil p)))))))))))))))
def c1530 : List Lit := [(1535, true), (19, true), (1525, false), (16, false)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c851, c854, c870, c879, c881, c871, c855, c1502, c853] c1530 (by decide) p (sat_cons (step851 p h) (sat_cons (step854 p h) (sat_cons (step870 p h) (sat_cons (step879 p h) (sat_cons (step881 p h) (sat_cons (step871 p h) (sat_cons (step855 p h) (sat_cons (step1502 p h) (sat_cons (step853 p h) (sat_nil p))))))))))
def c1531 : List Lit := [(99, false), (1716, true), (26, false), (60, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c471, c470, c1198] c1531 (by decide) p (sat_cons (step471 p h) (sat_cons (step470 p h) (sat_cons (step1198 p h) (sat_nil p))))
def c1532 : List Lit := [(109, true), (1736, true), (35, true), (88, true)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c703, c1239, c1229, c1230, c1237, c605, c1231, c1232, c600] c1532 (by decide) p (sat_cons (step703 p h) (sat_cons (step1239 p h) (sat_cons (step1229 p h) (sat_cons (step1230 p h) (sat_cons (step1237 p h) (sat_cons (step605 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step600 p h) (sat_nil p))))))))))
def c1533 : List Lit := [(1735, true), (35, true), (88, true)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c703, c1234, c1236, c1231, c1232, c1228, c600, c605] c1533 (by decide) p (sat_cons (step703 p h) (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step1228 p h) (sat_cons (step600 p h) (sat_cons (step605 p h) (sat_nil p)))))))))
def c1534 : List Lit := [(1743, true)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c707, c1248, c1250, c1245, c1246, c1242, c1243, c654, c632, c629] c1534 (by decide) p (sat_cons (step707 p h) (sat_cons (step1248 p h) (sat_cons (step1250 p h) (sat_cons (step1245 p h) (sat_cons (step1246 p h) (sat_cons (step1242 p h) (sat_cons (step1243 p h) (sat_cons (step654 p h) (sat_cons (step632 p h) (sat_cons (step629 p h) (sat_nil p)))))))))))
def c1535 : List Lit := [(1733, true), (117, false), (109, false), (84, false)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c702, c1231, c1232, c563, c624, c547, c569] c1535 (by decide) p (sat_cons (step702 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step563 p h) (sat_cons (step624 p h) (sat_cons (step547 p h) (sat_cons (step569 p h) (sat_nil p))))))))
def c1536 : List Lit := [(1749, true), (110, false), (35, true), (88, true), (1675, true)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1534, c703, c1533, c1113, c1112, c1262, c1265, c1253, c1532, c579, c1242, c1244, c1251, c1535, c1237, c1228, c604, c1479] c1536 (by decide) p (sat_cons (step1534 p h) (sat_cons (step703 p h) (sat_cons (step1533 p h) (sat_cons (step1113 p h) (sat_cons (step1112 p h) (sat_cons (step1262 p h) (sat_cons (step1265 p h) (sat_cons (step1253 p h) (sat_cons (step1532 p h) (sat_cons (step579 p h) (sat_cons (step1242 p h) (sat_cons (step1244 p h) (sat_cons (step1251 p h) (sat_cons (step1535 p h) (sat_cons (step1237 p h) (sat_cons (step1228 p h) (sat_cons (step604 p h) (sat_cons (step1479 p h) (sat_nil p)))))))))))))))))))
def c1537 : List Lit := [(1718, false), (1726, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1440, c1213, c1203, c1217, c1206, c1487] c1537 (by decide) p (sat_cons (step1440 p h) (sat_cons (step1213 p h) (sat_cons (step1203 p h) (sat_cons (step1217 p h) (sat_cons (step1206 p h) (sat_cons (step1487 p h) (sat_nil p)))))))
def c1538 : List Lit := [(1712, true), (94, true), (85, true), (84, false)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c697, c1183, c1193, c1191, c1184, c1186, c463, c455] c1538 (by decide) p (sat_cons (step697 p h) (sat_cons (step1183 p h) (sat_cons (step1193 p h) (sat_cons (step1191 p h) (sat_cons (step1184 p h) (sat_cons (step1186 p h) (sat_cons (step463 p h) (sat_cons (step455 p h) (sat_nil p)))))))))
def c1539 : List Lit := [(1709, true), (123, false), (101, false), (102, false)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c700, c1185, c1186, c484, c519, c524, c512] c1539 (by decide) p (sat_cons (step700 p h) (sat_cons (step1185 p h) (sat_cons (step1186 p h) (sat_cons (step484 p h) (sat_cons (step519 p h) (sat_cons (step524 p h) (sat_cons (step512 p h) (sat_nil p))))))))
def c1540 : List Lit := [(68, false), (1, false), (32, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1400, c1] c1540 (by decide) p (sat_cons (step1400 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1541 : List Lit := [(32, true), (68, true), (1, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c655, c2] c1541 (by decide) p (sat_cons (step655 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1542 : List Lit := [(3, false), (4, true)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c656, c4] c1542 (by decide) p (sat_cons (step656 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1543 : List Lit := [(3, false), (2, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c656, c5] c1543 (by decide) p (sat_cons (step656 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1544 : List Lit := [(8, false), (11, true)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c658, c17] c1544 (by decide) p (sat_cons (step658 p h) (sat_cons (step17 p h) (sat_nil p)))
def c1545 : List Lit := [(11, true), (9, true), (10, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c659, c20] c1545 (by decide) p (sat_cons (step659 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1546 : List Lit := [(4, true), (9, true), (10, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c659, c21] c1546 (by decide) p (sat_cons (step659 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1547 : List Lit := [(18, true), (13, false), (85, true)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c660, c25] c1547 (by decide) p (sat_cons (step660 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1548 : List Lit := [(12, true), (13, false), (85, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c660, c26] c1548 (by decide) p (sat_cons (step660 p h) (sat_cons (step26 p h) (sat_nil p)))
def c1549 : List Lit := [(12, true), (18, true), (13, false)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c660, c27] c1549 (by decide) p (sat_cons (step660 p h) (sat_cons (step27 p h) (sat_nil p)))
def c1550 : List Lit := [(23, true), (32, true), (86, true), (15, false)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c661, c33] c1550 (by decide) p (sat_cons (step661 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1551 : List Lit := [(14, true), (32, true), (15, false), (86, true)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c661, c34] c1551 (by decide) p (sat_cons (step661 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1552 : List Lit := [(23, true), (14, true), (86, true), (15, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c661, c35] c1552 (by decide) p (sat_cons (step661 p h) (sat_cons (step35 p h) (sat_nil p)))
def c1553 : List Lit := [(14, true), (32, true), (23, true), (15, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c661, c36] c1553 (by decide) p (sat_cons (step661 p h) (sat_cons (step36 p h) (sat_nil p)))
def c1554 : List Lit := [(35, true), (27, true), (88, true), (16, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c662, c38] c1554 (by decide) p (sat_cons (step662 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1555 : List Lit := [(18, true), (35, true), (88, true), (16, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c662, c39] c1555 (by decide) p (sat_cons (step662 p h) (sat_cons (step39 p h) (sat_nil p)))
def c1556 : List Lit := [(27, true), (18, true), (16, false), (88, true)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c662, c40] c1556 (by decide) p (sat_cons (step662 p h) (sat_cons (step40 p h) (sat_nil p)))
def c1557 : List Lit := [(27, true), (18, true), (35, true), (16, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c662, c41] c1557 (by decide) p (sat_cons (step662 p h) (sat_cons (step41 p h) (sat_nil p)))
def c1558 : List Lit := [(20, true), (12, true), (89, true), (17, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c663, c43] c1558 (by decide) p (sat_cons (step663 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1559 : List Lit := [(20, true), (90, true), (19, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c664, c54] c1559 (by decide) p (sat_cons (step664 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1560 : List Lit := [(90, true), (14, true), (19, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c664, c55] c1560 (by decide) p (sat_cons (step664 p h) (sat_cons (step55 p h) (sat_nil p)))
def c1561 : List Lit := [(20, true), (14, true), (19, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c664, c56] c1561 (by decide) p (sat_cons (step664 p h) (sat_cons (step56 p h) (sat_nil p)))
def c1562 : List Lit := [(23, true), (24, true), (22, false), (14, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c665, c67] c1562 (by decide) p (sat_cons (step665 p h) (sat_cons (step67 p h) (sat_nil p)))
def c1563 : List Lit := [(21, true), (14, true), (23, true), (22, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c665, c68] c1563 (by decide) p (sat_cons (step665 p h) (sat_cons (step68 p h) (sat_nil p)))
def c1564 : List Lit := [(24, true), (25, false), (23, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c666, c75] c1564 (by decide) p (sat_cons (step666 p h) (sat_cons (step75 p h) (sat_nil p)))
def c1565 : List Lit := [(27, true), (99, true), (26, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c667, c76] c1565 (by decide) p (sat_cons (step667 p h) (sat_cons (step76 p h) (sat_nil p)))
def c1566 : List Lit := [(21, true), (99, true), (26, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c667, c77] c1566 (by decide) p (sat_cons (step667 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1567 : List Lit := [(21, true), (27, true), (26, false)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c667, c78] c1567 (by decide) p (sat_cons (step667 p h) (sat_cons (step78 p h) (sat_nil p)))
def c1568 : List Lit := [(29, true), (18, true), (28, false)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c668, c85] c1568 (by decide) p (sat_cons (step668 p h) (sat_cons (step85 p h) (sat_nil p)))
def c1569 : List Lit := [(18, true), (28, false), (27, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c668, c86] c1569 (by decide) p (sat_cons (step668 p h) (sat_cons (step86 p h) (sat_nil p)))
def c1570 : List Lit := [(30, true), (32, true), (31, false), (35, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c669, c92] c1570 (by decide) p (sat_cons (step669 p h) (sat_cons (step92 p h) (sat_nil p)))
def c1571 : List Lit := [(110, true), (38, true), (33, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c670, c104] c1571 (by decide) p (sat_cons (step670 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1572 : List Lit := [(32, true), (110, true), (33, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c670, c105] c1572 (by decide) p (sat_cons (step670 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1573 : List Lit := [(32, true), (38, true), (33, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c670, c106] c1573 (by decide) p (sat_cons (step670 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1574 : List Lit := [(30, true), (34, false), (111, true), (35, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c671, c108] c1574 (by decide) p (sat_cons (step671 p h) (sat_cons (step108 p h) (sat_nil p)))
def c1575 : List Lit := [(2, true), (34, false), (35, true), (111, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c671, c109] c1575 (by decide) p (sat_cons (step671 p h) (sat_cons (step109 p h) (sat_nil p)))
def c1576 : List Lit := [(2, true), (30, true), (35, true), (34, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c671, c110] c1576 (by decide) p (sat_cons (step671 p h) (sat_cons (step110 p h) (sat_nil p)))
def c1577 : List Lit := [(38, true), (18, true), (35, true), (36, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c672, c129] c1577 (by decide) p (sat_cons (step672 p h) (sat_cons (step129 p h) (sat_nil p)))
def c1578 : List Lit := [(38, true), (4, true), (36, false), (35, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c672, c130] c1578 (by decide) p (sat_cons (step672 p h) (sat_cons (step130 p h) (sat_nil p)))
def c1579 : List Lit := [(4, true), (38, true), (36, false), (18, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c672, c131] c1579 (by decide) p (sat_cons (step672 p h) (sat_cons (step131 p h) (sat_nil p)))
def c1580 : List Lit := [(4, true), (18, true), (35, true), (36, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c672, c132] c1580 (by decide) p (sat_cons (step672 p h) (sat_cons (step132 p h) (sat_nil p)))
def c1581 : List Lit := [(37, false), (45, true), (32, true), (35, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c673, c136] c1581 (by decide) p (sat_cons (step673 p h) (sat_cons (step136 p h) (sat_nil p)))
def c1582 : List Lit := [(37, false), (32, true), (38, true), (35, true)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c673, c137] c1582 (by decide) p (sat_cons (step673 p h) (sat_cons (step137 p h) (sat_nil p)))
def c1583 : List Lit := [(41, false), (40, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c674, c145] c1583 (by decide) p (sat_cons (step674 p h) (sat_cons (step145 p h) (sat_nil p)))
def c1584 : List Lit := [(41, false), (39, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c674, c146] c1584 (by decide) p (sat_cons (step674 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1585 : List Lit := [(46, true), (43, false), (121, true)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c675, c148] c1585 (by decide) p (sat_cons (step675 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1586 : List Lit := [(40, true), (43, false), (121, true)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c675, c149] c1586 (by decide) p (sat_cons (step675 p h) (sat_cons (step149 p h) (sat_nil p)))
def c1587 : List Lit := [(44, false), (46, true)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c676, c150] c1587 (by decide) p (sat_cons (step676 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1588 : List Lit := [(44, false), (45, true)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c676, c151] c1588 (by decide) p (sat_cons (step676 p h) (sat_cons (step151 p h) (sat_nil p)))
def c1589 : List Lit := [(53, true), (48, false), (67, true), (85, true)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c677, c165] c1589 (by decide) p (sat_cons (step677 p h) (sat_cons (step165 p h) (sat_nil p)))
def c1590 : List Lit := [(48, false), (47, true), (67, true), (85, true)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c677, c166] c1590 (by decide) p (sat_cons (step677 p h) (sat_cons (step166 p h) (sat_nil p)))
def c1591 : List Lit := [(47, true), (53, true), (48, false), (85, true)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c677, c167] c1591 (by decide) p (sat_cons (step677 p h) (sat_cons (step167 p h) (sat_nil p)))
end B112E186
