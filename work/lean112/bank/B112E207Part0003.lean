import B112E207Part0002
namespace B112E207
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1539 : List Lit := [(1424, true), (57, false)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1388, c928, c1470, c905, c27, c677, c902, c680, c30, c674, c26] c1539 (by decide) p (sat_cons (step1388 p h) (sat_cons (step928 p h) (sat_cons (step1470 p h) (sat_cons (step905 p h) (sat_cons (step27 p h) (sat_cons (step677 p h) (sat_cons (step902 p h) (sat_cons (step680 p h) (sat_cons (step30 p h) (sat_cons (step674 p h) (sat_cons (step26 p h) (sat_nil p))))))))))))
def c1540 : List Lit := [(5, false), (122, true), (57, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c26, c25, c1320] c1540 (by decide) p (sat_cons (step26 p h) (sat_cons (step25 p h) (sat_cons (step1320 p h) (sat_nil p))))
def c1541 : List Lit := [(1445, true), (277, true), (20, true)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c961, c1485, c1484] c1541 (by decide) p (sat_cons (step961 p h) (sat_cons (step1485 p h) (sat_cons (step1484 p h) (sat_nil p))))
def c1542 : List Lit := [(1470, true), (41, false), (39, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1018, c1019, c174] c1542 (by decide) p (sat_cons (step1018 p h) (sat_cons (step1019 p h) (sat_cons (step174 p h) (sat_nil p))))
def c1543 : List Lit := [(1479, false), (1447, true), (1454, false), (1504, false), (1487, false), (57, false), (45, true), (1495, false), (1586, false), (4, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1313, c1295, c1310, c1119, c1095, c1096, c1118, c1467, c1309] c1543 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1313 p h) (sat_cons (step1295 p h) (sat_cons (step1310 p h) (sat_cons (step1119 p h) (sat_cons (step1095 p h) (sat_cons (step1096 p h) (sat_cons (step1118 p h) (sat_cons (step1467 p h) (sat_cons (step1309 p h) (sat_nil p)))))))))))
def c1544 : List Lit := [(1474, true), (156, true)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1024, c1026, c1022, c1542, c169] c1544 (by decide) p (sat_cons (step1024 p h) (sat_cons (step1026 p h) (sat_cons (step1022 p h) (sat_cons (step1542 p h) (sat_cons (step169 p h) (sat_nil p))))))
def c1545 : List Lit := [(4, true), (1, false), (15, true), (45, true)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c625, c5] c1545 (by decide) p (sat_cons (step625 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1546 : List Lit := [(2, true), (15, true), (1, false), (45, true)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c625, c6] c1546 (by decide) p (sat_cons (step625 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1547 : List Lit := [(1, false), (4, true), (2, true), (45, true)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c625, c7] c1547 (by decide) p (sat_cons (step625 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1548 : List Lit := [(1, false), (4, true), (2, true), (15, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c625, c8] c1548 (by decide) p (sat_cons (step625 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1549 : List Lit := [(3, false), (50, true), (18, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c626, c16] c1549 (by decide) p (sat_cons (step626 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1550 : List Lit := [(6, true), (7, false), (57, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c627, c31] c1550 (by decide) p (sat_cons (step627 p h) (sat_cons (step31 p h) (sat_nil p)))
def c1551 : List Lit := [(7, false), (5, true), (57, true)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c627, c32] c1551 (by decide) p (sat_cons (step627 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1552 : List Lit := [(7, false), (6, true), (5, true)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c627, c33] c1552 (by decide) p (sat_cons (step627 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1553 : List Lit := [(8, false), (10, true), (58, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c628, c35] c1553 (by decide) p (sat_cons (step628 p h) (sat_cons (step35 p h) (sat_nil p)))
def c1554 : List Lit := [(8, false), (2, true), (58, true)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c628, c36] c1554 (by decide) p (sat_cons (step628 p h) (sat_cons (step36 p h) (sat_nil p)))
def c1555 : List Lit := [(9, false), (11, true)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c629, c37] c1555 (by decide) p (sat_cons (step629 p h) (sat_cons (step37 p h) (sat_nil p)))
def c1556 : List Lit := [(9, false), (10, true)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c629, c38] c1556 (by decide) p (sat_cons (step629 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1557 : List Lit := [(12, true), (31, true), (13, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c630, c52] c1557 (by decide) p (sat_cons (step630 p h) (sat_cons (step52 p h) (sat_nil p)))
def c1558 : List Lit := [(13, false), (6, true), (31, true)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c630, c53] c1558 (by decide) p (sat_cons (step630 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1559 : List Lit := [(14, false), (12, true)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c631, c54] c1559 (by decide) p (sat_cons (step631 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1560 : List Lit := [(14, false), (11, true)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c631, c55] c1560 (by decide) p (sat_cons (step631 p h) (sat_cons (step55 p h) (sat_nil p)))
def c1561 : List Lit := [(22, true), (16, false), (18, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c632, c63] c1561 (by decide) p (sat_cons (step632 p h) (sat_cons (step63 p h) (sat_nil p)))
def c1562 : List Lit := [(16, false), (18, true), (15, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c632, c64] c1562 (by decide) p (sat_cons (step632 p h) (sat_cons (step64 p h) (sat_nil p)))
def c1563 : List Lit := [(25, true), (23, true), (18, true), (17, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c633, c69] c1563 (by decide) p (sat_cons (step633 p h) (sat_cons (step69 p h) (sat_nil p)))
def c1564 : List Lit := [(25, true), (18, true), (17, false), (15, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c633, c70] c1564 (by decide) p (sat_cons (step633 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1565 : List Lit := [(23, true), (18, true), (17, false), (15, true)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c633, c71] c1565 (by decide) p (sat_cons (step633 p h) (sat_cons (step71 p h) (sat_nil p)))
def c1566 : List Lit := [(19, false), (89, true), (18, true)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c634, c80] c1566 (by decide) p (sat_cons (step634 p h) (sat_cons (step80 p h) (sat_nil p)))
def c1567 : List Lit := [(20, false), (22, true), (4, true), (15, true), (23, true), (90, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c635, c101] c1567 (by decide) p (sat_cons (step635 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1568 : List Lit := [(20, false), (4, true), (15, true), (21, true), (22, true), (23, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c635, c102] c1568 (by decide) p (sat_cons (step635 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1569 : List Lit := [(24, false), (23, true), (18, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c636, c117] c1569 (by decide) p (sat_cons (step636 p h) (sat_cons (step117 p h) (sat_nil p)))
def c1570 : List Lit := [(24, false), (22, true), (18, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c636, c118] c1570 (by decide) p (sat_cons (step636 p h) (sat_cons (step118 p h) (sat_nil p)))
def c1571 : List Lit := [(26, false), (27, true), (31, true)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c637, c124] c1571 (by decide) p (sat_cons (step637 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1572 : List Lit := [(26, false), (25, true), (31, true)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c637, c125] c1572 (by decide) p (sat_cons (step637 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1573 : List Lit := [(30, true), (28, false), (31, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c638, c131] c1573 (by decide) p (sat_cons (step638 p h) (sat_cons (step131 p h) (sat_nil p)))
def c1574 : List Lit := [(28, false), (31, true), (21, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c638, c132] c1574 (by decide) p (sat_cons (step638 p h) (sat_cons (step132 p h) (sat_nil p)))
def c1575 : List Lit := [(32, false), (30, true), (31, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c639, c154] c1575 (by decide) p (sat_cons (step639 p h) (sat_cons (step154 p h) (sat_nil p)))
def c1576 : List Lit := [(34, false), (35, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c640, c156] c1576 (by decide) p (sat_cons (step640 p h) (sat_cons (step156 p h) (sat_nil p)))
def c1577 : List Lit := [(34, false), (21, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c640, c157] c1577 (by decide) p (sat_cons (step640 p h) (sat_cons (step157 p h) (sat_nil p)))
def c1578 : List Lit := [(40, true), (34, true), (35, false)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1349, c158] c1578 (by decide) p (sat_cons (step1349 p h) (sat_cons (step158 p h) (sat_nil p)))
def c1579 : List Lit := [(40, true), (35, false), (152, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1349, c159] c1579 (by decide) p (sat_cons (step1349 p h) (sat_cons (step159 p h) (sat_nil p)))
def c1580 : List Lit := [(34, true), (35, false), (152, true)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1349, c160] c1580 (by decide) p (sat_cons (step1349 p h) (sat_cons (step160 p h) (sat_nil p)))
def c1581 : List Lit := [(39, true), (40, false), (31, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c642, c172] c1581 (by decide) p (sat_cons (step642 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1582 : List Lit := [(40, false), (35, true), (31, true)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c642, c173] c1582 (by decide) p (sat_cons (step642 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1583 : List Lit := [(41, false), (38, true), (39, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c643, c175] c1583 (by decide) p (sat_cons (step643 p h) (sat_cons (step175 p h) (sat_nil p)))
def c1584 : List Lit := [(38, true), (37, true), (41, false)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c643, c176] c1584 (by decide) p (sat_cons (step643 p h) (sat_cons (step176 p h) (sat_nil p)))
def c1585 : List Lit := [(33, true), (43, false), (160, true)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1351, c178] c1585 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1351 p h) (sat_cons (step178 p h) (sat_nil p))))
def c1586 : List Lit := [(47, false), (53, true), (45, true)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c646, c226] c1586 (by decide) p (sat_cons (step646 p h) (sat_cons (step226 p h) (sat_nil p)))
def c1587 : List Lit := [(47, false), (50, true), (45, true)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c646, c227] c1587 (by decide) p (sat_cons (step646 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1588 : List Lit := [(48, false), (60, true), (45, true), (50, true), (55, true)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c647, c238] c1588 (by decide) p (sat_cons (step647 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1589 : List Lit := [(48, false), (60, true), (45, true), (55, true), (49, true)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c647, c239] c1589 (by decide) p (sat_cons (step647 p h) (sat_cons (step239 p h) (sat_nil p)))
def c1590 : List Lit := [(48, false), (49, true), (45, true), (55, true), (50, true)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c647, c240] c1590 (by decide) p (sat_cons (step647 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1591 : List Lit := [(55, true), (63, true), (45, true), (52, false), (53, true), (72, true), (90, true)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c648, c312] c1591 (by decide) p (sat_cons (step648 p h) (sat_cons (step312 p h) (sat_nil p)))
def c1592 : List Lit := [(55, true), (4, true), (72, true), (45, true), (52, false), (63, true), (90, true)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c648, c313] c1592 (by decide) p (sat_cons (step648 p h) (sat_cons (step313 p h) (sat_nil p)))
def c1593 : List Lit := [(90, true), (63, true), (4, true), (45, true), (52, false), (72, true), (53, true)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c648, c314] c1593 (by decide) p (sat_cons (step648 p h) (sat_cons (step314 p h) (sat_nil p)))
def c1594 : List Lit := [(55, true), (90, true), (4, true), (45, true), (52, false), (72, true), (53, true)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c648, c315] c1594 (by decide) p (sat_cons (step648 p h) (sat_cons (step315 p h) (sat_nil p)))
def c1595 : List Lit := [(55, true), (4, true), (63, true), (45, true), (52, false), (53, true), (90, true)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c648, c316] c1595 (by decide) p (sat_cons (step648 p h) (sat_cons (step316 p h) (sat_nil p)))
def c1596 : List Lit := [(55, true), (4, true), (63, true), (45, true), (52, false), (53, true), (72, true)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c648, c317] c1596 (by decide) p (sat_cons (step648 p h) (sat_cons (step317 p h) (sat_nil p)))
def c1597 : List Lit := [(92, true), (74, true), (57, true), (54, false), (66, true), (53, true)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c649, c346] c1597 (by decide) p (sat_cons (step649 p h) (sat_cons (step346 p h) (sat_nil p)))
def c1598 : List Lit := [(5, true), (53, true), (66, true), (54, false), (57, true), (74, true)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c649, c347] c1598 (by decide) p (sat_cons (step649 p h) (sat_cons (step347 p h) (sat_nil p)))
def c1599 : List Lit := [(56, false), (55, true), (53, true), (57, true)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c650, c358] c1599 (by decide) p (sat_cons (step650 p h) (sat_cons (step358 p h) (sat_nil p)))
def c1600 : List Lit := [(56, false), (55, true), (50, true), (57, true)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c650, c359] c1600 (by decide) p (sat_cons (step650 p h) (sat_cons (step359 p h) (sat_nil p)))
def c1601 : List Lit := [(56, false), (50, true), (53, true), (57, true)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c650, c360] c1601 (by decide) p (sat_cons (step650 p h) (sat_cons (step360 p h) (sat_nil p)))
def c1602 : List Lit := [(61, false), (62, true), (58, true), (60, true)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c651, c412] c1602 (by decide) p (sat_cons (step651 p h) (sat_cons (step412 p h) (sat_nil p)))
end B112E207
