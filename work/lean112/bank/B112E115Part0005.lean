import B112E115Part0004
namespace B112E115
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1559 : List Lit := [(69, true), (66, true), (67, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c557, c427] c1559 (by decide) p (sat_cons (step557 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1560 : List Lit := [(67, false), (69, true), (57, true)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c557, c428] c1560 (by decide) p (sat_cons (step557 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1561 : List Lit := [(66, true), (67, false), (57, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c557, c429] c1561 (by decide) p (sat_cons (step557 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1562 : List Lit := [(69, true), (31, true), (47, true), (68, false), (66, true), (58, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c558, c436] c1562 (by decide) p (sat_cons (step558 p h) (sat_cons (step436 p h) (sat_nil p)))
def c1563 : List Lit := [(72, true), (73, false), (64, true)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c559, c458] c1563 (by decide) p (sat_cons (step559 p h) (sat_cons (step458 p h) (sat_nil p)))
def c1564 : List Lit := [(71, true), (73, false), (64, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c559, c459] c1564 (by decide) p (sat_cons (step559 p h) (sat_cons (step459 p h) (sat_nil p)))
def c1565 : List Lit := [(76, true), (80, true), (74, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c560, c460] c1565 (by decide) p (sat_cons (step560 p h) (sat_cons (step460 p h) (sat_nil p)))
def c1566 : List Lit := [(80, true), (74, false), (2, true)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c560, c461] c1566 (by decide) p (sat_cons (step560 p h) (sat_cons (step461 p h) (sat_nil p)))
def c1567 : List Lit := [(76, true), (74, false), (2, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c560, c462] c1567 (by decide) p (sat_cons (step560 p h) (sat_cons (step462 p h) (sat_nil p)))
def c1568 : List Lit := [(76, true), (85, true), (75, false)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c561, c463] c1568 (by decide) p (sat_cons (step561 p h) (sat_cons (step463 p h) (sat_nil p)))
def c1569 : List Lit := [(77, true), (76, true), (75, false)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c561, c464] c1569 (by decide) p (sat_cons (step561 p h) (sat_cons (step464 p h) (sat_nil p)))
def c1570 : List Lit := [(76, true), (77, true), (78, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c562, c474] c1570 (by decide) p (sat_cons (step562 p h) (sat_cons (step474 p h) (sat_nil p)))
def c1571 : List Lit := [(77, true), (78, false), (5, true)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c562, c475] c1571 (by decide) p (sat_cons (step562 p h) (sat_cons (step475 p h) (sat_nil p)))
def c1572 : List Lit := [(76, true), (78, false), (5, true)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c562, c476] c1572 (by decide) p (sat_cons (step562 p h) (sat_cons (step476 p h) (sat_nil p)))
def c1573 : List Lit := [(82, false), (81, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c563, c482] c1573 (by decide) p (sat_cons (step563 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1574 : List Lit := [(82, false), (77, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c563, c483] c1574 (by decide) p (sat_cons (step563 p h) (sat_cons (step483 p h) (sat_nil p)))
def c1575 : List Lit := [(83, true), (89, true), (84, false)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c564, c486] c1575 (by decide) p (sat_cons (step564 p h) (sat_cons (step486 p h) (sat_nil p)))
def c1576 : List Lit := [(84, false), (89, true), (15, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c564, c487] c1576 (by decide) p (sat_cons (step564 p h) (sat_cons (step487 p h) (sat_nil p)))
def c1577 : List Lit := [(83, true), (84, false), (15, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c564, c488] c1577 (by decide) p (sat_cons (step564 p h) (sat_cons (step488 p h) (sat_nil p)))
def c1578 : List Lit := [(76, true), (86, false), (90, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c565, c491] c1578 (by decide) p (sat_cons (step565 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1579 : List Lit := [(76, true), (86, false), (85, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c565, c492] c1579 (by decide) p (sat_cons (step565 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1580 : List Lit := [(81, true), (88, false), (87, true), (89, true)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c566, c493] c1580 (by decide) p (sat_cons (step566 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1581 : List Lit := [(81, true), (88, false), (83, true), (87, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c566, c494] c1581 (by decide) p (sat_cons (step566 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1582 : List Lit := [(89, true), (90, true), (91, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c567, c504] c1582 (by decide) p (sat_cons (step567 p h) (sat_cons (step504 p h) (sat_nil p)))
def c1583 : List Lit := [(90, true), (91, false), (23, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c567, c505] c1583 (by decide) p (sat_cons (step567 p h) (sat_cons (step505 p h) (sat_nil p)))
def c1584 : List Lit := [(89, true), (91, false), (23, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c567, c506] c1584 (by decide) p (sat_cons (step567 p h) (sat_cons (step506 p h) (sat_nil p)))
def c1585 : List Lit := [(94, true), (92, false), (116, true)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c568, c507] c1585 (by decide) p (sat_cons (step568 p h) (sat_cons (step507 p h) (sat_nil p)))
def c1586 : List Lit := [(108, true), (106, false), (57, true)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c569, c510] c1586 (by decide) p (sat_cons (step569 p h) (sat_cons (step510 p h) (sat_nil p)))
def c1587 : List Lit := [(107, false), (109, true), (113, true)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c570, c512] c1587 (by decide) p (sat_cons (step570 p h) (sat_cons (step512 p h) (sat_nil p)))
def c1588 : List Lit := [(107, false), (113, true), (108, true)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c570, c513] c1588 (by decide) p (sat_cons (step570 p h) (sat_cons (step513 p h) (sat_nil p)))
def c1589 : List Lit := [(107, false), (109, true), (108, true)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c570, c514] c1589 (by decide) p (sat_cons (step570 p h) (sat_cons (step514 p h) (sat_nil p)))
def c1590 : List Lit := [(111, false), (114, true), (228, true)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c1239, c519] c1590 (by decide) p (sat_cons (step1239 p h) (sat_cons (step519 p h) (sat_nil p)))
def c1591 : List Lit := [(111, false), (112, true), (228, true)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c1239, c520] c1591 (by decide) p (sat_cons (step1239 p h) (sat_cons (step520 p h) (sat_nil p)))
def c1592 : List Lit := [(112, false), (111, true), (64, true)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c572, c522] c1592 (by decide) p (sat_cons (step572 p h) (sat_cons (step522 p h) (sat_nil p)))
def c1593 : List Lit := [(109, true), (112, false), (64, true)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c572, c523] c1593 (by decide) p (sat_cons (step572 p h) (sat_cons (step523 p h) (sat_nil p)))
def c1594 : List Lit := [(114, false), (111, true)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c573, c525] c1594 (by decide) p (sat_cons (step573 p h) (sat_cons (step525 p h) (sat_nil p)))
def c1595 : List Lit := [(114, false), (71, true)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c573, c526] c1595 (by decide) p (sat_cons (step573 p h) (sat_cons (step526 p h) (sat_nil p)))
def c1596 : List Lit := [(116, false), (106, true), (233, true)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c1240, c1241, c528] c1596 (by decide) p (sat_cons (step1240 p h) (sat_cons (step1241 p h) (sat_cons (step528 p h) (sat_nil p))))
def c1597 : List Lit := [(245, false), (257, false)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c1254, c585] c1597 (by decide) p (sat_cons (step1254 p h) (sat_cons (step585 p h) (sat_nil p)))
def c1598 : List Lit := [(279, false), (281, false)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c1264, c597] c1598 (by decide) p (sat_cons (step1264 p h) (sat_cons (step597 p h) (sat_nil p)))
def c1599 : List Lit := [(293, false), (299, false)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c1260, c616] c1599 (by decide) p (sat_cons (step1260 p h) (sat_cons (step616 p h) (sat_nil p)))
def c1600 : List Lit := [(305, false), (311, false)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c1259, c624] c1600 (by decide) p (sat_cons (step1259 p h) (sat_cons (step624 p h) (sat_nil p)))
def c1601 : List Lit := [(301, false), (313, false)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c1252, c628] c1601 (by decide) p (sat_cons (step1252 p h) (sat_cons (step628 p h) (sat_nil p)))
def c1602 : List Lit := [(315, false), (343, false)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c1246, c648] c1602 (by decide) p (sat_cons (step1246 p h) (sat_cons (step648 p h) (sat_nil p)))
def c1603 : List Lit := [(289, false), (345, false)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c1243, c653] c1603 (by decide) p (sat_cons (step1243 p h) (sat_cons (step653 p h) (sat_nil p)))
def c1604 : List Lit := [(351, false), (357, false)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c1258, c661] c1604 (by decide) p (sat_cons (step1258 p h) (sat_cons (step661 p h) (sat_nil p)))
def c1605 : List Lit := [(385, false), (399, false)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c1250, c683] c1605 (by decide) p (sat_cons (step1250 p h) (sat_cons (step683 p h) (sat_nil p)))
def c1606 : List Lit := [(206, false), (207, false)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c1265, c690] c1606 (by decide) p (sat_cons (step1265 p h) (sat_cons (step690 p h) (sat_nil p)))
def c1607 : List Lit := [(443, false), (445, false)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c1262, c705] c1607 (by decide) p (sat_cons (step1262 p h) (sat_cons (step705 p h) (sat_nil p)))
def c1608 : List Lit := [(447, false), (453, false)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c1255, c710] c1608 (by decide) p (sat_cons (step1255 p h) (sat_cons (step710 p h) (sat_nil p)))
def c1609 : List Lit := [(441, false), (455, false)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c1248, c715] c1609 (by decide) p (sat_cons (step1248 p h) (sat_cons (step715 p h) (sat_nil p)))
def c1610 : List Lit := [(403, false), (459, false)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c1242, c723] c1610 (by decide) p (sat_cons (step1242 p h) (sat_cons (step723 p h) (sat_nil p)))
def c1611 : List Lit := [(347, false), (461, false)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c728, c726] c1611 (by decide) p (sat_cons (step728 p h) (sat_cons (step726 p h) (sat_nil p)))
def c1612 : List Lit := [(839, true), (811, false)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c1375, c817] c1612 (by decide) p (sat_cons (step1375 p h) (sat_cons (step817 p h) (sat_nil p)))
def c1613 : List Lit := [(840, true), (812, false)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c1375, c823] c1613 (by decide) p (sat_cons (step1375 p h) (sat_cons (step823 p h) (sat_nil p)))
def c1614 : List Lit := [(841, true), (813, false)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c1375, c829] c1614 (by decide) p (sat_cons (step1375 p h) (sat_cons (step829 p h) (sat_nil p)))
def c1615 : List Lit := [(814, false), (842, true)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c1375, c835] c1615 (by decide) p (sat_cons (step1375 p h) (sat_cons (step835 p h) (sat_nil p)))
def c1616 : List Lit := [(815, false), (843, true)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c1375, c840] c1616 (by decide) p (sat_cons (step1375 p h) (sat_cons (step840 p h) (sat_nil p)))
def c1617 : List Lit := [(903, false), (919, true)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c1376, c959] c1617 (by decide) p (sat_cons (step1376 p h) (sat_cons (step959 p h) (sat_nil p)))
def c1618 : List Lit := [(844, false), (900, false)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1002] c1618 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1002 p h) (sat_nil p)))
def c1619 : List Lit := [(846, false), (898, false)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1011] c1619 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1011 p h) (sat_nil p)))
def c1620 : List Lit := [(974, true), (942, false)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c1294, c1098] c1620 (by decide) p (sat_cons (step1294 p h) (sat_cons (step1098 p h) (sat_nil p)))
def c1621 : List Lit := [(975, true), (943, false)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c1294, c1103] c1621 (by decide) p (sat_cons (step1294 p h) (sat_cons (step1103 p h) (sat_nil p)))
def c1622 : List Lit := [(976, true), (944, false)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c1294, c1108] c1622 (by decide) p (sat_cons (step1294 p h) (sat_cons (step1108 p h) (sat_nil p)))
end B112E115
