import B112E091Part0009
namespace B112E091
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1559 : List Lit := [(1453, false), (1372, true), (1417, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1548, c1389, c1390, c1386, c1549, c1535, c1558, c647, c644, c645, c1398, c750, c1406, c751, c754, c746, c785, c137, c135, c878, c1162, c669, c1231, c678, c729, c701, c683, c687, c679, c663, c665, c670, c671, c660, c152, c164, c114, c155] c1559 (by decide) p (sat_cons (step1548 p h) (sat_cons (step1389 p h) (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step1549 p h) (sat_cons (step1535 p h) (sat_cons (step1558 p h) (sat_cons (step647 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step1398 p h) (sat_cons (step750 p h) (sat_cons (step1406 p h) (sat_cons (step751 p h) (sat_cons (step754 p h) (sat_cons (step746 p h) (sat_cons (step785 p h) (sat_cons (step137 p h) (sat_cons (step135 p h) (sat_cons (step878 p h) (sat_cons (step1162 p h) (sat_cons (step669 p h) (sat_cons (step1231 p h) (sat_cons (step678 p h) (sat_cons (step729 p h) (sat_cons (step701 p h) (sat_cons (step683 p h) (sat_cons (step687 p h) (sat_cons (step679 p h) (sat_cons (step663 p h) (sat_cons (step665 p h) (sat_cons (step670 p h) (sat_cons (step671 p h) (sat_cons (step660 p h) (sat_cons (step152 p h) (sat_cons (step164 p h) (sat_cons (step114 p h) (sat_cons (step155 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1560 : List Lit := [(1453, true), (1417, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c854, c861, c981, c818, c807, c813] c1560 (by decide) p (sat_cons (step854 p h) (sat_cons (step861 p h) (sat_cons (step981 p h) (sat_cons (step818 p h) (sat_cons (step807 p h) (sat_cons (step813 p h) (sat_nil p)))))))
def c1561 : List Lit := [(1392, true), (1454, true), (35, false), (37, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1494, c1488] c1561 (by decide) p (sat_cons (step1494 p h) (sat_cons (step1488 p h) (sat_nil p)))
def c1562 : List Lit := [(1417, false)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1390, c1551, c1560, c891, c1558, c1559, c647, c755, c644, c645, c789, c790, c885, c1561] c1562 (by decide) p (sat_cons (step1390 p h) (sat_cons (step1551 p h) (sat_cons (step1560 p h) (sat_cons (step891 p h) (sat_cons (step1558 p h) (sat_cons (step1559 p h) (sat_cons (step647 p h) (sat_cons (step755 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step789 p h) (sat_cons (step790 p h) (sat_cons (step885 p h) (sat_cons (step1561 p h) (sat_nil p)))))))))))))))
def c1563 : List Lit := [(87, true)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1562, c804] c1563 (by decide) p (sat_cons (step1562 p h) (sat_cons (step804 p h) (sat_nil p)))
def c1564 : List Lit := [(1364, true), (63, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1384, c1383, c738, c1453, c185, c1487] c1564 (by decide) p (sat_cons (step1384 p h) (sat_cons (step1383 p h) (sat_cons (step738 p h) (sat_cons (step1453 p h) (sat_cons (step185 p h) (sat_cons (step1487 p h) (sat_nil p)))))))
def c1565 : List Lit := [(63, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1563, c1534, c1549, c1548, c1562, c1564, c740, c1220, c758, c785, c1438, c876, c647, c1233, c654, c1540, c731, c706, c729, c1452, c1231, c768, c878, c769, c854, c772, c981, c786, c807, c883, c810, c857, c817] c1565 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1563 p h) (sat_cons (step1534 p h) (sat_cons (step1549 p h) (sat_cons (step1548 p h) (sat_cons (step1562 p h) (sat_cons (step1564 p h) (sat_cons (step740 p h) (sat_cons (step1220 p h) (sat_cons (step758 p h) (sat_cons (step785 p h) (sat_cons (step1438 p h) (sat_cons (step876 p h) (sat_cons (step647 p h) (sat_cons (step1233 p h) (sat_cons (step654 p h) (sat_cons (step1540 p h) (sat_cons (step731 p h) (sat_cons (step706 p h) (sat_cons (step729 p h) (sat_cons (step1452 p h) (sat_cons (step1231 p h) (sat_cons (step768 p h) (sat_cons (step878 p h) (sat_cons (step769 p h) (sat_cons (step854 p h) (sat_cons (step772 p h) (sat_cons (step981 p h) (sat_cons (step786 p h) (sat_cons (step807 p h) (sat_cons (step883 p h) (sat_cons (step810 p h) (sat_cons (step857 p h) (sat_cons (step817 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c1566 : List Lit := [(1381, true)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1565, c765] c1566 (by decide) p (sat_cons (step1565 p h) (sat_cons (step765 p h) (sat_nil p)))
def c1567 : List Lit := [(35, false)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1555, c1562, c1515] c1567 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1555 p h) (sat_cons (step1562 p h) (sat_cons (step1515 p h) (sat_nil p)))))
def c1568 : List Lit := [(59, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1378, c1556, c983] c1568 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1378 p h) (sat_cons (step1556 p h) (sat_cons (step983 p h) (sat_nil p)))))
def c1569 : List Lit := [(1392, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1566, c773] c1569 (by decide) p (sat_cons (step1566 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1570 : List Lit := [(1388, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1566, c1555, c774] c1570 (by decide) p (sat_cons (step1566 p h) (sat_cons (step1555 p h) (sat_cons (step774 p h) (sat_nil p))))
def c1571 : List Lit := [(1306, true)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1567, c645] c1571 (by decide) p (sat_cons (step1567 p h) (sat_cons (step645 p h) (sat_nil p)))
def c1572 : List Lit := [(41, true)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1170] c1572 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1170 p h) (sat_nil p)))
def c1573 : List Lit := [(1401, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1392, c782] c1573 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1392 p h) (sat_cons (step782 p h) (sat_nil p))))
def c1574 : List Lit := [(1386, false)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1570, c769] c1574 (by decide) p (sat_cons (step1570 p h) (sat_cons (step769 p h) (sat_nil p)))
def c1575 : List Lit := [(1308, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c1571, c647] c1575 (by decide) p (sat_cons (step1571 p h) (sat_cons (step647 p h) (sat_nil p)))
def c1576 : List Lit := [(76, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1574, c768] c1576 (by decide) p (sat_cons (step1574 p h) (sat_cons (step768 p h) (sat_nil p)))
def c1577 : List Lit := [(1312, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1534, c654] c1577 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1534 p h) (sat_cons (step654 p h) (sat_nil p))))
def c1578 : List Lit := [(1414, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1396, c1267] c1578 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1396 p h) (sat_cons (step1267 p h) (sat_nil p))))
def c1579 : List Lit := [(43, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1562, c1408] c1579 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1562 p h) (sat_cons (step1408 p h) (sat_nil p))))
def c1580 : List Lit := [(1339, true)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1409, c703] c1580 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1409 p h) (sat_cons (step703 p h) (sat_nil p))))
def c1581 : List Lit := [(1425, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1578, c820] c1581 (by decide) p (sat_cons (step1578 p h) (sat_cons (step820 p h) (sat_nil p)))
def c1582 : List Lit := [(1322, true)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1563, c1281] c1582 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1563 p h) (sat_cons (step1281 p h) (sat_nil p))))
def c1583 : List Lit := [(1356, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c1580, c1549, c728] c1583 (by decide) p (sat_cons (step1580 p h) (sat_cons (step1549 p h) (sat_cons (step728 p h) (sat_nil p))))
def c1584 : List Lit := [(1331, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c1582, c1572, c1500] c1584 (by decide) p (sat_cons (step1582 p h) (sat_cons (step1572 p h) (sat_cons (step1500 p h) (sat_nil p))))
def c1585 : List Lit := [(1470, false)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1230] c1585 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1230 p h) (sat_nil p)))
def c1586 : List Lit := [(1340, true)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c1584, c1577, c704] c1586 (by decide) p (sat_cons (step1584 p h) (sat_cons (step1577 p h) (sat_cons (step704 p h) (sat_nil p))))
def c1587 : List Lit := [(1454, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1573, c879] c1587 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1573 p h) (sat_cons (step879 p h) (sat_nil p))))
def c1588 : List Lit := [(1357, true)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1549, c729] c1588 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1549 p h) (sat_cons (step729 p h) (sat_nil p))))
def c1589 : List Lit := [(1446, false)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c1587, c1581, c859] c1589 (by decide) p (sat_cons (step1587 p h) (sat_cons (step1581 p h) (sat_cons (step859 p h) (sat_nil p))))
def c1590 : List Lit := [(1469, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c1588, c1231] c1590 (by decide) p (sat_cons (step1588 p h) (sat_cons (step1231 p h) (sat_nil p)))
def c1591 : List Lit := [(91, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c1589, c981] c1591 (by decide) p (sat_cons (step1589 p h) (sat_cons (step981 p h) (sat_nil p)))
def c1592 : List Lit := [(1453, false)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c1590, c1573, c878] c1592 (by decide) p (sat_cons (step1590 p h) (sat_cons (step1573 p h) (sat_cons (step878 p h) (sat_nil p))))
def c1593 : List Lit := [(1419, true)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c1591, c807] c1593 (by decide) p (sat_cons (step1591 p h) (sat_cons (step807 p h) (sat_nil p)))
def c1594 : List Lit := [(1426, false)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c1592, c861] c1594 (by decide) p (sat_cons (step1592 p h) (sat_cons (step861 p h) (sat_nil p)))
def c1595 : List Lit := [(1421, true)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c1593, c810] c1595 (by decide) p (sat_cons (step1593 p h) (sat_cons (step810 p h) (sat_nil p)))
def c1596 : List Lit := []
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1594, c1578, c821] c1596 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1594 p h) (sat_cons (step1578 p h) (sat_cons (step821 p h) (sat_nil p)))))
end B112E091
