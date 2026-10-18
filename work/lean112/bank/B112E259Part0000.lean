import B112E259Inputs
namespace B112E259
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1540 : List Lit := [(47, true)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c214, c213] c1540 (by decide) p (sat_cons (step214 p h) (sat_cons (step213 p h) (sat_nil p)))
def c1541 : List Lit := [(163, true), (110, true)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1540, c215] c1541 (by decide) p (sat_cons (step1540 p h) (sat_cons (step215 p h) (sat_nil p)))
def c1542 : List Lit := [(109, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c636, c578] c1542 (by decide) p (sat_cons (step636 p h) (sat_cons (step578 p h) (sat_nil p)))
def c1543 : List Lit := [(113, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c638, c581] c1543 (by decide) p (sat_cons (step638 p h) (sat_cons (step581 p h) (sat_nil p)))
def c1544 : List Lit := [(458, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c841, c838] c1544 (by decide) p (sat_cons (step841 p h) (sat_cons (step838 p h) (sat_nil p)))
def c1545 : List Lit := [(344, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c841, c840] c1545 (by decide) p (sat_cons (step841 p h) (sat_cons (step840 p h) (sat_nil p)))
def c1546 : List Lit := [(456, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1544, c834] c1546 (by decide) p (sat_cons (step1544 p h) (sat_cons (step834 p h) (sat_nil p)))
def c1547 : List Lit := [(400, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1544, c837] c1547 (by decide) p (sat_cons (step1544 p h) (sat_cons (step837 p h) (sat_nil p)))
def c1548 : List Lit := [(342, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1545, c756] c1548 (by decide) p (sat_cons (step1545 p h) (sat_cons (step756 p h) (sat_nil p)))
def c1549 : List Lit := [(286, false)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1545, c759] c1549 (by decide) p (sat_cons (step1545 p h) (sat_cons (step759 p h) (sat_nil p)))
def c1550 : List Lit := [(398, false)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1547, c799] c1550 (by decide) p (sat_cons (step1547 p h) (sat_cons (step799 p h) (sat_nil p)))
def c1551 : List Lit := [(370, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1547, c802] c1551 (by decide) p (sat_cons (step1547 p h) (sat_cons (step802 p h) (sat_nil p)))
def c1552 : List Lit := [(340, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1548, c751] c1552 (by decide) p (sat_cons (step1548 p h) (sat_cons (step751 p h) (sat_nil p)))
def c1553 : List Lit := [(312, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1548, c754] c1553 (by decide) p (sat_cons (step1548 p h) (sat_cons (step754 p h) (sat_nil p)))
def c1554 : List Lit := [(284, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1549, c696] c1554 (by decide) p (sat_cons (step1549 p h) (sat_cons (step696 p h) (sat_nil p)))
def c1555 : List Lit := [(258, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1549, c699] c1555 (by decide) p (sat_cons (step1549 p h) (sat_cons (step699 p h) (sat_nil p)))
def c1556 : List Lit := [(368, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1551, c779] c1556 (by decide) p (sat_cons (step1551 p h) (sat_cons (step779 p h) (sat_nil p)))
def c1557 : List Lit := [(338, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1552, c747] c1557 (by decide) p (sat_cons (step1552 p h) (sat_cons (step747 p h) (sat_nil p)))
def c1558 : List Lit := [(298, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1553, c722] c1558 (by decide) p (sat_cons (step1553 p h) (sat_cons (step722 p h) (sat_nil p)))
def c1559 : List Lit := [(282, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1554, c691] c1559 (by decide) p (sat_cons (step1554 p h) (sat_cons (step691 p h) (sat_nil p)))
def c1560 : List Lit := [(270, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1554, c694] c1560 (by decide) p (sat_cons (step1554 p h) (sat_cons (step694 p h) (sat_nil p)))
def c1561 : List Lit := [(256, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1555, c665] c1561 (by decide) p (sat_cons (step1555 p h) (sat_cons (step665 p h) (sat_nil p)))
def c1562 : List Lit := [(244, false)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1555, c668] c1562 (by decide) p (sat_cons (step1555 p h) (sat_cons (step668 p h) (sat_nil p)))
def c1563 : List Lit := [(366, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1556, c776] c1563 (by decide) p (sat_cons (step1556 p h) (sat_cons (step776 p h) (sat_nil p)))
def c1564 : List Lit := [(330, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1557, c745] c1564 (by decide) p (sat_cons (step1557 p h) (sat_cons (step745 p h) (sat_nil p)))
def c1565 : List Lit := [(296, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1558, c709] c1565 (by decide) p (sat_cons (step1558 p h) (sat_cons (step709 p h) (sat_nil p)))
def c1566 : List Lit := [(274, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1559, c689] c1566 (by decide) p (sat_cons (step1559 p h) (sat_cons (step689 p h) (sat_nil p)))
def c1567 : List Lit := [(268, false)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1560, c677] c1567 (by decide) p (sat_cons (step1560 p h) (sat_cons (step677 p h) (sat_nil p)))
def c1568 : List Lit := [(254, false)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1561, c660] c1568 (by decide) p (sat_cons (step1561 p h) (sat_cons (step660 p h) (sat_nil p)))
def c1569 : List Lit := [(248, false)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1561, c663] c1569 (by decide) p (sat_cons (step1561 p h) (sat_cons (step663 p h) (sat_nil p)))
def c1570 : List Lit := [(242, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1562, c647] c1570 (by decide) p (sat_cons (step1562 p h) (sat_cons (step647 p h) (sat_nil p)))
def c1571 : List Lit := [(328, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1564, c737] c1571 (by decide) p (sat_cons (step1564 p h) (sat_cons (step737 p h) (sat_nil p)))
def c1572 : List Lit := [(238, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1570, c645] c1572 (by decide) p (sat_cons (step1570 p h) (sat_cons (step645 p h) (sat_nil p)))
def c1573 : List Lit := [(994, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1542, c1244] c1573 (by decide) p (sat_cons (step1542 p h) (sat_cons (step1244 p h) (sat_nil p)))
def c1574 : List Lit := [(996, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1573, c1245] c1574 (by decide) p (sat_cons (step1573 p h) (sat_cons (step1245 p h) (sat_nil p)))
def c1575 : List Lit := [(992, false), (997, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c1573, c1246] c1575 (by decide) p (sat_cons (step1573 p h) (sat_cons (step1246 p h) (sat_nil p)))
def c1576 : List Lit := [(993, false), (998, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1573, c1247] c1576 (by decide) p (sat_cons (step1573 p h) (sat_cons (step1247 p h) (sat_nil p)))
def c1577 : List Lit := [(1000, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c1543, c1248] c1577 (by decide) p (sat_cons (step1543 p h) (sat_cons (step1248 p h) (sat_nil p)))
def c1578 : List Lit := [(112, true), (1001, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1543, c1249] c1578 (by decide) p (sat_cons (step1543 p h) (sat_cons (step1249 p h) (sat_nil p)))
def c1579 : List Lit := [(1004, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1252] c1579 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1252 p h) (sat_nil p)))
def c1580 : List Lit := [(1002, false), (1005, true)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1253] c1580 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1253 p h) (sat_nil p)))
def c1581 : List Lit := [(1009, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1574, c1579, c1256] c1581 (by decide) p (sat_cons (step1574 p h) (sat_cons (step1579 p h) (sat_cons (step1256 p h) (sat_nil p))))
def c1582 : List Lit := [(1005, false), (1010, true)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c1574, c1257] c1582 (by decide) p (sat_cons (step1574 p h) (sat_cons (step1257 p h) (sat_nil p)))
def c1583 : List Lit := [(997, false), (1010, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1258] c1583 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1258 p h) (sat_nil p)))
def c1584 : List Lit := [(998, false), (1011, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1261] c1584 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c1585 : List Lit := [(1017, true)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c1581, c1262] c1585 (by decide) p (sat_cons (step1581 p h) (sat_cons (step1262 p h) (sat_nil p)))
def c1586 : List Lit := [(985, false), (1018, true)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c1581, c1265] c1586 (by decide) p (sat_cons (step1581 p h) (sat_cons (step1265 p h) (sat_nil p)))
def c1587 : List Lit := [(986, false), (1019, true)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c1581, c1269] c1587 (by decide) p (sat_cons (step1581 p h) (sat_cons (step1269 p h) (sat_nil p)))
def c1588 : List Lit := [(988, false), (1021, true)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c1581, c1274] c1588 (by decide) p (sat_cons (step1581 p h) (sat_cons (step1274 p h) (sat_nil p)))
def c1589 : List Lit := [(964, false), (1039, true)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1300] c1589 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1300 p h) (sat_nil p)))
def c1590 : List Lit := [(20, false), (4, false), (56, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c5, c13] c1590 (by decide) p (sat_cons (step5 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1591 : List Lit := [(1407, true), (16, false), (1418, true), (4, true)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1359, c111, c682, c687, c690, c698, c664, c661, c651, c650, c1358, c1323, c1325, c1348, c1345, c1326, c1336, c1338, c1324, c1333, c1330, c80, c39, c52] c1591 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1359 p h) (sat_cons (step111 p h) (sat_cons (step682 p h) (sat_cons (step687 p h) (sat_cons (step690 p h) (sat_cons (step698 p h) (sat_cons (step664 p h) (sat_cons (step661 p h) (sat_cons (step651 p h) (sat_cons (step650 p h) (sat_cons (step1358 p h) (sat_cons (step1323 p h) (sat_cons (step1325 p h) (sat_cons (step1348 p h) (sat_cons (step1345 p h) (sat_cons (step1326 p h) (sat_cons (step1336 p h) (sat_cons (step1338 p h) (sat_cons (step1324 p h) (sat_cons (step1333 p h) (sat_cons (step1330 p h) (sat_cons (step80 p h) (sat_cons (step39 p h) (sat_cons (step52 p h) (sat_nil p))))))))))))))))))))))))))
def c1592 : List Lit := [(1402, true), (16, false), (25, true), (125, true), (124, true), (24, false)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c591, c1336, c1338, c1333, c1330, c1331, c80, c44, c46, c52, c1508, c39, c37] c1592 (by decide) p (sat_cons (step591 p h) (sat_cons (step1336 p h) (sat_cons (step1338 p h) (sat_cons (step1333 p h) (sat_cons (step1330 p h) (sat_cons (step1331 p h) (sat_cons (step80 p h) (sat_cons (step44 p h) (sat_cons (step46 p h) (sat_cons (step52 p h) (sat_cons (step1508 p h) (sat_cons (step39 p h) (sat_cons (step37 p h) (sat_nil p))))))))))))))
def c1593 : List Lit := [(1400, true), (1415, true), (149, true), (28, false), (128, true), (19, false), (134, true)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c596, c1355, c1354, c1356, c1333, c1334, c90, c96, c95, c1514, c72, c183, c130, c146, c63] c1593 (by decide) p (sat_cons (step596 p h) (sat_cons (step1355 p h) (sat_cons (step1354 p h) (sat_cons (step1356 p h) (sat_cons (step1333 p h) (sat_cons (step1334 p h) (sat_cons (step90 p h) (sat_cons (step96 p h) (sat_cons (step95 p h) (sat_cons (step1514 p h) (sat_cons (step72 p h) (sat_cons (step183 p h) (sat_cons (step130 p h) (sat_cons (step146 p h) (sat_cons (step63 p h) (sat_nil p))))))))))))))))
def c1594 : List Lit := [(1615, true), (114, false), (106, false), (1600, false)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c1470, c1482, c1481, c1473, c1477, c1466, c1476, c584] c1594 (by decide) p (sat_cons (step1470 p h) (sat_cons (step1482 p h) (sat_cons (step1481 p h) (sat_cons (step1473 p h) (sat_cons (step1477 p h) (sat_cons (step1466 p h) (sat_cons (step1476 p h) (sat_cons (step584 p h) (sat_nil p)))))))))
def c1595 : List Lit := [(64, false), (9, true), (95, false), (74, false)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c618, c316, c374] c1595 (by decide) p (sat_cons (step618 p h) (sat_cons (step316 p h) (sat_cons (step374 p h) (sat_nil p))))
def c1596 : List Lit := [(1547, true), (74, false), (18, false), (76, true)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1437, c1438, c1435, c376] c1596 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1437 p h) (sat_cons (step1438 p h) (sat_cons (step1435 p h) (sat_cons (step376 p h) (sat_nil p))))))
def c1597 : List Lit := [(29, false), (13, true), (27, true), (145, true)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c594, c165, c167, c57, c1512] c1597 (by decide) p (sat_cons (step594 p h) (sat_cons (step165 p h) (sat_cons (step167 p h) (sat_cons (step57 p h) (sat_cons (step1512 p h) (sat_nil p))))))
def c1598 : List Lit := [(8, false), (14, false), (25, true), (124, true), (140, true), (24, false)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c591, c44, c46, c1508, c37, c25, c28, c119] c1598 (by decide) p (sat_cons (step591 p h) (sat_cons (step44 p h) (sat_cons (step46 p h) (sat_cons (step1508 p h) (sat_cons (step37 p h) (sat_cons (step25 p h) (sat_cons (step28 p h) (sat_cons (step119 p h) (sat_nil p)))))))))
def c1599 : List Lit := [(1616, true), (1601, false), (285, false)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c841, c1545, c637, c1471, c758, c750, c748, c730, c729, c726, c1541, c579, c757, c839, c833, c830, c829, c823, c822, c819, c572, c1484, c1483, c1474, c1477, c1466, c1476, c584] c1599 (by decide) p (sat_cons (step841 p h) (sat_cons (step1545 p h) (sat_cons (step637 p h) (sat_cons (step1471 p h) (sat_cons (step758 p h) (sat_cons (step750 p h) (sat_cons (step748 p h) (sat_cons (step730 p h) (sat_cons (step729 p h) (sat_cons (step726 p h) (sat_cons (step1541 p h) (sat_cons (step579 p h) (sat_cons (step757 p h) (sat_cons (step839 p h) (sat_cons (step833 p h) (sat_cons (step830 p h) (sat_cons (step829 p h) (sat_cons (step823 p h) (sat_cons (step822 p h) (sat_cons (step819 p h) (sat_cons (step572 p h) (sat_cons (step1484 p h) (sat_cons (step1483 p h) (sat_cons (step1474 p h) (sat_cons (step1477 p h) (sat_cons (step1466 p h) (sat_cons (step1476 p h) (sat_cons (step584 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1600 : List Lit := [(33, true), (1450, true), (13, true), (147, true), (28, false), (145, true), (19, false)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c1392, c1388, c1390, c1393, c178, c1597, c142] c1600 (by decide) p (sat_cons (step1392 p h) (sat_cons (step1388 p h) (sat_cons (step1390 p h) (sat_cons (step1393 p h) (sat_cons (step178 p h) (sat_cons (step1597 p h) (sat_cons (step142 p h) (sat_nil p))))))))
def c1601 : List Lit := [(1450, true), (13, true), (147, true), (149, true), (28, false), (145, true), (19, false)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c1600, c183, c143, c146, c1597, c178, c1393, c1389] c1601 (by decide) p (sat_cons (step1600 p h) (sat_cons (step183 p h) (sat_cons (step143 p h) (sat_cons (step146 p h) (sat_cons (step1597 p h) (sat_cons (step178 p h) (sat_cons (step1393 p h) (sat_cons (step1389 p h) (sat_nil p)))))))))
def c1602 : List Lit := [(1592, true), (72, false), (208, true), (83, true)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c1457, c1464, c1463, c1458, c1460, c1454, c1455, c1459, c542, c500, c536] c1602 (by decide) p (sat_cons (step1457 p h) (sat_cons (step1464 p h) (sat_cons (step1463 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1454 p h) (sat_cons (step1455 p h) (sat_cons (step1459 p h) (sat_cons (step542 p h) (sat_cons (step500 p h) (sat_cons (step536 p h) (sat_nil p))))))))))))
def c1603 : List Lit := [(92, false), (87, true), (90, false), (72, false), (208, true)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c536, c542] c1603 (by decide) p (sat_cons (step536 p h) (sat_cons (step542 p h) (sat_nil p)))
end B112E259
