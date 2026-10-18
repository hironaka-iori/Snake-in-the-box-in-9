import B112E158Inputs
namespace B112E158
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1570 : List Lit := [(79, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c563, c562] c1570 (by decide) p (sat_cons (step563 p h) (sat_cons (step562 p h) (sat_nil p)))
def c1571 : List Lit := [(197, true), (80, true)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1570, c564] c1571 (by decide) p (sat_cons (step1570 p h) (sat_cons (step564 p h) (sat_nil p)))
def c1572 : List Lit := [(466, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c903, c900] c1572 (by decide) p (sat_cons (step903 p h) (sat_cons (step900 p h) (sat_nil p)))
def c1573 : List Lit := [(350, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c903, c902] c1573 (by decide) p (sat_cons (step903 p h) (sat_cons (step902 p h) (sat_nil p)))
def c1574 : List Lit := [(464, false)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1572, c896] c1574 (by decide) p (sat_cons (step1572 p h) (sat_cons (step896 p h) (sat_nil p)))
def c1575 : List Lit := [(406, false)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c1572, c899] c1575 (by decide) p (sat_cons (step1572 p h) (sat_cons (step899 p h) (sat_nil p)))
def c1576 : List Lit := [(348, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1573, c814] c1576 (by decide) p (sat_cons (step1573 p h) (sat_cons (step814 p h) (sat_nil p)))
def c1577 : List Lit := [(292, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c1573, c817] c1577 (by decide) p (sat_cons (step1573 p h) (sat_cons (step817 p h) (sat_nil p)))
def c1578 : List Lit := [(434, false)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1574, c894] c1578 (by decide) p (sat_cons (step1574 p h) (sat_cons (step894 p h) (sat_nil p)))
def c1579 : List Lit := [(404, false)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1575, c861] c1579 (by decide) p (sat_cons (step1575 p h) (sat_cons (step861 p h) (sat_nil p)))
def c1580 : List Lit := [(346, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1576, c811] c1580 (by decide) p (sat_cons (step1576 p h) (sat_cons (step811 p h) (sat_nil p)))
def c1581 : List Lit := [(290, false)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1577, c778] c1581 (by decide) p (sat_cons (step1577 p h) (sat_cons (step778 p h) (sat_nil p)))
def c1582 : List Lit := [(262, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c1577, c781] c1582 (by decide) p (sat_cons (step1577 p h) (sat_cons (step781 p h) (sat_nil p)))
def c1583 : List Lit := [(418, false)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c1578, c880] c1583 (by decide) p (sat_cons (step1578 p h) (sat_cons (step880 p h) (sat_nil p)))
def c1584 : List Lit := [(402, false)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c1579, c856] c1584 (by decide) p (sat_cons (step1579 p h) (sat_cons (step856 p h) (sat_nil p)))
def c1585 : List Lit := [(388, false)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c1579, c859] c1585 (by decide) p (sat_cons (step1579 p h) (sat_cons (step859 p h) (sat_nil p)))
def c1586 : List Lit := [(330, false)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c1580, c809] c1586 (by decide) p (sat_cons (step1580 p h) (sat_cons (step809 p h) (sat_nil p)))
def c1587 : List Lit := [(288, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c1581, c773] c1587 (by decide) p (sat_cons (step1581 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1588 : List Lit := [(274, false)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c1581, c776] c1588 (by decide) p (sat_cons (step1581 p h) (sat_cons (step776 p h) (sat_nil p)))
def c1589 : List Lit := [(260, false)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c1582, c742] c1589 (by decide) p (sat_cons (step1582 p h) (sat_cons (step742 p h) (sat_nil p)))
def c1590 : List Lit := [(248, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c1582, c745] c1590 (by decide) p (sat_cons (step1582 p h) (sat_cons (step745 p h) (sat_nil p)))
def c1591 : List Lit := [(386, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c1585, c841] c1591 (by decide) p (sat_cons (step1585 p h) (sat_cons (step841 p h) (sat_nil p)))
def c1592 : List Lit := [(286, false)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c1587, c768] c1592 (by decide) p (sat_cons (step1587 p h) (sat_cons (step768 p h) (sat_nil p)))
def c1593 : List Lit := [(280, false)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c1587, c771] c1593 (by decide) p (sat_cons (step1587 p h) (sat_cons (step771 p h) (sat_nil p)))
def c1594 : List Lit := [(266, false)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c1588, c755] c1594 (by decide) p (sat_cons (step1588 p h) (sat_cons (step755 p h) (sat_nil p)))
def c1595 : List Lit := [(258, false)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c1589, c737] c1595 (by decide) p (sat_cons (step1589 p h) (sat_cons (step737 p h) (sat_nil p)))
def c1596 : List Lit := [(252, false)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c1589, c740] c1596 (by decide) p (sat_cons (step1589 p h) (sat_cons (step740 p h) (sat_nil p)))
def c1597 : List Lit := [(240, false)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c1590, c726] c1597 (by decide) p (sat_cons (step1590 p h) (sat_cons (step726 p h) (sat_nil p)))
def c1598 : List Lit := [(276, false)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c1593, c760] c1598 (by decide) p (sat_cons (step1593 p h) (sat_cons (step760 p h) (sat_nil p)))
def c1599 : List Lit := [(1566, true)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c693, c1293, c1297, c1285, c1287, c1274, c1276, c1283, c1279, c1280, c1272, c534, c529, c458, c494] c1599 (by decide) p (sat_cons (step693 p h) (sat_cons (step1293 p h) (sat_cons (step1297 p h) (sat_cons (step1285 p h) (sat_cons (step1287 p h) (sat_cons (step1274 p h) (sat_cons (step1276 p h) (sat_cons (step1283 p h) (sat_cons (step1279 p h) (sat_cons (step1280 p h) (sat_cons (step1272 p h) (sat_cons (step534 p h) (sat_cons (step529 p h) (sat_cons (step458 p h) (sat_cons (step494 p h) (sat_nil p))))))))))))))))
def c1600 : List Lit := [(1597, true)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c1599, c1347] c1600 (by decide) p (sat_cons (step1599 p h) (sat_cons (step1347 p h) (sat_nil p)))
def c1601 : List Lit := [(24, true), (1462, true)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c675, c1075, c1057, c1053, c1043, c1044, c1050, c1051, c1056, c1061, c1046, c1081, c1037, c1019, c1023, c1034, c1011, c1000, c1008, c997, c119, c93, c128] c1601 (by decide) p (sat_cons (step675 p h) (sat_cons (step1075 p h) (sat_cons (step1057 p h) (sat_cons (step1053 p h) (sat_cons (step1043 p h) (sat_cons (step1044 p h) (sat_cons (step1050 p h) (sat_cons (step1051 p h) (sat_cons (step1056 p h) (sat_cons (step1061 p h) (sat_cons (step1046 p h) (sat_cons (step1081 p h) (sat_cons (step1037 p h) (sat_cons (step1019 p h) (sat_cons (step1023 p h) (sat_cons (step1034 p h) (sat_cons (step1011 p h) (sat_cons (step1000 p h) (sat_cons (step1008 p h) (sat_cons (step997 p h) (sat_cons (step119 p h) (sat_cons (step93 p h) (sat_cons (step128 p h) (sat_nil p))))))))))))))))))))))))
def c1602 : List Lit := [(1573, true), (82, false)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c699, c569, c1312, c1313, c557] c1602 (by decide) p (sat_cons (step699 p h) (sat_cons (step569 p h) (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step557 p h) (sat_nil p))))))
def c1603 : List Lit := [(21, false), (20, false), (24, false)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c672, c103, c86] c1603 (by decide) p (sat_cons (step672 p h) (sat_cons (step103 p h) (sat_cons (step86 p h) (sat_nil p))))
def c1604 : List Lit := [(1441, true), (24, false)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c1034, c1035, c1603] c1604 (by decide) p (sat_cons (step1034 p h) (sat_cons (step1035 p h) (sat_cons (step1603 p h) (sat_nil p))))
def c1605 : List Lit := [(1462, true)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c675, c1075, c1601, c1604, c1037, c1060, c1061, c1081, c1048, c1050, c1019, c1023, c1046, c1042, c1011, c1000, c1008, c997, c119, c95, c128] c1605 (by decide) p (sat_cons (step675 p h) (sat_cons (step1075 p h) (sat_cons (step1601 p h) (sat_cons (step1604 p h) (sat_cons (step1037 p h) (sat_cons (step1060 p h) (sat_cons (step1061 p h) (sat_cons (step1081 p h) (sat_cons (step1048 p h) (sat_cons (step1050 p h) (sat_cons (step1019 p h) (sat_cons (step1023 p h) (sat_cons (step1046 p h) (sat_cons (step1042 p h) (sat_cons (step1011 p h) (sat_cons (step1000 p h) (sat_cons (step1008 p h) (sat_cons (step997 p h) (sat_cons (step119 p h) (sat_cons (step95 p h) (sat_cons (step128 p h) (sat_nil p))))))))))))))))))))))
def c1606 : List Lit := [(1450, true), (22, true), (17, false)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c675, c1048, c1050, c1046, c1042, c128, c119] c1606 (by decide) p (sat_cons (step675 p h) (sat_cons (step1048 p h) (sat_cons (step1050 p h) (sat_cons (step1046 p h) (sat_cons (step1042 p h) (sat_cons (step128 p h) (sat_cons (step119 p h) (sat_nil p))))))))
def c1607 : List Lit := [(25, false), (27, true), (17, false)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c674, c116, c117, c1534] c1607 (by decide) p (sat_cons (step674 p h) (sat_cons (step116 p h) (sat_cons (step117 p h) (sat_cons (step1534 p h) (sat_nil p)))))
def c1608 : List Lit := [(1513, true), (1504, false), (69, false), (28, false)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c1164, c1169, c1173, c1165, c1147, c1156, c1139, c498] c1608 (by decide) p (sat_cons (step1164 p h) (sat_cons (step1169 p h) (sat_cons (step1173 p h) (sat_cons (step1165 p h) (sat_cons (step1147 p h) (sat_cons (step1156 p h) (sat_cons (step1139 p h) (sat_cons (step498 p h) (sat_nil p)))))))))
def c1609 : List Lit := [(58, false), (1559, true), (69, false), (28, false)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c503, c504, c1281] c1609 (by decide) p (sat_cons (step503 p h) (sat_cons (step504 p h) (sat_cons (step1281 p h) (sat_nil p))))
def c1610 : List Lit := [(68, true), (1564, true), (69, false), (28, false), (73, true)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1291, c1279, c1281, c1289, c508, c1284] c1610 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1291 p h) (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_cons (step1289 p h) (sat_cons (step508 p h) (sat_cons (step1284 p h) (sat_nil p))))))))
def c1611 : List Lit := [(1513, true), (50, true), (53, true), (13, false), (24, false)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c669, c1143, c1145, c1154, c1161, c1177, c1173, c1146, c1164, c1144, c1155, c302, c63, c53] c1611 (by decide) p (sat_cons (step669 p h) (sat_cons (step1143 p h) (sat_cons (step1145 p h) (sat_cons (step1154 p h) (sat_cons (step1161 p h) (sat_cons (step1177 p h) (sat_cons (step1173 p h) (sat_cons (step1146 p h) (sat_cons (step1164 p h) (sat_cons (step1144 p h) (sat_cons (step1155 p h) (sat_cons (step302 p h) (sat_cons (step63 p h) (sat_cons (step53 p h) (sat_nil p)))))))))))))))
def c1612 : List Lit := [(1423, true), (73, false), (22, true)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c666, c1000, c1002, c997, c32, c2] c1612 (by decide) p (sat_cons (step666 p h) (sat_cons (step1000 p h) (sat_cons (step1002 p h) (sat_cons (step997 p h) (sat_cons (step32 p h) (sat_cons (step2 p h) (sat_nil p)))))))
def c1613 : List Lit := [(55, false), (51, false), (59, false), (61, false)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c685, c270, c356, c291] c1613 (by decide) p (sat_cons (step685 p h) (sat_cons (step270 p h) (sat_cons (step356 p h) (sat_cons (step291 p h) (sat_nil p)))))
def c1614 : List Lit := [(1589, true)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c1333, c1336, c1329, c1317, c1322, c1602] c1614 (by decide) p (sat_cons (step1333 p h) (sat_cons (step1336 p h) (sat_cons (step1329 p h) (sat_cons (step1317 p h) (sat_cons (step1322 p h) (sat_cons (step1602 p h) (sat_nil p)))))))
def c1615 : List Lit := [(1598, true)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1599, c1348] c1615 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1599 p h) (sat_cons (step1348 p h) (sat_nil p))))
def c1616 : List Lit := [(89, false), (98, false), (92, false)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c705, c596, c611] c1616 (by decide) p (sat_cons (step705 p h) (sat_cons (step596 p h) (sat_cons (step611 p h) (sat_nil p))))
def c1617 : List Lit := [(1625, true)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1405, c1397, c1384, c1386, c1389, c1382, c1616] c1617 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1405 p h) (sat_cons (step1397 p h) (sat_cons (step1384 p h) (sat_cons (step1386 p h) (sat_cons (step1389 p h) (sat_cons (step1382 p h) (sat_cons (step1616 p h) (sat_nil p)))))))))
def c1618 : List Lit := [(1583, true), (89, false)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c701, c1324, c1325, c580, c574] c1618 (by decide) p (sat_cons (step701 p h) (sat_cons (step1324 p h) (sat_cons (step1325 p h) (sat_cons (step580 p h) (sat_cons (step574 p h) (sat_nil p))))))
def c1619 : List Lit := [(1567, true), (69, true), (21, false), (73, true)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c693, c1282, c1285, c1294, c1298, c1286, c1288, c1274, c1276, c1284, c1279, c1272, c444, c534, c494] c1619 (by decide) p (sat_cons (step693 p h) (sat_cons (step1282 p h) (sat_cons (step1285 p h) (sat_cons (step1294 p h) (sat_cons (step1298 p h) (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step1274 p h) (sat_cons (step1276 p h) (sat_cons (step1284 p h) (sat_cons (step1279 p h) (sat_cons (step1272 p h) (sat_cons (step444 p h) (sat_cons (step534 p h) (sat_cons (step494 p h) (sat_nil p))))))))))))))))
def c1620 : List Lit := [(1622, true), (94, true), (98, true)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c704, c1389, c1400, c1398, c1391, c1393, c607, c608, c1567] c1620 (by decide) p (sat_cons (step704 p h) (sat_cons (step1389 p h) (sat_cons (step1400 p h) (sat_cons (step1398 p h) (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step607 p h) (sat_cons (step608 p h) (sat_cons (step1567 p h) (sat_nil p))))))))))
def c1621 : List Lit := [(1567, true), (21, false), (73, true)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1294, c1619, c1286, c1288, c1284, c1279, c1280, c529] c1621 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1294 p h) (sat_cons (step1619 p h) (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step1284 p h) (sat_cons (step1279 p h) (sat_cons (step1280 p h) (sat_cons (step529 p h) (sat_nil p))))))))))
def c1622 : List Lit := [(1648, true)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c711, c1442, c1445, c1435, c1437, c1421, c1433, c1429, c1418, c645, c659] c1622 (by decide) p (sat_cons (step711 p h) (sat_cons (step1442 p h) (sat_cons (step1445 p h) (sat_cons (step1435 p h) (sat_cons (step1437 p h) (sat_cons (step1421 p h) (sat_cons (step1433 p h) (sat_cons (step1429 p h) (sat_cons (step1418 p h) (sat_cons (step645 p h) (sat_cons (step659 p h) (sat_nil p))))))))))))
def c1623 : List Lit := [(1657, true)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c1622, c1617, c1456] c1623 (by decide) p (sat_cons (step1622 p h) (sat_cons (step1617 p h) (sat_cons (step1456 p h) (sat_nil p))))
def c1624 : List Lit := [(95, false), (97, false), (94, true), (100, false)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c704, c608, c1567] c1624 (by decide) p (sat_cons (step704 p h) (sat_cons (step608 p h) (sat_cons (step1567 p h) (sat_nil p))))
def c1625 : List Lit := [(59, false), (57, false), (1509, true), (58, true), (68, false)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c364, c367, c1154, c1158, c1163] c1625 (by decide) p (sat_cons (step364 p h) (sat_cons (step367 p h) (sat_cons (step1154 p h) (sat_cons (step1158 p h) (sat_cons (step1163 p h) (sat_nil p))))))
def c1626 : List Lit := [(1649, true), (118, true)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c711, c1432, c1435, c1443, c1446, c1436, c1438, c1421, c1434, c1429, c1418, c645, c659] c1626 (by decide) p (sat_cons (step711 p h) (sat_cons (step1432 p h) (sat_cons (step1435 p h) (sat_cons (step1443 p h) (sat_cons (step1446 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1421 p h) (sat_cons (step1434 p h) (sat_cons (step1429 p h) (sat_cons (step1418 p h) (sat_cons (step645 p h) (sat_cons (step659 p h) (sat_nil p))))))))))))))
def c1627 : List Lit := [(1555, true), (1509, true), (70, true), (58, true), (68, false), (21, false)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c693, c1274, c1276, c1272, c1625, c444, c496] c1627 (by decide) p (sat_cons (step693 p h) (sat_cons (step1274 p h) (sat_cons (step1276 p h) (sat_cons (step1272 p h) (sat_cons (step1625 p h) (sat_cons (step444 p h) (sat_cons (step496 p h) (sat_nil p))))))))
def c1628 : List Lit := [(1489, true), (37, false), (32, true), (92, false)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c1106, c1132, c1128, c1107, c1117, c1102, c1110, c206] c1628 (by decide) p (sat_cons (step1106 p h) (sat_cons (step1132 p h) (sat_cons (step1128 p h) (sat_cons (step1107 p h) (sat_cons (step1117 p h) (sat_cons (step1102 p h) (sat_cons (step1110 p h) (sat_cons (step206 p h) (sat_nil p)))))))))
def c1629 : List Lit := [(1513, true), (1495, false), (58, true)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c685, c1156, c1159, c1147, c1173, c1177, c1160, c1162, c1148, c1158, c1153, c1154, c1142, c1143, c268, c292, c318] c1629 (by decide) p (sat_cons (step685 p h) (sat_cons (step1156 p h) (sat_cons (step1159 p h) (sat_cons (step1147 p h) (sat_cons (step1173 p h) (sat_cons (step1177 p h) (sat_cons (step1160 p h) (sat_cons (step1162 p h) (sat_cons (step1148 p h) (sat_cons (step1158 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step1142 p h) (sat_cons (step1143 p h) (sat_cons (step268 p h) (sat_cons (step292 p h) (sat_cons (step318 p h) (sat_nil p))))))))))))))))))
def c1630 : List Lit := [(53, false), (55, false), (70, true), (68, false), (21, false)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c693, c361, c441, c496] c1630 (by decide) p (sat_cons (step693 p h) (sat_cons (step361 p h) (sat_cons (step441 p h) (sat_cons (step496 p h) (sat_nil p)))))
def c1631 : List Lit := [(86, false), (93, false), (87, false)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c701, c580, c575] c1631 (by decide) p (sat_cons (step701 p h) (sat_cons (step580 p h) (sat_cons (step575 p h) (sat_nil p))))
def c1632 : List Lit := [(1489, true), (1482, false), (37, false), (92, false)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c1124, c1628, c1118, c200, c1110] c1632 (by decide) p (sat_cons (step1124 p h) (sat_cons (step1628 p h) (sat_cons (step1118 p h) (sat_cons (step200 p h) (sat_cons (step1110 p h) (sat_nil p))))))
def c1633 : List Lit := [(1463, true), (1451, false), (52, true), (54, false), (1455, false)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c669, c1076, c1082, c1062, c1019, c1039, c1011, c1009, c53, c62] c1633 (by decide) p (sat_cons (step669 p h) (sat_cons (step1076 p h) (sat_cons (step1082 p h) (sat_cons (step1062 p h) (sat_cons (step1019 p h) (sat_cons (step1039 p h) (sat_cons (step1011 p h) (sat_cons (step1009 p h) (sat_cons (step53 p h) (sat_cons (step62 p h) (sat_nil p)))))))))))
end B112E158
