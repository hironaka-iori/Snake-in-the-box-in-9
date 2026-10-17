import B112E168Part0005
namespace B112E168
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1522 : List Lit := [(253, false), (279, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c1147, c545] c1522 (by decide) p (sat_cons (step1147 p h) (sat_cons (step545 p h) (sat_nil p)))
def c1523 : List Lit := [(281, false), (335, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c1144, c585] c1523 (by decide) p (sat_cons (step1144 p h) (sat_cons (step585 p h) (sat_nil p)))
def c1524 : List Lit := [(193, false), (377, false)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c1153, c615] c1524 (by decide) p (sat_cons (step1153 p h) (sat_cons (step615 p h) (sat_nil p)))
def c1525 : List Lit := [(375, false), (387, false)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c1149, c624] c1525 (by decide) p (sat_cons (step1149 p h) (sat_cons (step624 p h) (sat_nil p)))
def c1526 : List Lit := [(363, false), (389, false)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1146, c628] c1526 (by decide) p (sat_cons (step1146 p h) (sat_cons (step628 p h) (sat_nil p)))
def c1527 : List Lit := [(403, false), (415, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c1148, c648] c1527 (by decide) p (sat_cons (step1148 p h) (sat_cons (step648 p h) (sat_nil p)))
def c1528 : List Lit := [(337, false), (449, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c677, c675] c1528 (by decide) p (sat_cons (step677 p h) (sat_cons (step675 p h) (sat_nil p)))
def c1529 : List Lit := [(1395, false), (1407, true)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c1392, c740] c1529 (by decide) p (sat_cons (step1392 p h) (sat_cons (step740 p h) (sat_nil p)))
def c1530 : List Lit := [(1396, false), (1408, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c1392, c745] c1530 (by decide) p (sat_cons (step1392 p h) (sat_cons (step745 p h) (sat_nil p)))
def c1531 : List Lit := [(1415, true), (1387, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c1393, c755] c1531 (by decide) p (sat_cons (step1393 p h) (sat_cons (step755 p h) (sat_nil p)))
def c1532 : List Lit := [(1416, true), (1388, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c1393, c761] c1532 (by decide) p (sat_cons (step1393 p h) (sat_cons (step761 p h) (sat_nil p)))
def c1533 : List Lit := [(1417, true), (1389, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1393, c767] c1533 (by decide) p (sat_cons (step1393 p h) (sat_cons (step767 p h) (sat_nil p)))
def c1534 : List Lit := [(1390, false), (1418, true)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1393, c773] c1534 (by decide) p (sat_cons (step1393 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1535 : List Lit := [(1391, false), (1419, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1393, c777] c1535 (by decide) p (sat_cons (step1393 p h) (sat_cons (step777 p h) (sat_nil p)))
def c1536 : List Lit := [(1461, false), (1469, true)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1190, c857] c1536 (by decide) p (sat_cons (step1190 p h) (sat_cons (step857 p h) (sat_nil p)))
def c1537 : List Lit := [(1462, false), (1470, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1190, c858] c1537 (by decide) p (sat_cons (step1190 p h) (sat_cons (step858 p h) (sat_nil p)))
def c1538 : List Lit := [(1463, false), (1471, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1190, c859] c1538 (by decide) p (sat_cons (step1190 p h) (sat_cons (step859 p h) (sat_nil p)))
def c1539 : List Lit := [(1464, false), (1472, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1190, c860] c1539 (by decide) p (sat_cons (step1190 p h) (sat_cons (step860 p h) (sat_nil p)))
def c1540 : List Lit := [(1465, false), (1473, true)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1190, c861] c1540 (by decide) p (sat_cons (step1190 p h) (sat_cons (step861 p h) (sat_nil p)))
def c1541 : List Lit := [(1441, false), (1469, true)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1191, c862] c1541 (by decide) p (sat_cons (step1191 p h) (sat_cons (step862 p h) (sat_nil p)))
def c1542 : List Lit := [(1442, false), (1470, true)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1191, c868] c1542 (by decide) p (sat_cons (step1191 p h) (sat_cons (step868 p h) (sat_nil p)))
def c1543 : List Lit := [(1443, false), (1471, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1191, c874] c1543 (by decide) p (sat_cons (step1191 p h) (sat_cons (step874 p h) (sat_nil p)))
def c1544 : List Lit := [(1487, true), (1471, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1394, c883] c1544 (by decide) p (sat_cons (step1394 p h) (sat_cons (step883 p h) (sat_nil p)))
def c1545 : List Lit := [(1488, true), (1472, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1394, c884] c1545 (by decide) p (sat_cons (step1394 p h) (sat_cons (step884 p h) (sat_nil p)))
def c1546 : List Lit := [(1489, true), (1473, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1394, c885] c1546 (by decide) p (sat_cons (step1394 p h) (sat_cons (step885 p h) (sat_nil p)))
def c1547 : List Lit := [(1490, true), (1474, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1394, c886] c1547 (by decide) p (sat_cons (step1394 p h) (sat_cons (step886 p h) (sat_nil p)))
def c1548 : List Lit := [(1485, true), (1415, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1192, c888] c1548 (by decide) p (sat_cons (step1192 p h) (sat_cons (step888 p h) (sat_nil p)))
def c1549 : List Lit := [(1486, true), (1416, false)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1192, c896] c1549 (by decide) p (sat_cons (step1192 p h) (sat_cons (step896 p h) (sat_nil p)))
def c1550 : List Lit := [(1487, true), (1417, false)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1192, c903] c1550 (by decide) p (sat_cons (step1192 p h) (sat_cons (step903 p h) (sat_nil p)))
def c1551 : List Lit := [(1474, false), (1417, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1286, c909] c1551 (by decide) p (sat_cons (step1286 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1552 : List Lit := [(1488, true), (1418, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1192, c910] c1552 (by decide) p (sat_cons (step1192 p h) (sat_cons (step910 p h) (sat_nil p)))
def c1553 : List Lit := [(1418, false), (1473, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1286, c915] c1553 (by decide) p (sat_cons (step1286 p h) (sat_cons (step915 p h) (sat_nil p)))
def c1554 : List Lit := [(1489, true), (1419, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1192, c916] c1554 (by decide) p (sat_cons (step1192 p h) (sat_cons (step916 p h) (sat_nil p)))
def c1555 : List Lit := [(1419, false), (1472, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1286, c920] c1555 (by decide) p (sat_cons (step1286 p h) (sat_cons (step920 p h) (sat_nil p)))
def c1556 : List Lit := [(1490, true), (1420, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1192, c921] c1556 (by decide) p (sat_cons (step1192 p h) (sat_cons (step921 p h) (sat_nil p)))
def c1557 : List Lit := [(1420, false), (1471, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1286, c924] c1557 (by decide) p (sat_cons (step1286 p h) (sat_cons (step924 p h) (sat_nil p)))
def c1558 : List Lit := [(1491, true), (1421, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1192, c925] c1558 (by decide) p (sat_cons (step1192 p h) (sat_cons (step925 p h) (sat_nil p)))
def c1559 : List Lit := [(1421, false), (1470, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1286, c927] c1559 (by decide) p (sat_cons (step1286 p h) (sat_cons (step927 p h) (sat_nil p)))
def c1560 : List Lit := [(1492, true), (1422, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1192, c928] c1560 (by decide) p (sat_cons (step1192 p h) (sat_cons (step928 p h) (sat_nil p)))
def c1561 : List Lit := [(1585, false), (1593, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1283, c1064] c1561 (by decide) p (sat_cons (step1283 p h) (sat_cons (step1064 p h) (sat_nil p)))
def c1562 : List Lit := [(1586, false), (1594, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1283, c1065] c1562 (by decide) p (sat_cons (step1283 p h) (sat_cons (step1065 p h) (sat_nil p)))
def c1563 : List Lit := [(1593, true), (1565, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1225, c1067] c1563 (by decide) p (sat_cons (step1225 p h) (sat_cons (step1067 p h) (sat_nil p)))
def c1564 : List Lit := [(1594, true), (1566, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1225, c1069] c1564 (by decide) p (sat_cons (step1225 p h) (sat_cons (step1069 p h) (sat_nil p)))
def c1565 : List Lit := [(1567, false), (1595, true)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1225, c1071] c1565 (by decide) p (sat_cons (step1225 p h) (sat_cons (step1071 p h) (sat_nil p)))
def c1566 : List Lit := [(1608, true), (1538, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1077] c1566 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1077 p h) (sat_nil p)))
def c1567 : List Lit := [(1539, false), (1608, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1226, c1081] c1567 (by decide) p (sat_cons (step1226 p h) (sat_cons (step1081 p h) (sat_nil p)))
def c1568 : List Lit := [(1609, true), (1539, false)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1082] c1568 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c1569 : List Lit := [(1610, true), (1540, false)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1086] c1569 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1086 p h) (sat_nil p)))
def c1570 : List Lit := [(1541, false), (1610, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1226, c1089] c1570 (by decide) p (sat_cons (step1226 p h) (sat_cons (step1089 p h) (sat_nil p)))
def c1571 : List Lit := [(1611, true), (1541, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1090] c1571 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1090 p h) (sat_nil p)))
def c1572 : List Lit := [(1542, false), (1612, true)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1093] c1572 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1093 p h) (sat_nil p)))
def c1573 : List Lit := [(1543, false), (1613, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1096] c1573 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1096 p h) (sat_nil p)))
def c1574 : List Lit := [(1544, false), (1614, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1099] c1574 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1099 p h) (sat_nil p)))
def c1575 : List Lit := [(1545, false), (1615, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1100] c1575 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1100 p h) (sat_nil p)))
def c1576 : List Lit := [(1485, false), (1615, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1101] c1576 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c1577 : List Lit := [(1486, false), (1614, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1102] c1577 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1102 p h) (sat_nil p)))
def c1578 : List Lit := [(1487, false), (1613, false)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1103] c1578 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1103 p h) (sat_nil p)))
def c1579 : List Lit := [(1488, false), (1612, false)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1104] c1579 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1104 p h) (sat_nil p)))
def c1580 : List Lit := [(1489, false), (1611, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1105] c1580 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c1581 : List Lit := [(1490, false), (1610, false)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1106] c1581 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1106 p h) (sat_nil p)))
def c1582 : List Lit := [(1491, false), (1609, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1107] c1582 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1107 p h) (sat_nil p)))
def c1583 : List Lit := [(1492, false), (1608, false)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1108] c1583 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1108 p h) (sat_nil p)))
def c1584 : List Lit := [(8, false), (47, true), (1442, false), (1610, true), (27, true), (24, false), (1530, false)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1408, c694, c1161, c1531, c1437, c1118, c1182, c168, c169, c1018, c1282, c1563, c1078, c1083, c1582, c990, c894, c1178, c872, c1311] c1584 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1408 p h) (sat_cons (step694 p h) (sat_cons (step1161 p h) (sat_cons (step1531 p h) (sat_cons (step1437 p h) (sat_cons (step1118 p h) (sat_cons (step1182 p h) (sat_cons (step168 p h) (sat_cons (step169 p h) (sat_cons (step1018 p h) (sat_cons (step1282 p h) (sat_cons (step1563 p h) (sat_cons (step1078 p h) (sat_cons (step1083 p h) (sat_cons (step1582 p h) (sat_cons (step990 p h) (sat_cons (step894 p h) (sat_cons (step1178 p h) (sat_cons (step872 p h) (sat_cons (step1311 p h) (sat_nil p))))))))))))))))))))))
def c1585 : List Lit := [(47, true), (1473, false), (1442, false), (1610, true), (27, true), (24, false), (1530, false)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1437, c1118, c1182, c1566, c1583, c1584, c1400, c902, c901, c872, c1582, c1568, c1078, c990, c1563, c1178, c1282, c1311, c1018, c185] c1585 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1437 p h) (sat_cons (step1118 p h) (sat_cons (step1182 p h) (sat_cons (step1566 p h) (sat_cons (step1583 p h) (sat_cons (step1584 p h) (sat_cons (step1400 p h) (sat_cons (step902 p h) (sat_cons (step901 p h) (sat_cons (step872 p h) (sat_cons (step1582 p h) (sat_cons (step1568 p h) (sat_cons (step1078 p h) (sat_cons (step990 p h) (sat_cons (step1563 p h) (sat_cons (step1178 p h) (sat_cons (step1282 p h) (sat_cons (step1311 p h) (sat_cons (step1018 p h) (sat_cons (step185 p h) (sat_nil p))))))))))))))))))))))
end B112E168
