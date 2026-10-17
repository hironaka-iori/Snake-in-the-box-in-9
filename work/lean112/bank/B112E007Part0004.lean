import B112E007Part0003
namespace B112E007
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1556 : List Lit := [(349, false), (465, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c828, c826] c1556 (by decide) p (sat_cons (step828 p h) (sat_cons (step826 p h) (sat_nil p)))
def c1557 : List Lit := [(1521, false), (1533, true)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1352, c983] c1557 (by decide) p (sat_cons (step1352 p h) (sat_cons (step983 p h) (sat_nil p)))
def c1558 : List Lit := [(1522, false), (1534, true)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1352, c987] c1558 (by decide) p (sat_cons (step1352 p h) (sat_cons (step987 p h) (sat_nil p)))
def c1559 : List Lit := [(1523, false), (1535, true)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1352, c990] c1559 (by decide) p (sat_cons (step1352 p h) (sat_cons (step990 p h) (sat_nil p)))
def c1560 : List Lit := [(1533, false), (1541, true)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1355, c994] c1560 (by decide) p (sat_cons (step1355 p h) (sat_cons (step994 p h) (sat_nil p)))
def c1561 : List Lit := [(1534, false), (1542, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1355, c995] c1561 (by decide) p (sat_cons (step1355 p h) (sat_cons (step995 p h) (sat_nil p)))
def c1562 : List Lit := [(1535, false), (1543, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1355, c996] c1562 (by decide) p (sat_cons (step1355 p h) (sat_cons (step996 p h) (sat_nil p)))
def c1563 : List Lit := [(1536, false), (1544, true)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1355, c997] c1563 (by decide) p (sat_cons (step1355 p h) (sat_cons (step997 p h) (sat_nil p)))
def c1564 : List Lit := [(1514, false), (1542, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1353, c1002] c1564 (by decide) p (sat_cons (step1353 p h) (sat_cons (step1002 p h) (sat_nil p)))
def c1565 : List Lit := [(1541, false), (1556, true)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1354, c1012] c1565 (by decide) p (sat_cons (step1354 p h) (sat_cons (step1012 p h) (sat_nil p)))
def c1566 : List Lit := [(1542, false), (1557, true)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1354, c1013] c1566 (by decide) p (sat_cons (step1354 p h) (sat_cons (step1013 p h) (sat_nil p)))
def c1567 : List Lit := [(1543, false), (1558, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1354, c1014] c1567 (by decide) p (sat_cons (step1354 p h) (sat_cons (step1014 p h) (sat_nil p)))
def c1568 : List Lit := [(1544, false), (1559, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1354, c1015] c1568 (by decide) p (sat_cons (step1354 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c1569 : List Lit := [(1545, false), (1560, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1354, c1016] c1569 (by decide) p (sat_cons (step1354 p h) (sat_cons (step1016 p h) (sat_nil p)))
def c1570 : List Lit := [(1546, false), (1561, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1354, c1017] c1570 (by decide) p (sat_cons (step1354 p h) (sat_cons (step1017 p h) (sat_nil p)))
def c1571 : List Lit := [(1558, true), (1488, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1361, c1028] c1571 (by decide) p (sat_cons (step1361 p h) (sat_cons (step1028 p h) (sat_nil p)))
def c1572 : List Lit := [(1559, true), (1489, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1361, c1034] c1572 (by decide) p (sat_cons (step1361 p h) (sat_cons (step1034 p h) (sat_nil p)))
def c1573 : List Lit := [(1603, false), (1611, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1111] c1573 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1111 p h) (sat_nil p)))
def c1574 : List Lit := [(1604, false), (1612, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1112] c1574 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1112 p h) (sat_nil p)))
def c1575 : List Lit := [(1605, false), (1613, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1113] c1575 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1113 p h) (sat_nil p)))
def c1576 : List Lit := [(1606, false), (1614, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1114] c1576 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1114 p h) (sat_nil p)))
def c1577 : List Lit := [(1583, false), (1611, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1115] c1577 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1115 p h) (sat_nil p)))
def c1578 : List Lit := [(1584, false), (1612, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1120] c1578 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1120 p h) (sat_nil p)))
def c1579 : List Lit := [(1585, false), (1613, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1126] c1579 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1126 p h) (sat_nil p)))
def c1580 : List Lit := [(1586, false), (1614, true)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1131] c1580 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1131 p h) (sat_nil p)))
def c1581 : List Lit := [(1667, false), (1682, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1336, c1225] c1581 (by decide) p (sat_cons (step1336 p h) (sat_cons (step1225 p h) (sat_nil p)))
def c1582 : List Lit := [(1668, false), (1683, true)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c1336, c1226] c1582 (by decide) p (sat_cons (step1336 p h) (sat_cons (step1226 p h) (sat_nil p)))
def c1583 : List Lit := [(1665, false), (1681, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1227] c1583 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1227 p h) (sat_nil p)))
def c1584 : List Lit := [(1666, false), (1682, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1228] c1584 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1228 p h) (sat_nil p)))
def c1585 : List Lit := [(1667, false), (1683, true)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1229] c1585 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1229 p h) (sat_nil p)))
def c1586 : List Lit := [(1668, false), (1684, true)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1230] c1586 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1230 p h) (sat_nil p)))
def c1587 : List Lit := [(1669, false), (1685, true)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1231] c1587 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1231 p h) (sat_nil p)))
def c1588 : List Lit := [(1556, false), (1688, false)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1260] c1588 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1260 p h) (sat_nil p)))
def c1589 : List Lit := [(1557, false), (1687, false)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1261] c1589 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c1590 : List Lit := [(1558, false), (1686, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1262] c1590 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1262 p h) (sat_nil p)))
def c1591 : List Lit := [(1559, false), (1685, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1263] c1591 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1263 p h) (sat_nil p)))
def c1592 : List Lit := [(1560, false), (1684, false)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1264] c1592 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1264 p h) (sat_nil p)))
def c1593 : List Lit := [(1561, false), (1683, false)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1265] c1593 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1265 p h) (sat_nil p)))
def c1594 : List Lit := [(1562, false), (1682, false)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1266] c1594 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1266 p h) (sat_nil p)))
def c1595 : List Lit := [(1563, false), (1681, false)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1267] c1595 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1267 p h) (sat_nil p)))
def c1596 : List Lit := [(88, false), (1605, true), (86, true), (77, true), (106, false), (98, false)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c402, c398, c1083, c1072, c1085, c1074, c1103] c1596 (by decide) p (sat_cons (step402 p h) (sat_cons (step398 p h) (sat_cons (step1083 p h) (sat_cons (step1072 p h) (sat_cons (step1085 p h) (sat_cons (step1074 p h) (sat_cons (step1103 p h) (sat_nil p))))))))
def c1597 : List Lit := [(1529, true), (59, true), (175, true)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c972, c1438, c970] c1597 (by decide) p (sat_cons (step972 p h) (sat_cons (step1438 p h) (sat_cons (step970 p h) (sat_nil p))))
def c1598 : List Lit := [(1529, true), (56, true), (91, true)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c972, c1405, c1437, c201, c1413] c1598 (by decide) p (sat_cons (step972 p h) (sat_cons (step1405 p h) (sat_cons (step1437 p h) (sat_cons (step201 p h) (sat_cons (step1413 p h) (sat_nil p))))))
def c1599 : List Lit := [(37, true), (1513, true)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c954, c928, c924, c926, c927, c1356, c950] c1599 (by decide) p (sat_cons (step954 p h) (sat_cons (step928 p h) (sat_cons (step924 p h) (sat_cons (step926 p h) (sat_cons (step927 p h) (sat_cons (step1356 p h) (sat_cons (step950 p h) (sat_nil p))))))))
def c1600 : List Lit := [(1652, true), (233, true), (1513, true)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c946, c938, c1599, c1186, c1188, c1370, c1434, c1183, c1184, c1180, c531, c159, c936] c1600 (by decide) p (sat_cons (step946 p h) (sat_cons (step938 p h) (sat_cons (step1599 p h) (sat_cons (step1186 p h) (sat_cons (step1188 p h) (sat_cons (step1370 p h) (sat_cons (step1434 p h) (sat_cons (step1183 p h) (sat_cons (step1184 p h) (sat_cons (step1180 p h) (sat_cons (step531 p h) (sat_cons (step159 p h) (sat_cons (step936 p h) (sat_nil p))))))))))))))
def c1601 : List Lit := [(405, true), (1583, true), (10, false), (190, true), (70, true)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c1067, c1045, c1060, c757, c759, c1371, c755, c735, c287, c285, c744, c722, c1502, c254, c253, c740, c721, c1374, c718, c248, c237, c1043] c1601 (by decide) p (sat_cons (step1067 p h) (sat_cons (step1045 p h) (sat_cons (step1060 p h) (sat_cons (step757 p h) (sat_cons (step759 p h) (sat_cons (step1371 p h) (sat_cons (step755 p h) (sat_cons (step735 p h) (sat_cons (step287 p h) (sat_cons (step285 p h) (sat_cons (step744 p h) (sat_cons (step722 p h) (sat_cons (step1502 p h) (sat_cons (step254 p h) (sat_cons (step253 p h) (sat_cons (step740 p h) (sat_cons (step721 p h) (sat_cons (step1374 p h) (sat_cons (step718 p h) (sat_cons (step248 p h) (sat_cons (step237 p h) (sat_cons (step1043 p h) (sat_nil p)))))))))))))))))))))))
def c1602 : List Lit := [(1596, true), (81, false), (208, true), (1595, true)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c1081, c1082, c1340, c393, c413] c1602 (by decide) p (sat_cons (step1081 p h) (sat_cons (step1082 p h) (sat_cons (step1340 p h) (sat_cons (step393 p h) (sat_cons (step413 p h) (sat_nil p))))))
def c1603 : List Lit := [(81, false), (203, true), (208, true), (1599, true), (1626, true), (102, false)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1139, c1602, c1087, c1078, c1079, c348, c344, c359, c1342, c1141, c1135, c1136, c453] c1603 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1139 p h) (sat_cons (step1602 p h) (sat_cons (step1087 p h) (sat_cons (step1078 p h) (sat_cons (step1079 p h) (sat_cons (step348 p h) (sat_cons (step344 p h) (sat_cons (step359 p h) (sat_cons (step1342 p h) (sat_cons (step1141 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step453 p h) (sat_nil p)))))))))))))))
def c1604 : List Lit := [(1596, true), (208, true), (1594, true)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c1079, c1078, c1081, c1082, c405, c354, c412] c1604 (by decide) p (sat_cons (step1079 p h) (sat_cons (step1078 p h) (sat_cons (step1081 p h) (sat_cons (step1082 p h) (sat_cons (step405 p h) (sat_cons (step354 p h) (sat_cons (step412 p h) (sat_nil p))))))))
def c1605 : List Lit := [(93, false), (94, false), (211, true), (85, false)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c1344, c453] c1605 (by decide) p (sat_cons (step1344 p h) (sat_cons (step453 p h) (sat_nil p)))
def c1606 : List Lit := [(94, false), (211, true), (203, true), (1626, true), (102, false), (84, true), (85, false)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1136, c1141, c452, c346, c359] c1606 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1136 p h) (sat_cons (step1141 p h) (sat_cons (step452 p h) (sat_cons (step346 p h) (sat_cons (step359 p h) (sat_nil p)))))))
def c1607 : List Lit := [(211, true), (203, true), (1626, true), (102, false), (84, true), (85, false)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c1139, c1606, c1135, c1137, c1141, c1344, c451] c1607 (by decide) p (sat_cons (step1139 p h) (sat_cons (step1606 p h) (sat_cons (step1135 p h) (sat_cons (step1137 p h) (sat_cons (step1141 p h) (sat_cons (step1344 p h) (sat_cons (step451 p h) (sat_nil p))))))))
def c1608 : List Lit := [(96, false), (1629, true), (115, false), (86, false)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c465, c464, c1145] c1608 (by decide) p (sat_cons (step465 p h) (sat_cons (step464 p h) (sat_cons (step1145 p h) (sat_nil p))))
def c1609 : List Lit := [(1529, true), (172, true), (91, true)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c1405, c1437, c1392] c1609 (by decide) p (sat_cons (step1405 p h) (sat_cons (step1437 p h) (sat_cons (step1392 p h) (sat_nil p))))
def c1610 : List Lit := [(1519, true), (65, false), (82, true), (169, true)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c957, c958, c173, c187] c1610 (by decide) p (sat_cons (step957 p h) (sat_cons (step958 p h) (sat_cons (step173 p h) (sat_cons (step187 p h) (sat_nil p)))))
def c1611 : List Lit := [(46, true), (1510, true), (39, true), (313, true)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c1479, c934, c1373, c943] c1611 (by decide) p (sat_cons (step1479 p h) (sat_cons (step934 p h) (sat_cons (step1373 p h) (sat_cons (step943 p h) (sat_nil p)))))
def c1612 : List Lit := [(37, true), (1515, true), (1545, true), (45, false), (115, false), (1529, false), (313, true), (1519, false)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c667, c663, c666, c665, c1473, c924, c145, c927, c932, c952, c939, c1611, c161, c963, c988, c1005, c955, c951, c928, c942, c940, c926, c933, c935, c1431] c1612 (by decide) p (sat_cons (step667 p h) (sat_cons (step663 p h) (sat_cons (step666 p h) (sat_cons (step665 p h) (sat_cons (step1473 p h) (sat_cons (step924 p h) (sat_cons (step145 p h) (sat_cons (step927 p h) (sat_cons (step932 p h) (sat_cons (step952 p h) (sat_cons (step939 p h) (sat_cons (step1611 p h) (sat_cons (step161 p h) (sat_cons (step963 p h) (sat_cons (step988 p h) (sat_cons (step1005 p h) (sat_cons (step955 p h) (sat_cons (step951 p h) (sat_cons (step928 p h) (sat_cons (step942 p h) (sat_cons (step940 p h) (sat_cons (step926 p h) (sat_cons (step933 p h) (sat_cons (step935 p h) (sat_cons (step1431 p h) (sat_nil p))))))))))))))))))))))))))
def c1613 : List Lit := [(1545, true), (45, false), (115, false), (1534, false), (1529, false), (313, true), (1519, false)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c667, c663, c666, c665, c1008, c1612, c159, c160, c1479, c934, c963, c151, c988, c931, c1005, c940, c947, c951, c1611, c941, c927, c1472, c936, c925, c1433] c1613 (by decide) p (sat_cons (step667 p h) (sat_cons (step663 p h) (sat_cons (step666 p h) (sat_cons (step665 p h) (sat_cons (step1008 p h) (sat_cons (step1612 p h) (sat_cons (step159 p h) (sat_cons (step160 p h) (sat_cons (step1479 p h) (sat_cons (step934 p h) (sat_cons (step963 p h) (sat_cons (step151 p h) (sat_cons (step988 p h) (sat_cons (step931 p h) (sat_cons (step1005 p h) (sat_cons (step940 p h) (sat_cons (step947 p h) (sat_cons (step951 p h) (sat_cons (step1611 p h) (sat_cons (step941 p h) (sat_cons (step927 p h) (sat_cons (step1472 p h) (sat_cons (step936 p h) (sat_cons (step925 p h) (sat_cons (step1433 p h) (sat_nil p))))))))))))))))))))))))))
def c1614 : List Lit := [(1628, true), (1652, true), (233, true)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c1422, c1188, c1181] c1614 (by decide) p (sat_cons (step1422 p h) (sat_cons (step1188 p h) (sat_cons (step1181 p h) (sat_nil p))))
def c1615 : List Lit := [(1583, true), (405, true), (65, false)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c759, c733, c731, c727, c757, c755, c744, c740, c1060, c1371, c1374, c252, c248] c1615 (by decide) p (sat_cons (step759 p h) (sat_cons (step733 p h) (sat_cons (step731 p h) (sat_cons (step727 p h) (sat_cons (step757 p h) (sat_cons (step755 p h) (sat_cons (step744 p h) (sat_cons (step740 p h) (sat_cons (step1060 p h) (sat_cons (step1371 p h) (sat_cons (step1374 p h) (sat_cons (step252 p h) (sat_cons (step248 p h) (sat_nil p))))))))))))))
def c1616 : List Lit := [(72, false), (190, true), (194, true), (192, true), (77, false), (76, false), (105, false), (65, false)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c273, c287, c285, c248, c1502, c1506, c259, c294, c299, c1510] c1616 (by decide) p (sat_cons (step273 p h) (sat_cons (step287 p h) (sat_cons (step285 p h) (sat_cons (step248 p h) (sat_cons (step1502 p h) (sat_cons (step1506 p h) (sat_cons (step259 p h) (sat_cons (step294 p h) (sat_cons (step299 p h) (sat_cons (step1510 p h) (sat_nil p)))))))))))
def c1617 : List Lit := [(70, true), (79, false), (66, false), (1576, false), (71, true), (182, true), (186, true), (195, true), (77, false), (76, false), (1584, true), (65, false)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c303, c304, c297, c245, c237, c255, c1042, c1046, c1044, c1055, c1064] c1617 (by decide) p (sat_cons (step303 p h) (sat_cons (step304 p h) (sat_cons (step297 p h) (sat_cons (step245 p h) (sat_cons (step237 p h) (sat_cons (step255 p h) (sat_cons (step1042 p h) (sat_cons (step1046 p h) (sat_cons (step1044 p h) (sat_cons (step1055 p h) (sat_cons (step1064 p h) (sat_nil p))))))))))))
def c1618 : List Lit := [(67, true), (72, true), (192, true), (1580, true)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c1506, c1047, c294, c1056, c1051] c1618 (by decide) p (sat_cons (step1506 p h) (sat_cons (step1047 p h) (sat_cons (step294 p h) (sat_cons (step1056 p h) (sat_cons (step1051 p h) (sat_nil p))))))
def c1619 : List Lit := [(79, false), (66, false), (65, false), (1576, false), (71, true), (182, true), (186, true), (195, true), (77, false), (76, false), (1584, true)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1285, c244, c271, c302, c1046, c297, c1055, c237, c1064, c1042, c1044] c1619 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1285 p h) (sat_cons (step244 p h) (sat_cons (step271 p h) (sat_cons (step302 p h) (sat_cons (step1046 p h) (sat_cons (step297 p h) (sat_cons (step1055 p h) (sat_cons (step237 p h) (sat_cons (step1064 p h) (sat_cons (step1042 p h) (sat_cons (step1044 p h) (sat_nil p)))))))))))))
end B112E007
