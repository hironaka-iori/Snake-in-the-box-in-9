import B112E104Part0005
namespace B112E104
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1540 : List Lit := [(114, true), (115, false), (103, true), (117, true)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c562, c458] c1540 (by decide) p (sat_cons (step562 p h) (sat_cons (step458 p h) (sat_nil p)))
def c1541 : List Lit := [(119, false), (237, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1182, c567] c1541 (by decide) p (sat_cons (step1182 p h) (sat_cons (step567 p h) (sat_nil p)))
def c1542 : List Lit := [(239, false), (245, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1179, c572] c1542 (by decide) p (sat_cons (step1179 p h) (sat_cons (step572 p h) (sat_nil p)))
def c1543 : List Lit := [(247, false), (259, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1176, c583] c1543 (by decide) p (sat_cons (step1176 p h) (sat_cons (step583 p h) (sat_nil p)))
def c1544 : List Lit := [(261, false), (289, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1171, c602] c1544 (by decide) p (sat_cons (step1171 p h) (sat_cons (step602 p h) (sat_nil p)))
def c1545 : List Lit := [(303, false), (315, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1175, c616] c1545 (by decide) p (sat_cons (step1175 p h) (sat_cons (step616 p h) (sat_nil p)))
def c1546 : List Lit := [(317, false), (345, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1170, c638] c1546 (by decide) p (sat_cons (step1170 p h) (sat_cons (step638 p h) (sat_nil p)))
def c1547 : List Lit := [(291, false), (347, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1167, c643] c1547 (by decide) p (sat_cons (step1167 p h) (sat_cons (step643 p h) (sat_nil p)))
def c1548 : List Lit := [(393, false), (399, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1178, c685] c1548 (by decide) p (sat_cons (step1178 p h) (sat_cons (step685 p h) (sat_nil p)))
def c1549 : List Lit := [(387, false), (401, false)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1174, c689] c1549 (by decide) p (sat_cons (step1174 p h) (sat_cons (step689 p h) (sat_nil p)))
def c1550 : List Lit := [(405, false), (463, false)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1166, c741] c1550 (by decide) p (sat_cons (step1166 p h) (sat_cons (step741 p h) (sat_nil p)))
def c1551 : List Lit := [(349, false), (465, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c746, c744] c1551 (by decide) p (sat_cons (step746 p h) (sat_cons (step744 p h) (sat_nil p)))
def c1552 : List Lit := [(1437, false), (1450, true)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1208, c798] c1552 (by decide) p (sat_cons (step1208 p h) (sat_cons (step798 p h) (sat_nil p)))
def c1553 : List Lit := [(1438, false), (1451, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1208, c802] c1553 (by decide) p (sat_cons (step1208 p h) (sat_cons (step802 p h) (sat_nil p)))
def c1554 : List Lit := [(1439, false), (1452, true)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1208, c805] c1554 (by decide) p (sat_cons (step1208 p h) (sat_cons (step805 p h) (sat_nil p)))
def c1555 : List Lit := [(1440, false), (1453, true)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1208, c808] c1555 (by decide) p (sat_cons (step1208 p h) (sat_cons (step808 p h) (sat_nil p)))
def c1556 : List Lit := [(1474, false), (1486, true)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1205, c844] c1556 (by decide) p (sat_cons (step1205 p h) (sat_cons (step844 p h) (sat_nil p)))
def c1557 : List Lit := [(1475, false), (1487, true)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1205, c847] c1557 (by decide) p (sat_cons (step1205 p h) (sat_cons (step847 p h) (sat_nil p)))
def c1558 : List Lit := [(1476, false), (1488, true)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1205, c849] c1558 (by decide) p (sat_cons (step1205 p h) (sat_cons (step849 p h) (sat_nil p)))
def c1559 : List Lit := [(1510, false), (1519, true)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1206, c873] c1559 (by decide) p (sat_cons (step1206 p h) (sat_cons (step873 p h) (sat_nil p)))
def c1560 : List Lit := [(1511, false), (1520, true)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1206, c874] c1560 (by decide) p (sat_cons (step1206 p h) (sat_cons (step874 p h) (sat_nil p)))
def c1561 : List Lit := [(1486, false), (1519, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1203, c875] c1561 (by decide) p (sat_cons (step1203 p h) (sat_cons (step875 p h) (sat_nil p)))
def c1562 : List Lit := [(1487, false), (1520, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1203, c878] c1562 (by decide) p (sat_cons (step1203 p h) (sat_cons (step878 p h) (sat_nil p)))
def c1563 : List Lit := [(1488, false), (1521, true)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1203, c881] c1563 (by decide) p (sat_cons (step1203 p h) (sat_cons (step881 p h) (sat_nil p)))
def c1564 : List Lit := [(1489, false), (1522, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1203, c883] c1564 (by decide) p (sat_cons (step1203 p h) (sat_cons (step883 p h) (sat_nil p)))
def c1565 : List Lit := [(1519, false), (1539, true)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1220, c885] c1565 (by decide) p (sat_cons (step1220 p h) (sat_cons (step885 p h) (sat_nil p)))
def c1566 : List Lit := [(1540, true), (1520, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1220, c886] c1566 (by decide) p (sat_cons (step1220 p h) (sat_cons (step886 p h) (sat_nil p)))
def c1567 : List Lit := [(1521, false), (1541, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1220, c887] c1567 (by decide) p (sat_cons (step1220 p h) (sat_cons (step887 p h) (sat_nil p)))
def c1568 : List Lit := [(1522, false), (1542, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1220, c888] c1568 (by decide) p (sat_cons (step1220 p h) (sat_cons (step888 p h) (sat_nil p)))
def c1569 : List Lit := [(1539, true), (1462, false)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1207, c889] c1569 (by decide) p (sat_cons (step1207 p h) (sat_cons (step889 p h) (sat_nil p)))
def c1570 : List Lit := [(1540, true), (1463, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1207, c894] c1570 (by decide) p (sat_cons (step1207 p h) (sat_cons (step894 p h) (sat_nil p)))
def c1571 : List Lit := [(1540, true), (1464, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1204, c898] c1571 (by decide) p (sat_cons (step1204 p h) (sat_cons (step898 p h) (sat_nil p)))
def c1572 : List Lit := [(1541, true), (1464, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1207, c899] c1572 (by decide) p (sat_cons (step1207 p h) (sat_cons (step899 p h) (sat_nil p)))
def c1573 : List Lit := [(1564, false), (1596, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1209, c962] c1573 (by decide) p (sat_cons (step1209 p h) (sat_cons (step962 p h) (sat_nil p)))
def c1574 : List Lit := [(1565, false), (1597, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1209, c967] c1574 (by decide) p (sat_cons (step1209 p h) (sat_cons (step967 p h) (sat_nil p)))
def c1575 : List Lit := [(1566, false), (1598, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c1209, c971] c1575 (by decide) p (sat_cons (step1209 p h) (sat_cons (step971 p h) (sat_nil p)))
def c1576 : List Lit := [(1660, false), (1676, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1092] c1576 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1092 p h) (sat_nil p)))
def c1577 : List Lit := [(1661, false), (1677, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1093] c1577 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1093 p h) (sat_nil p)))
def c1578 : List Lit := [(1662, false), (1678, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1094] c1578 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1094 p h) (sat_nil p)))
def c1579 : List Lit := [(1663, false), (1679, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1095] c1579 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c1580 : List Lit := [(1597, false), (1662, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1222, c1105] c1580 (by decide) p (sat_cons (step1222 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c1581 : List Lit := [(1598, false), (1661, false)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1222, c1111] c1581 (by decide) p (sat_cons (step1222 p h) (sat_cons (step1111 p h) (sat_nil p)))
def c1582 : List Lit := [(1599, false), (1660, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c1222, c1117] c1582 (by decide) p (sat_cons (step1222 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c1583 : List Lit := [(1600, false), (1659, false)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c1222, c1120] c1583 (by decide) p (sat_cons (step1222 p h) (sat_cons (step1120 p h) (sat_nil p)))
def c1584 : List Lit := [(1539, false), (1679, false)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c1127, c1122] c1584 (by decide) p (sat_cons (step1127 p h) (sat_cons (step1122 p h) (sat_nil p)))
def c1585 : List Lit := [(1678, false), (1540, false)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c1127, c1123] c1585 (by decide) p (sat_cons (step1127 p h) (sat_cons (step1123 p h) (sat_nil p)))
def c1586 : List Lit := [(1541, false), (1677, false)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c1127, c1124] c1586 (by decide) p (sat_cons (step1127 p h) (sat_cons (step1124 p h) (sat_nil p)))
def c1587 : List Lit := [(1542, false), (1676, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c1127, c1125] c1587 (by decide) p (sat_cons (step1127 p h) (sat_cons (step1125 p h) (sat_nil p)))
def c1588 : List Lit := [(1543, false), (1675, false)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c1127, c1126] c1588 (by decide) p (sat_cons (step1127 p h) (sat_cons (step1126 p h) (sat_nil p)))
def c1589 : List Lit := [(1560, true), (1596, false), (1621, false), (105, true), (76, false), (1486, false), (107, false)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c911, c913, c909, c906, c210, c1358, c1320, c1505, c1027, c482, c466, c1023, c852, c1032, c1240, c1225, c876, c1099, c1566, c1585] c1589 (by decide) p (sat_cons (step911 p h) (sat_cons (step913 p h) (sat_cons (step909 p h) (sat_cons (step906 p h) (sat_cons (step210 p h) (sat_cons (step1358 p h) (sat_cons (step1320 p h) (sat_cons (step1505 p h) (sat_cons (step1027 p h) (sat_cons (step482 p h) (sat_cons (step466 p h) (sat_cons (step1023 p h) (sat_cons (step852 p h) (sat_cons (step1032 p h) (sat_cons (step1240 p h) (sat_cons (step1225 p h) (sat_cons (step876 p h) (sat_cons (step1099 p h) (sat_cons (step1566 p h) (sat_cons (step1585 p h) (sat_nil p)))))))))))))))))))))
def c1590 : List Lit := [(70, true), (1661, true), (1597, false), (1621, false), (105, true), (76, false), (107, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c1505, c1285, c482, c484, c1225, c1027, c1023, c1032] c1590 (by decide) p (sat_cons (step1505 p h) (sat_cons (step1285 p h) (sat_cons (step482 p h) (sat_cons (step484 p h) (sat_cons (step1225 p h) (sat_cons (step1027 p h) (sat_cons (step1023 p h) (sat_cons (step1032 p h) (sat_nil p)))))))))
def c1591 : List Lit := [(67, false), (106, true), (107, false), (108, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c1529, c1430, c924, c1398, c1370, c1561, c1565, c1584, c1235, c355, c349, c984, c1211, c1415, c959, c997, c1589, c918, c963, c1104, c1590, c1137, c212, c211, c1337, c1423, c909, c906, c1566, c1078, c914, c1585, c919, c1109, c968] c1591 (by decide) p (sat_cons (step1529 p h) (sat_cons (step1430 p h) (sat_cons (step924 p h) (sat_cons (step1398 p h) (sat_cons (step1370 p h) (sat_cons (step1561 p h) (sat_cons (step1565 p h) (sat_cons (step1584 p h) (sat_cons (step1235 p h) (sat_cons (step355 p h) (sat_cons (step349 p h) (sat_cons (step984 p h) (sat_cons (step1211 p h) (sat_cons (step1415 p h) (sat_cons (step959 p h) (sat_cons (step997 p h) (sat_cons (step1589 p h) (sat_cons (step918 p h) (sat_cons (step963 p h) (sat_cons (step1104 p h) (sat_cons (step1590 p h) (sat_cons (step1137 p h) (sat_cons (step212 p h) (sat_cons (step211 p h) (sat_cons (step1337 p h) (sat_cons (step1423 p h) (sat_cons (step909 p h) (sat_cons (step906 p h) (sat_cons (step1566 p h) (sat_cons (step1078 p h) (sat_cons (step914 p h) (sat_cons (step1585 p h) (sat_cons (step919 p h) (sat_cons (step1109 p h) (sat_cons (step968 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1592 : List Lit := [(117, true), (1625, false), (67, true), (76, false), (103, true), (1486, false), (107, false)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1423, c1505, c1566, c1078, c212, c211, c1585, c909, c907, c1109, c917, c1575, c920] c1592 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1423 p h) (sat_cons (step1505 p h) (sat_cons (step1566 p h) (sat_cons (step1078 p h) (sat_cons (step212 p h) (sat_cons (step211 p h) (sat_cons (step1585 p h) (sat_cons (step909 p h) (sat_cons (step907 p h) (sat_cons (step1109 p h) (sat_cons (step917 p h) (sat_cons (step1575 p h) (sat_cons (step920 p h) (sat_nil p)))))))))))))))
def c1593 : List Lit := [(102, true), (106, true), (107, false), (108, false)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c1591, c905, c913, c918, c1573, c1529, c1530, c1149, c982, c1430, c924, c1398, c1370, c984, c990, c1415, c996, c997, c1592, c482, c484, c466, c483, c1137, c1023, c852, c1027, c1264, c1240, c1032, c876, c1225, c1566, c1099, c1585] c1593 (by decide) p (sat_cons (step1591 p h) (sat_cons (step905 p h) (sat_cons (step913 p h) (sat_cons (step918 p h) (sat_cons (step1573 p h) (sat_cons (step1529 p h) (sat_cons (step1530 p h) (sat_cons (step1149 p h) (sat_cons (step982 p h) (sat_cons (step1430 p h) (sat_cons (step924 p h) (sat_cons (step1398 p h) (sat_cons (step1370 p h) (sat_cons (step984 p h) (sat_cons (step990 p h) (sat_cons (step1415 p h) (sat_cons (step996 p h) (sat_cons (step997 p h) (sat_cons (step1592 p h) (sat_cons (step482 p h) (sat_cons (step484 p h) (sat_cons (step466 p h) (sat_cons (step483 p h) (sat_cons (step1137 p h) (sat_cons (step1023 p h) (sat_cons (step852 p h) (sat_cons (step1027 p h) (sat_cons (step1264 p h) (sat_cons (step1240 p h) (sat_cons (step1032 p h) (sat_cons (step876 p h) (sat_cons (step1225 p h) (sat_cons (step1566 p h) (sat_cons (step1099 p h) (sat_cons (step1585 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1594 : List Lit := [(117, false), (106, true), (107, false), (108, false)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c1370, c1561, c1565, c1584, c1591, c905, c913, c918, c1529, c1593, c360, c1211, c963, c1104, c364, c1009, c1016, c1530, c1430, c924, c484, c483, c1137, c1027, c1590, c1417, c985, c1367, c307, c992, c1360] c1594 (by decide) p (sat_cons (step1370 p h) (sat_cons (step1561 p h) (sat_cons (step1565 p h) (sat_cons (step1584 p h) (sat_cons (step1591 p h) (sat_cons (step905 p h) (sat_cons (step913 p h) (sat_cons (step918 p h) (sat_cons (step1529 p h) (sat_cons (step1593 p h) (sat_cons (step360 p h) (sat_cons (step1211 p h) (sat_cons (step963 p h) (sat_cons (step1104 p h) (sat_cons (step364 p h) (sat_cons (step1009 p h) (sat_cons (step1016 p h) (sat_cons (step1530 p h) (sat_cons (step1430 p h) (sat_cons (step924 p h) (sat_cons (step484 p h) (sat_cons (step483 p h) (sat_cons (step1137 p h) (sat_cons (step1027 p h) (sat_cons (step1590 p h) (sat_cons (step1417 p h) (sat_cons (step985 p h) (sat_cons (step1367 p h) (sat_cons (step307 p h) (sat_cons (step992 p h) (sat_cons (step1360 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1595 : List Lit := [(106, true), (107, false), (108, false)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c1430, c924, c1398, c1370, c1529, c1530, c1149, c982, c989, c995, c1591, c1593, c360, c1211, c1594, c1337, c1423, c1505, c1566, c1064, c212, c211, c1585, c909, c907, c1118, c1381, c917, c977, c920, c975, c973, c1519, c245, c950, c244, c939, c937, c947] c1595 (by decide) p (sat_cons (step1430 p h) (sat_cons (step924 p h) (sat_cons (step1398 p h) (sat_cons (step1370 p h) (sat_cons (step1529 p h) (sat_cons (step1530 p h) (sat_cons (step1149 p h) (sat_cons (step982 p h) (sat_cons (step989 p h) (sat_cons (step995 p h) (sat_cons (step1591 p h) (sat_cons (step1593 p h) (sat_cons (step360 p h) (sat_cons (step1211 p h) (sat_cons (step1594 p h) (sat_cons (step1337 p h) (sat_cons (step1423 p h) (sat_cons (step1505 p h) (sat_cons (step1566 p h) (sat_cons (step1064 p h) (sat_cons (step212 p h) (sat_cons (step211 p h) (sat_cons (step1585 p h) (sat_cons (step909 p h) (sat_cons (step907 p h) (sat_cons (step1118 p h) (sat_cons (step1381 p h) (sat_cons (step917 p h) (sat_cons (step977 p h) (sat_cons (step920 p h) (sat_cons (step975 p h) (sat_cons (step973 p h) (sat_cons (step1519 p h) (sat_cons (step245 p h) (sat_cons (step950 p h) (sat_cons (step244 p h) (sat_cons (step939 p h) (sat_cons (step937 p h) (sat_cons (step947 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1596 : List Lit := [(117, true), (1620, false), (1558, false), (1588, false), (106, false), (76, false), (103, true), (1486, false), (107, false)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1423, c1505, c1566, c211, c418, c1585, c906, c1519, c914, c975, c919, c977, c968, c1001, c1109, c1078] c1596 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1423 p h) (sat_cons (step1505 p h) (sat_cons (step1566 p h) (sat_cons (step211 p h) (sat_cons (step418 p h) (sat_cons (step1585 p h) (sat_cons (step906 p h) (sat_cons (step1519 p h) (sat_cons (step914 p h) (sat_cons (step975 p h) (sat_cons (step919 p h) (sat_cons (step977 p h) (sat_cons (step968 p h) (sat_cons (step1001 p h) (sat_cons (step1109 p h) (sat_cons (step1078 p h) (sat_nil p))))))))))))))))))
def c1597 : List Lit := [(107, false), (108, false)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c1370, c1398, c1430, c924, c1595, c391, c407, c401, c410, c411, c1402, c1215, c909, c981, c984, c911, c990, c918, c963, c1596, c478, c482, c484, c466, c483, c416, c975, c1023, c852, c1027, c1465, c977, c1240, c1032, c825, c1001, c1037, c827, c1078, c845, c1102, c879, c1586, c1567] c1597 (by decide) p (sat_cons (step1370 p h) (sat_cons (step1398 p h) (sat_cons (step1430 p h) (sat_cons (step924 p h) (sat_cons (step1595 p h) (sat_cons (step391 p h) (sat_cons (step407 p h) (sat_cons (step401 p h) (sat_cons (step410 p h) (sat_cons (step411 p h) (sat_cons (step1402 p h) (sat_cons (step1215 p h) (sat_cons (step909 p h) (sat_cons (step981 p h) (sat_cons (step984 p h) (sat_cons (step911 p h) (sat_cons (step990 p h) (sat_cons (step918 p h) (sat_cons (step963 p h) (sat_cons (step1596 p h) (sat_cons (step478 p h) (sat_cons (step482 p h) (sat_cons (step484 p h) (sat_cons (step466 p h) (sat_cons (step483 p h) (sat_cons (step416 p h) (sat_cons (step975 p h) (sat_cons (step1023 p h) (sat_cons (step852 p h) (sat_cons (step1027 p h) (sat_cons (step1465 p h) (sat_cons (step977 p h) (sat_cons (step1240 p h) (sat_cons (step1032 p h) (sat_cons (step825 p h) (sat_cons (step1001 p h) (sat_cons (step1037 p h) (sat_cons (step827 p h) (sat_cons (step1078 p h) (sat_cons (step845 p h) (sat_cons (step1102 p h) (sat_cons (step879 p h) (sat_cons (step1586 p h) (sat_cons (step1567 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c1598 : List Lit := [(1644, false), (102, true), (1625, false), (1612, false), (1588, false), (69, true), (1615, false), (1679, true), (107, true)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c909, c911, c918, c963, c1104, c1080, c1008, c1016, c1042, c1047, c1085, c1079, c1019, c1002, c1110, c1010, c991, c968, c986, c919, c1238, c914, c906] c1598 (by decide) p (sat_cons (step909 p h) (sat_cons (step911 p h) (sat_cons (step918 p h) (sat_cons (step963 p h) (sat_cons (step1104 p h) (sat_cons (step1080 p h) (sat_cons (step1008 p h) (sat_cons (step1016 p h) (sat_cons (step1042 p h) (sat_cons (step1047 p h) (sat_cons (step1085 p h) (sat_cons (step1079 p h) (sat_cons (step1019 p h) (sat_cons (step1002 p h) (sat_cons (step1110 p h) (sat_cons (step1010 p h) (sat_cons (step991 p h) (sat_cons (step968 p h) (sat_cons (step986 p h) (sat_cons (step919 p h) (sat_cons (step1238 p h) (sat_cons (step914 p h) (sat_cons (step906 p h) (sat_nil p))))))))))))))))))))))))
def c1599 : List Lit := [(1641, false), (112, false), (1644, true), (102, true), (1612, false), (1597, false), (1615, false), (1486, false), (76, false), (117, false)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c1029, c1032, c1023, c1162, c1537, c1262, c444, c1002, c986, c991] c1599 (by decide) p (sat_cons (step1029 p h) (sat_cons (step1032 p h) (sat_cons (step1023 p h) (sat_cons (step1162 p h) (sat_cons (step1537 p h) (sat_cons (step1262 p h) (sat_cons (step444 p h) (sat_cons (step1002 p h) (sat_cons (step986 p h) (sat_cons (step991 p h) (sat_nil p)))))))))))
def c1600 : List Lit := [(118, true), (102, true), (1625, false), (1612, false), (1588, false), (1648, false), (69, true), (1615, false), (1486, false), (76, false), (117, false), (107, true)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1565, c1584, c1598, c1078, c909, c911, c918, c963, c1025, c1224, c1599, c1027, c468, c485, c852, c1023, c1240, c1031, c876, c1566, c1585, c1103, c1109, c1084, c1079, c968, c1002, c1046, c919, c991, c1019, c914, c986, c1010, c906, c1238] c1600 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1565 p h) (sat_cons (step1584 p h) (sat_cons (step1598 p h) (sat_cons (step1078 p h) (sat_cons (step909 p h) (sat_cons (step911 p h) (sat_cons (step918 p h) (sat_cons (step963 p h) (sat_cons (step1025 p h) (sat_cons (step1224 p h) (sat_cons (step1599 p h) (sat_cons (step1027 p h) (sat_cons (step468 p h) (sat_cons (step485 p h) (sat_cons (step852 p h) (sat_cons (step1023 p h) (sat_cons (step1240 p h) (sat_cons (step1031 p h) (sat_cons (step876 p h) (sat_cons (step1566 p h) (sat_cons (step1585 p h) (sat_cons (step1103 p h) (sat_cons (step1109 p h) (sat_cons (step1084 p h) (sat_cons (step1079 p h) (sat_cons (step968 p h) (sat_cons (step1002 p h) (sat_cons (step1046 p h) (sat_cons (step919 p h) (sat_cons (step991 p h) (sat_cons (step1019 p h) (sat_cons (step914 p h) (sat_cons (step986 p h) (sat_cons (step1010 p h) (sat_cons (step906 p h) (sat_cons (step1238 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c1601 : List Lit := [(102, true), (1625, false), (1612, false), (1588, false), (1648, false), (69, true), (1615, false), (1486, false), (76, false), (117, false), (107, true)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c1078, c909, c911, c918, c963, c1600, c487, c486, c469, c1026, c1023, c852, c1031, c1240, c876, c1566, c1585, c1103, c1109, c1084, c1079, c968, c1002, c1046, c919, c991, c1019, c914, c986, c1010, c906, c1238] c1601 (by decide) p (sat_cons (step1078 p h) (sat_cons (step909 p h) (sat_cons (step911 p h) (sat_cons (step918 p h) (sat_cons (step963 p h) (sat_cons (step1600 p h) (sat_cons (step487 p h) (sat_cons (step486 p h) (sat_cons (step469 p h) (sat_cons (step1026 p h) (sat_cons (step1023 p h) (sat_cons (step852 p h) (sat_cons (step1031 p h) (sat_cons (step1240 p h) (sat_cons (step876 p h) (sat_cons (step1566 p h) (sat_cons (step1585 p h) (sat_cons (step1103 p h) (sat_cons (step1109 p h) (sat_cons (step1084 p h) (sat_cons (step1079 p h) (sat_cons (step968 p h) (sat_cons (step1002 p h) (sat_cons (step1046 p h) (sat_cons (step919 p h) (sat_cons (step991 p h) (sat_cons (step1019 p h) (sat_cons (step914 p h) (sat_cons (step986 p h) (sat_cons (step1010 p h) (sat_cons (step906 p h) (sat_cons (step1238 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1602 : List Lit := [(118, false), (112, true), (1625, false), (1597, false), (1486, false), (76, false), (117, false), (1634, false)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c487, c486, c469, c1026, c1024, c852, c1034, c1240, c1042, c876, c1079, c1566, c1103, c1585] c1602 (by decide) p (sat_cons (step487 p h) (sat_cons (step486 p h) (sat_cons (step469 p h) (sat_cons (step1026 p h) (sat_cons (step1024 p h) (sat_cons (step852 p h) (sat_cons (step1034 p h) (sat_cons (step1240 p h) (sat_cons (step1042 p h) (sat_cons (step876 p h) (sat_cons (step1079 p h) (sat_cons (step1566 p h) (sat_cons (step1103 p h) (sat_cons (step1585 p h) (sat_nil p)))))))))))))))
def c1603 : List Lit := [(97, false), (100, false), (1625, false), (1588, false), (69, true), (1486, false), (76, false), (117, false), (108, false)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1565, c1584, c909, c911, c918, c963, c1104, c1080, c1597, c1008, c1016, c303, c1602, c1224, c1042, c1047, c1079, c1019, c1017, c1110, c1010, c1011, c968, c294, c919, c922, c912, c914, c904, c910, c905, c906, c903, c185, c205, c1492] c1603 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1565 p h) (sat_cons (step1584 p h) (sat_cons (step909 p h) (sat_cons (step911 p h) (sat_cons (step918 p h) (sat_cons (step963 p h) (sat_cons (step1104 p h) (sat_cons (step1080 p h) (sat_cons (step1597 p h) (sat_cons (step1008 p h) (sat_cons (step1016 p h) (sat_cons (step303 p h) (sat_cons (step1602 p h) (sat_cons (step1224 p h) (sat_cons (step1042 p h) (sat_cons (step1047 p h) (sat_cons (step1079 p h) (sat_cons (step1019 p h) (sat_cons (step1017 p h) (sat_cons (step1110 p h) (sat_cons (step1010 p h) (sat_cons (step1011 p h) (sat_cons (step968 p h) (sat_cons (step294 p h) (sat_cons (step919 p h) (sat_cons (step922 p h) (sat_cons (step912 p h) (sat_cons (step914 p h) (sat_cons (step904 p h) (sat_cons (step910 p h) (sat_cons (step905 p h) (sat_cons (step906 p h) (sat_cons (step903 p h) (sat_cons (step185 p h) (sat_cons (step205 p h) (sat_cons (step1492 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
end B112E104
