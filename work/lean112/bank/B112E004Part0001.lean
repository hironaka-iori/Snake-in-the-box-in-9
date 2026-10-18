import B112E004Part0000
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1798 : List Lit := [(1666, false), (108, true), (1682, true)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c833, c1546, c1589, c1556, c1559, c1586, c1548, c1566, c1568, c1564, c1560, c758, c746] c1798 (by decide) p (sat_cons (step833 p h) (sat_cons (step1546 p h) (sat_cons (step1589 p h) (sat_cons (step1556 p h) (sat_cons (step1559 p h) (sat_cons (step1586 p h) (sat_cons (step1548 p h) (sat_cons (step1566 p h) (sat_cons (step1568 p h) (sat_cons (step1564 p h) (sat_cons (step1560 p h) (sat_cons (step758 p h) (sat_cons (step746 p h) (sat_nil p))))))))))))))
def c1799 : List Lit := [(1463, false), (1479, true)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c1768, c784, c789, c1167, c1138, c1141, c1165, c1132, c1133, c1157, c72, c67, c1146, c1148, c1155, c1149, c1150, c104, c92] c1799 (by decide) p (sat_cons (step1768 p h) (sat_cons (step784 p h) (sat_cons (step789 p h) (sat_cons (step1167 p h) (sat_cons (step1138 p h) (sat_cons (step1141 p h) (sat_cons (step1165 p h) (sat_cons (step1132 p h) (sat_cons (step1133 p h) (sat_cons (step1157 p h) (sat_cons (step72 p h) (sat_cons (step67 p h) (sat_cons (step1146 p h) (sat_cons (step1148 p h) (sat_cons (step1155 p h) (sat_cons (step1149 p h) (sat_cons (step1150 p h) (sat_cons (step104 p h) (sat_cons (step92 p h) (sat_nil p))))))))))))))))))))
def c1800 : List Lit := [(26, true), (1474, true), (30, false), (21, false)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c790, c1157, c1146, c1148, c1155, c119, c1150, c137, c92] c1800 (by decide) p (sat_cons (step790 p h) (sat_cons (step1157 p h) (sat_cons (step1146 p h) (sat_cons (step1148 p h) (sat_cons (step1155 p h) (sat_cons (step119 p h) (sat_cons (step1150 p h) (sat_cons (step137 p h) (sat_cons (step92 p h) (sat_nil p))))))))))
def c1801 : List Lit := [(1474, true), (30, false), (21, false)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c790, c1800, c1778, c1150, c1155, c1147, c119, c91, c137] c1801 (by decide) p (sat_cons (step790 p h) (sat_cons (step1800 p h) (sat_cons (step1778 p h) (sat_cons (step1150 p h) (sat_cons (step1155 p h) (sat_cons (step1147 p h) (sat_cons (step119 p h) (sat_cons (step91 p h) (sat_cons (step137 p h) (sat_nil p))))))))))
def c1802 : List Lit := [(116, false), (117, false), (106, false)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c833, c758, c746] c1802 (by decide) p (sat_cons (step833 p h) (sat_cons (step758 p h) (sat_cons (step746 p h) (sat_nil p))))
def c1803 : List Lit := [(1505, false), (39, false), (51, false), (1514, true)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c1222, c1215, c1216, c1226, c1211, c1202, c206, c1200] c1803 (by decide) p (sat_cons (step1222 p h) (sat_cons (step1215 p h) (sat_cons (step1216 p h) (sat_cons (step1226 p h) (sat_cons (step1211 p h) (sat_cons (step1202 p h) (sat_cons (step206 p h) (sat_cons (step1200 p h) (sat_nil p)))))))))
def c1804 : List Lit := [(39, false), (1514, true), (51, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c1803, c1207, c212, c204, c1211, c1200, c1213, c1202, c1226] c1804 (by decide) p (sat_cons (step1803 p h) (sat_cons (step1207 p h) (sat_cons (step212 p h) (sat_cons (step204 p h) (sat_cons (step1211 p h) (sat_cons (step1200 p h) (sat_cons (step1213 p h) (sat_cons (step1202 p h) (sat_cons (step1226 p h) (sat_nil p))))))))))
def c1805 : List Lit := [(1532, false), (1548, true), (1521, false), (43, true), (37, true)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c1772, c792, c796, c1250, c1293, c1278, c1264, c1277, c1282, c1300, c1251, c1243, c1804, c161, c1200, c1202, c1226, c1213, c1211, c243, c395, c396, c1255] c1805 (by decide) p (sat_cons (step1772 p h) (sat_cons (step792 p h) (sat_cons (step796 p h) (sat_cons (step1250 p h) (sat_cons (step1293 p h) (sat_cons (step1278 p h) (sat_cons (step1264 p h) (sat_cons (step1277 p h) (sat_cons (step1282 p h) (sat_cons (step1300 p h) (sat_cons (step1251 p h) (sat_cons (step1243 p h) (sat_cons (step1804 p h) (sat_cons (step161 p h) (sat_cons (step1200 p h) (sat_cons (step1202 p h) (sat_cons (step1226 p h) (sat_cons (step1213 p h) (sat_cons (step1211 p h) (sat_cons (step243 p h) (sat_cons (step395 p h) (sat_cons (step396 p h) (sat_cons (step1255 p h) (sat_nil p))))))))))))))))))))))))
def c1806 : List Lit := [(39, true), (1514, true), (1528, true), (43, true), (37, true)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c792, c796, c1254, c1253, c161, c1200, c1202, c1226, c1213, c1211, c243, c398] c1806 (by decide) p (sat_cons (step792 p h) (sat_cons (step796 p h) (sat_cons (step1254 p h) (sat_cons (step1253 p h) (sat_cons (step161 p h) (sat_cons (step1200 p h) (sat_cons (step1202 p h) (sat_cons (step1226 p h) (sat_cons (step1213 p h) (sat_cons (step1211 p h) (sat_cons (step243 p h) (sat_cons (step398 p h) (sat_nil p)))))))))))))
def c1807 : List Lit := [(35, true), (55, true), (52, false), (1514, true), (53, false)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c801, c1230, c1203, c1200, c1201, c1202, c1226, c1213, c1210, c348, c270, c386] c1807 (by decide) p (sat_cons (step801 p h) (sat_cons (step1230 p h) (sat_cons (step1203 p h) (sat_cons (step1200 p h) (sat_cons (step1201 p h) (sat_cons (step1202 p h) (sat_cons (step1226 p h) (sat_cons (step1213 p h) (sat_cons (step1210 p h) (sat_cons (step348 p h) (sat_cons (step270 p h) (sat_cons (step386 p h) (sat_nil p)))))))))))))
def c1808 : List Lit := [(1505, false), (34, false), (35, false), (1514, true)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c1222, c1215, c1216, c1226, c1210, c1202, c153, c1199] c1808 (by decide) p (sat_cons (step1222 p h) (sat_cons (step1215 p h) (sat_cons (step1216 p h) (sat_cons (step1226 p h) (sat_cons (step1210 p h) (sat_cons (step1202 p h) (sat_cons (step153 p h) (sat_cons (step1199 p h) (sat_nil p)))))))))
def c1809 : List Lit := [(1514, true), (1528, true), (1523, true), (43, true), (37, true)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c792, c1254, c1253, c1222, c1214, c1806, c1804, c1244, c436, c1807, c163, c1808, c1207, c203, c1211, c1212, c1213, c153, c1226, c1199, c1202] c1809 (by decide) p (sat_cons (step792 p h) (sat_cons (step1254 p h) (sat_cons (step1253 p h) (sat_cons (step1222 p h) (sat_cons (step1214 p h) (sat_cons (step1806 p h) (sat_cons (step1804 p h) (sat_cons (step1244 p h) (sat_cons (step436 p h) (sat_cons (step1807 p h) (sat_cons (step163 p h) (sat_cons (step1808 p h) (sat_cons (step1207 p h) (sat_cons (step203 p h) (sat_cons (step1211 p h) (sat_cons (step1212 p h) (sat_cons (step1213 p h) (sat_cons (step153 p h) (sat_cons (step1226 p h) (sat_cons (step1199 p h) (sat_cons (step1202 p h) (sat_nil p))))))))))))))))))))))
def c1810 : List Lit := [(35, false), (45, false), (47, false), (51, false), (1511, true), (37, true)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c792, c161, c163, c204, c206, c263, c1207, c1212, c1217] c1810 (by decide) p (sat_cons (step792 p h) (sat_cons (step161 p h) (sat_cons (step163 p h) (sat_cons (step204 p h) (sat_cons (step206 p h) (sat_cons (step263 p h) (sat_cons (step1207 p h) (sat_cons (step1212 p h) (sat_cons (step1217 p h) (sat_nil p))))))))))
def c1811 : List Lit := [(44, true), (1510, true), (54, true), (51, false), (43, true)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c796, c1214, c1210, c1212, c1216, c243, c1207, c212] c1811 (by decide) p (sat_cons (step796 p h) (sat_cons (step1214 p h) (sat_cons (step1210 p h) (sat_cons (step1212 p h) (sat_cons (step1216 p h) (sat_cons (step243 p h) (sat_cons (step1207 p h) (sat_cons (step212 p h) (sat_nil p)))))))))
def c1812 : List Lit := [(1548, true), (1521, false), (43, true), (37, true)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c1772, c802, c801, c796, c1250, c1276, c1293, c1307, c1286, c1223, c1252, c1805, c1261, c1253, c1254, c1809, c1300, c1281, c1251, c1242, c1243, c436, c401, c354, c392, c386, c1810, c1200, c1202, c1227, c1811, c270, c1201, c1203, c1231, c1213, c1215, c1211, c1207, c243, c212] c1812 (by decide) p (sat_cons (step1772 p h) (sat_cons (step802 p h) (sat_cons (step801 p h) (sat_cons (step796 p h) (sat_cons (step1250 p h) (sat_cons (step1276 p h) (sat_cons (step1293 p h) (sat_cons (step1307 p h) (sat_cons (step1286 p h) (sat_cons (step1223 p h) (sat_cons (step1252 p h) (sat_cons (step1805 p h) (sat_cons (step1261 p h) (sat_cons (step1253 p h) (sat_cons (step1254 p h) (sat_cons (step1809 p h) (sat_cons (step1300 p h) (sat_cons (step1281 p h) (sat_cons (step1251 p h) (sat_cons (step1242 p h) (sat_cons (step1243 p h) (sat_cons (step436 p h) (sat_cons (step401 p h) (sat_cons (step354 p h) (sat_cons (step392 p h) (sat_cons (step386 p h) (sat_cons (step1810 p h) (sat_cons (step1200 p h) (sat_cons (step1202 p h) (sat_cons (step1227 p h) (sat_cons (step1811 p h) (sat_cons (step270 p h) (sat_cons (step1201 p h) (sat_cons (step1203 p h) (sat_cons (step1231 p h) (sat_cons (step1213 p h) (sat_cons (step1215 p h) (sat_cons (step1211 p h) (sat_cons (step1207 p h) (sat_cons (step243 p h) (sat_cons (step212 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c1813 : List Lit := [(1675, true)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c833, c1566, c1568, c1564, c1560, c1561, c758, c747] c1813 (by decide) p (sat_cons (step833 p h) (sat_cons (step1566 p h) (sat_cons (step1568 p h) (sat_cons (step1564 p h) (sat_cons (step1560 p h) (sat_cons (step1561 p h) (sat_cons (step758 p h) (sat_cons (step747 p h) (sat_nil p)))))))))
def c1814 : List Lit := [(1679, true)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1574] c1814 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1574 p h) (sat_nil p)))
def c1815 : List Lit := [(1610, true), (88, false), (38, false)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c1428, c1429, c581] c1815 (by decide) p (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step581 p h) (sat_nil p))))
def c1816 : List Lit := [(1590, true), (66, true), (73, true), (50, true), (51, false)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c811, c1388, c1392, c1394, c1390, c1386, c518, c524] c1816 (by decide) p (sat_cons (step811 p h) (sat_cons (step1388 p h) (sat_cons (step1392 p h) (sat_cons (step1394 p h) (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step518 p h) (sat_cons (step524 p h) (sat_nil p)))))))))
def c1817 : List Lit := [(1692, false), (1618, false), (1590, false), (1514, false), (1714, true), (1488, false), (1528, false), (1525, false)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1400, c1473, c1646, c1652, c1670, c1480, c1346, c1405, c1301, c1380, c1278, c1377, c1262, c1789] c1817 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1400 p h) (sat_cons (step1473 p h) (sat_cons (step1646 p h) (sat_cons (step1652 p h) (sat_cons (step1670 p h) (sat_cons (step1480 p h) (sat_cons (step1346 p h) (sat_cons (step1405 p h) (sat_cons (step1301 p h) (sat_cons (step1380 p h) (sat_cons (step1278 p h) (sat_cons (step1377 p h) (sat_cons (step1262 p h) (sat_cons (step1789 p h) (sat_nil p))))))))))))))))
def c1818 : List Lit := [(1657, true), (100, false), (1649, false), (52, false), (1641, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1517, c1503, c1531, c1535, c1520, c1506, c1512, c1497, c659] c1818 (by decide) p (sat_cons (step1517 p h) (sat_cons (step1503 p h) (sat_cons (step1531 p h) (sat_cons (step1535 p h) (sat_cons (step1520 p h) (sat_cons (step1506 p h) (sat_cons (step1512 p h) (sat_cons (step1497 p h) (sat_cons (step659 p h) (sat_nil p))))))))))
def c1819 : List Lit := [(1644, true), (100, false), (52, false), (97, true)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1504, c1506, c1502, c1497, c658] c1819 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1504 p h) (sat_cons (step1506 p h) (sat_cons (step1502 p h) (sat_cons (step1497 p h) (sat_cons (step658 p h) (sat_nil p)))))))
def c1820 : List Lit := [(98, false), (100, false), (1648, true), (1680, true), (52, false)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1813, c835, c1577, c1552, c1550, c1549, c1575, c1567, c662, c664, c1513, c1565, c736, c772, c774] c1820 (by decide) p (sat_cons (step1813 p h) (sat_cons (step835 p h) (sat_cons (step1577 p h) (sat_cons (step1552 p h) (sat_cons (step1550 p h) (sat_cons (step1549 p h) (sat_cons (step1575 p h) (sat_cons (step1567 p h) (sat_cons (step662 p h) (sat_cons (step664 p h) (sat_cons (step1513 p h) (sat_cons (step1565 p h) (sat_cons (step736 p h) (sat_cons (step772 p h) (sat_cons (step774 p h) (sat_nil p))))))))))))))))
def c1821 : List Lit := [(105, false), (1663, true)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c827, c1547, c1546, c713, c718] c1821 (by decide) p (sat_cons (step827 p h) (sat_cons (step1547 p h) (sat_cons (step1546 p h) (sat_cons (step713 p h) (sat_cons (step718 p h) (sat_nil p))))))
def c1822 : List Lit := [(114, true), (1680, true)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1577, c1554, c1547, c1575, c1571, c1561, c1562, c1569, c1802, c1564] c1822 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1577 p h) (sat_cons (step1554 p h) (sat_cons (step1547 p h) (sat_cons (step1575 p h) (sat_cons (step1571 p h) (sat_cons (step1561 p h) (sat_cons (step1562 p h) (sat_cons (step1569 p h) (sat_cons (step1802 p h) (sat_cons (step1564 p h) (sat_nil p))))))))))))
def c1823 : List Lit := [(1550, false), (1455, false), (1613, false), (1594, false), (1570, true), (1691, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1796, c1677, c1188, c1356, c1347, c1189, c1671, c1774, c1645, c1420, c1473, c1445] c1823 (by decide) p (sat_cons (step1796 p h) (sat_cons (step1677 p h) (sat_cons (step1188 p h) (sat_cons (step1356 p h) (sat_cons (step1347 p h) (sat_cons (step1189 p h) (sat_cons (step1671 p h) (sat_cons (step1774 p h) (sat_cons (step1645 p h) (sat_cons (step1420 p h) (sat_cons (step1473 p h) (sat_cons (step1445 p h) (sat_nil p)))))))))))))
def c1824 : List Lit := [(1602, true), (109, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c815, c1417, c1418, c557, c546] c1824 (by decide) p (sat_cons (step815 p h) (sat_cons (step1417 p h) (sat_cons (step1418 p h) (sat_cons (step557 p h) (sat_cons (step546 p h) (sat_nil p))))))
def c1825 : List Lit := [(82, false), (1443, false), (1509, false), (1490, true), (1500, false), (1569, true), (1538, false), (15, true)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c815, c1109, c1112, c1125, c557, c558, c1686, c1136, c1799, c1189, c1194, c1355, c1126, c1308, c1113, c1231, c1111, c1205, c117] c1825 (by decide) p (sat_cons (step815 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1125 p h) (sat_cons (step557 p h) (sat_cons (step558 p h) (sat_cons (step1686 p h) (sat_cons (step1136 p h) (sat_cons (step1799 p h) (sat_cons (step1189 p h) (sat_cons (step1194 p h) (sat_cons (step1355 p h) (sat_cons (step1126 p h) (sat_cons (step1308 p h) (sat_cons (step1113 p h) (sat_cons (step1231 p h) (sat_cons (step1111 p h) (sat_cons (step1205 p h) (sat_cons (step117 p h) (sat_nil p))))))))))))))))))))
def c1826 : List Lit := [(80, false), (21, false), (109, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c814, c552, c544] c1826 (by decide) p (sat_cons (step814 p h) (sat_cons (step552 p h) (sat_cons (step544 p h) (sat_nil p))))
def c1827 : List Lit := [(21, false), (1603, true), (109, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c815, c1826, c1419, c557, c545] c1827 (by decide) p (sat_cons (step815 p h) (sat_cons (step1826 p h) (sat_cons (step1419 p h) (sat_cons (step557 p h) (sat_cons (step545 p h) (sat_nil p))))))
def c1828 : List Lit := [(1514, true), (36, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c792, c1199, c1202, c1230, c1226, c1203, c1213, c1215, c1201, c1211, c1207, c1208, c173, c161, c203] c1828 (by decide) p (sat_cons (step792 p h) (sat_cons (step1199 p h) (sat_cons (step1202 p h) (sat_cons (step1230 p h) (sat_cons (step1226 p h) (sat_cons (step1203 p h) (sat_cons (step1213 p h) (sat_cons (step1215 p h) (sat_cons (step1201 p h) (sat_cons (step1211 p h) (sat_cons (step1207 p h) (sat_cons (step1208 p h) (sat_cons (step173 p h) (sat_cons (step161 p h) (sat_cons (step203 p h) (sat_nil p))))))))))))))))
def c1829 : List Lit := [(1614, false), (1691, false), (1595, false), (109, false), (1454, false), (1548, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1796, c1677, c1182, c1335, c1668, c1660, c1482, c1824, c1420, c1451, c1446, c1421, c1481, c1827, c1655, c1136, c1669, c1799, c1345, c1183] c1829 (by decide) p (sat_cons (step1796 p h) (sat_cons (step1677 p h) (sat_cons (step1182 p h) (sat_cons (step1335 p h) (sat_cons (step1668 p h) (sat_cons (step1660 p h) (sat_cons (step1482 p h) (sat_cons (step1824 p h) (sat_cons (step1420 p h) (sat_cons (step1451 p h) (sat_cons (step1446 p h) (sat_cons (step1421 p h) (sat_cons (step1481 p h) (sat_cons (step1827 p h) (sat_cons (step1655 p h) (sat_cons (step1136 p h) (sat_cons (step1669 p h) (sat_cons (step1799 p h) (sat_cons (step1345 p h) (sat_cons (step1183 p h) (sat_nil p)))))))))))))))))))))
def c1830 : List Lit := [(1680, true), (1614, true), (109, false), (88, false), (38, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1813, c828, c1575, c1577, c1822, c1554, c1546, c1547, c1783, c720, c1435, c1425, c709, c716, c744, c745, c1560, c1564, c1569] c1830 (by decide) p (sat_cons (step1813 p h) (sat_cons (step828 p h) (sat_cons (step1575 p h) (sat_cons (step1577 p h) (sat_cons (step1822 p h) (sat_cons (step1554 p h) (sat_cons (step1546 p h) (sat_cons (step1547 p h) (sat_cons (step1783 p h) (sat_cons (step720 p h) (sat_cons (step1435 p h) (sat_cons (step1425 p h) (sat_cons (step709 p h) (sat_cons (step716 p h) (sat_cons (step744 p h) (sat_cons (step745 p h) (sat_cons (step1560 p h) (sat_cons (step1564 p h) (sat_cons (step1569 p h) (sat_nil p))))))))))))))))))))
def c1831 : List Lit := [(1671, true), (113, false), (106, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1561, c744] c1831 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1561 p h) (sat_cons (step744 p h) (sat_nil p))))
def c1832 : List Lit := [(1450, true), (1442, true), (21, false), (40, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c779, c1112, c1114, c1109, c1110, c1107, c10, c1785, c20, c1100, c21] c1832 (by decide) p (sat_cons (step779 p h) (sat_cons (step1112 p h) (sat_cons (step1114 p h) (sat_cons (step1109 p h) (sat_cons (step1110 p h) (sat_cons (step1107 p h) (sat_cons (step10 p h) (sat_cons (step1785 p h) (sat_cons (step20 p h) (sat_cons (step1100 p h) (sat_cons (step21 p h) (sat_nil p))))))))))))
def c1833 : List Lit := [(1649, false), (39, true), (1647, false), (1658, true), (97, true)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1503, c1532, c1523, c1520, c1795, c1536] c1833 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1503 p h) (sat_cons (step1532 p h) (sat_cons (step1523 p h) (sat_cons (step1520 p h) (sat_cons (step1795 p h) (sat_cons (step1536 p h) (sat_nil p))))))))
def c1834 : List Lit := [(105, false), (84, false), (109, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c827, c714, c708] c1834 (by decide) p (sat_cons (step827 p h) (sat_cons (step714 p h) (sat_cons (step708 p h) (sat_nil p))))
def c1835 : List Lit := [(1647, false), (1658, true), (97, true), (1649, false), (5, false), (40, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1520, c1833, c1536, c196, c1506, c1498] c1835 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1520 p h) (sat_cons (step1833 p h) (sat_cons (step1536 p h) (sat_cons (step196 p h) (sat_cons (step1506 p h) (sat_cons (step1498 p h) (sat_nil p))))))))
def c1836 : List Lit := [(15, true), (1451, true), (5, false), (40, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c779, c1113, c1109, c1111, c1115, c1107, c21, c7, c20] c1836 (by decide) p (sat_cons (step779 p h) (sat_cons (step1113 p h) (sat_cons (step1109 p h) (sat_cons (step1111 p h) (sat_cons (step1115 p h) (sat_cons (step1107 p h) (sat_cons (step21 p h) (sat_cons (step7 p h) (sat_cons (step20 p h) (sat_nil p))))))))))
def c1837 : List Lit := [(7, true), (39, true), (13, false), (5, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c778, c15, c13, c1679] c1837 (by decide) p (sat_cons (step778 p h) (sat_cons (step15 p h) (sat_cons (step13 p h) (sat_cons (step1679 p h) (sat_nil p)))))
def c1838 : List Lit := [(78, false), (83, false), (16, true), (101, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c813, c537, c542] c1838 (by decide) p (sat_cons (step813 p h) (sat_cons (step537 p h) (sat_cons (step542 p h) (sat_nil p))))
def c1839 : List Lit := [(1595, false), (1600, false), (1692, false), (1454, false), (1548, false), (1612, false), (109, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c1796, c1677, c1824, c1423, c1449, c1182, c1335, c1668, c1656, c1481, c1454, c1424, c1827, c1480, c1136, c1652, c1799, c1669, c1183, c1345] c1839 (by decide) p (sat_cons (step1796 p h) (sat_cons (step1677 p h) (sat_cons (step1824 p h) (sat_cons (step1423 p h) (sat_cons (step1449 p h) (sat_cons (step1182 p h) (sat_cons (step1335 p h) (sat_cons (step1668 p h) (sat_cons (step1656 p h) (sat_cons (step1481 p h) (sat_cons (step1454 p h) (sat_cons (step1424 p h) (sat_cons (step1827 p h) (sat_cons (step1480 p h) (sat_cons (step1136 p h) (sat_cons (step1652 p h) (sat_cons (step1799 p h) (sat_cons (step1669 p h) (sat_cons (step1183 p h) (sat_cons (step1345 p h) (sat_nil p)))))))))))))))))))))
def c1840 : List Lit := [(1582, true), (51, false), (40, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1382, c1792, c215] c1840 (by decide) p (sat_cons (step1382 p h) (sat_cons (step1792 p h) (sat_cons (step215 p h) (sat_nil p))))
def c1841 : List Lit := [(1454, true)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c1120, c1124, c1112, c1114, c1101, c1109, c1107, c1099, c1785] c1841 (by decide) p (sat_cons (step1120 p h) (sat_cons (step1124 p h) (sat_cons (step1112 p h) (sat_cons (step1114 p h) (sat_cons (step1101 p h) (sat_cons (step1109 p h) (sat_cons (step1107 p h) (sat_cons (step1099 p h) (sat_cons (step1785 p h) (sat_nil p))))))))))
def c1842 : List Lit := [(1487, true)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1796, c1182] c1842 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1796 p h) (sat_cons (step1182 p h) (sat_nil p))))
def c1843 : List Lit := [(1617, true), (1653, true), (1669, true), (78, false), (1604, false), (21, false), (16, true), (103, true)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c818, c827, c1448, c1444, c1421, c1431, c1433, c1827, c1428, c1429, c1425, c1426, c1550, c569, c1838, c1558, c576, c1512, c588, c1521, c1548, c1516, c714, c707] c1843 (by decide) p (sat_cons (step818 p h) (sat_cons (step827 p h) (sat_cons (step1448 p h) (sat_cons (step1444 p h) (sat_cons (step1421 p h) (sat_cons (step1431 p h) (sat_cons (step1433 p h) (sat_cons (step1827 p h) (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step1425 p h) (sat_cons (step1426 p h) (sat_cons (step1550 p h) (sat_cons (step569 p h) (sat_cons (step1838 p h) (sat_cons (step1558 p h) (sat_cons (step576 p h) (sat_cons (step1512 p h) (sat_cons (step588 p h) (sat_cons (step1521 p h) (sat_cons (step1548 p h) (sat_cons (step1516 p h) (sat_cons (step714 p h) (sat_cons (step707 p h) (sat_nil p)))))))))))))))))))))))))
def c1844 : List Lit := [(1657, true), (97, true), (1649, false)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c820, c1501, c1503, c1517, c1531, c1535, c1520, c1504, c1506, c1511, c1512, c1502, c1497, c1498, c656, c597, c616, c603] c1844 (by decide) p (sat_cons (step820 p h) (sat_cons (step1501 p h) (sat_cons (step1503 p h) (sat_cons (step1517 p h) (sat_cons (step1531 p h) (sat_cons (step1535 p h) (sat_cons (step1520 p h) (sat_cons (step1504 p h) (sat_cons (step1506 p h) (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step1502 p h) (sat_cons (step1497 p h) (sat_cons (step1498 p h) (sat_cons (step656 p h) (sat_cons (step597 p h) (sat_cons (step616 p h) (sat_cons (step603 p h) (sat_nil p)))))))))))))))))))
def c1845 : List Lit := [(1602, true), (21, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c815, c1417, c1418, c557, c543] c1845 (by decide) p (sat_cons (step815 p h) (sat_cons (step1417 p h) (sat_cons (step1418 p h) (sat_cons (step557 p h) (sat_cons (step543 p h) (sat_nil p))))))
def c1846 : List Lit := [(82, false), (21, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c815, c557, c558, c1686] c1846 (by decide) p (sat_cons (step815 p h) (sat_cons (step557 p h) (sat_cons (step558 p h) (sat_cons (step1686 p h) (sat_nil p)))))
def c1847 : List Lit := [(1548, true), (1532, false), (1521, false), (38, true)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c1772, c792, c1250, c1277, c1208, c1215, c1293, c1300, c1282, c1222, c1226, c1828, c1251, c1218, c1202, c1243, c1209, c1200, c1804, c171, c161] c1847 (by decide) p (sat_cons (step1772 p h) (sat_cons (step792 p h) (sat_cons (step1250 p h) (sat_cons (step1277 p h) (sat_cons (step1208 p h) (sat_cons (step1215 p h) (sat_cons (step1293 p h) (sat_cons (step1300 p h) (sat_cons (step1282 p h) (sat_cons (step1222 p h) (sat_cons (step1226 p h) (sat_cons (step1828 p h) (sat_cons (step1251 p h) (sat_cons (step1218 p h) (sat_cons (step1202 p h) (sat_cons (step1243 p h) (sat_cons (step1209 p h) (sat_cons (step1200 p h) (sat_cons (step1804 p h) (sat_cons (step171 p h) (sat_cons (step161 p h) (sat_nil p))))))))))))))))))))))
def c1848 : List Lit := [(1500, true), (39, true), (40, false)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c792, c1199, c1200, c171, c161] c1848 (by decide) p (sat_cons (step792 p h) (sat_cons (step1199 p h) (sat_cons (step1200 p h) (sat_cons (step171 p h) (sat_cons (step161 p h) (sat_nil p))))))
def c1849 : List Lit := [(1658, true), (1649, false), (100, false), (52, false), (97, true), (39, true)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c1517, c1540, c1833, c1512, c662, c659, c1502, c1497, c1507] c1849 (by decide) p (sat_cons (step1517 p h) (sat_cons (step1540 p h) (sat_cons (step1833 p h) (sat_cons (step1512 p h) (sat_cons (step662 p h) (sat_cons (step659 p h) (sat_cons (step1502 p h) (sat_cons (step1497 p h) (sat_cons (step1507 p h) (sat_nil p))))))))))
def c1850 : List Lit := [(1664, false), (120, false), (117, true), (102, false), (1682, true)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1586, c1557, c1558, c1582, c1549, c1567, c774, c1565] c1850 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1586 p h) (sat_cons (step1557 p h) (sat_cons (step1558 p h) (sat_cons (step1582 p h) (sat_cons (step1549 p h) (sat_cons (step1567 p h) (sat_cons (step774 p h) (sat_cons (step1565 p h) (sat_nil p))))))))))
def c1851 : List Lit := [(56, false), (1521, true), (49, false), (97, false)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c323, c326, c1241] c1851 (by decide) p (sat_cons (step323 p h) (sat_cons (step326 p h) (sat_cons (step1241 p h) (sat_nil p))))
def c1852 : List Lit := [(71, false), (50, true), (67, false), (32, false), (21, false), (51, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c811, c524, c124, c520] c1852 (by decide) p (sat_cons (step811 p h) (sat_cons (step524 p h) (sat_cons (step124 p h) (sat_cons (step520 p h) (sat_nil p)))))
def c1853 : List Lit := [(14, true), (39, true), (127, true), (5, false), (21, false), (1456, true), (12, true)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c778, c13, c14, c8, c9, c24, c1782] c1853 (by decide) p (sat_cons (step778 p h) (sat_cons (step13 p h) (sat_cons (step14 p h) (sat_cons (step8 p h) (sat_cons (step9 p h) (sat_cons (step24 p h) (sat_cons (step1782 p h) (sat_nil p))))))))
def c1854 : List Lit := [(13, true), (1452, true), (3, false), (12, true)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1106, c1116, c1110, c1111, c1118, c1785, c1108] c1854 (by decide) p (sat_cons (step1106 p h) (sat_cons (step1116 p h) (sat_cons (step1110 p h) (sat_cons (step1111 p h) (sat_cons (step1118 p h) (sat_cons (step1785 p h) (sat_cons (step1108 p h) (sat_nil p))))))))
def c1855 : List Lit := [(1489, true), (3, false), (51, false), (52, false), (12, true)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1796, c776, c786, c1739, c781, c1797, c1121, c1193, c1189, c1122, c1126, c1799, c1101, c1103, c1135, c1136, c1098, c3, c77, c38, c850, c853, c854, c858, c888, c940, c934, c910, c896, c895, c894, c150, c1854, c334, c9, c107, c48, c44] c1855 (by decide) p (sat_cons (step1796 p h) (sat_cons (step776 p h) (sat_cons (step786 p h) (sat_cons (step1739 p h) (sat_cons (step781 p h) (sat_cons (step1797 p h) (sat_cons (step1121 p h) (sat_cons (step1193 p h) (sat_cons (step1189 p h) (sat_cons (step1122 p h) (sat_cons (step1126 p h) (sat_cons (step1799 p h) (sat_cons (step1101 p h) (sat_cons (step1103 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step1098 p h) (sat_cons (step3 p h) (sat_cons (step77 p h) (sat_cons (step38 p h) (sat_cons (step850 p h) (sat_cons (step853 p h) (sat_cons (step854 p h) (sat_cons (step858 p h) (sat_cons (step888 p h) (sat_cons (step940 p h) (sat_cons (step934 p h) (sat_cons (step910 p h) (sat_cons (step896 p h) (sat_cons (step895 p h) (sat_cons (step894 p h) (sat_cons (step150 p h) (sat_cons (step1854 p h) (sat_cons (step334 p h) (sat_cons (step9 p h) (sat_cons (step107 p h) (sat_cons (step48 p h) (sat_cons (step44 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1856 : List Lit := [(22, true), (1468, true), (18, true), (21, true), (143, true)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c784, c1137, c81, c1145, c71, c1134] c1856 (by decide) p (sat_cons (step784 p h) (sat_cons (step1137 p h) (sat_cons (step81 p h) (sat_cons (step1145 p h) (sat_cons (step71 p h) (sat_cons (step1134 p h) (sat_nil p)))))))
def c1857 : List Lit := [(29, false), (1475, true), (32, false), (33, false), (13, false)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c789, c144, c110, c113, c103, c1147, c1151, c1156] c1857 (by decide) p (sat_cons (step789 p h) (sat_cons (step144 p h) (sat_cons (step110 p h) (sat_cons (step113 p h) (sat_cons (step103 p h) (sat_cons (step1147 p h) (sat_cons (step1151 p h) (sat_cons (step1156 p h) (sat_nil p)))))))))
def c1858 : List Lit := [(39, false), (1518, true), (36, true), (44, true), (5, false), (51, false), (38, true)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c194, c197, c190, c1209, c1212, c1201, c1220, c1203, c1234] c1858 (by decide) p (sat_cons (step194 p h) (sat_cons (step197 p h) (sat_cons (step190 p h) (sat_cons (step1209 p h) (sat_cons (step1212 p h) (sat_cons (step1201 p h) (sat_cons (step1220 p h) (sat_cons (step1203 p h) (sat_cons (step1234 p h) (sat_nil p))))))))))
def c1859 : List Lit := [(1690, true), (100, false), (52, false), (1641, false)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1813, c1503, c1603, c1818, c1514, c1515, c1821, c665, c1554, c1512, c1577, c1519, c1598, c1530] c1859 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1813 p h) (sat_cons (step1503 p h) (sat_cons (step1603 p h) (sat_cons (step1818 p h) (sat_cons (step1514 p h) (sat_cons (step1515 p h) (sat_cons (step1821 p h) (sat_cons (step665 p h) (sat_cons (step1554 p h) (sat_cons (step1512 p h) (sat_cons (step1577 p h) (sat_cons (step1519 p h) (sat_cons (step1598 p h) (sat_cons (step1530 p h) (sat_nil p))))))))))))))))
def c1860 : List Lit := [(1582, true), (6, true), (127, true), (13, false), (5, false), (51, false)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c1382, c1840, c200, c24, c1837] c1860 (by decide) p (sat_cons (step1382 p h) (sat_cons (step1840 p h) (sat_cons (step200 p h) (sat_cons (step24 p h) (sat_cons (step1837 p h) (sat_nil p))))))
def c1861 : List Lit := [(1612, true), (88, true)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c819, c1431, c1433, c1428, c1429, c1425, c580, c569] c1861 (by decide) p (sat_cons (step819 p h) (sat_cons (step1431 p h) (sat_cons (step1433 p h) (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step1425 p h) (sat_cons (step580 p h) (sat_cons (step569 p h) (sat_nil p)))))))))
end B112E004
