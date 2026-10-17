import B112E158Part0005
namespace B112E158
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1954 : List Lit := [(1558, true), (28, false), (21, false)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c1280, c1704, c99, c1780] c1954 (by decide) p (sat_cons (step1280 p h) (sat_cons (step1704 p h) (sat_cons (step99 p h) (sat_cons (step1780 p h) (sat_nil p)))))
def c1955 : List Lit := [(58, false), (1564, true), (28, false), (69, false)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c1609, c505, c1291, c1283] c1955 (by decide) p (sat_cons (step1609 p h) (sat_cons (step505 p h) (sat_cons (step1291 p h) (sat_cons (step1283 p h) (sat_nil p)))))
def c1956 : List Lit := [(48, false), (1564, true), (28, false), (69, false), (65, true)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c500, c501, c1281, c1283, c1291] c1956 (by decide) p (sat_cons (step500 p h) (sat_cons (step501 p h) (sat_cons (step1281 p h) (sat_cons (step1283 p h) (sat_cons (step1291 p h) (sat_nil p))))))
def c1957 : List Lit := [(1678, true), (1568, false), (1649, false), (1567, false)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c1920, c1494, c1749, c1361, c1386, c1726, c1618] c1957 (by decide) p (sat_cons (step1920 p h) (sat_cons (step1494 p h) (sat_cons (step1749 p h) (sat_cons (step1361 p h) (sat_cons (step1386 p h) (sat_cons (step1726 p h) (sat_cons (step1618 p h) (sat_nil p))))))))
def c1958 : List Lit := [(1628, true), (1621, false), (1583, true)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c1618, c1665, c1381, c1387, c1411, c1413, c1647, c1388, c1692] c1958 (by decide) p (sat_cons (step1618 p h) (sat_cons (step1665 p h) (sat_cons (step1381 p h) (sat_cons (step1387 p h) (sat_cons (step1411 p h) (sat_cons (step1413 p h) (sat_cons (step1647 p h) (sat_cons (step1388 p h) (sat_cons (step1692 p h) (sat_nil p))))))))))
def c1959 : List Lit := [(1464, true), (1423, false), (26, true), (24, true), (1448, false), (55, false)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c1023, c1656, c1088, c1083, c1024, c1058, c1011, c1054, c1008, c1044, c1765, c67] c1959 (by decide) p (sat_cons (step1023 p h) (sat_cons (step1656 p h) (sat_cons (step1088 p h) (sat_cons (step1083 p h) (sat_cons (step1024 p h) (sat_cons (step1058 p h) (sat_cons (step1011 p h) (sat_cons (step1054 p h) (sat_cons (step1008 p h) (sat_cons (step1044 p h) (sat_cons (step1765 p h) (sat_cons (step67 p h) (sat_nil p)))))))))))))
def c1960 : List Lit := [(25, true), (1457, true), (145, true), (24, true), (1448, false)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c1044, c123, c1054, c1771, c1063, c1035, c1037] c1960 (by decide) p (sat_cons (step1044 p h) (sat_cons (step123 p h) (sat_cons (step1054 p h) (sat_cons (step1771 p h) (sat_cons (step1063 p h) (sat_cons (step1035 p h) (sat_cons (step1037 p h) (sat_nil p))))))))
def c1961 : List Lit := [(23, true), (132, true), (22, true), (21, false)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c1775, c1773, c59, c1532] c1961 (by decide) p (sat_cons (step1775 p h) (sat_cons (step1773 p h) (sat_cons (step59 p h) (sat_cons (step1532 p h) (sat_nil p)))))
def c1962 : List Lit := [(1679, true), (1569, false), (1649, false)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c1920, c1949, c1500, c1381, c1367, c1665, c1726] c1962 (by decide) p (sat_cons (step1920 p h) (sat_cons (step1949 p h) (sat_cons (step1500 p h) (sat_cons (step1381 p h) (sat_cons (step1367 p h) (sat_cons (step1665 p h) (sat_cons (step1726 p h) (sat_nil p))))))))
def c1963 : List Lit := [(1435, true), (1428, false), (76, false), (193, true), (194, true), (22, true)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c1011, c1020, c1024, c1014, c1002, c1612, c1006, c556, c1759, c1843, c9, c559] c1963 (by decide) p (sat_cons (step1011 p h) (sat_cons (step1020 p h) (sat_cons (step1024 p h) (sat_cons (step1014 p h) (sat_cons (step1002 p h) (sat_cons (step1612 p h) (sat_cons (step1006 p h) (sat_cons (step556 p h) (sat_cons (step1759 p h) (sat_cons (step1843 p h) (sat_cons (step9 p h) (sat_cons (step559 p h) (sat_nil p)))))))))))))
def c1964 : List Lit := [(1543, true), (64, true), (53, false), (1464, false), (1463, false), (1508, false), (48, true), (44, true), (1497, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c1139, c1148, c1178, c1112, c1115, c1123, c1240, c1213, c1133, c1248, c1206, c1200, c1124, c1183, c1116, c1118, c1151, c1114, c1109, c1141, c1712] c1964 (by decide) p (sat_cons (step1139 p h) (sat_cons (step1148 p h) (sat_cons (step1178 p h) (sat_cons (step1112 p h) (sat_cons (step1115 p h) (sat_cons (step1123 p h) (sat_cons (step1240 p h) (sat_cons (step1213 p h) (sat_cons (step1133 p h) (sat_cons (step1248 p h) (sat_cons (step1206 p h) (sat_cons (step1200 p h) (sat_cons (step1124 p h) (sat_cons (step1183 p h) (sat_cons (step1116 p h) (sat_cons (step1118 p h) (sat_cons (step1151 p h) (sat_cons (step1114 p h) (sat_cons (step1109 p h) (sat_cons (step1141 p h) (sat_cons (step1712 p h) (sat_nil p))))))))))))))))))))))
def c1965 : List Lit := [(61, false), (62, true), (55, false), (64, true), (53, false)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c271, c1820] c1965 (by decide) p (sat_cons (step271 p h) (sat_cons (step1820 p h) (sat_nil p)))
def c1966 : List Lit := [(117, false), (1569, false), (1628, true), (1680, true), (44, false), (1649, false)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c1736, c1735, c1461, c1958, c1501, c1726, c1367] c1966 (by decide) p (sat_cons (step1736 p h) (sat_cons (step1735 p h) (sat_cons (step1461 p h) (sat_cons (step1958 p h) (sat_cons (step1501 p h) (sat_cons (step1726 p h) (sat_cons (step1367 p h) (sat_nil p))))))))
def c1967 : List Lit := [(1569, false), (118, true), (1628, true), (1680, true), (44, false), (1649, false)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c1916, c1496, c1966, c1434, c1708, c1921, c1462, c1501, c1403, c1409, c1367, c1385, c1726, c1692, c1665, c1647] c1967 (by decide) p (sat_cons (step1916 p h) (sat_cons (step1496 p h) (sat_cons (step1966 p h) (sat_cons (step1434 p h) (sat_cons (step1708 p h) (sat_cons (step1921 p h) (sat_cons (step1462 p h) (sat_cons (step1501 p h) (sat_cons (step1403 p h) (sat_cons (step1409 p h) (sat_cons (step1367 p h) (sat_cons (step1385 p h) (sat_cons (step1726 p h) (sat_cons (step1692 p h) (sat_cons (step1665 p h) (sat_cons (step1647 p h) (sat_nil p)))))))))))))))))
def c1968 : List Lit := [(55, false), (64, true), (53, false), (59, false), (61, false), (103, true), (31, true)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c271, c360, c1813] c1968 (by decide) p (sat_cons (step271 p h) (sat_cons (step360 p h) (sat_cons (step1813 p h) (sat_nil p))))
def c1969 : List Lit := [(112, true), (64, true), (1650, true), (103, true), (117, true)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c1708, c1434, c1433, c1444, c1441, c1872, c1869, c1686, c1430, c1415, c1438, c1423, c1447] c1969 (by decide) p (sat_cons (step1708 p h) (sat_cons (step1434 p h) (sat_cons (step1433 p h) (sat_cons (step1444 p h) (sat_cons (step1441 p h) (sat_cons (step1872 p h) (sat_cons (step1869 p h) (sat_cons (step1686 p h) (sat_cons (step1430 p h) (sat_cons (step1415 p h) (sat_cons (step1438 p h) (sat_cons (step1423 p h) (sat_cons (step1447 p h) (sat_nil p))))))))))))))
def c1970 : List Lit := [(1678, true), (1568, false), (1567, false), (44, false)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c1915, c1489, c1957, c1723, c1673, c1665, c1433, c1726, c1736, c1361, c1923, c1494] c1970 (by decide) p (sat_cons (step1915 p h) (sat_cons (step1489 p h) (sat_cons (step1957 p h) (sat_cons (step1723 p h) (sat_cons (step1673 p h) (sat_cons (step1665 p h) (sat_cons (step1433 p h) (sat_cons (step1726 p h) (sat_cons (step1736 p h) (sat_cons (step1361 p h) (sat_cons (step1923 p h) (sat_cons (step1494 p h) (sat_nil p)))))))))))))
def c1971 : List Lit := [(68, false), (1497, false), (1477, false), (39, true), (1525, true), (55, true), (118, false), (69, false)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c521, c527, c1705, c1158, c1160] c1971 (by decide) p (sat_cons (step521 p h) (sat_cons (step527 p h) (sat_cons (step1705 p h) (sat_cons (step1158 p h) (sat_cons (step1160 p h) (sat_nil p))))))
def c1972 : List Lit := [(1497, false), (1477, false), (39, true), (1525, true), (65, true), (55, true), (118, false), (69, false), (1564, true)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c1971, c1281, c1291, c1283, c528, c522, c1158, c1705, c1160] c1972 (by decide) p (sat_cons (step1971 p h) (sat_cons (step1281 p h) (sat_cons (step1291 p h) (sat_cons (step1283 p h) (sat_cons (step528 p h) (sat_cons (step522 p h) (sat_cons (step1158 p h) (sat_cons (step1705 p h) (sat_cons (step1160 p h) (sat_nil p))))))))))
def c1973 : List Lit := [(1497, true), (66, true), (101, false), (1554, true), (54, false)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c1142, c1143, c318, c1812, c289, c264, c1827, c1273] c1973 (by decide) p (sat_cons (step1142 p h) (sat_cons (step1143 p h) (sat_cons (step318 p h) (sat_cons (step1812 p h) (sat_cons (step289 p h) (sat_cons (step264 p h) (sat_cons (step1827 p h) (sat_cons (step1273 p h) (sat_nil p)))))))))
def c1974 : List Lit := [(1658, true), (44, false)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c1923, c1920, c1736, c1673, c1433] c1974 (by decide) p (sat_cons (step1923 p h) (sat_cons (step1920 p h) (sat_cons (step1736 p h) (sat_cons (step1673 p h) (sat_cons (step1433 p h) (sat_nil p))))))
def c1975 : List Lit := [(1680, true), (1570, false), (44, false)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c1917, c1974, c1501, c1505, c1723, c1373, c1665, c1726] c1975 (by decide) p (sat_cons (step1917 p h) (sat_cons (step1974 p h) (sat_cons (step1501 p h) (sat_cons (step1505 p h) (sat_cons (step1723 p h) (sat_cons (step1373 p h) (sat_cons (step1665 p h) (sat_cons (step1726 p h) (sat_nil p)))))))))
def c1976 : List Lit := [(1434, true), (1477, true)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c1104, c1102, c1106, c1023, c1721, c1002, c179] c1976 (by decide) p (sat_cons (step1104 p h) (sat_cons (step1102 p h) (sat_cons (step1106 p h) (sat_cons (step1023 p h) (sat_cons (step1721 p h) (sat_cons (step1002 p h) (sat_cons (step179 p h) (sat_nil p))))))))
def c1977 : List Lit := [(1485, true), (93, false), (1482, true), (39, true)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c1113, c1112, c1120, c1711, c1111, c229, c1799] c1977 (by decide) p (sat_cons (step1113 p h) (sat_cons (step1112 p h) (sat_cons (step1120 p h) (sat_cons (step1711 p h) (sat_cons (step1111 p h) (sat_cons (step229 p h) (sat_cons (step1799 p h) (sat_nil p))))))))
def c1978 : List Lit := [(1649, true), (55, false)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c1443, c1626, c1673, c1703, c1440, c1433, c1415, c1416, c656, c1678, c1863, c1418, c634, c1421, c1429, c1446, c1437] c1978 (by decide) p (sat_cons (step1443 p h) (sat_cons (step1626 p h) (sat_cons (step1673 p h) (sat_cons (step1703 p h) (sat_cons (step1440 p h) (sat_cons (step1433 p h) (sat_cons (step1415 p h) (sat_cons (step1416 p h) (sat_cons (step656 p h) (sat_cons (step1678 p h) (sat_cons (step1863 p h) (sat_cons (step1418 p h) (sat_cons (step634 p h) (sat_cons (step1421 p h) (sat_cons (step1429 p h) (sat_cons (step1446 p h) (sat_cons (step1437 p h) (sat_nil p))))))))))))))))))
def c1979 : List Lit := [(114, true), (1642, false), (1650, true)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c1444, c1441, c1429, c1431, c1438, c1447, c1421, c1423, c1418, c1416, c1868, c651] c1979 (by decide) p (sat_cons (step1444 p h) (sat_cons (step1441 p h) (sat_cons (step1429 p h) (sat_cons (step1431 p h) (sat_cons (step1438 p h) (sat_cons (step1447 p h) (sat_cons (step1421 p h) (sat_cons (step1423 p h) (sat_cons (step1418 p h) (sat_cons (step1416 p h) (sat_cons (step1868 p h) (sat_cons (step651 p h) (sat_nil p)))))))))))))
def c1980 : List Lit := [(107, false), (117, true), (55, false), (1650, true)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1979, c1444, c1441, c1686, c634, c1863] c1980 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1979 p h) (sat_cons (step1444 p h) (sat_cons (step1441 p h) (sat_cons (step1686 p h) (sat_cons (step634 p h) (sat_cons (step1863 p h) (sat_nil p))))))))
def c1981 : List Lit := [(55, false), (1659, true), (44, false)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c1921, c1978, c1461, c1736, c1433, c1435, c1450, c1426, c1980, c1415, c1417, c1423, c1424, c1447, c1418, c1438, c1868, c1430, c651] c1981 (by decide) p (sat_cons (step1921 p h) (sat_cons (step1978 p h) (sat_cons (step1461 p h) (sat_cons (step1736 p h) (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1450 p h) (sat_cons (step1426 p h) (sat_cons (step1980 p h) (sat_cons (step1415 p h) (sat_cons (step1417 p h) (sat_cons (step1423 p h) (sat_cons (step1424 p h) (sat_cons (step1447 p h) (sat_cons (step1418 p h) (sat_cons (step1438 p h) (sat_cons (step1868 p h) (sat_cons (step1430 p h) (sat_cons (step651 p h) (sat_nil p))))))))))))))))))))
def c1982 : List Lit := [(1650, true), (107, true), (1642, false)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c1415, c1423, c1435, c1450, c1447, c1426, c1424, c1438, c1417, c1418, c1430, c1868, c651] c1982 (by decide) p (sat_cons (step1415 p h) (sat_cons (step1423 p h) (sat_cons (step1435 p h) (sat_cons (step1450 p h) (sat_cons (step1447 p h) (sat_cons (step1426 p h) (sat_cons (step1424 p h) (sat_cons (step1438 p h) (sat_cons (step1417 p h) (sat_cons (step1418 p h) (sat_cons (step1430 p h) (sat_cons (step1868 p h) (sat_cons (step651 p h) (sat_nil p))))))))))))))
def c1983 : List Lit := [(110, false), (104, false), (111, false)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c1868, c651] c1983 (by decide) p (sat_cons (step1868 p h) (sat_cons (step651 p h) (sat_nil p)))
def c1984 : List Lit := [(1619, false), (1626, true)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c1403, c1395, c1398, c1406, c1389, c1384, c1386, c1382, c1616] c1984 (by decide) p (sat_cons (step1403 p h) (sat_cons (step1395 p h) (sat_cons (step1398 p h) (sat_cons (step1406 p h) (sat_cons (step1389 p h) (sat_cons (step1384 p h) (sat_cons (step1386 p h) (sat_cons (step1382 p h) (sat_cons (step1616 p h) (sat_nil p))))))))))
def c1985 : List Lit := [(52, true), (1428, true), (219, true), (102, false), (107, true)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c1009, c1008, c1860, c1763, c618, c47] c1985 (by decide) p (sat_cons (step1009 p h) (sat_cons (step1008 p h) (sat_cons (step1860 p h) (sat_cons (step1763 p h) (sat_cons (step618 p h) (sat_cons (step47 p h) (sat_nil p)))))))
def c1986 : List Lit := [(1485, false), (1544, true), (1516, false), (1455, false)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c1907, c1215, c1124, c1129, c1208, c1976, c1241, c1082] c1986 (by decide) p (sat_cons (step1907 p h) (sat_cons (step1215 p h) (sat_cons (step1124 p h) (sat_cons (step1129 p h) (sat_cons (step1208 p h) (sat_cons (step1976 p h) (sat_cons (step1241 p h) (sat_cons (step1082 p h) (sat_nil p)))))))))
def c1987 : List Lit := [(1484, true), (40, true), (44, false)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c1115, c1117, c1113, c1109, c242, c1799] c1987 (by decide) p (sat_cons (step1115 p h) (sat_cons (step1117 p h) (sat_cons (step1113 p h) (sat_cons (step1109 p h) (sat_cons (step242 p h) (sat_cons (step1799 p h) (sat_nil p)))))))
def c1988 : List Lit := [(1515, true), (52, true), (1495, false), (1506, false), (54, true)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c1147, c1153, c1163, c1175, c1179, c1166, c1148, c1155, c1142, c1650, c1812] c1988 (by decide) p (sat_cons (step1147 p h) (sat_cons (step1153 p h) (sat_cons (step1163 p h) (sat_cons (step1175 p h) (sat_cons (step1179 p h) (sat_cons (step1166 p h) (sat_cons (step1148 p h) (sat_cons (step1155 p h) (sat_cons (step1142 p h) (sat_cons (step1650 p h) (sat_cons (step1812 p h) (sat_nil p))))))))))))
def c1989 : List Lit := [(21, true), (1442, true), (24, true), (141, true)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c1036, c104, c1772] c1989 (by decide) p (sat_cons (step1036 p h) (sat_cons (step104 p h) (sat_cons (step1772 p h) (sat_nil p))))
def c1990 : List Lit := [(24, true), (1463, true), (1428, false), (403, true)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c1011, c1019, c1082, c857, c840, c837, c836, c1571, c1844, c842, c834, c833, c838, c835, c855, c853, c847, c844, c846, c845, c1043, c567, c1050, c1847, c1056, c571, c1087, c1846, c1024, c1963, c1000, c1652, c997] c1990 (by decide) p (sat_cons (step1011 p h) (sat_cons (step1019 p h) (sat_cons (step1082 p h) (sat_cons (step857 p h) (sat_cons (step840 p h) (sat_cons (step837 p h) (sat_cons (step836 p h) (sat_cons (step1571 p h) (sat_cons (step1844 p h) (sat_cons (step842 p h) (sat_cons (step834 p h) (sat_cons (step833 p h) (sat_cons (step838 p h) (sat_cons (step835 p h) (sat_cons (step855 p h) (sat_cons (step853 p h) (sat_cons (step847 p h) (sat_cons (step844 p h) (sat_cons (step846 p h) (sat_cons (step845 p h) (sat_cons (step1043 p h) (sat_cons (step567 p h) (sat_cons (step1050 p h) (sat_cons (step1847 p h) (sat_cons (step1056 p h) (sat_cons (step571 p h) (sat_cons (step1087 p h) (sat_cons (step1846 p h) (sat_cons (step1024 p h) (sat_cons (step1963 p h) (sat_cons (step1000 p h) (sat_cons (step1652 p h) (sat_cons (step997 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c1991 : List Lit := [(30, false), (1477, true), (44, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c1104, c1102, c1101, c1106, c150, c130, c175, c1785] c1991 (by decide) p (sat_cons (step1104 p h) (sat_cons (step1102 p h) (sat_cons (step1101 p h) (sat_cons (step1106 p h) (sat_cons (step150 p h) (sat_cons (step130 p h) (sat_cons (step175 p h) (sat_cons (step1785 p h) (sat_nil p)))))))))
def c1992 : List Lit := [(39, true), (1485, true), (93, false)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1977, c1118] c1992 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1977 p h) (sat_cons (step1118 p h) (sat_nil p))))
def c1993 : List Lit := [(1464, true), (37, true), (1448, false), (32, false), (1428, false)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c1656, c1011, c1019, c1083, c1088, c1637, c1024, c1688, c1000, c1002, c1751, c997, c1] c1993 (by decide) p (sat_cons (step1656 p h) (sat_cons (step1011 p h) (sat_cons (step1019 p h) (sat_cons (step1083 p h) (sat_cons (step1088 p h) (sat_cons (step1637 p h) (sat_cons (step1024 p h) (sat_cons (step1688 p h) (sat_cons (step1000 p h) (sat_cons (step1002 p h) (sat_cons (step1751 p h) (sat_cons (step997 p h) (sat_cons (step1 p h) (sat_nil p))))))))))))))
def c1994 : List Lit := [(54, false), (19, false), (13, false), (102, false)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c62, c306, c1762] c1994 (by decide) p (sat_cons (step62 p h) (sat_cons (step306 p h) (sat_cons (step1762 p h) (sat_nil p))))
def c1995 : List Lit := [(1633, false), (1651, true), (109, true)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c1454, c1419, c1427, c1453, c1428, c1435, c1437, c1420, c1433, c1429, c1699] c1995 (by decide) p (sat_cons (step1454 p h) (sat_cons (step1419 p h) (sat_cons (step1427 p h) (sat_cons (step1453 p h) (sat_cons (step1428 p h) (sat_cons (step1435 p h) (sat_cons (step1437 p h) (sat_cons (step1420 p h) (sat_cons (step1433 p h) (sat_cons (step1429 p h) (sat_cons (step1699 p h) (sat_nil p))))))))))))
def c1996 : List Lit := [(1485, true), (45, false), (39, true)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1120, c1118, c1111, c1732] c1996 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1120 p h) (sat_cons (step1118 p h) (sat_cons (step1111 p h) (sat_cons (step1732 p h) (sat_nil p))))))
def c1997 : List Lit := [(1650, true), (105, false), (54, false), (102, false)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c628, c1416, c629, c1419, c1424, c1450, c1737, c1435, c1433] c1997 (by decide) p (sat_cons (step628 p h) (sat_cons (step1416 p h) (sat_cons (step629 p h) (sat_cons (step1419 p h) (sat_cons (step1424 p h) (sat_cons (step1450 p h) (sat_cons (step1737 p h) (sat_cons (step1435 p h) (sat_cons (step1433 p h) (sat_nil p))))))))))
def c1998 : List Lit := [(1463, true), (24, true), (19, true), (52, true), (54, false)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c1039, c1043, c1050, c1061, c1076, c1082, c1633, c1637, c1066, c1019, c1023, c1053, c1046, c1040, c1011, c1000, c1044, c1034, c1008, c997, c1638, c93] c1998 (by decide) p (sat_cons (step1039 p h) (sat_cons (step1043 p h) (sat_cons (step1050 p h) (sat_cons (step1061 p h) (sat_cons (step1076 p h) (sat_cons (step1082 p h) (sat_cons (step1633 p h) (sat_cons (step1637 p h) (sat_cons (step1066 p h) (sat_cons (step1019 p h) (sat_cons (step1023 p h) (sat_cons (step1053 p h) (sat_cons (step1046 p h) (sat_cons (step1040 p h) (sat_cons (step1011 p h) (sat_cons (step1000 p h) (sat_cons (step1044 p h) (sat_cons (step1034 p h) (sat_cons (step1008 p h) (sat_cons (step997 p h) (sat_cons (step1638 p h) (sat_cons (step93 p h) (sat_nil p)))))))))))))))))))))))
def c1999 : List Lit := [(1513, true), (1507, false), (50, true), (69, false), (118, false), (52, true)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c1143, c1177, c1733, c1148, c516, c1139] c1999 (by decide) p (sat_cons (step1143 p h) (sat_cons (step1177 p h) (sat_cons (step1733 p h) (sat_cons (step1148 p h) (sat_cons (step516 p h) (sat_cons (step1139 p h) (sat_nil p)))))))
def c2000 : List Lit := [(1448, false), (1463, true), (54, false), (102, false)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c1076, c1656, c1637, c1082, c1994, c1019, c1009, c1011] c2000 (by decide) p (sat_cons (step1076 p h) (sat_cons (step1656 p h) (sat_cons (step1637 p h) (sat_cons (step1082 p h) (sat_cons (step1994 p h) (sat_cons (step1019 p h) (sat_cons (step1009 p h) (sat_cons (step1011 p h) (sat_nil p)))))))))
def c2001 : List Lit := [(1680, true), (1628, true), (1568, false), (1660, false), (1650, false)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c1915, c1496, c1491, c1361, c1467, c1726, c1412, c1618, c1958, c1388, c1397, c1692, c1389] c2001 (by decide) p (sat_cons (step1915 p h) (sat_cons (step1496 p h) (sat_cons (step1491 p h) (sat_cons (step1361 p h) (sat_cons (step1467 p h) (sat_cons (step1726 p h) (sat_cons (step1412 p h) (sat_cons (step1618 p h) (sat_cons (step1958 p h) (sat_cons (step1388 p h) (sat_cons (step1397 p h) (sat_cons (step1692 p h) (sat_cons (step1389 p h) (sat_nil p))))))))))))))
def c2002 : List Lit := [(1583, true), (1616, true), (98, false)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c1618, c1692, c1388] c2002 (by decide) p (sat_cons (step1618 p h) (sat_cons (step1692 p h) (sat_cons (step1388 p h) (sat_nil p))))
def c2003 : List Lit := [(28, false), (1564, true), (115, true), (118, false)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c1873, c1872, c1563, c512, c511, c1283, c1281, c1291] c2003 (by decide) p (sat_cons (step1873 p h) (sat_cons (step1872 p h) (sat_cons (step1563 p h) (sat_cons (step512 p h) (sat_cons (step511 p h) (sat_cons (step1283 p h) (sat_cons (step1281 p h) (sat_cons (step1291 p h) (sat_nil p)))))))))
def c2004 : List Lit := [(107, false), (89, false), (55, false), (115, true)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c1863, c632] c2004 (by decide) p (sat_cons (step1863 p h) (sat_cons (step632 p h) (sat_nil p)))
def c2005 : List Lit := [(1512, true), (69, false), (118, false), (54, false), (1497, false)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c1176, c1716, c1148, c1156, c1139, c516] c2005 (by decide) p (sat_cons (step1176 p h) (sat_cons (step1716 p h) (sat_cons (step1148 p h) (sat_cons (step1156 p h) (sat_cons (step1139 p h) (sat_cons (step516 p h) (sat_nil p)))))))
def c2006 : List Lit := [(1523, true), (39, true), (1477, false), (1512, false), (69, false), (118, false), (1497, false)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1117, c1128, c1205, c1181, c1151, c1211, c1129, c1996, c1140, c1141, c1629, c516] c2006 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1117 p h) (sat_cons (step1128 p h) (sat_cons (step1205 p h) (sat_cons (step1181 p h) (sat_cons (step1151 p h) (sat_cons (step1211 p h) (sat_cons (step1129 p h) (sat_cons (step1996 p h) (sat_cons (step1140 p h) (sat_cons (step1141 p h) (sat_cons (step1629 p h) (sat_cons (step516 p h) (sat_nil p))))))))))))))
def c2007 : List Lit := [(61, false), (50, false), (1483, true), (63, false), (54, false), (52, true), (55, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c426, c267, c1827, c1823, c1820, c479, c1547, c1114] c2007 (by decide) p (sat_cons (step426 p h) (sat_cons (step267 p h) (sat_cons (step1827 p h) (sat_cons (step1823 p h) (sat_cons (step1820 p h) (sat_cons (step479 p h) (sat_cons (step1547 p h) (sat_cons (step1114 p h) (sat_nil p)))))))))
def c2008 : List Lit := [(1564, true), (73, true), (65, true), (69, false), (118, false)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1280, c1289, c1291, c1284, c1281, c532] c2008 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1280 p h) (sat_cons (step1289 p h) (sat_cons (step1291 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step532 p h) (sat_nil p))))))))
def c2009 : List Lit := [(1498, false), (48, true), (1523, true), (39, true), (1502, true)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c1139, c1152, c1149, c1141, c1181, c1996, c1205, c1124] c2009 (by decide) p (sat_cons (step1139 p h) (sat_cons (step1152 p h) (sat_cons (step1149 p h) (sat_cons (step1141 p h) (sat_cons (step1181 p h) (sat_cons (step1996 p h) (sat_cons (step1205 p h) (sat_cons (step1124 p h) (sat_nil p)))))))))
def c2010 : List Lit := [(1513, false), (58, false), (1523, true), (1541, true), (1428, false), (1484, false), (34, false), (54, false)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c1123, c1198, c1205, c1246, c1128, c1106, c1706, c196, c1045, c1993] c2010 (by decide) p (sat_cons (step1123 p h) (sat_cons (step1198 p h) (sat_cons (step1205 p h) (sat_cons (step1246 p h) (sat_cons (step1128 p h) (sat_cons (step1106 p h) (sat_cons (step1706 p h) (sat_cons (step196 p h) (sat_cons (step1045 p h) (sat_cons (step1993 p h) (sat_nil p)))))))))))
def c2011 : List Lit := [(1495, true), (37, true), (34, false)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c1139, c1140, c1809, c251] c2011 (by decide) p (sat_cons (step1139 p h) (sat_cons (step1140 p h) (sat_cons (step1809 p h) (sat_cons (step251 p h) (sat_nil p)))))
def c2012 : List Lit := [(1514, false), (1428, false), (37, true), (54, false), (1541, true), (1523, true)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c1192, c1199, c1246, c1127, c1106, c1706, c1993, c1045] c2012 (by decide) p (sat_cons (step1192 p h) (sat_cons (step1199 p h) (sat_cons (step1246 p h) (sat_cons (step1127 p h) (sat_cons (step1106 p h) (sat_cons (step1706 p h) (sat_cons (step1993 p h) (sat_cons (step1045 p h) (sat_nil p)))))))))
def c2013 : List Lit := [(1435, true), (4, false), (1428, false), (39, false)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c1011, c1020, c1024, c1014, c1002, c1005, c21] c2013 (by decide) p (sat_cons (step1011 p h) (sat_cons (step1020 p h) (sat_cons (step1024 p h) (sat_cons (step1014 p h) (sat_cons (step1002 p h) (sat_cons (step1005 p h) (sat_cons (step21 p h) (sat_nil p))))))))
def c2014 : List Lit := [(1450, false), (4, false), (1464, true), (1428, false), (39, false)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c2013, c1088, c1056, c1092, c1061, c1039, c22, c23, c1002, c1005, c1025, c1014] c2014 (by decide) p (sat_cons (step2013 p h) (sat_cons (step1088 p h) (sat_cons (step1056 p h) (sat_cons (step1092 p h) (sat_cons (step1061 p h) (sat_cons (step1039 p h) (sat_cons (step22 p h) (sat_cons (step23 p h) (sat_cons (step1002 p h) (sat_cons (step1005 p h) (sat_cons (step1025 p h) (sat_cons (step1014 p h) (sat_nil p)))))))))))))
def c2015 : List Lit := [(4, false), (1464, true), (1428, false), (39, false)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c2013, c1088, c2014, c1065, c1050, c1043, c1604, c1037, c1040, c1060, c22, c23, c1092, c1002, c1005, c1025, c1014] c2015 (by decide) p (sat_cons (step2013 p h) (sat_cons (step1088 p h) (sat_cons (step2014 p h) (sat_cons (step1065 p h) (sat_cons (step1050 p h) (sat_cons (step1043 p h) (sat_cons (step1604 p h) (sat_cons (step1037 p h) (sat_cons (step1040 p h) (sat_cons (step1060 p h) (sat_cons (step22 p h) (sat_cons (step23 p h) (sat_cons (step1092 p h) (sat_cons (step1002 p h) (sat_cons (step1005 p h) (sat_cons (step1025 p h) (sat_cons (step1014 p h) (sat_nil p))))))))))))))))))
def c2016 : List Lit := [(1454, true)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c1056, c1060, c1050, c1037, c1043, c1604] c2016 (by decide) p (sat_cons (step1056 p h) (sat_cons (step1060 p h) (sat_cons (step1050 p h) (sat_cons (step1037 p h) (sat_cons (step1043 p h) (sat_cons (step1604 p h) (sat_nil p)))))))
def c2017 : List Lit := [(1461, true)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c2016, c1074] c2017 (by decide) p (sat_cons (step2016 p h) (sat_cons (step1074 p h) (sat_nil p)))
end B112E158
