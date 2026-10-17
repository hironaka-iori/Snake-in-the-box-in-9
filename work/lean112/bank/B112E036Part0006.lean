import B112E036Part0005
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2029 : List Lit := [(101, true), (1791, true), (39, false), (1772, false), (106, true), (58, true), (38, false)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c1404, c1406, c1434, c1399, c1389, c1391, c1398, c175, c1430, c1831, c1407, c551, c1405] c2029 (by decide) p (sat_cons (step1404 p h) (sat_cons (step1406 p h) (sat_cons (step1434 p h) (sat_cons (step1399 p h) (sat_cons (step1389 p h) (sat_cons (step1391 p h) (sat_cons (step1398 p h) (sat_cons (step175 p h) (sat_cons (step1430 p h) (sat_cons (step1831 p h) (sat_cons (step1407 p h) (sat_cons (step551 p h) (sat_cons (step1405 p h) (sat_nil p))))))))))))))
def c2030 : List Lit := [(1784, true), (100, false), (101, false), (106, true)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c1404, c1407, c1409, c1405, c1400, c1401, c624, c678, c1926, c636] c2030 (by decide) p (sat_cons (step1404 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1405 p h) (sat_cons (step1400 p h) (sat_cons (step1401 p h) (sat_cons (step624 p h) (sat_cons (step678 p h) (sat_cons (step1926 p h) (sat_cons (step636 p h) (sat_nil p)))))))))))
def c2031 : List Lit := [(61, false), (53, true), (1808, true), (103, false)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c1870, c744, c745, c1461, c1455] c2031 (by decide) p (sat_cons (step1870 p h) (sat_cons (step744 p h) (sat_cons (step745 p h) (sat_cons (step1461 p h) (sat_cons (step1455 p h) (sat_nil p))))))
def c2032 : List Lit := [(1807, false), (115, true), (1817, true)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c1442, c1444, c1478, c1463, c1467, c1482, c1453, c1445, c1447, c1443, c1438, c1439, c730, c712, c1953] c2032 (by decide) p (sat_cons (step1442 p h) (sat_cons (step1444 p h) (sat_cons (step1478 p h) (sat_cons (step1463 p h) (sat_cons (step1467 p h) (sat_cons (step1482 p h) (sat_cons (step1453 p h) (sat_cons (step1445 p h) (sat_cons (step1447 p h) (sat_cons (step1443 p h) (sat_cons (step1438 p h) (sat_cons (step1439 p h) (sat_cons (step730 p h) (sat_cons (step712 p h) (sat_cons (step1953 p h) (sat_nil p))))))))))))))))
def c2033 : List Lit := [(1807, true), (103, false)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c1458, c1460, c1455, c1456, c747, c767, c1964] c2033 (by decide) p (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step747 p h) (sat_cons (step767 p h) (sat_cons (step1964 p h) (sat_nil p))))))))
def c2034 : List Lit := [(3, false), (13, false), (4, false), (35, false)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c9, c8, c1801] c2034 (by decide) p (sat_cons (step9 p h) (sat_cons (step8 p h) (sat_cons (step1801 p h) (sat_nil p))))
def c2035 : List Lit := [(13, false), (4, false), (1556, true), (35, false), (6, true)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c2034, c1796, c1012, c42, c1798] c2035 (by decide) p (sat_cons (step2034 p h) (sat_cons (step1796 p h) (sat_cons (step1012 p h) (sat_cons (step42 p h) (sat_cons (step1798 p h) (sat_nil p))))))
def c2036 : List Lit := [(4, false), (1560, true), (35, false), (6, true)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c1021, c2035, c1014, c1019, c1010, c1011, c5, c1796] c2036 (by decide) p (sat_cons (step1021 p h) (sat_cons (step2035 p h) (sat_cons (step1014 p h) (sat_cons (step1019 p h) (sat_cons (step1010 p h) (sat_cons (step1011 p h) (sat_cons (step5 p h) (sat_cons (step1796 p h) (sat_nil p)))))))))
def c2037 : List Lit := [(1601, true), (1559, false), (4, true)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c996, c1004, c1029, c1989, c1083, c1034, c1716, c1007, c998] c2037 (by decide) p (sat_cons (step996 p h) (sat_cons (step1004 p h) (sat_cons (step1029 p h) (sat_cons (step1989 p h) (sat_cons (step1083 p h) (sat_cons (step1034 p h) (sat_cons (step1716 p h) (sat_cons (step1007 p h) (sat_cons (step998 p h) (sat_nil p))))))))))
def c2038 : List Lit := [(1669, true), (1615, false), (1652, false), (1637, false)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c1136, c1158, c1193, c1212, c1217, c1198, c1137, c1161, c1686] c2038 (by decide) p (sat_cons (step1136 p h) (sat_cons (step1158 p h) (sat_cons (step1193 p h) (sat_cons (step1212 p h) (sat_cons (step1217 p h) (sat_cons (step1198 p h) (sat_cons (step1137 p h) (sat_cons (step1161 p h) (sat_cons (step1686 p h) (sat_nil p))))))))))
def c2039 : List Lit := [(1611, true), (5, true), (8, false), (2, false)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c1104, c1105, c127, c1, c1787] c2039 (by decide) p (sat_cons (step1104 p h) (sat_cons (step1105 p h) (sat_cons (step127 p h) (sat_cons (step1 p h) (sat_cons (step1787 p h) (sat_nil p))))))
def c2040 : List Lit := [(1657, true), (63, false), (52, true)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c1873, c1156, c1158, c1994, c1192, c1159, c2027, c1157, c302] c2040 (by decide) p (sat_cons (step1873 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1994 p h) (sat_cons (step1192 p h) (sat_cons (step1159 p h) (sat_cons (step2027 p h) (sat_cons (step1157 p h) (sat_cons (step302 p h) (sat_nil p))))))))))
def c2041 : List Lit := [(109, false), (1789, true), (93, true), (227, true), (97, false), (37, false), (38, false)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c1428, c549, c551, c1387, c576, c1390, c1395, c1398, c1424, c1388, c1406, c1919, c514, c1404] c2041 (by decide) p (sat_cons (step1428 p h) (sat_cons (step549 p h) (sat_cons (step551 p h) (sat_cons (step1387 p h) (sat_cons (step576 p h) (sat_cons (step1390 p h) (sat_cons (step1395 p h) (sat_cons (step1398 p h) (sat_cons (step1424 p h) (sat_cons (step1388 p h) (sat_cons (step1406 p h) (sat_cons (step1919 p h) (sat_cons (step514 p h) (sat_cons (step1404 p h) (sat_nil p)))))))))))))))
def c2042 : List Lit := [(95, false), (106, false), (1772, true), (37, false)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c514, c512, c1388] c2042 (by decide) p (sat_cons (step514 p h) (sat_cons (step512 p h) (sat_cons (step1388 p h) (sat_nil p))))
def c2043 : List Lit := [(1808, false), (1818, true), (95, true), (117, true)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1444, c1464, c1696] c2043 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1444 p h) (sat_cons (step1464 p h) (sat_cons (step1696 p h) (sat_nil p)))))
def c2044 : List Lit := [(1800, true), (95, true), (117, true)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1445, c1447, c1443, c1439, c1947, c1946, c1642] c2044 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1445 p h) (sat_cons (step1447 p h) (sat_cons (step1443 p h) (sat_cons (step1439 p h) (sat_cons (step1947 p h) (sat_cons (step1946 p h) (sat_cons (step1642 p h) (sat_nil p)))))))))
def c2045 : List Lit := [(1788, true), (97, false), (38, false)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c1687, c1423, c1419, c1406, c1732, c1403, c1395, c549, c1387] c2045 (by decide) p (sat_cons (step1687 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step1406 p h) (sat_cons (step1732 p h) (sat_cons (step1403 p h) (sat_cons (step1395 p h) (sat_cons (step549 p h) (sat_cons (step1387 p h) (sat_nil p))))))))))
def c2046 : List Lit := [(1735, true), (11, false)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c1328, c1330, c1325, c1326, c1322, c1760, c389, c404, c1900] c2046 (by decide) p (sat_cons (step1328 p h) (sat_cons (step1330 p h) (sat_cons (step1325 p h) (sat_cons (step1326 p h) (sat_cons (step1322 p h) (sat_cons (step1760 p h) (sat_cons (step389 p h) (sat_cons (step404 p h) (sat_cons (step1900 p h) (sat_nil p))))))))))
def c2047 : List Lit := [(1615, true), (89, true), (88, false), (35, true), (37, false)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c1112, c2023, c1105, c103] c2047 (by decide) p (sat_cons (step1112 p h) (sat_cons (step2023 p h) (sat_cons (step1105 p h) (sat_cons (step103 p h) (sat_nil p)))))
def c2048 : List Lit := [(1658, true), (1636, false), (63, false)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c1163, c1873, c1995, c1197, c1164, c2027, c1155, c302] c2048 (by decide) p (sat_cons (step1163 p h) (sat_cons (step1873 p h) (sat_cons (step1995 p h) (sat_cons (step1197 p h) (sat_cons (step1164 p h) (sat_cons (step2027 p h) (sat_cons (step1155 p h) (sat_cons (step302 p h) (sat_nil p)))))))))
def c2049 : List Lit := [(1623, true), (101, false), (88, false), (37, false)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c1126, c1711, c1118, c108] c2049 (by decide) p (sat_cons (step1126 p h) (sat_cons (step1711 p h) (sat_cons (step1118 p h) (sat_cons (step108 p h) (sat_nil p)))))
def c2050 : List Lit := [(347, true), (1624, true), (35, true), (47, true), (50, true), (17, true)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c871, c872, c228, c223, c1746, c1836] c2050 (by decide) p (sat_cons (step871 p h) (sat_cons (step872 p h) (sat_cons (step228 p h) (sat_cons (step223 p h) (sat_cons (step1746 p h) (sat_cons (step1836 p h) (sat_nil p)))))))
def c2051 : List Lit := [(41, true), (1624, true), (1615, true), (47, true), (35, true), (50, true), (17, true)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c2050, c876, c881, c889, c1971, c870, c869, c867, c866, c1129, c1110, c1108, c1112, c1105, c1104, c99, c2023, c1107, c132, c1826, c1597, c1118, c1120, c191, c1127, c1836, c1121, c223, c196, c1969, c1846, c228] c2051 (by decide) p (sat_cons (step2050 p h) (sat_cons (step876 p h) (sat_cons (step881 p h) (sat_cons (step889 p h) (sat_cons (step1971 p h) (sat_cons (step870 p h) (sat_cons (step869 p h) (sat_cons (step867 p h) (sat_cons (step866 p h) (sat_cons (step1129 p h) (sat_cons (step1110 p h) (sat_cons (step1108 p h) (sat_cons (step1112 p h) (sat_cons (step1105 p h) (sat_cons (step1104 p h) (sat_cons (step99 p h) (sat_cons (step2023 p h) (sat_cons (step1107 p h) (sat_cons (step132 p h) (sat_cons (step1826 p h) (sat_cons (step1597 p h) (sat_cons (step1118 p h) (sat_cons (step1120 p h) (sat_cons (step191 p h) (sat_cons (step1127 p h) (sat_cons (step1836 p h) (sat_cons (step1121 p h) (sat_cons (step223 p h) (sat_cons (step196 p h) (sat_cons (step1969 p h) (sat_cons (step1846 p h) (sat_cons (step228 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c2052 : List Lit := [(1624, true), (1615, true), (47, true), (35, true), (50, true), (17, true)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1108, c1112, c1105, c1104, c99, c1107, c132, c1826, c1125, c2051, c187, c1122, c1123, c195, c1127, c1846, c1119, c228, c1836, c1969, c223] c2052 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1108 p h) (sat_cons (step1112 p h) (sat_cons (step1105 p h) (sat_cons (step1104 p h) (sat_cons (step99 p h) (sat_cons (step1107 p h) (sat_cons (step132 p h) (sat_cons (step1826 p h) (sat_cons (step1125 p h) (sat_cons (step2051 p h) (sat_cons (step187 p h) (sat_cons (step1122 p h) (sat_cons (step1123 p h) (sat_cons (step195 p h) (sat_cons (step1127 p h) (sat_cons (step1846 p h) (sat_cons (step1119 p h) (sat_cons (step228 p h) (sat_cons (step1836 p h) (sat_cons (step1969 p h) (sat_cons (step223 p h) (sat_nil p)))))))))))))))))))))))
def c2053 : List Lit := [(45, false), (49, true), (41, false), (33, false)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c195, c1846] c2053 (by decide) p (sat_cons (step195 p h) (sat_cons (step1846 p h) (sat_nil p)))
def c2054 : List Lit := [(1551, true), (1611, true), (4, false), (13, false)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c1002, c1004, c999, c997, c12, c2039] c2054 (by decide) p (sat_cons (step1002 p h) (sat_cons (step1004 p h) (sat_cons (step999 p h) (sat_cons (step997 p h) (sat_cons (step12 p h) (sat_cons (step2039 p h) (sat_nil p)))))))
def c2055 : List Lit := [(1555, true), (3, false), (4, false)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c1010, c1011, c5] c2055 (by decide) p (sat_cons (step1010 p h) (sat_cons (step1011 p h) (sat_cons (step5 p h) (sat_nil p))))
def c2056 : List Lit := [(1717, true), (74, false), (7, false)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c1297, c1298, c366] c2056 (by decide) p (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step366 p h) (sat_nil p))))
def c2057 : List Lit := [(70, false), (1744, true), (89, false), (32, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c425, c426, c1333, c1335, c1340] c2057 (by decide) p (sat_cons (step425 p h) (sat_cons (step426 p h) (sat_cons (step1333 p h) (sat_cons (step1335 p h) (sat_cons (step1340 p h) (sat_nil p))))))
def c2058 : List Lit := [(1721, true), (74, false), (7, false), (72, true)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c2056, c1295, c1304, c1306, c1296, c364, c365, c1299] c2058 (by decide) p (sat_cons (step2056 p h) (sat_cons (step1295 p h) (sat_cons (step1304 p h) (sat_cons (step1306 p h) (sat_cons (step1296 p h) (sat_cons (step364 p h) (sat_cons (step365 p h) (sat_cons (step1299 p h) (sat_nil p)))))))))
def c2059 : List Lit := [(1743, true), (89, false), (32, false)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1339, c1335, c1333, c429] c2059 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1339 p h) (sat_cons (step1335 p h) (sat_cons (step1333 p h) (sat_cons (step429 p h) (sat_nil p))))))
def c2060 : List Lit := [(1771, true), (103, false), (88, false)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1387, c455, c527, c1921] c2060 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step455 p h) (sat_cons (step527 p h) (sat_cons (step1921 p h) (sat_nil p))))))
def c2061 : List Lit := [(1816, true), (112, true)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c1439, c1446, c1481, c1477, c1449, c1447, c1466, c1440, c1441, c1442, c1453, c713, c730, c1953] c2061 (by decide) p (sat_cons (step1439 p h) (sat_cons (step1446 p h) (sat_cons (step1481 p h) (sat_cons (step1477 p h) (sat_cons (step1449 p h) (sat_cons (step1447 p h) (sat_cons (step1466 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1442 p h) (sat_cons (step1453 p h) (sat_cons (step713 p h) (sat_cons (step730 p h) (sat_cons (step1953 p h) (sat_nil p)))))))))))))))
def c2062 : List Lit := [(96, false), (95, true), (93, false), (1720, true), (105, false), (106, false), (109, false), (88, false)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c661, c447, c1930, c1917, c555, c666, c668, c1298, c1928, c1303, c487, c1295] c2062 (by decide) p (sat_cons (step661 p h) (sat_cons (step447 p h) (sat_cons (step1930 p h) (sat_cons (step1917 p h) (sat_cons (step555 p h) (sat_cons (step666 p h) (sat_cons (step668 p h) (sat_cons (step1298 p h) (sat_cons (step1928 p h) (sat_cons (step1303 p h) (sat_cons (step487 p h) (sat_cons (step1295 p h) (sat_nil p)))))))))))))
def c2063 : List Lit := [(95, true), (93, false), (1720, true), (1772, true), (105, false), (106, false), (109, false), (88, false)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c2062, c1388, c453, c1921] c2063 (by decide) p (sat_cons (step2062 p h) (sat_cons (step1388 p h) (sat_cons (step453 p h) (sat_cons (step1921 p h) (sat_nil p)))))
def c2064 : List Lit := [(93, false), (1720, true), (88, false), (1772, true), (105, false), (106, false), (109, false)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c2063, c530, c528, c1388] c2064 (by decide) p (sat_cons (step2063 p h) (sat_cons (step530 p h) (sat_cons (step528 p h) (sat_cons (step1388 p h) (sat_nil p)))))
def c2065 : List Lit := [(1817, true), (106, false), (1807, false), (1799, false), (88, false)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1478, c2032, c1482, c1467, c532, c2044, c1453, c1946, c713] c2065 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1478 p h) (sat_cons (step2032 p h) (sat_cons (step1482 p h) (sat_cons (step1467 p h) (sat_cons (step532 p h) (sat_cons (step2044 p h) (sat_cons (step1453 p h) (sat_cons (step1946 p h) (sat_cons (step713 p h) (sat_nil p)))))))))))
def c2066 : List Lit := [(111, false), (97, true), (95, true), (1772, true), (109, false), (106, false), (88, false), (89, false)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c419, c421, c1921, c1388, c661, c1917] c2066 (by decide) p (sat_cons (step419 p h) (sat_cons (step421 p h) (sat_cons (step1921 p h) (sat_cons (step1388 p h) (sat_cons (step661 p h) (sat_cons (step1917 p h) (sat_nil p)))))))
def c2067 : List Lit := [(117, false), (95, true), (105, false), (1772, true), (1801, true), (109, false), (106, false), (100, false), (112, true), (88, false), (89, false)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c563, c2066, c1947, c1442, c1450, c1440, c501, c727, c1943] c2067 (by decide) p (sat_cons (step563 p h) (sat_cons (step2066 p h) (sat_cons (step1947 p h) (sat_cons (step1442 p h) (sat_cons (step1450 p h) (sat_cons (step1440 p h) (sat_cons (step501 p h) (sat_cons (step727 p h) (sat_cons (step1943 p h) (sat_nil p))))))))))
def c2068 : List Lit := [(95, true), (105, false), (1772, true), (1801, true), (109, false), (106, false), (100, false), (112, true), (88, false), (89, false)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c1439, c1448, c2067, c1443, c1947, c421, c2066, c1921, c560, c1388] c2068 (by decide) p (sat_cons (step1439 p h) (sat_cons (step1448 p h) (sat_cons (step2067 p h) (sat_cons (step1443 p h) (sat_cons (step1947 p h) (sat_cons (step421 p h) (sat_cons (step2066 p h) (sat_cons (step1921 p h) (sat_cons (step560 p h) (sat_cons (step1388 p h) (sat_nil p)))))))))))
def c2069 : List Lit := [(95, false), (1772, true), (106, false), (88, false)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c530, c528, c1388] c2069 (by decide) p (sat_cons (step530 p h) (sat_cons (step528 p h) (sat_cons (step1388 p h) (sat_nil p))))
def c2070 : List Lit := [(1772, true), (91, true), (93, false), (109, false), (106, false), (100, false), (88, false)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c2069, c1921, c1388, c661, c447, c560, c1917] c2070 (by decide) p (sat_cons (step2069 p h) (sat_cons (step1921 p h) (sat_cons (step1388 p h) (sat_cons (step661 p h) (sat_cons (step447 p h) (sat_cons (step560 p h) (sat_cons (step1917 p h) (sat_nil p))))))))
def c2071 : List Lit := [(98, false), (95, true), (93, false), (100, false)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c1919, c570] c2071 (by decide) p (sat_cons (step1919 p h) (sat_cons (step570 p h) (sat_nil p)))
def c2072 : List Lit := [(95, true), (1779, false), (93, false), (106, true), (100, false), (1791, true), (1773, false), (88, false)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c1404, c1409, c1430, c1398, c2071, c1386, c1388, c1395, c447, c569, c1426, c1918, c1410, c560, c1405] c2072 (by decide) p (sat_cons (step1404 p h) (sat_cons (step1409 p h) (sat_cons (step1430 p h) (sat_cons (step1398 p h) (sat_cons (step2071 p h) (sat_cons (step1386 p h) (sat_cons (step1388 p h) (sat_cons (step1395 p h) (sat_cons (step447 p h) (sat_cons (step569 p h) (sat_cons (step1426 p h) (sat_cons (step1918 p h) (sat_cons (step1410 p h) (sat_cons (step560 p h) (sat_cons (step1405 p h) (sat_nil p))))))))))))))))
def c2073 : List Lit := [(115, true), (1742, true), (1801, true), (100, false), (112, true)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c1439, c1448, c1442, c1443, c1450, c1735, c1440] c2073 (by decide) p (sat_cons (step1439 p h) (sat_cons (step1448 p h) (sat_cons (step1442 p h) (sat_cons (step1443 p h) (sat_cons (step1450 p h) (sat_cons (step1735 p h) (sat_cons (step1440 p h) (sat_nil p))))))))
def c2074 : List Lit := [(1779, false), (115, false), (93, false), (106, true), (100, false), (1791, true), (1773, false), (88, false)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c1404, c1409, c1430, c1398, c2072, c531, c529, c1388] c2074 (by decide) p (sat_cons (step1404 p h) (sat_cons (step1409 p h) (sat_cons (step1430 p h) (sat_cons (step1398 p h) (sat_cons (step2072 p h) (sat_cons (step531 p h) (sat_cons (step529 p h) (sat_cons (step1388 p h) (sat_nil p)))))))))
def c2075 : List Lit := [(103, false), (1801, false), (1783, false), (1830, true), (1773, false), (88, false)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c2033, c2060, c1463, c1395, c1487, c1424, c1507] c2075 (by decide) p (sat_cons (step2033 p h) (sat_cons (step2060 p h) (sat_cons (step1463 p h) (sat_cons (step1395 p h) (sat_cons (step1487 p h) (sat_cons (step1424 p h) (sat_cons (step1507 p h) (sat_nil p))))))))
def c2076 : List Lit := [(1771, true), (100, false), (88, false)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1387, c527, c571, c1919] c2076 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step527 p h) (sat_cons (step571 p h) (sat_cons (step1919 p h) (sat_nil p))))))
def c2077 : List Lit := [(1817, true), (1807, false), (100, false), (1795, false)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1446, c1478, c1482, c1467, c1447, c1453, c1728] c2077 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1446 p h) (sat_cons (step1478 p h) (sat_cons (step1482 p h) (sat_cons (step1467 p h) (sat_cons (step1447 p h) (sat_cons (step1453 p h) (sat_cons (step1728 p h) (sat_nil p)))))))))
def c2078 : List Lit := [(118, true), (109, false), (1818, true), (1779, true), (100, false), (112, true)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c1400, c678, c1401, c2033, c1439, c1446, c1479, c1471, c1453, c1454, c1467, c627, c1483, c1928, c1449, c501, c1440] c2078 (by decide) p (sat_cons (step1400 p h) (sat_cons (step678 p h) (sat_cons (step1401 p h) (sat_cons (step2033 p h) (sat_cons (step1439 p h) (sat_cons (step1446 p h) (sat_cons (step1479 p h) (sat_cons (step1471 p h) (sat_cons (step1453 p h) (sat_cons (step1454 p h) (sat_cons (step1467 p h) (sat_cons (step627 p h) (sat_cons (step1483 p h) (sat_cons (step1928 p h) (sat_cons (step1449 p h) (sat_cons (step501 p h) (sat_cons (step1440 p h) (sat_nil p))))))))))))))))))
def c2079 : List Lit := [(118, false), (1801, true), (105, false), (100, false), (112, true)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c1728, c1450, c1440, c501, c1943, c728] c2079 (by decide) p (sat_cons (step1728 p h) (sat_cons (step1450 p h) (sat_cons (step1440 p h) (sat_cons (step501 p h) (sat_cons (step1943 p h) (sat_cons (step728 p h) (sat_nil p)))))))
def c2080 : List Lit := [(1783, false), (1779, true), (1830, true), (100, false), (1773, false), (112, true), (88, false)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c2076, c1395, c1439, c1401, c2033, c2077, c1513, c1425, c1407, c1400, c1424, c2075, c1507, c1429, c1398, c2079, c1453, c2078, c1467, c1405, c2069, c1483, c2044, c1449, c1440, c501, c1943, c727] c2080 (by decide) p (sat_cons (step2076 p h) (sat_cons (step1395 p h) (sat_cons (step1439 p h) (sat_cons (step1401 p h) (sat_cons (step2033 p h) (sat_cons (step2077 p h) (sat_cons (step1513 p h) (sat_cons (step1425 p h) (sat_cons (step1407 p h) (sat_cons (step1400 p h) (sat_cons (step1424 p h) (sat_cons (step2075 p h) (sat_cons (step1507 p h) (sat_cons (step1429 p h) (sat_cons (step1398 p h) (sat_cons (step2079 p h) (sat_cons (step1453 p h) (sat_cons (step2078 p h) (sat_cons (step1467 p h) (sat_cons (step1405 p h) (sat_cons (step2069 p h) (sat_cons (step1483 p h) (sat_cons (step2044 p h) (sat_cons (step1449 p h) (sat_cons (step1440 p h) (sat_cons (step501 p h) (sat_cons (step1943 p h) (sat_cons (step727 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2081 : List Lit := [(118, true), (1779, true), (1830, true), (100, false), (1773, false), (112, true), (88, false), (89, false)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c2080, c1406, c1404, c1403, c1401, c2033, c1400, c2076, c1395, c1423, c1500, c1453, c2078, c1467, c1507, c1488, c1428, c1398, c2069, c2068] c2081 (by decide) p (sat_cons (step2080 p h) (sat_cons (step1406 p h) (sat_cons (step1404 p h) (sat_cons (step1403 p h) (sat_cons (step1401 p h) (sat_cons (step2033 p h) (sat_cons (step1400 p h) (sat_cons (step2076 p h) (sat_cons (step1395 p h) (sat_cons (step1423 p h) (sat_cons (step1500 p h) (sat_cons (step1453 p h) (sat_cons (step2078 p h) (sat_cons (step1467 p h) (sat_cons (step1507 p h) (sat_cons (step1488 p h) (sat_cons (step1428 p h) (sat_cons (step1398 p h) (sat_cons (step2069 p h) (sat_cons (step2068 p h) (sat_nil p)))))))))))))))))))))
def c2082 : List Lit := [(111, false), (1772, true), (106, false), (109, false), (100, false), (88, false), (89, false)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c2069, c421, c2066, c1921, c560, c1388] c2082 (by decide) p (sat_cons (step2069 p h) (sat_cons (step421 p h) (sat_cons (step2066 p h) (sat_cons (step1921 p h) (sat_cons (step560 p h) (sat_cons (step1388 p h) (sat_nil p)))))))
def c2083 : List Lit := [(1779, true), (1830, true), (100, false), (112, true), (101, true), (88, false), (89, false)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c1389, c2076, c1395, c1423, c1500, c1439, c1400, c1401, c2033, c1463, c1490, c2077, c1513, c2080, c1433, c1406, c1403, c1404, c678, c2081, c2079, c1488, c1487, c1467, c1507, c1452, c1428, c627, c1398, c1928, c1956, c2069, c498, c501, c1440, c1451, c2082, c1947, c1443, c1776, c455, c1921] c2083 (by decide) p (sat_cons (step1389 p h) (sat_cons (step2076 p h) (sat_cons (step1395 p h) (sat_cons (step1423 p h) (sat_cons (step1500 p h) (sat_cons (step1439 p h) (sat_cons (step1400 p h) (sat_cons (step1401 p h) (sat_cons (step2033 p h) (sat_cons (step1463 p h) (sat_cons (step1490 p h) (sat_cons (step2077 p h) (sat_cons (step1513 p h) (sat_cons (step2080 p h) (sat_cons (step1433 p h) (sat_cons (step1406 p h) (sat_cons (step1403 p h) (sat_cons (step1404 p h) (sat_cons (step678 p h) (sat_cons (step2081 p h) (sat_cons (step2079 p h) (sat_cons (step1488 p h) (sat_cons (step1487 p h) (sat_cons (step1467 p h) (sat_cons (step1507 p h) (sat_cons (step1452 p h) (sat_cons (step1428 p h) (sat_cons (step627 p h) (sat_cons (step1398 p h) (sat_cons (step1928 p h) (sat_cons (step1956 p h) (sat_cons (step2069 p h) (sat_cons (step498 p h) (sat_cons (step501 p h) (sat_cons (step1440 p h) (sat_cons (step1451 p h) (sat_cons (step2082 p h) (sat_cons (step1947 p h) (sat_cons (step1443 p h) (sat_cons (step1776 p h) (sat_cons (step455 p h) (sat_cons (step1921 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
def c2084 : List Lit := [(1801, false), (1818, true), (1830, true), (1773, false)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c1486, c1487, c1513, c1463, c1466, c1736, c1452] c2084 (by decide) p (sat_cons (step1486 p h) (sat_cons (step1487 p h) (sat_cons (step1513 p h) (sat_cons (step1463 p h) (sat_cons (step1466 p h) (sat_cons (step1736 p h) (sat_cons (step1452 p h) (sat_nil p))))))))
def c2085 : List Lit := [(1807, true), (113, false), (106, false), (109, false)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c1458, c1460, c1455, c1456, c767, c664, c1964, c1959, c749] c2085 (by decide) p (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step767 p h) (sat_cons (step664 p h) (sat_cons (step1964 p h) (sat_cons (step1959 p h) (sat_cons (step749 p h) (sat_nil p))))))))))
def c2086 : List Lit := [(1720, true), (72, true), (97, true)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1305, c1303, c1296, c1297, c1298, c370, c1894] c2086 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1305 p h) (sat_cons (step1303 p h) (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step370 p h) (sat_cons (step1894 p h) (sat_nil p)))))))))
def c2087 : List Lit := [(1800, true), (105, false), (95, true), (100, false), (112, true)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c1449, c2044, c1440, c501, c727, c1943] c2087 (by decide) p (sat_cons (step1449 p h) (sat_cons (step2044 p h) (sat_cons (step1440 p h) (sat_cons (step501 p h) (sat_cons (step727 p h) (sat_cons (step1943 p h) (sat_nil p)))))))
def c2088 : List Lit := [(1599, true)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c1075, c1987, c1716, c1028, c997, c1004] c2088 (by decide) p (sat_cons (step1075 p h) (sat_cons (step1987 p h) (sat_cons (step1716 p h) (sat_cons (step1028 p h) (sat_cons (step997 p h) (sat_cons (step1004 p h) (sat_nil p)))))))
def c2089 : List Lit := [(96, false), (73, false), (93, false), (97, true), (99, true), (88, false)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c517, c1918, c447] c2089 (by decide) p (sat_cons (step517 p h) (sat_cons (step1918 p h) (sat_cons (step447 p h) (sat_nil p))))
def c2090 : List Lit := [(98, false), (93, false), (99, true), (88, false)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c1920, c453] c2090 (by decide) p (sat_cons (step1920 p h) (sat_cons (step453 p h) (sat_nil p)))
def c2091 : List Lit := [(1547, true), (5, false), (72, false)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c996, c997, c13] c2091 (by decide) p (sat_cons (step996 p h) (sat_cons (step997 p h) (sat_cons (step13 p h) (sat_nil p))))
def c2092 : List Lit := [(96, false), (95, true), (93, false), (97, true), (99, true), (88, false)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c447, c1918] c2092 (by decide) p (sat_cons (step447 p h) (sat_cons (step1918 p h) (sat_nil p)))
end B112E036
