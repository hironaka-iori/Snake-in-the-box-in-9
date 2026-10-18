import B112E008Part0006
namespace B112E008
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2055 : List Lit := [(1542, true)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c1074, c1653, c1652, c1059, c1069, c1056, c1610] c2055 (by decide) p (sat_cons (step1074 p h) (sat_cons (step1653 p h) (sat_cons (step1652 p h) (sat_cons (step1059 p h) (sat_cons (step1069 p h) (sat_cons (step1056 p h) (sat_cons (step1610 p h) (sat_nil p))))))))
def c2056 : List Lit := [(1582, false), (1761, false), (1593, false), (1618, true), (1554, false), (57, true), (40, false), (1686, false), (1660, false)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c1186, c1189, c1204, c1232, c1231, c1205, c1263, c1190, c1192, c2041, c1188, c1183, c1184, c1521, c362, c1701, c1369, c2014, c1311] c2056 (by decide) p (sat_cons (step1186 p h) (sat_cons (step1189 p h) (sat_cons (step1204 p h) (sat_cons (step1232 p h) (sat_cons (step1231 p h) (sat_cons (step1205 p h) (sat_cons (step1263 p h) (sat_cons (step1190 p h) (sat_cons (step1192 p h) (sat_cons (step2041 p h) (sat_cons (step1188 p h) (sat_cons (step1183 p h) (sat_cons (step1184 p h) (sat_cons (step1521 p h) (sat_cons (step362 p h) (sat_cons (step1701 p h) (sat_cons (step1369 p h) (sat_cons (step2014 p h) (sat_cons (step1311 p h) (sat_nil p))))))))))))))))))))
def c2057 : List Lit := [(1525, false), (1545, true), (1534, false), (19, true)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c1072, c1083, c1057, c1063, c1062, c1058, c1081, c1610, c1073, c1069] c2057 (by decide) p (sat_cons (step1072 p h) (sat_cons (step1083 p h) (sat_cons (step1057 p h) (sat_cons (step1063 p h) (sat_cons (step1062 p h) (sat_cons (step1058 p h) (sat_cons (step1081 p h) (sat_cons (step1610 p h) (sat_cons (step1073 p h) (sat_cons (step1069 p h) (sat_nil p)))))))))))
def c2058 : List Lit := [(1544, true), (1534, false), (19, true)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c1072, c1057, c1059, c1078, c1080, c1073, c1060, c1069, c1058, c1610] c2058 (by decide) p (sat_cons (step1072 p h) (sat_cons (step1057 p h) (sat_cons (step1059 p h) (sat_cons (step1078 p h) (sat_cons (step1080 p h) (sat_cons (step1073 p h) (sat_cons (step1060 p h) (sat_cons (step1069 p h) (sat_cons (step1058 p h) (sat_cons (step1610 p h) (sat_nil p)))))))))))
def c2059 : List Lit := [(1750, true), (113, false), (1735, false), (86, false)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c1437, c1461, c1459, c1440, c1451, c1431, c1449, c722, c1955, c702] c2059 (by decide) p (sat_cons (step1437 p h) (sat_cons (step1461 p h) (sat_cons (step1459 p h) (sat_cons (step1440 p h) (sat_cons (step1451 p h) (sat_cons (step1431 p h) (sat_cons (step1449 p h) (sat_cons (step722 p h) (sat_cons (step1955 p h) (sat_cons (step702 p h) (sat_nil p)))))))))))
def c2060 : List Lit := [(110, false), (113, false), (90, false), (86, false)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c502, c702, c1957] c2060 (by decide) p (sat_cons (step502 p h) (sat_cons (step702 p h) (sat_cons (step1957 p h) (sat_nil p))))
def c2061 : List Lit := [(1745, true), (115, false), (1727, true), (113, false), (1711, false)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c1451, c1453, c1448, c1446, c723, c1380, c1389, c1418, c1400, c1402, c1397, c1395, c1688, c670] c2061 (by decide) p (sat_cons (step1451 p h) (sat_cons (step1453 p h) (sat_cons (step1448 p h) (sat_cons (step1446 p h) (sat_cons (step723 p h) (sat_cons (step1380 p h) (sat_cons (step1389 p h) (sat_cons (step1418 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1397 p h) (sat_cons (step1395 p h) (sat_cons (step1688 p h) (sat_cons (step670 p h) (sat_nil p)))))))))))))))
def c2062 : List Lit := [(1745, false), (1761, true), (110, true), (1735, false), (99, true)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c1383, c1386, c1412, c1474, c1431, c1440, c1465, c1462, c1443, c1479, c1433, c1417, c1413, c1387, c1389, c1400, c1385, c1380, c1397, c1398, c688, c597, c672, c1954] c2062 (by decide) p (sat_cons (step1383 p h) (sat_cons (step1386 p h) (sat_cons (step1412 p h) (sat_cons (step1474 p h) (sat_cons (step1431 p h) (sat_cons (step1440 p h) (sat_cons (step1465 p h) (sat_cons (step1462 p h) (sat_cons (step1443 p h) (sat_cons (step1479 p h) (sat_cons (step1433 p h) (sat_cons (step1417 p h) (sat_cons (step1413 p h) (sat_cons (step1387 p h) (sat_cons (step1389 p h) (sat_cons (step1400 p h) (sat_cons (step1385 p h) (sat_cons (step1380 p h) (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step688 p h) (sat_cons (step597 p h) (sat_cons (step672 p h) (sat_cons (step1954 p h) (sat_nil p)))))))))))))))))))))))))
def c2063 : List Lit := [(1719, true), (1743, true)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c1448, c1397, c1398, c1688, c673] c2063 (by decide) p (sat_cons (step1448 p h) (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step1688 p h) (sat_cons (step673 p h) (sat_nil p))))))
def c2064 : List Lit := [(99, true), (1745, true), (1727, true), (113, false)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c1451, c2063, c1400, c1418, c1387, c1453, c1446, c1383, c2061, c1963, c1389, c1385, c1380, c598] c2064 (by decide) p (sat_cons (step1451 p h) (sat_cons (step2063 p h) (sat_cons (step1400 p h) (sat_cons (step1418 p h) (sat_cons (step1387 p h) (sat_cons (step1453 p h) (sat_cons (step1446 p h) (sat_cons (step1383 p h) (sat_cons (step2061 p h) (sat_cons (step1963 p h) (sat_cons (step1389 p h) (sat_cons (step1385 p h) (sat_cons (step1380 p h) (sat_cons (step598 p h) (sat_nil p)))))))))))))))
def c2065 : List Lit := [(1711, false), (1745, true), (1727, true), (113, false)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c2064, c1451, c2063, c1400, c1418, c1448, c1386, c1389, c1414, c1380, c1401, c1403, c1394, c1395, c614, c1941, c639, c1399, c553, c668, c686, c1947] c2065 (by decide) p (sat_cons (step2064 p h) (sat_cons (step1451 p h) (sat_cons (step2063 p h) (sat_cons (step1400 p h) (sat_cons (step1418 p h) (sat_cons (step1448 p h) (sat_cons (step1386 p h) (sat_cons (step1389 p h) (sat_cons (step1414 p h) (sat_cons (step1380 p h) (sat_cons (step1401 p h) (sat_cons (step1403 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step614 p h) (sat_cons (step1941 p h) (sat_cons (step639 p h) (sat_cons (step1399 p h) (sat_cons (step553 p h) (sat_cons (step668 p h) (sat_cons (step686 p h) (sat_cons (step1947 p h) (sat_nil p)))))))))))))))))))))))
def c2066 : List Lit := [(94, false), (97, false), (116, false), (113, false)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c723, c598, c1963] c2066 (by decide) p (sat_cons (step723 p h) (sat_cons (step598 p h) (sat_cons (step1963 p h) (sat_nil p))))
def c2067 : List Lit := [(1596, true), (55, false), (112, false)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c1183, c1184, c347] c2067 (by decide) p (sat_cons (step1183 p h) (sat_cons (step1184 p h) (sat_cons (step347 p h) (sat_nil p))))
def c2068 : List Lit := [(1617, true), (34, false), (40, false), (1600, false), (38, true), (1574, false), (43, true), (1568, false)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c2002, c1132, c1141, c1152, c1231, c1204, c1236, c1697, c1153, c2053, c1144, c1134] c2068 (by decide) p (sat_cons (step2002 p h) (sat_cons (step1132 p h) (sat_cons (step1141 p h) (sat_cons (step1152 p h) (sat_cons (step1231 p h) (sat_cons (step1204 p h) (sat_cons (step1236 p h) (sat_cons (step1697 p h) (sat_cons (step1153 p h) (sat_cons (step2053 p h) (sat_cons (step1144 p h) (sat_cons (step1134 p h) (sat_nil p)))))))))))))
def c2069 : List Lit := [(1554, true), (1525, false), (1518, false), (19, true), (23, false), (56, false), (57, false)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c1057, c1062, c1685, c1093, c1705, c2057, c1021, c1650, c1720, c117, c1019] c2069 (by decide) p (sat_cons (step1057 p h) (sat_cons (step1062 p h) (sat_cons (step1685 p h) (sat_cons (step1093 p h) (sat_cons (step1705 p h) (sat_cons (step2057 p h) (sat_cons (step1021 p h) (sat_cons (step1650 p h) (sat_cons (step1720 p h) (sat_cons (step117 p h) (sat_cons (step1019 p h) (sat_nil p))))))))))))
def c2070 : List Lit := [(89, false), (1712, true), (93, false), (40, false), (101, false), (100, false)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c554, c636, c1385] c2070 (by decide) p (sat_cons (step554 p h) (sat_cons (step636 p h) (sat_cons (step1385 p h) (sat_nil p))))
def c2071 : List Lit := [(1735, false), (1721, true), (1751, true), (1760, true), (1743, false), (99, true), (104, true)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1394, c1400, c1398, c1451, c1462, c1437, c1440, c1742, c1460, c1432, c1387, c1454, c689, c1954, c1385, c1446, c600] c2071 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1394 p h) (sat_cons (step1400 p h) (sat_cons (step1398 p h) (sat_cons (step1451 p h) (sat_cons (step1462 p h) (sat_cons (step1437 p h) (sat_cons (step1440 p h) (sat_cons (step1742 p h) (sat_cons (step1460 p h) (sat_cons (step1432 p h) (sat_cons (step1387 p h) (sat_cons (step1454 p h) (sat_cons (step689 p h) (sat_cons (step1954 p h) (sat_cons (step1385 p h) (sat_cons (step1446 p h) (sat_cons (step600 p h) (sat_nil p)))))))))))))))))))
def c2072 : List Lit := [(107, false), (113, false), (98, true), (102, false), (103, false), (1715, true), (99, true), (104, true), (105, false)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c689, c1951, c1947, c699, c553, c1385, c1380, c1390] c2072 (by decide) p (sat_cons (step689 p h) (sat_cons (step1951 p h) (sat_cons (step1947 p h) (sat_cons (step699 p h) (sat_cons (step553 p h) (sat_cons (step1385 p h) (sat_cons (step1380 p h) (sat_cons (step1390 p h) (sat_nil p)))))))))
def c2073 : List Lit := [(1721, true), (1751, true), (1760, true), (99, true), (104, true), (105, false), (100, false)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c1688, c1451, c1456, c1483, c1422, c1383, c1400, c1402, c1398, c1394, c617, c2071, c1434, c2072, c1432, c1439, c1742, c1460, c1387, c1389, c1454, c1385, c1380, c1446, c2066] c2073 (by decide) p (sat_cons (step1688 p h) (sat_cons (step1451 p h) (sat_cons (step1456 p h) (sat_cons (step1483 p h) (sat_cons (step1422 p h) (sat_cons (step1383 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1398 p h) (sat_cons (step1394 p h) (sat_cons (step617 p h) (sat_cons (step2071 p h) (sat_cons (step1434 p h) (sat_cons (step2072 p h) (sat_cons (step1432 p h) (sat_cons (step1439 p h) (sat_cons (step1742 p h) (sat_cons (step1460 p h) (sat_cons (step1387 p h) (sat_cons (step1389 p h) (sat_cons (step1454 p h) (sat_cons (step1385 p h) (sat_cons (step1380 p h) (sat_cons (step1446 p h) (sat_cons (step2066 p h) (sat_nil p))))))))))))))))))))))))))
def c2074 : List Lit := [(1760, true), (99, true), (104, true), (105, false), (1725, false), (100, false)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c1688, c1451, c1456, c1383, c1386, c1483, c1473, c2073, c1413, c1418, c1478, c1387, c1389, c1457, c1459, c1385, c1380, c1454, c1437, c1446, c1434, c2066] c2074 (by decide) p (sat_cons (step1688 p h) (sat_cons (step1451 p h) (sat_cons (step1456 p h) (sat_cons (step1383 p h) (sat_cons (step1386 p h) (sat_cons (step1483 p h) (sat_cons (step1473 p h) (sat_cons (step2073 p h) (sat_cons (step1413 p h) (sat_cons (step1418 p h) (sat_cons (step1478 p h) (sat_cons (step1387 p h) (sat_cons (step1389 p h) (sat_cons (step1457 p h) (sat_cons (step1459 p h) (sat_cons (step1385 p h) (sat_cons (step1380 p h) (sat_cons (step1454 p h) (sat_cons (step1437 p h) (sat_cons (step1446 p h) (sat_cons (step1434 p h) (sat_cons (step2066 p h) (sat_nil p)))))))))))))))))))))))
def c2075 : List Lit := [(107, false), (94, false), (97, false), (104, true), (105, false)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c699, c597, c1953] c2075 (by decide) p (sat_cons (step699 p h) (sat_cons (step597 p h) (sat_cons (step1953 p h) (sat_nil p))))
def c2076 : List Lit := [(102, false), (92, true), (103, false), (94, false), (104, true), (100, false)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c617, c686, c1947] c2076 (by decide) p (sat_cons (step617 p h) (sat_cons (step686 p h) (sat_cons (step1947 p h) (sat_nil p))))
def c2077 : List Lit := [(1552, true)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c2055, c1088, c1096, c1698, c1039, c2045, c1017, c1791, c1028, c1031, c1788, c1034, c1038, c1025, c1091, c1819, c1685, c51, c1054] c2077 (by decide) p (sat_cons (step2055 p h) (sat_cons (step1088 p h) (sat_cons (step1096 p h) (sat_cons (step1698 p h) (sat_cons (step1039 p h) (sat_cons (step2045 p h) (sat_cons (step1017 p h) (sat_cons (step1791 p h) (sat_cons (step1028 p h) (sat_cons (step1031 p h) (sat_cons (step1788 p h) (sat_cons (step1034 p h) (sat_cons (step1038 p h) (sat_cons (step1025 p h) (sat_cons (step1091 p h) (sat_cons (step1819 p h) (sat_cons (step1685 p h) (sat_cons (step51 p h) (sat_cons (step1054 p h) (sat_nil p))))))))))))))))))))
def c2078 : List Lit := [(96, true), (91, true), (95, true), (97, false), (105, false)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c1937, c1940, c1598] c2078 (by decide) p (sat_cons (step1937 p h) (sat_cons (step1940 p h) (sat_cons (step1598 p h) (sat_nil p))))
def c2079 : List Lit := [(1598, true), (34, false), (40, false), (93, true)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c1186, c1187, c238, c365, c1868] c2079 (by decide) p (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step238 p h) (sat_cons (step365 p h) (sat_cons (step1868 p h) (sat_nil p))))))
def c2080 : List Lit := [(1601, false), (1617, true), (1568, false), (36, false), (1574, false), (1590, false), (90, false)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c1138, c1151, c1224, c2003, c1205, c1231, c1178, c1152, c1170, c1141, c202, c1133] c2080 (by decide) p (sat_cons (step1138 p h) (sat_cons (step1151 p h) (sat_cons (step1224 p h) (sat_cons (step2003 p h) (sat_cons (step1205 p h) (sat_cons (step1231 p h) (sat_cons (step1178 p h) (sat_cons (step1152 p h) (sat_cons (step1170 p h) (sat_cons (step1141 p h) (sat_cons (step202 p h) (sat_cons (step1133 p h) (sat_nil p)))))))))))))
def c2081 : List Lit := [(1596, false), (1601, true), (1617, true), (40, false), (47, false), (103, false), (33, true), (1574, false), (51, true), (93, true)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1192, c2049, c2079, c1125, c1123] c2081 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1192 p h) (sat_cons (step2049 p h) (sat_cons (step2079 p h) (sat_cons (step1125 p h) (sat_cons (step1123 p h) (sat_nil p)))))))
def c2082 : List Lit := [(1617, true), (40, false), (47, false), (103, false), (33, true), (36, false), (1574, false), (51, true), (93, true), (90, false)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c1122, c1124, c1172, c2080, c2081, c1183, c204, c203, c1170, c1133, c1178, c1141, c1203, c1152, c1236, c1231, c1157, c1204, c1125, c1189, c1123, c2079] c2082 (by decide) p (sat_cons (step1122 p h) (sat_cons (step1124 p h) (sat_cons (step1172 p h) (sat_cons (step2080 p h) (sat_cons (step2081 p h) (sat_cons (step1183 p h) (sat_cons (step204 p h) (sat_cons (step203 p h) (sat_cons (step1170 p h) (sat_cons (step1133 p h) (sat_cons (step1178 p h) (sat_cons (step1141 p h) (sat_cons (step1203 p h) (sat_cons (step1152 p h) (sat_cons (step1236 p h) (sat_cons (step1231 p h) (sat_cons (step1157 p h) (sat_cons (step1204 p h) (sat_cons (step1125 p h) (sat_cons (step1189 p h) (sat_cons (step1123 p h) (sat_cons (step2079 p h) (sat_nil p)))))))))))))))))))))))
def c2083 : List Lit := [(1688, true), (1681, false), (71, false), (105, false)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c1333, c1342, c1345, c1336, c1322, c1326, c1327, c1316, c457, c1921, c432] c2083 (by decide) p (sat_cons (step1333 p h) (sat_cons (step1342 p h) (sat_cons (step1345 p h) (sat_cons (step1336 p h) (sat_cons (step1322 p h) (sat_cons (step1326 p h) (sat_cons (step1327 p h) (sat_cons (step1316 p h) (sat_cons (step457 p h) (sat_cons (step1921 p h) (sat_cons (step432 p h) (sat_nil p))))))))))))
def c2084 : List Lit := [(82, false), (84, true), (74, false), (71, false)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c1921, c432] c2084 (by decide) p (sat_cons (step1921 p h) (sat_cons (step432 p h) (sat_nil p)))
def c2085 : List Lit := [(1519, true), (1505, false), (1, false), (71, false)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c1020, c1045, c1042, c1023, c1033, c5, c1025] c2085 (by decide) p (sat_cons (step1020 p h) (sat_cons (step1045 p h) (sat_cons (step1042 p h) (sat_cons (step1023 p h) (sat_cons (step1033 p h) (sat_cons (step5 p h) (sat_cons (step1025 p h) (sat_nil p))))))))
def c2086 : List Lit := [(1554, true), (6, false), (1543, false), (1519, false), (1, false), (71, false)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c1103, c1098, c1790, c1791, c1028] c2086 (by decide) p (sat_cons (step1103 p h) (sat_cons (step1098 p h) (sat_cons (step1790 p h) (sat_cons (step1791 p h) (sat_cons (step1028 p h) (sat_nil p))))))
def c2087 : List Lit := [(15, false), (83, false), (1526, true), (6, false)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c82, c80, c1055] c2087 (by decide) p (sat_cons (step82 p h) (sat_cons (step80 p h) (sat_cons (step1055 p h) (sat_nil p))))
def c2088 : List Lit := [(29, false), (15, true), (1544, true), (6, false)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c1728, c1851, c1650, c114, c2058] c2088 (by decide) p (sat_cons (step1728 p h) (sat_cons (step1851 p h) (sat_cons (step1650 p h) (sat_cons (step114 p h) (sat_cons (step2058 p h) (sat_nil p))))))
def c2089 : List Lit := [(20, true), (1525, false), (1544, true), (6, false)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c1655, c1063, c1056, c1058, c1062, c1722, c1080, c1650, c1072] c2089 (by decide) p (sat_cons (step1655 p h) (sat_cons (step1063 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1062 p h) (sat_cons (step1722 p h) (sat_cons (step1080 p h) (sat_cons (step1650 p h) (sat_cons (step1072 p h) (sat_nil p))))))))))
def c2090 : List Lit := [(1525, false), (1544, true), (6, false)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c1061, c1078, c2089, c1610, c1069, c1652, c1073, c1080, c1650, c1062, c1841, c113, c1057] c2090 (by decide) p (sat_cons (step1061 p h) (sat_cons (step1078 p h) (sat_cons (step2089 p h) (sat_cons (step1610 p h) (sat_cons (step1069 p h) (sat_cons (step1652 p h) (sat_cons (step1073 p h) (sat_cons (step1080 p h) (sat_cons (step1650 p h) (sat_cons (step1062 p h) (sat_cons (step1841 p h) (sat_cons (step113 p h) (sat_cons (step1057 p h) (sat_nil p))))))))))))))
def c2091 : List Lit := [(83, true), (73, true), (1688, true), (71, false)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1322, c1345, c1337, c1326, c1328, c1334, c1335, c1348, c1329, c1330, c1324, c488, c1318, c1677] c2091 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1322 p h) (sat_cons (step1345 p h) (sat_cons (step1337 p h) (sat_cons (step1326 p h) (sat_cons (step1328 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step1348 p h) (sat_cons (step1329 p h) (sat_cons (step1330 p h) (sat_cons (step1324 p h) (sat_cons (step488 p h) (sat_cons (step1318 p h) (sat_cons (step1677 p h) (sat_nil p))))))))))))))))
def c2092 : List Lit := [(87, true), (1760, true), (112, true), (56, false)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1437, c1458, c1483, c1730, c1473, c1464, c1704, c1956, c1431, c1440, c1441, c1461, c1462, c1436, c1478, c2064, c1409, c1756] c2092 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1437 p h) (sat_cons (step1458 p h) (sat_cons (step1483 p h) (sat_cons (step1730 p h) (sat_cons (step1473 p h) (sat_cons (step1464 p h) (sat_cons (step1704 p h) (sat_cons (step1956 p h) (sat_cons (step1431 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step1436 p h) (sat_cons (step1478 p h) (sat_cons (step2064 p h) (sat_cons (step1409 p h) (sat_cons (step1756 p h) (sat_nil p))))))))))))))))))))
def c2093 : List Lit := [(1719, true), (94, false), (107, false), (1746, true)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c1397, c1398, c2063, c672, c688, c1454, c1954, c1446, c599] c2093 (by decide) p (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step2063 p h) (sat_cons (step672 p h) (sat_cons (step688 p h) (sat_cons (step1454 p h) (sat_cons (step1954 p h) (sat_cons (step1446 p h) (sat_cons (step599 p h) (sat_nil p))))))))))
def c2094 : List Lit := [(94, false), (107, false), (113, false), (1722, true), (99, false), (1746, true)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c1401, c2093, c1403, c1394, c1395, c614, c687, c1941, c639, c1399, c553, c667, c1947] c2094 (by decide) p (sat_cons (step1401 p h) (sat_cons (step2093 p h) (sat_cons (step1403 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step614 p h) (sat_cons (step687 p h) (sat_cons (step1941 p h) (sat_cons (step639 p h) (sat_cons (step1399 p h) (sat_cons (step553 p h) (sat_cons (step667 p h) (sat_cons (step1947 p h) (sat_nil p))))))))))))))
def c2095 : List Lit := [(1666, true), (65, true), (63, true), (47, false), (71, true)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c1737, c2016, c1311, c1798, c1290, c1901, c1288] c2095 (by decide) p (sat_cons (step1737 p h) (sat_cons (step2016 p h) (sat_cons (step1311 p h) (sat_cons (step1798 p h) (sat_cons (step1290 p h) (sat_cons (step1901 p h) (sat_cons (step1288 p h) (sat_nil p))))))))
def c2096 : List Lit := [(1667, true), (60, true), (65, true), (63, true), (47, false), (71, true)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c2014, c1737, c1314, c1312, c1292, c1798, c1288, c1901] c2096 (by decide) p (sat_cons (step2014 p h) (sat_cons (step1737 p h) (sat_cons (step1314 p h) (sat_cons (step1312 p h) (sat_cons (step1292 p h) (sat_cons (step1798 p h) (sat_cons (step1288 p h) (sat_cons (step1901 p h) (sat_nil p)))))))))
def c2097 : List Lit := [(34, false), (40, false), (41, true), (35, false), (38, false), (92, true)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c152, c234, c1865] c2097 (by decide) p (sat_cons (step152 p h) (sat_cons (step234 p h) (sat_cons (step1865 p h) (sat_nil p))))
def c2098 : List Lit := [(15, false), (83, false), (1554, true), (29, false)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c1684, c2047, c83, c1685, c1064, c1802, c1017, c1705, c1098, c1020, c1021, c1023, c1042, c1019, c1031, c1033, c1028, c1025, c1026, c1, c57, c24, c1804] c2098 (by decide) p (sat_cons (step1684 p h) (sat_cons (step2047 p h) (sat_cons (step83 p h) (sat_cons (step1685 p h) (sat_cons (step1064 p h) (sat_cons (step1802 p h) (sat_cons (step1017 p h) (sat_cons (step1705 p h) (sat_cons (step1098 p h) (sat_cons (step1020 p h) (sat_cons (step1021 p h) (sat_cons (step1023 p h) (sat_cons (step1042 p h) (sat_cons (step1019 p h) (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1028 p h) (sat_cons (step1025 p h) (sat_cons (step1026 p h) (sat_cons (step1 p h) (sat_cons (step57 p h) (sat_cons (step24 p h) (sat_cons (step1804 p h) (sat_nil p))))))))))))))))))))))))
def c2099 : List Lit := [(1505, false), (5, false), (1519, true)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c1045, c1020, c1023, c1042, c1031, c1033, c1028, c1025, c1026, c1, c57, c24, c1804] c2099 (by decide) p (sat_cons (step1045 p h) (sat_cons (step1020 p h) (sat_cons (step1023 p h) (sat_cons (step1042 p h) (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1028 p h) (sat_cons (step1025 p h) (sat_cons (step1026 p h) (sat_cons (step1 p h) (sat_cons (step57 p h) (sat_cons (step24 p h) (sat_cons (step1804 p h) (sat_nil p))))))))))))))
def c2100 : List Lit := [(6, false), (1525, false), (23, false), (1637, true), (29, false), (1582, false)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c1728, c118, c114, c1650, c1186, c2057, c1189, c1089, c2002, c1254, c1230] c2100 (by decide) p (sat_cons (step1728 p h) (sat_cons (step118 p h) (sat_cons (step114 p h) (sat_cons (step1650 p h) (sat_cons (step1186 p h) (sat_cons (step2057 p h) (sat_cons (step1189 p h) (sat_cons (step1089 p h) (sat_cons (step2002 p h) (sat_cons (step1254 p h) (sat_cons (step1230 p h) (sat_nil p))))))))))))
def c2101 : List Lit := [(6, true), (1519, true)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c1045, c1021, c1017, c1019, c2099] c2101 (by decide) p (sat_cons (step1045 p h) (sat_cons (step1021 p h) (sat_cons (step1017 p h) (sat_cons (step1019 p h) (sat_cons (step2099 p h) (sat_nil p))))))
def c2102 : List Lit := [(1519, true), (15, true), (1637, true), (29, false), (1582, false)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c1851, c2045, c2101, c2100, c1053, c1054, c1836, c88] c2102 (by decide) p (sat_cons (step1851 p h) (sat_cons (step2045 p h) (sat_cons (step2101 p h) (sat_cons (step2100 p h) (sat_cons (step1053 p h) (sat_cons (step1054 p h) (sat_cons (step1836 p h) (sat_cons (step88 p h) (sat_nil p)))))))))
def c2103 : List Lit := [(1525, false), (15, true), (1637, true), (29, false), (1582, false)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c2007, c1261, c2102, c1098, c2088, c1017, c1020, c1041, c1851, c1685, c1097, c1254, c1230, c2002, c1189, c1186, c1187, c121, c2069] c2103 (by decide) p (sat_cons (step2007 p h) (sat_cons (step1261 p h) (sat_cons (step2102 p h) (sat_cons (step1098 p h) (sat_cons (step2088 p h) (sat_cons (step1017 p h) (sat_cons (step1020 p h) (sat_cons (step1041 p h) (sat_cons (step1851 p h) (sat_cons (step1685 p h) (sat_cons (step1097 p h) (sat_cons (step1254 p h) (sat_cons (step1230 p h) (sat_cons (step2002 p h) (sat_cons (step1189 p h) (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step121 p h) (sat_cons (step2069 p h) (sat_nil p))))))))))))))))))))
def c2104 : List Lit := [(15, true), (1637, true), (29, false), (1582, false)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c2055, c2007, c1261, c1851, c2102, c1098, c2088, c1721, c1017, c1020, c2103, c1053, c1054, c1711, c1043, c1102, c1254, c1230, c2002, c1189, c1186, c121, c122, c2058, c1650] c2104 (by decide) p (sat_cons (step2055 p h) (sat_cons (step2007 p h) (sat_cons (step1261 p h) (sat_cons (step1851 p h) (sat_cons (step2102 p h) (sat_cons (step1098 p h) (sat_cons (step2088 p h) (sat_cons (step1721 p h) (sat_cons (step1017 p h) (sat_cons (step1020 p h) (sat_cons (step2103 p h) (sat_cons (step1053 p h) (sat_cons (step1054 p h) (sat_cons (step1711 p h) (sat_cons (step1043 p h) (sat_cons (step1102 p h) (sat_cons (step1254 p h) (sat_cons (step1230 p h) (sat_cons (step2002 p h) (sat_cons (step1189 p h) (sat_cons (step1186 p h) (sat_cons (step121 p h) (sat_cons (step122 p h) (sat_cons (step2058 p h) (sat_cons (step1650 p h) (sat_nil p))))))))))))))))))))))))))
def c2105 : List Lit := [(1525, true), (15, false), (29, false)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c1053, c1054, c84] c2105 (by decide) p (sat_cons (step1053 p h) (sat_cons (step1054 p h) (sat_cons (step84 p h) (sat_nil p))))
def c2106 : List Lit := [(6, true), (1637, true), (29, false), (1582, false), (34, false)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c2104, c2105, c1685, c2007, c1261, c1017, c2101, c1020, c1097, c1041, c1254, c1230, c2002, c1189, c1191, c1186, c1187, c1184, c368, c331, c1893, c121, c2069] c2106 (by decide) p (sat_cons (step2104 p h) (sat_cons (step2105 p h) (sat_cons (step1685 p h) (sat_cons (step2007 p h) (sat_cons (step1261 p h) (sat_cons (step1017 p h) (sat_cons (step2101 p h) (sat_cons (step1020 p h) (sat_cons (step1097 p h) (sat_cons (step1041 p h) (sat_cons (step1254 p h) (sat_cons (step1230 p h) (sat_cons (step2002 p h) (sat_cons (step1189 p h) (sat_cons (step1191 p h) (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step1184 p h) (sat_cons (step368 p h) (sat_cons (step331 p h) (sat_cons (step1893 p h) (sat_cons (step121 p h) (sat_cons (step2069 p h) (sat_nil p))))))))))))))))))))))))
def c2107 : List Lit := [(1600, true), (23, true), (6, false), (34, false)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c1189, c1191, c1186, c1187, c1184, c368, c227, c1894] c2107 (by decide) p (sat_cons (step1189 p h) (sat_cons (step1191 p h) (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step1184 p h) (sat_cons (step368 p h) (sat_cons (step227 p h) (sat_cons (step1894 p h) (sat_nil p)))))))))
def c2108 : List Lit := [(1637, true), (29, false), (1582, false), (34, false)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c2104, c2105, c2106, c1728, c1557, c1650, c2107, c2002, c1230, c1254, c1089, c2057, c15, c1839] c2108 (by decide) p (sat_cons (step2104 p h) (sat_cons (step2105 p h) (sat_cons (step2106 p h) (sat_cons (step1728 p h) (sat_cons (step1557 p h) (sat_cons (step1650 p h) (sat_cons (step2107 p h) (sat_cons (step2002 p h) (sat_cons (step1230 p h) (sat_cons (step1254 p h) (sat_cons (step1089 p h) (sat_cons (step2057 p h) (sat_cons (step15 p h) (sat_cons (step1839 p h) (sat_nil p)))))))))))))))
def c2109 : List Lit := [(19, false), (6, false), (23, true), (34, false)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c15, c1839] c2109 (by decide) p (sat_cons (step15 p h) (sat_cons (step1839 p h) (sat_nil p)))
def c2110 : List Lit := [(1546, true), (19, true), (1526, false), (1534, false)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c1057, c1065, c1072, c1086, c1084, c1066, c1073, c1058, c1069, c1610] c2110 (by decide) p (sat_cons (step1057 p h) (sat_cons (step1065 p h) (sat_cons (step1072 p h) (sat_cons (step1086 p h) (sat_cons (step1084 p h) (sat_cons (step1066 p h) (sat_cons (step1073 p h) (sat_cons (step1058 p h) (sat_cons (step1069 p h) (sat_cons (step1610 p h) (sat_nil p)))))))))))
def c2111 : List Lit := [(45, true), (54, false), (1593, true), (90, false)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c1180, c1169, c1171, c1178, c204, c1172, c1173, c1876, c306] c2111 (by decide) p (sat_cons (step1180 p h) (sat_cons (step1169 p h) (sat_cons (step1171 p h) (sat_cons (step1178 p h) (sat_cons (step204 p h) (sat_cons (step1172 p h) (sat_cons (step1173 p h) (sat_cons (step1876 p h) (sat_cons (step306 p h) (sat_nil p))))))))))
def c2112 : List Lit := [(35, false), (45, false), (54, false), (39, false), (90, false), (34, false)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c2053, c203, c209, c176, c1861] c2112 (by decide) p (sat_cons (step2053 p h) (sat_cons (step203 p h) (sat_cons (step209 p h) (sat_cons (step176 p h) (sat_cons (step1861 p h) (sat_nil p))))))
def c2113 : List Lit := [(1779, true)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c1771, c1773] c2113 (by decide) p (sat_cons (step1771 p h) (sat_cons (step1773 p h) (sat_nil p)))
def c2114 : List Lit := [(1642, false)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c2113, c2044] c2114 (by decide) p (sat_cons (step2113 p h) (sat_cons (step2044 p h) (sat_nil p)))
def c2115 : List Lit := [(46, true), (45, false), (34, false)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c1878, c1879, c1568] c2115 (by decide) p (sat_cons (step1878 p h) (sat_cons (step1879 p h) (sat_cons (step1568 p h) (sat_nil p))))
def c2116 : List Lit := [(57, false), (53, false), (39, true), (23, true), (34, false)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c331, c1895] c2116 (by decide) p (sat_cons (step331 p h) (sat_cons (step1895 p h) (sat_nil p)))
def c2117 : List Lit := [(52, false), (2, false), (45, false), (34, false)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c173, c169, c1880] c2117 (by decide) p (sat_cons (step173 p h) (sat_cons (step169 p h) (sat_cons (step1880 p h) (sat_nil p))))
def c2118 : List Lit := [(13, false), (46, false), (45, false), (1593, true)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c282, c280, c1172, c1170, c1178] c2118 (by decide) p (sat_cons (step282 p h) (sat_cons (step280 p h) (sat_cons (step1172 p h) (sat_cons (step1170 p h) (sat_cons (step1178 p h) (sat_nil p))))))
end B112E008
