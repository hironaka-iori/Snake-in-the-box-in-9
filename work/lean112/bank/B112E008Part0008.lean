import B112E008Part0007
namespace B112E008
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2119 : List Lit := [(1519, true), (2, false), (1514, false), (34, false)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c2101, c1042, c13, c1022] c2119 (by decide) p (sat_cons (step2101 p h) (sat_cons (step1042 p h) (sat_cons (step13 p h) (sat_cons (step1022 p h) (sat_nil p)))))
def c2120 : List Lit := [(1507, true), (2, false), (34, false)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c1020, c1022, c1017, c13] c2120 (by decide) p (sat_cons (step1020 p h) (sat_cons (step1022 p h) (sat_cons (step1017 p h) (sat_cons (step13 p h) (sat_nil p)))))
def c2121 : List Lit := [(32, false), (45, false), (2, false), (34, false)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c165, c167, c1880] c2121 (by decide) p (sat_cons (step165 p h) (sat_cons (step167 p h) (sat_cons (step1880 p h) (sat_nil p))))
def c2122 : List Lit := [(99, false), (1681, true), (1722, true), (90, false)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c1774, c1756] c2122 (by decide) p (sat_cons (step1774 p h) (sat_cons (step1756 p h) (sat_nil p)))
def c2123 : List Lit := [(94, false), (1687, true), (104, true), (100, false), (102, false), (103, false)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c2076, c550, c548, c1330, c1316, c1332, c1322, c1344] c2123 (by decide) p (sat_cons (step2076 p h) (sat_cons (step550 p h) (sat_cons (step548 p h) (sat_cons (step1330 p h) (sat_cons (step1316 p h) (sat_cons (step1332 p h) (sat_cons (step1322 p h) (sat_cons (step1344 p h) (sat_nil p)))))))))
def c2124 : List Lit := [(1682, false), (110, false), (97, false), (1697, true), (100, false), (105, false), (90, false)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c2021, c1340, c1344, c1363, c1322, c2015, c1317, c1737, c529, c496, c1775, c638, c557, c1928] c2124 (by decide) p (sat_cons (step2021 p h) (sat_cons (step1340 p h) (sat_cons (step1344 p h) (sat_cons (step1363 p h) (sat_cons (step1322 p h) (sat_cons (step2015 p h) (sat_cons (step1317 p h) (sat_cons (step1737 p h) (sat_cons (step529 p h) (sat_cons (step496 p h) (sat_cons (step1775 p h) (sat_cons (step638 p h) (sat_cons (step557 p h) (sat_cons (step1928 p h) (sat_nil p)))))))))))))))
def c2125 : List Lit := [(1680, true), (97, false), (100, false), (105, false), (90, false)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c1329, c1330, c638, c532, c557, c1689] c2125 (by decide) p (sat_cons (step1329 p h) (sat_cons (step1330 p h) (sat_cons (step638 p h) (sat_cons (step532 p h) (sat_cons (step557 p h) (sat_cons (step1689 p h) (sat_nil p)))))))
def c2126 : List Lit := [(1721, true), (1780, true), (99, true), (1711, false), (1715, true), (1725, false), (90, false)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c2028, c1400, c1402, c1397, c1398, c2063, c1394, c1395, c666, c1451, c2074, c1513, c2021, c2123, c1380, c1390, c1389, c1385, c2125, c1417, c1332, c1479, c2124, c1462, c1761] c2126 (by decide) p (sat_cons (step2028 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step2063 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step666 p h) (sat_cons (step1451 p h) (sat_cons (step2074 p h) (sat_cons (step1513 p h) (sat_cons (step2021 p h) (sat_cons (step2123 p h) (sat_cons (step1380 p h) (sat_cons (step1390 p h) (sat_cons (step1389 p h) (sat_cons (step1385 p h) (sat_cons (step2125 p h) (sat_cons (step1417 p h) (sat_cons (step1332 p h) (sat_cons (step1479 p h) (sat_cons (step2124 p h) (sat_cons (step1462 p h) (sat_cons (step1761 p h) (sat_nil p))))))))))))))))))))))))))
def c2127 : List Lit := [(1697, true), (1680, false), (1682, false), (105, false)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c1340, c2021, c1363, c1341, c1344, c2015, c1335, c1322, c1737, c1326, c1327, c1316, c457, c2084] c2127 (by decide) p (sat_cons (step1340 p h) (sat_cons (step2021 p h) (sat_cons (step1363 p h) (sat_cons (step1341 p h) (sat_cons (step1344 p h) (sat_cons (step2015 p h) (sat_cons (step1335 p h) (sat_cons (step1322 p h) (sat_cons (step1737 p h) (sat_cons (step1326 p h) (sat_cons (step1327 p h) (sat_cons (step1316 p h) (sat_cons (step457 p h) (sat_cons (step2084 p h) (sat_nil p)))))))))))))))
def c2128 : List Lit := [(1738, true), (110, true), (74, false), (98, true), (104, true), (103, false), (102, false)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1442, c1440, c1433, c1434, c689, c549, c1947] c2128 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1442 p h) (sat_cons (step1440 p h) (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step689 p h) (sat_cons (step549 p h) (sat_cons (step1947 p h) (sat_nil p)))))))))
def c2129 : List Lit := [(1763, false), (1688, false), (1582, false), (1660, false)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c2077, c2015, c1365, c2007, c1250, c2037, c1537, c1530, c1371, c2038, c1311, c1251, c2014, c1230, c1662, c2002] c2129 (by decide) p (sat_cons (step2077 p h) (sat_cons (step2015 p h) (sat_cons (step1365 p h) (sat_cons (step2007 p h) (sat_cons (step1250 p h) (sat_cons (step2037 p h) (sat_cons (step1537 p h) (sat_cons (step1530 p h) (sat_cons (step1371 p h) (sat_cons (step2038 p h) (sat_cons (step1311 p h) (sat_cons (step1251 p h) (sat_cons (step2014 p h) (sat_cons (step1230 p h) (sat_cons (step1662 p h) (sat_cons (step2002 p h) (sat_nil p)))))))))))))))))
def c2130 : List Lit := [(1605, true), (1590, false), (36, false), (90, false)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c1203, c2002, c1178, c1191, c1170, c1183, c204] c2130 (by decide) p (sat_cons (step1203 p h) (sat_cons (step2002 p h) (sat_cons (step1178 p h) (sat_cons (step1191 p h) (sat_cons (step1170 p h) (sat_cons (step1183 p h) (sat_cons (step204 p h) (sat_nil p))))))))
def c2131 : List Lit := [(97, true), (1726, true)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c1417, c1387, c1384, c1385, c1386, c1413, c1400, c1402, c1397, c1398, c1394, c1395, c639, c616, c1941] c2131 (by decide) p (sat_cons (step1417 p h) (sat_cons (step1387 p h) (sat_cons (step1384 p h) (sat_cons (step1385 p h) (sat_cons (step1386 p h) (sat_cons (step1413 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step639 p h) (sat_cons (step616 p h) (sat_cons (step1941 p h) (sat_nil p))))))))))))))))
def c2132 : List Lit := [(1726, true), (95, false), (90, false)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c1417, c2131, c578, c1380, c1388, c1389, c1413, c1383, c1400, c1402, c1397, c1398, c1394, c1395, c639, c616, c1941] c2132 (by decide) p (sat_cons (step1417 p h) (sat_cons (step2131 p h) (sat_cons (step578 p h) (sat_cons (step1380 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1413 p h) (sat_cons (step1383 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step639 p h) (sat_cons (step616 p h) (sat_cons (step1941 p h) (sat_nil p))))))))))))))))))
def c2133 : List Lit := [(99, false), (98, true), (100, false), (105, false)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c639, c1941] c2133 (by decide) p (sat_cons (step639 p h) (sat_cons (step1941 p h) (sat_nil p)))
def c2134 : List Lit := [(1544, true), (1519, true)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c2101, c1039, c2090, c1791, c1053, c1054, c1711] c2134 (by decide) p (sat_cons (step2101 p h) (sat_cons (step1039 p h) (sat_cons (step2090 p h) (sat_cons (step1791 p h) (sat_cons (step1053 p h) (sat_cons (step1054 p h) (sat_cons (step1711 p h) (sat_nil p))))))))
def c2135 : List Lit := [(1518, true)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c1038, c1041, c1031, c1033, c1020, c1022, c1028, c1025, c1018, c57, c1, c1818] c2135 (by decide) p (sat_cons (step1038 p h) (sat_cons (step1041 p h) (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1020 p h) (sat_cons (step1022 p h) (sat_cons (step1028 p h) (sat_cons (step1025 p h) (sat_cons (step1018 p h) (sat_cons (step57 p h) (sat_cons (step1 p h) (sat_cons (step1818 p h) (sat_nil p)))))))))))))
def c2136 : List Lit := [(1600, true), (36, true), (1543, true)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c1189, c1191, c1186, c1183, c1184, c1668, c1888, c343] c2136 (by decide) p (sat_cons (step1189 p h) (sat_cons (step1191 p h) (sat_cons (step1186 p h) (sat_cons (step1183 p h) (sat_cons (step1184 p h) (sat_cons (step1668 p h) (sat_cons (step1888 p h) (sat_cons (step343 p h) (sat_nil p)))))))))
def c2137 : List Lit := [(20, true), (1553, true)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c2055, c2135, c1092, c2134, c1097, c1685, c1054, c1053, c1654, c1060, c1102, c1056, c1058, c1059, c1077, c1652, c1072, c1069, c1650, c1609, c1841, c113, c1711, c1017, c1043, c1020] c2137 (by decide) p (sat_cons (step2055 p h) (sat_cons (step2135 p h) (sat_cons (step1092 p h) (sat_cons (step2134 p h) (sat_cons (step1097 p h) (sat_cons (step1685 p h) (sat_cons (step1054 p h) (sat_cons (step1053 p h) (sat_cons (step1654 p h) (sat_cons (step1060 p h) (sat_cons (step1102 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step1077 p h) (sat_cons (step1652 p h) (sat_cons (step1072 p h) (sat_cons (step1069 p h) (sat_cons (step1650 p h) (sat_cons (step1609 p h) (sat_cons (step1841 p h) (sat_cons (step113 p h) (sat_cons (step1711 p h) (sat_cons (step1017 p h) (sat_cons (step1043 p h) (sat_cons (step1020 p h) (sat_nil p)))))))))))))))))))))))))))
def c2138 : List Lit := [(1553, true)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c2055, c2135, c1102, c1092, c2134, c1097, c1075, c1685, c1053, c1054, c2137, c1608, c1610, c1711, c1069, c1043, c1652, c1073, c1020, c1077, c1650, c1017, c1059, c1722, c1057] c2138 (by decide) p (sat_cons (step2055 p h) (sat_cons (step2135 p h) (sat_cons (step1102 p h) (sat_cons (step1092 p h) (sat_cons (step2134 p h) (sat_cons (step1097 p h) (sat_cons (step1075 p h) (sat_cons (step1685 p h) (sat_cons (step1053 p h) (sat_cons (step1054 p h) (sat_cons (step2137 p h) (sat_cons (step1608 p h) (sat_cons (step1610 p h) (sat_cons (step1711 p h) (sat_cons (step1069 p h) (sat_cons (step1043 p h) (sat_cons (step1652 p h) (sat_cons (step1073 p h) (sat_cons (step1020 p h) (sat_cons (step1077 p h) (sat_cons (step1650 p h) (sat_cons (step1017 p h) (sat_cons (step1059 p h) (sat_cons (step1722 p h) (sat_cons (step1057 p h) (sat_nil p))))))))))))))))))))))))))
def c2139 : List Lit := [(1621, false)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c2138, c2114, c1259] c2139 (by decide) p (sat_cons (step2138 p h) (sat_cons (step2114 p h) (sat_cons (step1259 p h) (sat_nil p))))
def c2140 : List Lit := [(98, true), (104, true), (107, false), (105, false), (1714, true), (89, false)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c1387, c1679, c2075, c1385, c1943, c1941, c1592] c2140 (by decide) p (sat_cons (step1387 p h) (sat_cons (step1679 p h) (sat_cons (step2075 p h) (sat_cons (step1385 p h) (sat_cons (step1943 p h) (sat_cons (step1941 p h) (sat_cons (step1592 p h) (sat_nil p))))))))
def c2141 : List Lit := [(99, false), (98, false), (103, false), (1718, true)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c616, c615, c1396] c2141 (by decide) p (sat_cons (step616 p h) (sat_cons (step615 p h) (sat_cons (step1396 p h) (sat_nil p))))
def c2142 : List Lit := [(107, false), (1719, true), (1714, true), (1718, true), (89, false)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c1398, c1397, c1387, c672, c2140, c2141, c1383, c1385, c1389, c2075, c1380] c2142 (by decide) p (sat_cons (step1398 p h) (sat_cons (step1397 p h) (sat_cons (step1387 p h) (sat_cons (step672 p h) (sat_cons (step2140 p h) (sat_cons (step2141 p h) (sat_cons (step1383 p h) (sat_cons (step1385 p h) (sat_cons (step1389 p h) (sat_cons (step2075 p h) (sat_cons (step1380 p h) (sat_nil p))))))))))))
def c2143 : List Lit := [(99, true), (1752, true), (107, true), (1743, false), (105, false), (1714, true), (89, false)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c1387, c1383, c1385, c1389, c1380, c1381, c532, c578, c2078, c1932, c598, c505, c1446, c1433, c1454, c1442, c1463] c2143 (by decide) p (sat_cons (step1387 p h) (sat_cons (step1383 p h) (sat_cons (step1385 p h) (sat_cons (step1389 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step532 p h) (sat_cons (step578 p h) (sat_cons (step2078 p h) (sat_cons (step1932 p h) (sat_cons (step598 p h) (sat_cons (step505 p h) (sat_cons (step1446 p h) (sat_cons (step1433 p h) (sat_cons (step1454 p h) (sat_cons (step1442 p h) (sat_cons (step1463 p h) (sat_nil p))))))))))))))))))
def c2144 : List Lit := [(99, false), (1719, true), (1718, true), (89, false)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c1398, c1397, c637, c2141, c1941] c2144 (by decide) p (sat_cons (step1398 p h) (sat_cons (step1397 p h) (sat_cons (step637 p h) (sat_cons (step2141 p h) (sat_cons (step1941 p h) (sat_nil p))))))
def c2145 : List Lit := [(106, true), (104, true), (98, true), (1617, true), (42, true), (33, true), (51, true), (36, false), (90, false), (94, false), (93, true), (103, false)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c1122, c1124, c1172, c2130, c1236, c1153, c1135, c1947, c1948, c543, c2082, c1132, c1137, c1142] c2145 (by decide) p (sat_cons (step1122 p h) (sat_cons (step1124 p h) (sat_cons (step1172 p h) (sat_cons (step2130 p h) (sat_cons (step1236 p h) (sat_cons (step1153 p h) (sat_cons (step1135 p h) (sat_cons (step1947 p h) (sat_cons (step1948 p h) (sat_cons (step543 p h) (sat_cons (step2082 p h) (sat_cons (step1132 p h) (sat_cons (step1137 p h) (sat_cons (step1142 p h) (sat_nil p)))))))))))))))
def c2146 : List Lit := [(104, true), (88, false), (98, true), (1617, true), (42, true), (33, true), (51, true), (96, false), (36, false), (90, false), (94, false), (93, true), (103, false), (1718, true), (89, false)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c1172, c2130, c1236, c1135, c2145, c576, c686, c1950, c1396, c2082, c509, c1137, c1123, c1139, c1125, c1157] c2146 (by decide) p (sat_cons (step1172 p h) (sat_cons (step2130 p h) (sat_cons (step1236 p h) (sat_cons (step1135 p h) (sat_cons (step2145 p h) (sat_cons (step576 p h) (sat_cons (step686 p h) (sat_cons (step1950 p h) (sat_cons (step1396 p h) (sat_cons (step2082 p h) (sat_cons (step509 p h) (sat_cons (step1137 p h) (sat_cons (step1123 p h) (sat_cons (step1139 p h) (sat_cons (step1125 p h) (sat_cons (step1157 p h) (sat_nil p)))))))))))))))))
def c2147 : List Lit := [(104, false), (98, true), (1665, false), (1680, false), (1672, false), (42, true), (33, true), (51, true), (36, false), (90, false), (94, false), (1762, false), (93, true), (103, false), (105, false), (1718, true)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c2138, c1172, c2130, c1122, c1124, c1135, c1138, c1151, c1222, c1253, c2038, c1536, c1366, c1332, c1321, c1344, c1364, c1522, c2040, c1255, c660, c666, c1326, c1396, c1335, c686, c1349, c1345, c1323, c1365, c1316, c1529, c548, c2039, c1949, c1254, c2082, c1230, c1137, c1152, c1139] c2147 (by decide) p (sat_cons (step2138 p h) (sat_cons (step1172 p h) (sat_cons (step2130 p h) (sat_cons (step1122 p h) (sat_cons (step1124 p h) (sat_cons (step1135 p h) (sat_cons (step1138 p h) (sat_cons (step1151 p h) (sat_cons (step1222 p h) (sat_cons (step1253 p h) (sat_cons (step2038 p h) (sat_cons (step1536 p h) (sat_cons (step1366 p h) (sat_cons (step1332 p h) (sat_cons (step1321 p h) (sat_cons (step1344 p h) (sat_cons (step1364 p h) (sat_cons (step1522 p h) (sat_cons (step2040 p h) (sat_cons (step1255 p h) (sat_cons (step660 p h) (sat_cons (step666 p h) (sat_cons (step1326 p h) (sat_cons (step1396 p h) (sat_cons (step1335 p h) (sat_cons (step686 p h) (sat_cons (step1349 p h) (sat_cons (step1345 p h) (sat_cons (step1323 p h) (sat_cons (step1365 p h) (sat_cons (step1316 p h) (sat_cons (step1529 p h) (sat_cons (step548 p h) (sat_cons (step2039 p h) (sat_cons (step1949 p h) (sat_cons (step1254 p h) (sat_cons (step2082 p h) (sat_cons (step1230 p h) (sat_cons (step1137 p h) (sat_cons (step1152 p h) (sat_cons (step1139 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c2148 : List Lit := [(98, true), (1665, false), (1680, false), (1672, false), (42, true), (33, true), (51, true), (96, false), (36, false), (91, true), (90, false), (94, false), (1762, false), (93, true), (103, false), (105, false), (1718, true), (89, false)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c2138, c1332, c1321, c1344, c1364, c1522, c2040, c1255, c2147, c2145, c2146, c686, c1927, c1396, c638] c2148 (by decide) p (sat_cons (step2138 p h) (sat_cons (step1332 p h) (sat_cons (step1321 p h) (sat_cons (step1344 p h) (sat_cons (step1364 p h) (sat_cons (step1522 p h) (sat_cons (step2040 p h) (sat_cons (step1255 p h) (sat_cons (step2147 p h) (sat_cons (step2145 p h) (sat_cons (step2146 p h) (sat_cons (step686 p h) (sat_cons (step1927 p h) (sat_cons (step1396 p h) (sat_cons (step638 p h) (sat_nil p))))))))))))))))
def c2149 : List Lit := [(1719, true), (100, false), (102, false), (1714, true), (1718, true), (89, false)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c1387, c1674, c1412, c1397, c1398, c2063, c2142, c2144, c666, c638, c617, c1383, c1385, c1679, c1389, c557, c2076, c1381, c553, c532, c578, c2125, c1434, c1928, c1933, c2078, c1690, c505, c492, c482, c585, c591, c598, c1433, c1737, c1320, c1446, c1443, c2015, c1454, c1466, c2148, c1475] c2149 (by decide) p (sat_cons (step1387 p h) (sat_cons (step1674 p h) (sat_cons (step1412 p h) (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step2063 p h) (sat_cons (step2142 p h) (sat_cons (step2144 p h) (sat_cons (step666 p h) (sat_cons (step638 p h) (sat_cons (step617 p h) (sat_cons (step1383 p h) (sat_cons (step1385 p h) (sat_cons (step1679 p h) (sat_cons (step1389 p h) (sat_cons (step557 p h) (sat_cons (step2076 p h) (sat_cons (step1381 p h) (sat_cons (step553 p h) (sat_cons (step532 p h) (sat_cons (step578 p h) (sat_cons (step2125 p h) (sat_cons (step1434 p h) (sat_cons (step1928 p h) (sat_cons (step1933 p h) (sat_cons (step2078 p h) (sat_cons (step1690 p h) (sat_cons (step505 p h) (sat_cons (step492 p h) (sat_cons (step482 p h) (sat_cons (step585 p h) (sat_cons (step591 p h) (sat_cons (step598 p h) (sat_cons (step1433 p h) (sat_cons (step1737 p h) (sat_cons (step1320 p h) (sat_cons (step1446 p h) (sat_cons (step1443 p h) (sat_cons (step2015 p h) (sat_cons (step1454 p h) (sat_cons (step1466 p h) (sat_cons (step2148 p h) (sat_cons (step1475 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c2150 : List Lit := [(95, false), (77, false), (92, false), (94, false)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c568, c574, c1914] c2150 (by decide) p (sat_cons (step568 p h) (sat_cons (step574 p h) (sat_cons (step1914 p h) (sat_nil p))))
def c2151 : List Lit := [(1574, false), (1568, false), (36, false), (90, false), (38, true), (1616, true)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c2008, c1153, c1132, c1141, c1144, c1152, c1134, c1230, c203, c2002, c1183, c1191] c2151 (by decide) p (sat_cons (step2008 p h) (sat_cons (step1153 p h) (sat_cons (step1132 p h) (sat_cons (step1141 p h) (sat_cons (step1144 p h) (sat_cons (step1152 p h) (sat_cons (step1134 p h) (sat_cons (step1230 p h) (sat_cons (step203 p h) (sat_cons (step2002 p h) (sat_cons (step1183 p h) (sat_cons (step1191 p h) (sat_nil p)))))))))))))
def c2152 : List Lit := [(99, false), (89, false), (100, false), (103, false)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c615, c636, c1941] c2152 (by decide) p (sat_cons (step615 p h) (sat_cons (step636 p h) (sat_cons (step1941 p h) (sat_nil p))))
def c2153 : List Lit := [(1578, false), (1637, true)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c2138, c1254, c2008, c1148, c1153, c1124, c1126, c1121, c1118, c2108] c2153 (by decide) p (sat_cons (step2138 p h) (sat_cons (step1254 p h) (sat_cons (step2008 p h) (sat_cons (step1148 p h) (sat_cons (step1153 p h) (sat_cons (step1124 p h) (sat_cons (step1126 p h) (sat_cons (step1121 p h) (sat_cons (step1118 p h) (sat_cons (step2108 p h) (sat_nil p)))))))))))
def c2154 : List Lit := [(34, true), (36, false), (35, false), (1577, false), (1616, true)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c2008, c1157, c1125, c1121, c1123, c1124, c196, c1152, c1183, c1230, c1191, c2002] c2154 (by decide) p (sat_cons (step2008 p h) (sat_cons (step1157 p h) (sat_cons (step1125 p h) (sat_cons (step1121 p h) (sat_cons (step1123 p h) (sat_cons (step1124 p h) (sat_cons (step196 p h) (sat_cons (step1152 p h) (sat_cons (step1183 p h) (sat_cons (step1230 p h) (sat_cons (step1191 p h) (sat_cons (step2002 p h) (sat_nil p)))))))))))))
def c2155 : List Lit := [(19, false), (53, false), (57, false), (29, false)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.LocalRup.prove_clause [c121, c328, c1837] c2155 (by decide) p (sat_cons (step121 p h) (sat_cons (step328 p h) (sat_cons (step1837 p h) (sat_nil p))))
def c2156 : List Lit := [(1675, true), (73, true), (97, false), (94, false)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1324, c1323, c1318, c1320, c433, c591, c1914] c2156 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1324 p h) (sat_cons (step1323 p h) (sat_cons (step1318 p h) (sat_cons (step1320 p h) (sat_cons (step433 p h) (sat_cons (step591 p h) (sat_cons (step1914 p h) (sat_nil p)))))))))
def c2157 : List Lit := [(110, true), (1734, true), (1720, true), (1761, true), (94, false), (99, true), (1735, false)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c2062, c1433, c1764] c2157 (by decide) p (sat_cons (step2062 p h) (sat_cons (step1433 p h) (sat_cons (step1764 p h) (sat_nil p))))
def c2158 : List Lit := [(1761, true), (94, false), (1714, false), (99, true), (112, true), (87, true)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c1417, c1435, c1437, c1458, c1489, c1479, c1419, c1464, c1401, c1443, c2157, c1957, c1956, c1606, c1436, c1438, c1441, c1462, c1432, c1764] c2158 (by decide) p (sat_cons (step1417 p h) (sat_cons (step1435 p h) (sat_cons (step1437 p h) (sat_cons (step1458 p h) (sat_cons (step1489 p h) (sat_cons (step1479 p h) (sat_cons (step1419 p h) (sat_cons (step1464 p h) (sat_cons (step1401 p h) (sat_cons (step1443 p h) (sat_cons (step2157 p h) (sat_cons (step1957 p h) (sat_cons (step1956 p h) (sat_cons (step1606 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1441 p h) (sat_cons (step1462 p h) (sat_cons (step1432 p h) (sat_cons (step1764 p h) (sat_nil p)))))))))))))))))))))
def c2159 : List Lit := [(1682, true), (74, false), (71, false), (89, false)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c1332, c1334, c1330, c1327, c488, c1677] c2159 (by decide) p (sat_cons (step1332 p h) (sat_cons (step1334 p h) (sat_cons (step1330 p h) (sat_cons (step1327 p h) (sat_cons (step488 p h) (sat_cons (step1677 p h) (sat_nil p)))))))
def c2160 : List Lit := [(54, false), (56, false), (60, false), (53, false)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c1701, c369] c2160 (by decide) p (sat_cons (step1701 p h) (sat_cons (step369 p h) (sat_nil p)))
def c2161 : List Lit := [(1601, true), (57, true), (60, false)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c1186, c1190, c1188, c1192, c1183, c1184, c2160] c2161 (by decide) p (sat_cons (step1186 p h) (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1192 p h) (sat_cons (step1183 p h) (sat_cons (step1184 p h) (sat_cons (step2160 p h) (sat_nil p))))))))
def c2162 : List Lit := [(1737, true), (87, true)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c1437, c1439, c1434, c1431, c1957, c1956, c1606] c2162 (by decide) p (sat_cons (step1437 p h) (sat_cons (step1439 p h) (sat_cons (step1434 p h) (sat_cons (step1431 p h) (sat_cons (step1957 p h) (sat_cons (step1956 p h) (sat_cons (step1606 p h) (sat_nil p))))))))
def c2163 : List Lit := [(1581, true), (1564, false)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c1126, c1155, c1151, c1127, c1779, c1121] c2163 (by decide) p (sat_cons (step1126 p h) (sat_cons (step1155 p h) (sat_cons (step1151 p h) (sat_cons (step1127 p h) (sat_cons (step1779 p h) (sat_cons (step1121 p h) (sat_nil p)))))))
def c2164 : List Lit := [(297, true), (25, true), (1565, true), (29, true)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c839, c840, c145, c1725] c2164 (by decide) p (sat_cons (step839 p h) (sat_cons (step840 p h) (sat_cons (step145 p h) (sat_cons (step1725 p h) (sat_nil p)))))
def c2165 : List Lit := [(5, false), (33, false), (87, true), (74, false), (71, false)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c429, c9, c1907] c2165 (by decide) p (sat_cons (step429 p h) (sat_cons (step9 p h) (sat_cons (step1907 p h) (sat_nil p))))
def c2166 : List Lit := [(1601, true), (1598, false), (34, false), (60, false)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c2161, c1192, c1183, c1184, c346, c370, c331, c1885] c2166 (by decide) p (sat_cons (step2161 p h) (sat_cons (step1192 p h) (sat_cons (step1183 p h) (sat_cons (step1184 p h) (sat_cons (step346 p h) (sat_cons (step370 p h) (sat_cons (step331 p h) (sat_cons (step1885 p h) (sat_nil p)))))))))
def c2167 : List Lit := [(1760, true), (1713, false), (1733, false), (1745, true), (87, true)]
theorem step2167 (p : Nat → Bool) (h : Constraints p) : clause p c2167 = true :=
  Snake9.LocalRup.prove_clause [c1451, c2063, c1400, c1413, c2162, c1458, c1483, c1478, c1414, c1461, c1756, c1440, c2064, c1434] c2167 (by decide) p (sat_cons (step1451 p h) (sat_cons (step2063 p h) (sat_cons (step1400 p h) (sat_cons (step1413 p h) (sat_cons (step2162 p h) (sat_cons (step1458 p h) (sat_cons (step1483 p h) (sat_cons (step1478 p h) (sat_cons (step1414 p h) (sat_cons (step1461 p h) (sat_cons (step1756 p h) (sat_cons (step1440 p h) (sat_cons (step2064 p h) (sat_cons (step1434 p h) (sat_nil p)))))))))))))))
def c2168 : List Lit := [(1714, true), (99, true), (89, false), (87, true)]
theorem step2168 (p : Nat → Bool) (h : Constraints p) : clause p c2168 = true :=
  Snake9.LocalRup.prove_clause [c1383, c1387, c1389, c1385, c1380, c1381, c532, c578, c1932] c2168 (by decide) p (sat_cons (step1383 p h) (sat_cons (step1387 p h) (sat_cons (step1389 p h) (sat_cons (step1385 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step532 p h) (sat_cons (step578 p h) (sat_cons (step1932 p h) (sat_nil p))))))))))
def c2169 : List Lit := [(1728, true), (1709, false), (97, true), (1721, false), (87, true)]
theorem step2169 (p : Nat → Bool) (h : Constraints p) : clause p c2169 = true :=
  Snake9.LocalRup.prove_clause [c1384, c1389, c1423, c1419, c1390, c1756, c1385] c2169 (by decide) p (sat_cons (step1384 p h) (sat_cons (step1389 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step1390 p h) (sat_cons (step1756 p h) (sat_cons (step1385 p h) (sat_nil p))))))))
def c2170 : List Lit := [(1578, true), (1566, true), (41, true), (38, true), (42, true), (1593, true)]
theorem step2170 (p : Nat → Bool) (h : Constraints p) : clause p c2170 = true :=
  Snake9.LocalRup.prove_clause [c1122, c1121, c1132, c1135, c1142, c1144, c1137, c1134, c1697, c209, c146, c1859] c2170 (by decide) p (sat_cons (step1122 p h) (sat_cons (step1121 p h) (sat_cons (step1132 p h) (sat_cons (step1135 p h) (sat_cons (step1142 p h) (sat_cons (step1144 p h) (sat_cons (step1137 p h) (sat_cons (step1134 p h) (sat_cons (step1697 p h) (sat_cons (step209 p h) (sat_cons (step146 p h) (sat_cons (step1859 p h) (sat_nil p)))))))))))))
def c2171 : List Lit := [(1727, true), (89, false), (1721, false), (1713, false), (87, true)]
theorem step2171 (p : Nat → Bool) (h : Constraints p) : clause p c2171 = true :=
  Snake9.LocalRup.prove_clause [c1414, c1418, c1756, c2168] c2171 (by decide) p (sat_cons (step1414 p h) (sat_cons (step1418 p h) (sat_cons (step1756 p h) (sat_cons (step2168 p h) (sat_nil p)))))
def c2172 : List Lit := [(1582, true), (41, true), (38, true), (42, true), (1593, true)]
theorem step2172 (p : Nat → Bool) (h : Constraints p) : clause p c2172 = true :=
  Snake9.LocalRup.prove_clause [c1135, c1132, c1141, c1148, c1152, c2170, c1124] c2172 (by decide) p (sat_cons (step1135 p h) (sat_cons (step1132 p h) (sat_cons (step1141 p h) (sat_cons (step1148 p h) (sat_cons (step1152 p h) (sat_cons (step2170 p h) (sat_cons (step1124 p h) (sat_nil p))))))))
def c2173 : List Lit := [(1727, true), (1721, false), (1709, false), (87, true)]
theorem step2173 (p : Nat → Bool) (h : Constraints p) : clause p c2173 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1414, c1418, c1756, c1389, c1383] c2173 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1414 p h) (sat_cons (step1418 p h) (sat_cons (step1756 p h) (sat_cons (step1389 p h) (sat_cons (step1383 p h) (sat_nil p)))))))
def c2174 : List Lit := [(89, true), (1698, true), (87, true), (1672, false)]
theorem step2174 (p : Nat → Bool) (h : Constraints p) : clause p c2174 = true :=
  Snake9.LocalRup.prove_clause [c1321, c2022, c1345, c1333, c1329, c1332, c1344, c1364, c1348, c2015, c1335, c1323, c1737, c1331, c1327, c1316, c1677] c2174 (by decide) p (sat_cons (step1321 p h) (sat_cons (step2022 p h) (sat_cons (step1345 p h) (sat_cons (step1333 p h) (sat_cons (step1329 p h) (sat_cons (step1332 p h) (sat_cons (step1344 p h) (sat_cons (step1364 p h) (sat_cons (step1348 p h) (sat_cons (step2015 p h) (sat_cons (step1335 p h) (sat_cons (step1323 p h) (sat_cons (step1737 p h) (sat_cons (step1331 p h) (sat_cons (step1327 p h) (sat_cons (step1316 p h) (sat_cons (step1677 p h) (sat_nil p))))))))))))))))))
def c2175 : List Lit := [(98, false), (1718, true), (103, false), (86, false)]
theorem step2175 (p : Nat → Bool) (h : Constraints p) : clause p c2175 = true :=
  Snake9.LocalRup.prove_clause [c613, c612, c1396] c2175 (by decide) p (sat_cons (step613 p h) (sat_cons (step612 p h) (sat_cons (step1396 p h) (sat_nil p))))
def c2176 : List Lit := [(99, false), (103, false), (86, false), (87, true)]
theorem step2176 (p : Nat → Bool) (h : Constraints p) : clause p c2176 = true :=
  Snake9.LocalRup.prove_clause [c1943, c610] c2176 (by decide) p (sat_cons (step1943 p h) (sat_cons (step610 p h) (sat_nil p)))
def c2177 : List Lit := [(1580, true)]
theorem step2177 (p : Nat → Bool) (h : Constraints p) : clause p c2177 = true :=
  Snake9.LocalRup.prove_clause [c1146, c1150, c1779, c1124, c1121] c2177 (by decide) p (sat_cons (step1146 p h) (sat_cons (step1150 p h) (sat_cons (step1779 p h) (sat_cons (step1124 p h) (sat_cons (step1121 p h) (sat_nil p))))))
def c2178 : List Lit := [(1615, true), (1576, true), (1605, false)]
theorem step2178 (p : Nat → Bool) (h : Constraints p) : clause p c2178 = true :=
  Snake9.LocalRup.prove_clause [c2177, c1138, c1136, c1140, c1133, c1135, c1132, c252, c1691, c1874, c211, c1697, c1779, c1222, c1217, c1155, c1204, c1125, c1191, c1123, c1183, c149, c196, c1860] c2178 (by decide) p (sat_cons (step2177 p h) (sat_cons (step1138 p h) (sat_cons (step1136 p h) (sat_cons (step1140 p h) (sat_cons (step1133 p h) (sat_cons (step1135 p h) (sat_cons (step1132 p h) (sat_cons (step252 p h) (sat_cons (step1691 p h) (sat_cons (step1874 p h) (sat_cons (step211 p h) (sat_cons (step1697 p h) (sat_cons (step1779 p h) (sat_cons (step1222 p h) (sat_cons (step1217 p h) (sat_cons (step1155 p h) (sat_cons (step1204 p h) (sat_cons (step1125 p h) (sat_cons (step1191 p h) (sat_cons (step1123 p h) (sat_cons (step1183 p h) (sat_cons (step149 p h) (sat_cons (step196 p h) (sat_cons (step1860 p h) (sat_nil p)))))))))))))))))))))))))
def c2179 : List Lit := [(1606, true), (1700, true), (45, true), (39, true), (41, true), (35, false), (38, false), (40, false), (1678, false), (1660, false)]
theorem step2179 (p : Nat → Bool) (h : Constraints p) : clause p c2179 = true :=
  Snake9.LocalRup.prove_clause [c1697, c1208, c2003, c1204, c1189, c1191, c1662, c1186, c1187, c1183, c1184, c1700, c1672, c1892, c1181, c334, c1171, c201, c1888, c1860, c336, c155, c1900, c1330, c1288, c1335, c1292, c1341, c1314, c1376] c2179 (by decide) p (sat_cons (step1697 p h) (sat_cons (step1208 p h) (sat_cons (step2003 p h) (sat_cons (step1204 p h) (sat_cons (step1189 p h) (sat_cons (step1191 p h) (sat_cons (step1662 p h) (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step1183 p h) (sat_cons (step1184 p h) (sat_cons (step1700 p h) (sat_cons (step1672 p h) (sat_cons (step1892 p h) (sat_cons (step1181 p h) (sat_cons (step334 p h) (sat_cons (step1171 p h) (sat_cons (step201 p h) (sat_cons (step1888 p h) (sat_cons (step1860 p h) (sat_cons (step336 p h) (sat_cons (step155 p h) (sat_cons (step1900 p h) (sat_cons (step1330 p h) (sat_cons (step1288 p h) (sat_cons (step1335 p h) (sat_cons (step1292 p h) (sat_cons (step1341 p h) (sat_cons (step1314 p h) (sat_cons (step1376 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2180 : List Lit := [(32, false), (1606, false), (35, false), (38, false), (96, false), (34, true), (1678, false), (1730, false), (1665, false)]
theorem step2180 (p : Nat → Bool) (h : Constraints p) : clause p c2180 = true :=
  Snake9.LocalRup.prove_clause [c2138, c1497, c155, c149, c1330, c1123, c1335, c1125, c1341, c1155, c1364, c1223, c1254, c2039, c1529, c1523, c1365, c1498, c1345, c1456, c1458, c1321, c1453, c1439, c1320, c1446, c1432, c596] c2180 (by decide) p (sat_cons (step2138 p h) (sat_cons (step1497 p h) (sat_cons (step155 p h) (sat_cons (step149 p h) (sat_cons (step1330 p h) (sat_cons (step1123 p h) (sat_cons (step1335 p h) (sat_cons (step1125 p h) (sat_cons (step1341 p h) (sat_cons (step1155 p h) (sat_cons (step1364 p h) (sat_cons (step1223 p h) (sat_cons (step1254 p h) (sat_cons (step2039 p h) (sat_cons (step1529 p h) (sat_cons (step1523 p h) (sat_cons (step1365 p h) (sat_cons (step1498 p h) (sat_cons (step1345 p h) (sat_cons (step1456 p h) (sat_cons (step1458 p h) (sat_cons (step1321 p h) (sat_cons (step1453 p h) (sat_cons (step1439 p h) (sat_cons (step1320 p h) (sat_cons (step1446 p h) (sat_cons (step1432 p h) (sat_cons (step596 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2181 : List Lit := [(1784, true), (1683, false), (96, false), (1730, false), (1665, false)]
theorem step2181 (p : Nat → Bool) (h : Constraints p) : clause p c2181 = true :=
  Snake9.LocalRup.prove_clause [c1341, c1364, c1497, c1529, c1523, c1365, c1498, c1345, c1456, c1458, c1321, c1453, c1439, c1320, c1446, c1432, c596] c2181 (by decide) p (sat_cons (step1341 p h) (sat_cons (step1364 p h) (sat_cons (step1497 p h) (sat_cons (step1529 p h) (sat_cons (step1523 p h) (sat_cons (step1365 p h) (sat_cons (step1498 p h) (sat_cons (step1345 p h) (sat_cons (step1456 p h) (sat_cons (step1458 p h) (sat_cons (step1321 p h) (sat_cons (step1453 p h) (sat_cons (step1439 p h) (sat_cons (step1320 p h) (sat_cons (step1446 p h) (sat_cons (step1432 p h) (sat_cons (step596 p h) (sat_nil p))))))))))))))))))
def c2182 : List Lit := [(1616, true), (36, false), (1606, false), (45, true), (39, true), (35, false), (40, false), (34, true)]
theorem step2182 (p : Nat → Bool) (h : Constraints p) : clause p c2182 = true :=
  Snake9.LocalRup.prove_clause [c2177, c1697, c1218, c1223, c1205, c1155, c1194, c1125, c1123, c196, c195, c1183, c1185, c1171, c1191, c1192, c1209, c1186, c1181, c363, c1672] c2182 (by decide) p (sat_cons (step2177 p h) (sat_cons (step1697 p h) (sat_cons (step1218 p h) (sat_cons (step1223 p h) (sat_cons (step1205 p h) (sat_cons (step1155 p h) (sat_cons (step1194 p h) (sat_cons (step1125 p h) (sat_cons (step1123 p h) (sat_cons (step196 p h) (sat_cons (step195 p h) (sat_cons (step1183 p h) (sat_cons (step1185 p h) (sat_cons (step1171 p h) (sat_cons (step1191 p h) (sat_cons (step1192 p h) (sat_cons (step1209 p h) (sat_cons (step1186 p h) (sat_cons (step1181 p h) (sat_cons (step363 p h) (sat_cons (step1672 p h) (sat_nil p))))))))))))))))))))))
end B112E008
