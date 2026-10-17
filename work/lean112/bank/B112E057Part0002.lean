import B112E057Part0001
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2153 : List Lit := [(973, true), (955, false), (45, false), (6, false)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c1445, c2070, c1466, c1446, c2066, c1441, c1451, c344] c2153 (by decide) p (sat_cons (step1445 p h) (sat_cons (step2070 p h) (sat_cons (step1466 p h) (sat_cons (step1446 p h) (sat_cons (step2066 p h) (sat_cons (step1441 p h) (sat_cons (step1451 p h) (sat_cons (step344 p h) (sat_nil p)))))))))
def c2154 : List Lit := [(60, false), (940, true), (45, false), (6, false)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c342, c339, c1404] c2154 (by decide) p (sat_cons (step342 p h) (sat_cons (step339 p h) (sat_cons (step1404 p h) (sat_nil p))))
def c2155 : List Lit := [(1059, true)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.LocalRup.prove_clause [c1009, c1607, c1611, c1601, c1585, c1593, c1594, c1582, c1583, c754, c703, c725] c2155 (by decide) p (sat_cons (step1009 p h) (sat_cons (step1607 p h) (sat_cons (step1611 p h) (sat_cons (step1601 p h) (sat_cons (step1585 p h) (sat_cons (step1593 p h) (sat_cons (step1594 p h) (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step754 p h) (sat_cons (step703 p h) (sat_cons (step725 p h) (sat_nil p)))))))))))))
def c2156 : List Lit := [(17, false), (1063, true), (1043, false), (89, true), (86, true), (88, false), (123, false)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c742, c740, c1595, c1584, c1604, c1589, c1623] c2156 (by decide) p (sat_cons (step742 p h) (sat_cons (step740 p h) (sat_cons (step1595 p h) (sat_cons (step1584 p h) (sat_cons (step1604 p h) (sat_cons (step1589 p h) (sat_cons (step1623 p h) (sat_nil p))))))))
def c2157 : List Lit := [(1062, true), (89, true), (1043, false), (86, true), (88, false), (123, false)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c1594, c1601, c1583, c1588, c1618, c1622, c1604, c1589, c1595, c1584, c761] c2157 (by decide) p (sat_cons (step1594 p h) (sat_cons (step1601 p h) (sat_cons (step1583 p h) (sat_cons (step1588 p h) (sat_cons (step1618 p h) (sat_cons (step1622 p h) (sat_cons (step1604 p h) (sat_cons (step1589 p h) (sat_cons (step1595 p h) (sat_cons (step1584 p h) (sat_cons (step761 p h) (sat_nil p))))))))))))
def c2158 : List Lit := [(77, true), (1039, true), (81, false), (82, false), (1027, false)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c2086, c1560, c1554, c1555, c1559, c622, c1571, c1544, c2081] c2158 (by decide) p (sat_cons (step2086 p h) (sat_cons (step1560 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step1559 p h) (sat_cons (step622 p h) (sat_cons (step1571 p h) (sat_cons (step1544 p h) (sat_cons (step2081 p h) (sat_nil p))))))))))
def c2159 : List Lit := [(112, false), (40, true), (114, false), (70, true), (77, false)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c1022, c905, c890] c2159 (by decide) p (sat_cons (step1022 p h) (sat_cons (step905 p h) (sat_cons (step890 p h) (sat_nil p))))
def c2160 : List Lit := [(4, false), (40, false), (112, false), (934, true)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c292, c296, c1393] c2160 (by decide) p (sat_cons (step292 p h) (sat_cons (step296 p h) (sat_cons (step1393 p h) (sat_nil p))))
def c2161 : List Lit := [(982, true), (956, false), (45, true)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c992, c1448, c2070, c1478, c1481, c2071, c1416, c1449, c1408, c1410, c1441, c1405, c1403, c399, c407] c2161 (by decide) p (sat_cons (step992 p h) (sat_cons (step1448 p h) (sat_cons (step2070 p h) (sat_cons (step1478 p h) (sat_cons (step1481 p h) (sat_cons (step2071 p h) (sat_cons (step1416 p h) (sat_cons (step1449 p h) (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1441 p h) (sat_cons (step1405 p h) (sat_cons (step1403 p h) (sat_cons (step399 p h) (sat_cons (step407 p h) (sat_nil p))))))))))))))))
def c2162 : List Lit := [(947, true)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c988, c1416, c1420, c1408, c1410, c1394, c1406, c1402, c1403, c1391, c1392, c332, c303, c363] c2162 (by decide) p (sat_cons (step988 p h) (sat_cons (step1416 p h) (sat_cons (step1420 p h) (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1394 p h) (sat_cons (step1406 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step1391 p h) (sat_cons (step1392 p h) (sat_cons (step332 p h) (sat_cons (step303 p h) (sat_cons (step363 p h) (sat_nil p)))))))))))))))
def c2163 : List Lit := [(1087, false), (1135, true), (82, false), (1113, false)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c1018, c1756, c1768, c1707, c1708, c1764, c1695, c1697, c1757, c1693, c1689, c1690, c1742, c869, c1738, c849, c689] c2163 (by decide) p (sat_cons (step1018 p h) (sat_cons (step1756 p h) (sat_cons (step1768 p h) (sat_cons (step1707 p h) (sat_cons (step1708 p h) (sat_cons (step1764 p h) (sat_cons (step1695 p h) (sat_cons (step1697 p h) (sat_cons (step1757 p h) (sat_cons (step1693 p h) (sat_cons (step1689 p h) (sat_cons (step1690 p h) (sat_cons (step1742 p h) (sat_cons (step869 p h) (sat_cons (step1738 p h) (sat_cons (step849 p h) (sat_cons (step689 p h) (sat_nil p))))))))))))))))))
def c2164 : List Lit := [(1095, true), (72, false), (82, false)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c1018, c1695, c1697, c1693, c1689, c1690, c869, c676, c849] c2164 (by decide) p (sat_cons (step1018 p h) (sat_cons (step1695 p h) (sat_cons (step1697 p h) (sat_cons (step1693 p h) (sat_cons (step1689 p h) (sat_cons (step1690 p h) (sat_cons (step869 p h) (sat_cons (step676 p h) (sat_cons (step849 p h) (sat_nil p))))))))))
def c2165 : List Lit := [(1100, true), (84, true), (1095, false), (1058, true), (89, true), (70, true), (77, false)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c1014, c1018, c1708, c1681, c1683, c1678, c1679, c1676, c2133, c821, c1689, c1690, c810, c849, c795, c796, c866, c1598, c1595, c1606] c2165 (by decide) p (sat_cons (step1014 p h) (sat_cons (step1018 p h) (sat_cons (step1708 p h) (sat_cons (step1681 p h) (sat_cons (step1683 p h) (sat_cons (step1678 p h) (sat_cons (step1679 p h) (sat_cons (step1676 p h) (sat_cons (step2133 p h) (sat_cons (step821 p h) (sat_cons (step1689 p h) (sat_cons (step1690 p h) (sat_cons (step810 p h) (sat_cons (step849 p h) (sat_cons (step795 p h) (sat_cons (step796 p h) (sat_cons (step866 p h) (sat_cons (step1598 p h) (sat_cons (step1595 p h) (sat_cons (step1606 p h) (sat_nil p)))))))))))))))))))))
def c2166 : List Lit := [(1045, true), (76, true), (73, false), (77, false)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c1002, c1582, c1583, c697, c518, c511] c2166 (by decide) p (sat_cons (step1002 p h) (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step697 p h) (sat_cons (step518 p h) (sat_cons (step511 p h) (sat_nil p)))))))
def c2167 : List Lit := [(1095, true), (1045, true)]
theorem step2167 (p : Nat → Bool) (h : Constraints p) : clause p c2167 = true :=
  Snake9.LocalRup.prove_clause [c1019, c1583, c1582, c1695, c1697, c1693, c1689, c1690, c869, c755, c857] c2167 (by decide) p (sat_cons (step1019 p h) (sat_cons (step1583 p h) (sat_cons (step1582 p h) (sat_cons (step1695 p h) (sat_cons (step1697 p h) (sat_cons (step1693 p h) (sat_cons (step1689 p h) (sat_cons (step1690 p h) (sat_cons (step869 p h) (sat_cons (step755 p h) (sat_cons (step857 p h) (sat_nil p))))))))))))
def c2168 : List Lit := [(985, true), (961, false), (943, true)]
theorem step2168 (p : Nat → Bool) (h : Constraints p) : clause p c2168 = true :=
  Snake9.LocalRup.prove_clause [c988, c987, c2162, c1410, c1402, c1403, c1408, c1406, c332, c358, c348, c1451, c2066, c1475, c363, c1484, c1488, c1476, c1424, c2067, c1395, c1453, c313, c308, c1393] c2168 (by decide) p (sat_cons (step988 p h) (sat_cons (step987 p h) (sat_cons (step2162 p h) (sat_cons (step1410 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step1408 p h) (sat_cons (step1406 p h) (sat_cons (step332 p h) (sat_cons (step358 p h) (sat_cons (step348 p h) (sat_cons (step1451 p h) (sat_cons (step2066 p h) (sat_cons (step1475 p h) (sat_cons (step363 p h) (sat_cons (step1484 p h) (sat_cons (step1488 p h) (sat_cons (step1476 p h) (sat_cons (step1424 p h) (sat_cons (step2067 p h) (sat_cons (step1395 p h) (sat_cons (step1453 p h) (sat_cons (step313 p h) (sat_cons (step308 p h) (sat_cons (step1393 p h) (sat_nil p))))))))))))))))))))))))))
def c2169 : List Lit := [(95, true), (1101, true), (1045, true), (1088, true)]
theorem step2169 (p : Nat → Bool) (h : Constraints p) : clause p c2169 = true :=
  Snake9.LocalRup.prove_clause [c1019, c1583, c1582, c1676, c2109, c1684, c1689, c1678, c755, c858, c851] c2169 (by decide) p (sat_cons (step1019 p h) (sat_cons (step1583 p h) (sat_cons (step1582 p h) (sat_cons (step1676 p h) (sat_cons (step2109 p h) (sat_cons (step1684 p h) (sat_cons (step1689 p h) (sat_cons (step1678 p h) (sat_cons (step755 p h) (sat_cons (step858 p h) (sat_cons (step851 p h) (sat_nil p))))))))))))
def c2170 : List Lit := [(105, false), (101, false), (1045, true)]
theorem step2170 (p : Nat → Bool) (h : Constraints p) : clause p c2170 = true :=
  Snake9.LocalRup.prove_clause [c1019, c1583, c1582, c755, c858, c851] c2170 (by decide) p (sat_cons (step1019 p h) (sat_cons (step1583 p h) (sat_cons (step1582 p h) (sat_cons (step755 p h) (sat_cons (step858 p h) (sat_cons (step851 p h) (sat_nil p)))))))
def c2171 : List Lit := [(114, true), (1125, true), (1110, true), (1107, false), (88, true)]
theorem step2171 (p : Nat → Bool) (h : Constraints p) : clause p c2171 = true :=
  Snake9.LocalRup.prove_clause [c1027, c1727, c1728, c1732, c1754, c1741, c1742, c1740, c1737, c1738, c962, c922, c947] c2171 (by decide) p (sat_cons (step1027 p h) (sat_cons (step1727 p h) (sat_cons (step1728 p h) (sat_cons (step1732 p h) (sat_cons (step1754 p h) (sat_cons (step1741 p h) (sat_cons (step1742 p h) (sat_cons (step1740 p h) (sat_cons (step1737 p h) (sat_cons (step1738 p h) (sat_cons (step962 p h) (sat_cons (step922 p h) (sat_cons (step947 p h) (sat_nil p))))))))))))))
def c2172 : List Lit := [(1119, true), (118, false), (88, true)]
theorem step2172 (p : Nat → Bool) (h : Constraints p) : clause p c2172 = true :=
  Snake9.LocalRup.prove_clause [c1027, c1741, c1742, c1740, c1737, c1738, c962, c922, c947] c2172 (by decide) p (sat_cons (step1027 p h) (sat_cons (step1741 p h) (sat_cons (step1742 p h) (sat_cons (step1740 p h) (sat_cons (step1737 p h) (sat_cons (step1738 p h) (sat_cons (step962 p h) (sat_cons (step922 p h) (sat_cons (step947 p h) (sat_nil p))))))))))
def c2173 : List Lit := [(933, true), (40, false), (47, false)]
theorem step2173 (p : Nat → Bool) (h : Constraints p) : clause p c2173 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1392, c303] c2173 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1392 p h) (sat_cons (step303 p h) (sat_nil p))))
def c2174 : List Lit := [(60, true), (54, true), (976, true), (955, false), (59, true)]
theorem step2174 (p : Nat → Bool) (h : Constraints p) : clause p c2174 = true :=
  Snake9.LocalRup.prove_clause [c2025, c2027, c2028, c1262, c993, c440, c1138, c1139, c1143, c1158, c1188, c1256, c1260, c1133, c1128, c1123, c1121, c1113, c1110, c416, c1112, c1111, c1453, c418, c2067, c415, c1476, c1442, c1447] c2174 (by decide) p (sat_cons (step2025 p h) (sat_cons (step2027 p h) (sat_cons (step2028 p h) (sat_cons (step1262 p h) (sat_cons (step993 p h) (sat_cons (step440 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1143 p h) (sat_cons (step1158 p h) (sat_cons (step1188 p h) (sat_cons (step1256 p h) (sat_cons (step1260 p h) (sat_cons (step1133 p h) (sat_cons (step1128 p h) (sat_cons (step1123 p h) (sat_cons (step1121 p h) (sat_cons (step1113 p h) (sat_cons (step1110 p h) (sat_cons (step416 p h) (sat_cons (step1112 p h) (sat_cons (step1111 p h) (sat_cons (step1453 p h) (sat_cons (step418 p h) (sat_cons (step2067 p h) (sat_cons (step415 p h) (sat_cons (step1476 p h) (sat_cons (step1442 p h) (sat_cons (step1447 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2175 : List Lit := [(60, true), (957, false), (976, true), (50, true), (59, true)]
theorem step2175 (p : Nat → Bool) (h : Constraints p) : clause p c2175 = true :=
  Snake9.LocalRup.prove_clause [c2025, c2027, c2028, c1262, c2026, c997, c1438, c1446, c1473, c440, c1138, c1139, c1143, c1158, c1188, c1256, c1260, c1133, c1128, c1123, c1119, c1117, c1115, c1453, c430, c2174, c2067, c1461, c1476, c2064, c1449, c435, c1439, c408] c2175 (by decide) p (sat_cons (step2025 p h) (sat_cons (step2027 p h) (sat_cons (step2028 p h) (sat_cons (step1262 p h) (sat_cons (step2026 p h) (sat_cons (step997 p h) (sat_cons (step1438 p h) (sat_cons (step1446 p h) (sat_cons (step1473 p h) (sat_cons (step440 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1143 p h) (sat_cons (step1158 p h) (sat_cons (step1188 p h) (sat_cons (step1256 p h) (sat_cons (step1260 p h) (sat_cons (step1133 p h) (sat_cons (step1128 p h) (sat_cons (step1123 p h) (sat_cons (step1119 p h) (sat_cons (step1117 p h) (sat_cons (step1115 p h) (sat_cons (step1453 p h) (sat_cons (step430 p h) (sat_cons (step2174 p h) (sat_cons (step2067 p h) (sat_cons (step1461 p h) (sat_cons (step1476 p h) (sat_cons (step2064 p h) (sat_cons (step1449 p h) (sat_cons (step435 p h) (sat_cons (step1439 p h) (sat_cons (step408 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c2176 : List Lit := [(45, false), (54, false), (60, false), (171, true), (44, false)]
theorem step2176 (p : Nat → Bool) (h : Constraints p) : clause p c2176 = true :=
  Snake9.LocalRup.prove_clause [c350, c353, c336] c2176 (by decide) p (sat_cons (step350 p h) (sat_cons (step353 p h) (sat_cons (step336 p h) (sat_nil p))))
def c2177 : List Lit := [(54, false), (125, false), (60, false), (375, true), (44, false)]
theorem step2177 (p : Nat → Bool) (h : Constraints p) : clause p c2177 = true :=
  Snake9.LocalRup.prove_clause [c992, c995, c2026, c1130, c1096, c1093, c1092, c1091, c1128, c1123, c1119, c1117, c1115, c2176, c406, c426, c429, c411] c2177 (by decide) p (sat_cons (step992 p h) (sat_cons (step995 p h) (sat_cons (step2026 p h) (sat_cons (step1130 p h) (sat_cons (step1096 p h) (sat_cons (step1093 p h) (sat_cons (step1092 p h) (sat_cons (step1091 p h) (sat_cons (step1128 p h) (sat_cons (step1123 p h) (sat_cons (step1119 p h) (sat_cons (step1117 p h) (sat_cons (step1115 p h) (sat_cons (step2176 p h) (sat_cons (step406 p h) (sat_cons (step426 p h) (sat_cons (step429 p h) (sat_cons (step411 p h) (sat_nil p)))))))))))))))))))
def c2178 : List Lit := [(931, true), (37, false), (64, false)]
theorem step2178 (p : Nat → Bool) (h : Constraints p) : clause p c2178 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1389, c279] c2178 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step279 p h) (sat_nil p))))
def c2179 : List Lit := [(907, true)]
theorem step2179 (p : Nat → Bool) (h : Constraints p) : clause p c2179 = true :=
  Snake9.LocalRup.prove_clause [c976, c1340, c1344, c1332, c1318, c1329, c1315, c1316, c2126, c208, c195] c2179 (by decide) p (sat_cons (step976 p h) (sat_cons (step1340 p h) (sat_cons (step1344 p h) (sat_cons (step1332 p h) (sat_cons (step1318 p h) (sat_cons (step1329 p h) (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step2126 p h) (sat_cons (step208 p h) (sat_cons (step195 p h) (sat_nil p))))))))))))
def c2180 : List Lit := [(984, true), (963, false), (50, true), (943, false), (959, false), (968, false), (948, false), (973, false), (933, false)]
theorem step2180 (p : Nat → Bool) (h : Constraints p) : clause p c2180 = true :=
  Snake9.LocalRup.prove_clause [c997, c1438, c1492, c1487, c1425, c1471, c1467, c1397, c1448, c1446, c1459, c1388, c1389, c1439, c1441, c2064, c279, c408, c437] c2180 (by decide) p (sat_cons (step997 p h) (sat_cons (step1438 p h) (sat_cons (step1492 p h) (sat_cons (step1487 p h) (sat_cons (step1425 p h) (sat_cons (step1471 p h) (sat_cons (step1467 p h) (sat_cons (step1397 p h) (sat_cons (step1448 p h) (sat_cons (step1446 p h) (sat_cons (step1459 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1439 p h) (sat_cons (step1441 p h) (sat_cons (step2064 p h) (sat_cons (step279 p h) (sat_cons (step408 p h) (sat_cons (step437 p h) (sat_nil p))))))))))))))))))))
def c2181 : List Lit := [(872, false), (918, true)]
theorem step2181 (p : Nat → Bool) (h : Constraints p) : clause p c2181 = true :=
  Snake9.LocalRup.prove_clause [c2179, c975, c1373, c1301, c1302, c1367, c1284, c1286, c2125, c1281, c1278, c1279, c1312, c1313, c181, c112, c150, c178] c2181 (by decide) p (sat_cons (step2179 p h) (sat_cons (step975 p h) (sat_cons (step1373 p h) (sat_cons (step1301 p h) (sat_cons (step1302 p h) (sat_cons (step1367 p h) (sat_cons (step1284 p h) (sat_cons (step1286 p h) (sat_cons (step2125 p h) (sat_cons (step1281 p h) (sat_cons (step1278 p h) (sat_cons (step1279 p h) (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step181 p h) (sat_cons (step112 p h) (sat_cons (step150 p h) (sat_cons (step178 p h) (sat_nil p)))))))))))))))))))
def c2182 : List Lit := [(872, true), (40, false), (7, true), (70, false)]
theorem step2182 (p : Nat → Bool) (h : Constraints p) : clause p c2182 = true :=
  Snake9.LocalRup.prove_clause [c1267, c1271, c1273, c1269, c1264, c1265, c23, c2144] c2182 (by decide) p (sat_cons (step1267 p h) (sat_cons (step1271 p h) (sat_cons (step1273 p h) (sat_cons (step1269 p h) (sat_cons (step1264 p h) (sat_cons (step1265 p h) (sat_cons (step23 p h) (sat_cons (step2144 p h) (sat_nil p)))))))))
def c2183 : List Lit := [(59, true), (872, false), (931, true), (969, true), (919, true)]
theorem step2183 (p : Nat → Bool) (h : Constraints p) : clause p c2183 = true :=
  Snake9.LocalRup.prove_clause [c2028, c2027, c2025, c982, c1262, c1389, c1388, c440, c1452, c1138, c1459, c1139, c2064, c1143, c2178, c1158, c267, c1188, c262, c261, c1256, c1330, c2119, c1260, c232, c1135, c1059, c1072, c1060, c1068, c1067] c2183 (by decide) p (sat_cons (step2028 p h) (sat_cons (step2027 p h) (sat_cons (step2025 p h) (sat_cons (step982 p h) (sat_cons (step1262 p h) (sat_cons (step1389 p h) (sat_cons (step1388 p h) (sat_cons (step440 p h) (sat_cons (step1452 p h) (sat_cons (step1138 p h) (sat_cons (step1459 p h) (sat_cons (step1139 p h) (sat_cons (step2064 p h) (sat_cons (step1143 p h) (sat_cons (step2178 p h) (sat_cons (step1158 p h) (sat_cons (step267 p h) (sat_cons (step1188 p h) (sat_cons (step262 p h) (sat_cons (step261 p h) (sat_cons (step1256 p h) (sat_cons (step1330 p h) (sat_cons (step2119 p h) (sat_cons (step1260 p h) (sat_cons (step232 p h) (sat_cons (step1135 p h) (sat_cons (step1059 p h) (sat_cons (step1072 p h) (sat_cons (step1060 p h) (sat_cons (step1068 p h) (sat_cons (step1067 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2184 : List Lit := [(50, true), (43, false), (46, false), (48, false), (984, true), (943, false), (959, false), (968, false), (948, false), (973, false), (933, false)]
theorem step2184 (p : Nat → Bool) (h : Constraints p) : clause p c2184 = true :=
  Snake9.LocalRup.prove_clause [c992, c1487, c1471, c1438, c2180, c1446, c1451, c1441, c348, c399, c407] c2184 (by decide) p (sat_cons (step992 p h) (sat_cons (step1487 p h) (sat_cons (step1471 p h) (sat_cons (step1438 p h) (sat_cons (step2180 p h) (sat_cons (step1446 p h) (sat_cons (step1451 p h) (sat_cons (step1441 p h) (sat_cons (step348 p h) (sat_cons (step399 p h) (sat_cons (step407 p h) (sat_nil p))))))))))))
def c2185 : List Lit := [(40, false), (59, false), (50, false), (934, true)]
theorem step2185 (p : Nat → Bool) (h : Constraints p) : clause p c2185 = true :=
  Snake9.LocalRup.prove_clause [c309, c314, c1393] c2185 (by decide) p (sat_cons (step309 p h) (sat_cons (step314 p h) (sat_cons (step1393 p h) (sat_nil p))))
def c2186 : List Lit := [(39, false), (40, true), (50, false), (48, false)]
theorem step2186 (p : Nat → Bool) (h : Constraints p) : clause p c2186 = true :=
  Snake9.LocalRup.prove_clause [c984, c286, c368] c2186 (by decide) p (sat_cons (step984 p h) (sat_cons (step286 p h) (sat_cons (step368 p h) (sat_nil p))))
def c2187 : List Lit := [(54, false), (43, false), (46, false), (48, false)]
theorem step2187 (p : Nat → Bool) (h : Constraints p) : clause p c2187 = true :=
  Snake9.LocalRup.prove_clause [c992, c399, c347, c407] c2187 (by decide) p (sat_cons (step992 p h) (sat_cons (step399 p h) (sat_cons (step347 p h) (sat_cons (step407 p h) (sat_nil p)))))
def c2188 : List Lit := [(40, true), (51, false), (50, false), (48, false), (934, true)]
theorem step2188 (p : Nat → Bool) (h : Constraints p) : clause p c2188 = true :=
  Snake9.LocalRup.prove_clause [c990, c371, c2186, c1393, c395, c379] c2188 (by decide) p (sat_cons (step990 p h) (sat_cons (step371 p h) (sat_cons (step2186 p h) (sat_cons (step1393 p h) (sat_cons (step395 p h) (sat_cons (step379 p h) (sat_nil p)))))))
def c2189 : List Lit := [(984, true), (47, true), (943, false), (7, true), (70, false), (959, false), (968, false), (948, false), (973, false), (919, true), (933, false)]
theorem step2189 (p : Nat → Bool) (h : Constraints p) : clause p c2189 = true :=
  Snake9.LocalRup.prove_clause [c1406, c1394, c1492, c1487, c1425, c1422, c1471, c1467, c1395, c1397, c1409, c1411, c1407, c1402, c1403, c2184, c2187, c1441, c1446, c1437, c2188, c2182, c2185, c2183] c2189 (by decide) p (sat_cons (step1406 p h) (sat_cons (step1394 p h) (sat_cons (step1492 p h) (sat_cons (step1487 p h) (sat_cons (step1425 p h) (sat_cons (step1422 p h) (sat_cons (step1471 p h) (sat_cons (step1467 p h) (sat_cons (step1395 p h) (sat_cons (step1397 p h) (sat_cons (step1409 p h) (sat_cons (step1411 p h) (sat_cons (step1407 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step2184 p h) (sat_cons (step2187 p h) (sat_cons (step1441 p h) (sat_cons (step1446 p h) (sat_cons (step1437 p h) (sat_cons (step2188 p h) (sat_cons (step2182 p h) (sat_cons (step2185 p h) (sat_cons (step2183 p h) (sat_nil p)))))))))))))))))))))))))
def c2190 : List Lit := [(918, true), (7, true), (70, false)]
theorem step2190 (p : Nat → Bool) (h : Constraints p) : clause p c2190 = true :=
  Snake9.LocalRup.prove_clause [c2179, c981, c966, c1267, c1270, c1373, c2181, c1298, c1271, c1273, c1269, c1264, c1265, c2144, c20, c22, c7, c258, c1278, c1329, c1286, c1287, c1297, c1282, c1367, c14, c1341, c2, c1335, c31, c1327] c2190 (by decide) p (sat_cons (step2179 p h) (sat_cons (step981 p h) (sat_cons (step966 p h) (sat_cons (step1267 p h) (sat_cons (step1270 p h) (sat_cons (step1373 p h) (sat_cons (step2181 p h) (sat_cons (step1298 p h) (sat_cons (step1271 p h) (sat_cons (step1273 p h) (sat_cons (step1269 p h) (sat_cons (step1264 p h) (sat_cons (step1265 p h) (sat_cons (step2144 p h) (sat_cons (step20 p h) (sat_cons (step22 p h) (sat_cons (step7 p h) (sat_cons (step258 p h) (sat_cons (step1278 p h) (sat_cons (step1329 p h) (sat_cons (step1286 p h) (sat_cons (step1287 p h) (sat_cons (step1297 p h) (sat_cons (step1282 p h) (sat_cons (step1367 p h) (sat_cons (step14 p h) (sat_cons (step1341 p h) (sat_cons (step2 p h) (sat_cons (step1335 p h) (sat_cons (step31 p h) (sat_cons (step1327 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2191 : List Lit := [(47, true), (984, true), (7, true), (70, false), (959, false), (968, false), (948, false), (973, false), (919, true), (933, false)]
theorem step2191 (p : Nat → Bool) (h : Constraints p) : clause p c2191 = true :=
  Snake9.LocalRup.prove_clause [c1406, c2189, c1408] c2191 (by decide) p (sat_cons (step1406 p h) (sat_cons (step2189 p h) (sat_cons (step1408 p h) (sat_nil p))))
def c2192 : List Lit := [(3, true), (5, true), (1, false)]
theorem step2192 (p : Nat → Bool) (h : Constraints p) : clause p c2192 = true :=
  Snake9.LocalRup.prove_clause [c966, c2] c2192 (by decide) p (sat_cons (step966 p h) (sat_cons (step2 p h) (sat_nil p)))
def c2193 : List Lit := [(2, true), (1, false), (5, true)]
theorem step2193 (p : Nat → Bool) (h : Constraints p) : clause p c2193 = true :=
  Snake9.LocalRup.prove_clause [c966, c3] c2193 (by decide) p (sat_cons (step966 p h) (sat_cons (step3 p h) (sat_nil p)))
def c2194 : List Lit := [(23, true), (13, true), (4, false), (40, true), (70, true)]
theorem step2194 (p : Nat → Bool) (h : Constraints p) : clause p c2194 = true :=
  Snake9.LocalRup.prove_clause [c967, c26] c2194 (by decide) p (sat_cons (step967 p h) (sat_cons (step26 p h) (sat_nil p)))
def c2195 : List Lit := [(2, true), (23, true), (4, false), (40, true), (70, true)]
theorem step2195 (p : Nat → Bool) (h : Constraints p) : clause p c2195 = true :=
  Snake9.LocalRup.prove_clause [c967, c27] c2195 (by decide) p (sat_cons (step967 p h) (sat_cons (step27 p h) (sat_nil p)))
def c2196 : List Lit := [(2, true), (23, true), (13, true), (4, false), (40, true)]
theorem step2196 (p : Nat → Bool) (h : Constraints p) : clause p c2196 = true :=
  Snake9.LocalRup.prove_clause [c967, c28] c2196 (by decide) p (sat_cons (step967 p h) (sat_cons (step28 p h) (sat_nil p)))
def c2197 : List Lit := [(8, true), (5, true), (45, true), (6, false)]
theorem step2197 (p : Nat → Bool) (h : Constraints p) : clause p c2197 = true :=
  Snake9.LocalRup.prove_clause [c968, c54] c2197 (by decide) p (sat_cons (step968 p h) (sat_cons (step54 p h) (sat_nil p)))
def c2198 : List Lit := [(8, true), (45, true), (6, false), (3, true)]
theorem step2198 (p : Nat → Bool) (h : Constraints p) : clause p c2198 = true :=
  Snake9.LocalRup.prove_clause [c968, c55] c2198 (by decide) p (sat_cons (step968 p h) (sat_cons (step55 p h) (sat_nil p)))
def c2199 : List Lit := [(3, true), (5, true), (6, false), (45, true)]
theorem step2199 (p : Nat → Bool) (h : Constraints p) : clause p c2199 = true :=
  Snake9.LocalRup.prove_clause [c968, c56] c2199 (by decide) p (sat_cons (step968 p h) (sat_cons (step56 p h) (sat_nil p)))
def c2200 : List Lit := [(3, true), (8, true), (6, false), (5, true)]
theorem step2200 (p : Nat → Bool) (h : Constraints p) : clause p c2200 = true :=
  Snake9.LocalRup.prove_clause [c968, c57] c2200 (by decide) p (sat_cons (step968 p h) (sat_cons (step57 p h) (sat_nil p)))
def c2201 : List Lit := [(7, false), (8, true), (76, true), (18, true)]
theorem step2201 (p : Nat → Bool) (h : Constraints p) : clause p c2201 = true :=
  Snake9.LocalRup.prove_clause [c969, c60] c2201 (by decide) p (sat_cons (step969 p h) (sat_cons (step60 p h) (sat_nil p)))
def c2202 : List Lit := [(7, false), (5, true), (18, true), (76, true)]
theorem step2202 (p : Nat → Bool) (h : Constraints p) : clause p c2202 = true :=
  Snake9.LocalRup.prove_clause [c969, c61] c2202 (by decide) p (sat_cons (step969 p h) (sat_cons (step61 p h) (sat_nil p)))
def c2203 : List Lit := [(7, false), (8, true), (76, true), (5, true)]
theorem step2203 (p : Nat → Bool) (h : Constraints p) : clause p c2203 = true :=
  Snake9.LocalRup.prove_clause [c969, c62] c2203 (by decide) p (sat_cons (step969 p h) (sat_cons (step62 p h) (sat_nil p)))
def c2204 : List Lit := [(7, false), (8, true), (5, true), (18, true)]
theorem step2204 (p : Nat → Bool) (h : Constraints p) : clause p c2204 = true :=
  Snake9.LocalRup.prove_clause [c969, c63] c2204 (by decide) p (sat_cons (step969 p h) (sat_cons (step63 p h) (sat_nil p)))
def c2205 : List Lit := [(29, true), (20, true), (9, false), (78, true)]
theorem step2205 (p : Nat → Bool) (h : Constraints p) : clause p c2205 = true :=
  Snake9.LocalRup.prove_clause [c970, c71] c2205 (by decide) p (sat_cons (step970 p h) (sat_cons (step71 p h) (sat_nil p)))
def c2206 : List Lit := [(29, true), (8, true), (9, false), (78, true)]
theorem step2206 (p : Nat → Bool) (h : Constraints p) : clause p c2206 = true :=
  Snake9.LocalRup.prove_clause [c970, c72] c2206 (by decide) p (sat_cons (step970 p h) (sat_cons (step72 p h) (sat_nil p)))
def c2207 : List Lit := [(20, true), (8, true), (9, false), (78, true)]
theorem step2207 (p : Nat → Bool) (h : Constraints p) : clause p c2207 = true :=
  Snake9.LocalRup.prove_clause [c970, c73] c2207 (by decide) p (sat_cons (step970 p h) (sat_cons (step73 p h) (sat_nil p)))
def c2208 : List Lit := [(20, true), (29, true), (9, false), (8, true)]
theorem step2208 (p : Nat → Bool) (h : Constraints p) : clause p c2208 = true :=
  Snake9.LocalRup.prove_clause [c970, c74] c2208 (by decide) p (sat_cons (step970 p h) (sat_cons (step74 p h) (sat_nil p)))
def c2209 : List Lit := [(12, true), (13, true), (16, true), (10, false)]
theorem step2209 (p : Nat → Bool) (h : Constraints p) : clause p c2209 = true :=
  Snake9.LocalRup.prove_clause [c971, c77] c2209 (by decide) p (sat_cons (step971 p h) (sat_cons (step77 p h) (sat_nil p)))
def c2210 : List Lit := [(2, true), (13, true), (16, true), (10, false)]
theorem step2210 (p : Nat → Bool) (h : Constraints p) : clause p c2210 = true :=
  Snake9.LocalRup.prove_clause [c971, c78] c2210 (by decide) p (sat_cons (step971 p h) (sat_cons (step78 p h) (sat_nil p)))
def c2211 : List Lit := [(2, true), (12, true), (10, false), (13, true)]
theorem step2211 (p : Nat → Bool) (h : Constraints p) : clause p c2211 = true :=
  Snake9.LocalRup.prove_clause [c971, c79] c2211 (by decide) p (sat_cons (step971 p h) (sat_cons (step79 p h) (sat_nil p)))
def c2212 : List Lit := [(31, true), (14, true), (11, false), (12, true), (80, true)]
theorem step2212 (p : Nat → Bool) (h : Constraints p) : clause p c2212 = true :=
  Snake9.LocalRup.prove_clause [c972, c87] c2212 (by decide) p (sat_cons (step972 p h) (sat_cons (step87 p h) (sat_nil p)))
def c2213 : List Lit := [(80, true), (12, true), (14, true), (11, false), (3, true)]
theorem step2213 (p : Nat → Bool) (h : Constraints p) : clause p c2213 = true :=
  Snake9.LocalRup.prove_clause [c972, c88] c2213 (by decide) p (sat_cons (step972 p h) (sat_cons (step88 p h) (sat_nil p)))
def c2214 : List Lit := [(20, true), (14, true), (13, true), (15, false), (52, true), (84, true)]
theorem step2214 (p : Nat → Bool) (h : Constraints p) : clause p c2214 = true :=
  Snake9.LocalRup.prove_clause [c973, c144] c2214 (by decide) p (sat_cons (step973 p h) (sat_cons (step144 p h) (sat_nil p)))
def c2215 : List Lit := [(14, true), (52, true), (12, true), (20, true), (15, false), (84, true)]
theorem step2215 (p : Nat → Bool) (h : Constraints p) : clause p c2215 = true :=
  Snake9.LocalRup.prove_clause [c973, c145] c2215 (by decide) p (sat_cons (step973 p h) (sat_cons (step145 p h) (sat_nil p)))
def c2216 : List Lit := [(84, true), (52, true), (12, true), (20, true), (13, true), (15, false)]
theorem step2216 (p : Nat → Bool) (h : Constraints p) : clause p c2216 = true :=
  Snake9.LocalRup.prove_clause [c973, c146] c2216 (by decide) p (sat_cons (step973 p h) (sat_cons (step146 p h) (sat_nil p)))
end B112E057
