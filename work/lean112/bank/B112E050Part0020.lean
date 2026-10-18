import B112E050Part0019
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c3096 : List Lit := [(1736, false), (21, false), (1642, false), (1745, false), (1742, false), (54, true), (19, true), (1636, false), (113, false), (114, true), (123, false), (1829, false), (96, true), (108, false)]
theorem step3096 (p : Nat → Bool) (h : Constraints p) : clause p c3096 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1241, c1269, c1298, c2868, c2860, c1459, c1486, c1704, c2250, c1350, c3095, c1127, c1865, c2301, c3065, c577] c3096 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1241 p h) (sat_cons (step1269 p h) (sat_cons (step1298 p h) (sat_cons (step2868 p h) (sat_cons (step2860 p h) (sat_cons (step1459 p h) (sat_cons (step1486 p h) (sat_cons (step1704 p h) (sat_cons (step2250 p h) (sat_cons (step1350 p h) (sat_cons (step3095 p h) (sat_cons (step1127 p h) (sat_cons (step1865 p h) (sat_cons (step2301 p h) (sat_cons (step3065 p h) (sat_cons (step577 p h) (sat_nil p))))))))))))))))))
def c3097 : List Lit := [(62, true), (1653, true), (1607, false), (1732, true), (1647, false), (1745, false), (1744, false), (1636, false), (110, true), (117, true), (113, false), (109, false), (114, true), (123, false), (1829, false)]
theorem step3097 (p : Nat → Bool) (h : Constraints p) : clause p c3097 = true :=
  Snake9.LocalRup.prove_clause [c1250, c3039, c1252, c1704, c1270, c2250, c1299, c1342] c3097 (by decide) p (sat_cons (step1250 p h) (sat_cons (step3039 p h) (sat_cons (step1252 p h) (sat_cons (step1704 p h) (sat_cons (step1270 p h) (sat_cons (step2250 p h) (sat_cons (step1299 p h) (sat_cons (step1342 p h) (sat_nil p)))))))))
def c3098 : List Lit := [(1736, false), (1642, false), (1745, false), (1742, false), (54, true), (19, true), (95, true), (1636, false), (113, false), (114, true), (123, false), (1829, false), (96, true), (108, false)]
theorem step3098 (p : Nat → Bool) (h : Constraints p) : clause p c3098 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1241, c1269, c1298, c1125, c1864, c2860, c1459, c3096, c1486, c1136, c1704, c1143, c2250, c1155, c1350, c2202, c2203, c1342, c1156, c1305, c1144, c2457, c1139, c577] c3098 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1241 p h) (sat_cons (step1269 p h) (sat_cons (step1298 p h) (sat_cons (step1125 p h) (sat_cons (step1864 p h) (sat_cons (step2860 p h) (sat_cons (step1459 p h) (sat_cons (step3096 p h) (sat_cons (step1486 p h) (sat_cons (step1136 p h) (sat_cons (step1704 p h) (sat_cons (step1143 p h) (sat_cons (step2250 p h) (sat_cons (step1155 p h) (sat_cons (step1350 p h) (sat_cons (step2202 p h) (sat_cons (step2203 p h) (sat_cons (step1342 p h) (sat_cons (step1156 p h) (sat_cons (step1305 p h) (sat_cons (step1144 p h) (sat_cons (step2457 p h) (sat_cons (step1139 p h) (sat_cons (step577 p h) (sat_nil p))))))))))))))))))))))))))
def c3099 : List Lit := [(1830, true), (97, false), (1779, false), (1777, false), (96, true), (108, false), (1817, true), (1783, false)]
theorem step3099 (p : Nat → Bool) (h : Constraints p) : clause p c3099 = true :=
  Snake9.TreeRup.prove_clause [c3093, c1612, c1581, c1561, c2233, c1647, c2234, c1596, c2531, c1654, c2295, c1562, c1543, c1541, c1535, c2959, c2882, c2358, c2337, c1534, c2833, c2870, c640, c3010, c2175, c1599, c3003, c1585, c3067, c2397, c1579, c1573, c1574, c2163, c479, c482, c463, c473, c782, c1437, c1438, c1125, c1235, c1587, c1442, c1443, c1593, c2394, c2409, c821, c1419, c1233, c2266, c1241, c1696, c2251, c3098, c1430, c1428, c3062, c1423, c1898, c2202, c1343, c1300, c1271, c1253, c3097, c330, c256, c2112] c3099 (by decide) p (sat_cons (step3093 p h) (sat_cons (step1612 p h) (sat_cons (step1581 p h) (sat_cons (step1561 p h) (sat_cons (step2233 p h) (sat_cons (step1647 p h) (sat_cons (step2234 p h) (sat_cons (step1596 p h) (sat_cons (step2531 p h) (sat_cons (step1654 p h) (sat_cons (step2295 p h) (sat_cons (step1562 p h) (sat_cons (step1543 p h) (sat_cons (step1541 p h) (sat_cons (step1535 p h) (sat_cons (step2959 p h) (sat_cons (step2882 p h) (sat_cons (step2358 p h) (sat_cons (step2337 p h) (sat_cons (step1534 p h) (sat_cons (step2833 p h) (sat_cons (step2870 p h) (sat_cons (step640 p h) (sat_cons (step3010 p h) (sat_cons (step2175 p h) (sat_cons (step1599 p h) (sat_cons (step3003 p h) (sat_cons (step1585 p h) (sat_cons (step3067 p h) (sat_cons (step2397 p h) (sat_cons (step1579 p h) (sat_cons (step1573 p h) (sat_cons (step1574 p h) (sat_cons (step2163 p h) (sat_cons (step479 p h) (sat_cons (step482 p h) (sat_cons (step463 p h) (sat_cons (step473 p h) (sat_cons (step782 p h) (sat_cons (step1437 p h) (sat_cons (step1438 p h) (sat_cons (step1125 p h) (sat_cons (step1235 p h) (sat_cons (step1587 p h) (sat_cons (step1442 p h) (sat_cons (step1443 p h) (sat_cons (step1593 p h) (sat_cons (step2394 p h) (sat_cons (step2409 p h) (sat_cons (step821 p h) (sat_cons (step1419 p h) (sat_cons (step1233 p h) (sat_cons (step2266 p h) (sat_cons (step1241 p h) (sat_cons (step1696 p h) (sat_cons (step2251 p h) (sat_cons (step3098 p h) (sat_cons (step1430 p h) (sat_cons (step1428 p h) (sat_cons (step3062 p h) (sat_cons (step1423 p h) (sat_cons (step1898 p h) (sat_cons (step2202 p h) (sat_cons (step1343 p h) (sat_cons (step1300 p h) (sat_cons (step1271 p h) (sat_cons (step1253 p h) (sat_cons (step3097 p h) (sat_cons (step330 p h) (sat_cons (step256 p h) (sat_cons (step2112 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c3100 : List Lit := [(1760, true), (1745, false), (114, true), (123, false)]
theorem step3100 (p : Nat → Bool) (h : Constraints p) : clause p c3100 = true :=
  Snake9.LocalRup.prove_clause [c1449, c2860, c1485, c1493, c2356, c1454, c1399, c2359, c3024, c3080] c3100 (by decide) p (sat_cons (step1449 p h) (sat_cons (step2860 p h) (sat_cons (step1485 p h) (sat_cons (step1493 p h) (sat_cons (step2356 p h) (sat_cons (step1454 p h) (sat_cons (step1399 p h) (sat_cons (step2359 p h) (sat_cons (step3024 p h) (sat_cons (step3080 p h) (sat_nil p)))))))))))
def c3101 : List Lit := [(1725, true), (80, false), (1736, true), (123, false)]
theorem step3101 (p : Nat → Bool) (h : Constraints p) : clause p c3101 = true :=
  Snake9.LocalRup.prove_clause [c3087, c1399, c2359, c1403, c3082, c3024, c1375, c1423, c1373, c1428, c1955] c3101 (by decide) p (sat_cons (step3087 p h) (sat_cons (step1399 p h) (sat_cons (step2359 p h) (sat_cons (step1403 p h) (sat_cons (step3082 p h) (sat_cons (step3024 p h) (sat_cons (step1375 p h) (sat_cons (step1423 p h) (sat_cons (step1373 p h) (sat_cons (step1428 p h) (sat_cons (step1955 p h) (sat_nil p))))))))))))
def c3102 : List Lit := [(85, false), (82, false), (83, false), (73, true), (80, false), (1728, true), (123, false), (108, false)]
theorem step3102 (p : Nat → Bool) (h : Constraints p) : clause p c3102 = true :=
  Snake9.LocalRup.prove_clause [c2586, c336, c364, c1385, c2111, c1396, c260, c259, c1410, c1371, c1380] c3102 (by decide) p (sat_cons (step2586 p h) (sat_cons (step336 p h) (sat_cons (step364 p h) (sat_cons (step1385 p h) (sat_cons (step2111 p h) (sat_cons (step1396 p h) (sat_cons (step260 p h) (sat_cons (step259 p h) (sat_cons (step1410 p h) (sat_cons (step1371 p h) (sat_cons (step1380 p h) (sat_nil p))))))))))))
def c3103 : List Lit := [(1707, true), (67, false), (108, false)]
theorem step3103 (p : Nat → Bool) (h : Constraints p) : clause p c3103 = true :=
  Snake9.LocalRup.prove_clause [c1369, c1370, c258] c3103 (by decide) p (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step258 p h) (sat_nil p))))
def c3104 : List Lit := [(91, false), (87, false), (114, true), (123, false), (97, false), (108, false)]
theorem step3104 (p : Nat → Bool) (h : Constraints p) : clause p c3104 = true :=
  Snake9.LocalRup.prove_clause [c593, c429, c2118] c3104 (by decide) p (sat_cons (step593 p h) (sat_cons (step429 p h) (sat_cons (step2118 p h) (sat_nil p))))
def c3105 : List Lit := [(1707, true), (1671, true), (117, true), (127, false), (123, false), (109, false), (1796, true), (108, false)]
theorem step3105 (p : Nat → Bool) (h : Constraints p) : clause p c3105 = true :=
  Snake9.LocalRup.prove_clause [c1369, c1370, c3103, c630, c2085, c2086, c2175, c238, c1991, c3003, c1249, c1238, c1299, c3068] c3105 (by decide) p (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step3103 p h) (sat_cons (step630 p h) (sat_cons (step2085 p h) (sat_cons (step2086 p h) (sat_cons (step2175 p h) (sat_cons (step238 p h) (sat_cons (step1991 p h) (sat_cons (step3003 p h) (sat_cons (step1249 p h) (sat_cons (step1238 p h) (sat_cons (step1299 p h) (sat_cons (step3068 p h) (sat_nil p)))))))))))))))
def c3106 : List Lit := [(1803, true), (83, false), (109, false), (1800, true), (97, false), (108, false), (1811, true)]
theorem step3106 (p : Nat → Bool) (h : Constraints p) : clause p c3106 = true :=
  Snake9.LocalRup.prove_clause [c1585, c2397, c2409, c1579, c1587, c1573, c828, c671, c782, c2179] c3106 (by decide) p (sat_cons (step1585 p h) (sat_cons (step2397 p h) (sat_cons (step2409 p h) (sat_cons (step1579 p h) (sat_cons (step1587 p h) (sat_cons (step1573 p h) (sat_cons (step828 p h) (sat_cons (step671 p h) (sat_cons (step782 p h) (sat_cons (step2179 p h) (sat_nil p)))))))))))
def c3107 : List Lit := [(1731, true), (109, false), (1800, true), (97, false), (108, false), (1811, true)]
theorem step3107 (p : Nat → Bool) (h : Constraints p) : clause p c3107 = true :=
  Snake9.LocalRup.prove_clause [c1419, c3106, c1599, c1590, c1592, c2373, c1587, c1988, c2171, c829] c3107 (by decide) p (sat_cons (step1419 p h) (sat_cons (step3106 p h) (sat_cons (step1599 p h) (sat_cons (step1590 p h) (sat_cons (step1592 p h) (sat_cons (step2373 p h) (sat_cons (step1587 p h) (sat_cons (step1988 p h) (sat_cons (step2171 p h) (sat_cons (step829 p h) (sat_nil p)))))))))))
def c3108 : List Lit := [(69, false), (53, false), (110, true), (113, false), (117, true), (114, true), (109, false)]
theorem step3108 (p : Nat → Bool) (h : Constraints p) : clause p c3108 = true :=
  Snake9.LocalRup.prove_clause [c710, c266, c2156] c3108 (by decide) p (sat_cons (step710 p h) (sat_cons (step266 p h) (sat_cons (step2156 p h) (sat_nil p))))
def c3109 : List Lit := [(1726, true), (1708, false), (80, true), (113, false), (114, true)]
theorem step3109 (p : Nat → Bool) (h : Constraints p) : clause p c3109 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1990, c1382, c1384, c2412, c2364, c1389, c1381, c1412] c3109 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1990 p h) (sat_cons (step1382 p h) (sat_cons (step1384 p h) (sat_cons (step2412 p h) (sat_cons (step2364 p h) (sat_cons (step1389 p h) (sat_cons (step1381 p h) (sat_cons (step1412 p h) (sat_nil p))))))))))
def c3110 : List Lit := [(1689, true), (80, true), (123, false), (1635, false), (108, false)]
theorem step3110 (p : Nat → Bool) (h : Constraints p) : clause p c3110 = true :=
  Snake9.LocalRup.prove_clause [c2868, c1289, c1329, c2577, c1290, c577, c1927] c3110 (by decide) p (sat_cons (step2868 p h) (sat_cons (step1289 p h) (sat_cons (step1329 p h) (sat_cons (step2577 p h) (sat_cons (step1290 p h) (sat_cons (step577 p h) (sat_cons (step1927 p h) (sat_nil p))))))))
def c3111 : List Lit := [(1596, true), (87, false), (1751, true), (91, true), (85, true), (1731, false)]
theorem step3111 (p : Nat → Bool) (h : Constraints p) : clause p c3111 = true :=
  Snake9.LocalRup.prove_clause [c3049, c1898] c3111 (by decide) p (sat_cons (step3049 p h) (sat_cons (step1898 p h) (sat_nil p)))
def c3112 : List Lit := [(1580, false), (1620, false), (1670, true), (87, false), (1742, true), (1745, true), (1597, true), (1652, false), (27, true), (91, true), (97, false)]
theorem step3112 (p : Nat → Bool) (h : Constraints p) : clause p c3112 = true :=
  Snake9.LocalRup.prove_clause [c1139, c1141, c1160, c1252, c1864, c1133, c1156, c1862, c1142, c1144, c1140, c1135, c1136, c29, c1913, c2607, c1298, c1261, c1265, c1255, c1238, c1240, c1246, c1247, c1235, c1236, c1232, c171, c200, c167, c2062, c1909, c191, c1445, c1438, c1435, c486, c427, c2115] c3112 (by decide) p (sat_cons (step1139 p h) (sat_cons (step1141 p h) (sat_cons (step1160 p h) (sat_cons (step1252 p h) (sat_cons (step1864 p h) (sat_cons (step1133 p h) (sat_cons (step1156 p h) (sat_cons (step1862 p h) (sat_cons (step1142 p h) (sat_cons (step1144 p h) (sat_cons (step1140 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step29 p h) (sat_cons (step1913 p h) (sat_cons (step2607 p h) (sat_cons (step1298 p h) (sat_cons (step1261 p h) (sat_cons (step1265 p h) (sat_cons (step1255 p h) (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1246 p h) (sat_cons (step1247 p h) (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step1232 p h) (sat_cons (step171 p h) (sat_cons (step200 p h) (sat_cons (step167 p h) (sat_cons (step2062 p h) (sat_cons (step1909 p h) (sat_cons (step191 p h) (sat_cons (step1445 p h) (sat_cons (step1438 p h) (sat_cons (step1435 p h) (sat_cons (step486 p h) (sat_cons (step427 p h) (sat_cons (step2115 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c3113 : List Lit := [(21, false), (1580, true), (1745, true), (91, true), (113, false)]
theorem step3113 (p : Nat → Bool) (h : Constraints p) : clause p c3113 = true :=
  Snake9.LocalRup.prove_clause [c1126, c1125, c2793, c55, c2760, c2028, c1445, c399, c1435] c3113 (by decide) p (sat_cons (step1126 p h) (sat_cons (step1125 p h) (sat_cons (step2793 p h) (sat_cons (step55 p h) (sat_cons (step2760 p h) (sat_cons (step2028 p h) (sat_cons (step1445 p h) (sat_cons (step399 p h) (sat_cons (step1435 p h) (sat_nil p))))))))))
def c3114 : List Lit := [(115, true), (39, false), (117, true), (1800, true), (97, false)]
theorem step3114 (p : Nat → Bool) (h : Constraints p) : clause p c3114 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1575, c2446, c779] c3114 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1575 p h) (sat_cons (step2446 p h) (sat_cons (step779 p h) (sat_nil p)))))
def c3115 : List Lit := [(1644, false), (1659, true), (102, true), (80, true)]
theorem step3115 (p : Nat → Bool) (h : Constraints p) : clause p c3115 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1265, c1252, c1250, c1941, c2080] c3115 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1265 p h) (sat_cons (step1252 p h) (sat_cons (step1250 p h) (sat_cons (step1941 p h) (sat_cons (step2080 p h) (sat_nil p)))))))
def c3116 : List Lit := [(115, false), (93, false), (54, false), (1742, true)]
theorem step3116 (p : Nat → Bool) (h : Constraints p) : clause p c3116 = true :=
  Snake9.LocalRup.prove_clause [c467, c470, c1438] c3116 (by decide) p (sat_cons (step467 p h) (sat_cons (step470 p h) (sat_cons (step1438 p h) (sat_nil p))))
def c3117 : List Lit := [(115, true), (109, false), (1800, true), (97, false), (1811, true)]
theorem step3117 (p : Nat → Bool) (h : Constraints p) : clause p c3117 = true :=
  Snake9.LocalRup.prove_clause [c2959, c2374, c1577, c1574, c1575, c2446, c1579, c782, c2397, c1587, c1599, c1590] c3117 (by decide) p (sat_cons (step2959 p h) (sat_cons (step2374 p h) (sat_cons (step1577 p h) (sat_cons (step1574 p h) (sat_cons (step1575 p h) (sat_cons (step2446 p h) (sat_cons (step1579 p h) (sat_cons (step782 p h) (sat_cons (step2397 p h) (sat_cons (step1587 p h) (sat_cons (step1599 p h) (sat_cons (step1590 p h) (sat_nil p)))))))))))))
def c3118 : List Lit := [(1751, true), (85, true), (95, true), (1736, false), (1731, false), (1739, false), (109, false), (97, false)]
theorem step3118 (p : Nat → Bool) (h : Constraints p) : clause p c3118 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1442, c1459, c1463, c1443, c1429, c1438, c1424, c486, c371, c2123] c3118 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1442 p h) (sat_cons (step1459 p h) (sat_cons (step1463 p h) (sat_cons (step1443 p h) (sat_cons (step1429 p h) (sat_cons (step1438 p h) (sat_cons (step1424 p h) (sat_cons (step486 p h) (sat_cons (step371 p h) (sat_cons (step2123 p h) (sat_nil p))))))))))))
def c3119 : List Lit := [(54, false), (1658, false), (1737, false), (1725, false), (93, false), (115, false), (1739, false), (1830, false)]
theorem step3119 (p : Nat → Bool) (h : Constraints p) : clause p c3119 = true :=
  Snake9.LocalRup.prove_clause [c3116, c453, c1443, c1125, c1464, c2475, c1496, c2247, c1720] c3119 (by decide) p (sat_cons (step3116 p h) (sat_cons (step453 p h) (sat_cons (step1443 p h) (sat_cons (step1125 p h) (sat_cons (step1464 p h) (sat_cons (step2475 p h) (sat_cons (step1496 p h) (sat_cons (step2247 p h) (sat_cons (step1720 p h) (sat_nil p))))))))))
def c3120 : List Lit := [(1606, true), (1637, true), (108, false)]
theorem step3120 (p : Nat → Bool) (h : Constraints p) : clause p c3120 = true :=
  Snake9.LocalRup.prove_clause [c1872, c1875, c2201, c1915, c1896, c1867, c2265, c1099, c1141, c1916, c1139] c3120 (by decide) p (sat_cons (step1872 p h) (sat_cons (step1875 p h) (sat_cons (step2201 p h) (sat_cons (step1915 p h) (sat_cons (step1896 p h) (sat_cons (step1867 p h) (sat_cons (step2265 p h) (sat_cons (step1099 p h) (sat_cons (step1141 p h) (sat_cons (step1916 p h) (sat_cons (step1139 p h) (sat_nil p))))))))))))
def c3121 : List Lit := [(1595, true), (7, false), (44, false), (1638, true)]
theorem step3121 (p : Nat → Bool) (h : Constraints p) : clause p c3121 = true :=
  Snake9.LocalRup.prove_clause [c1867, c1154, c1143, c1132, c1136, c1862, c2673] c3121 (by decide) p (sat_cons (step1867 p h) (sat_cons (step1154 p h) (sat_cons (step1143 p h) (sat_cons (step1132 p h) (sat_cons (step1136 p h) (sat_cons (step1862 p h) (sat_cons (step2673 p h) (sat_nil p))))))))
def c3122 : List Lit := [(1590, true), (7, false), (44, false), (1637, true)]
theorem step3122 (p : Nat → Bool) (h : Constraints p) : clause p c3122 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1143, c1138, c1139, c1136, c1913, c1916, c1187] c3122 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1136 p h) (sat_cons (step1913 p h) (sat_cons (step1916 p h) (sat_cons (step1187 p h) (sat_nil p)))))))))
def c3123 : List Lit := [(27, false), (21, false), (7, false), (44, false), (1637, true), (97, false), (108, false)]
theorem step3123 (p : Nat → Bool) (h : Constraints p) : clause p c3123 = true :=
  Snake9.LocalRup.prove_clause [c1916, c1187, c648, c87, c61, c2043] c3123 (by decide) p (sat_cons (step1916 p h) (sat_cons (step1187 p h) (sat_cons (step648 p h) (sat_cons (step87 p h) (sat_cons (step61 p h) (sat_cons (step2043 p h) (sat_nil p)))))))
def c3124 : List Lit := [(1580, true), (1746, true), (21, false), (95, true), (93, false), (115, false), (113, false)]
theorem step3124 (p : Nat → Bool) (h : Constraints p) : clause p c3124 = true :=
  Snake9.LocalRup.prove_clause [c1125, c1126, c457, c55, c1438, c2028, c1446, c402, c399, c1435] c3124 (by decide) p (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step457 p h) (sat_cons (step55 p h) (sat_cons (step1438 p h) (sat_cons (step2028 p h) (sat_cons (step1446 p h) (sat_cons (step402 p h) (sat_cons (step399 p h) (sat_cons (step1435 p h) (sat_nil p)))))))))))
def c3125 : List Lit := [(1618, false), (21, false), (7, false), (44, false), (1671, true), (1654, false), (1644, false)]
theorem step3125 (p : Nat → Bool) (h : Constraints p) : clause p c3125 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1265, c1305, c1194, c2723, c2628, c2608, c1891, c118, c1233, c2047, c1241, c112, c1270, c2751, c1299] c3125 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1265 p h) (sat_cons (step1305 p h) (sat_cons (step1194 p h) (sat_cons (step2723 p h) (sat_cons (step2628 p h) (sat_cons (step2608 p h) (sat_cons (step1891 p h) (sat_cons (step118 p h) (sat_cons (step1233 p h) (sat_cons (step2047 p h) (sat_cons (step1241 p h) (sat_cons (step112 p h) (sat_cons (step1270 p h) (sat_cons (step2751 p h) (sat_cons (step1299 p h) (sat_nil p)))))))))))))))))
def c3126 : List Lit := [(27, false), (30, false), (7, false), (44, false), (1637, true), (97, false), (108, false)]
theorem step3126 (p : Nat → Bool) (h : Constraints p) : clause p c3126 = true :=
  Snake9.LocalRup.prove_clause [c135, c136, c137, c87, c1190, c1204, c2742, c1192, c1202, c1221, c1212] c3126 (by decide) p (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step137 p h) (sat_cons (step87 p h) (sat_cons (step1190 p h) (sat_cons (step1204 p h) (sat_cons (step2742 p h) (sat_cons (step1192 p h) (sat_cons (step1202 p h) (sat_cons (step1221 p h) (sat_cons (step1212 p h) (sat_nil p))))))))))))
def c3127 : List Lit := [(24, true), (25, false), (27, true), (154, true)]
theorem step3127 (p : Nat → Bool) (h : Constraints p) : clause p c3127 = true :=
  Snake9.LocalRup.prove_clause [c2034, c2036, c73, c1749] c3127 (by decide) p (sat_cons (step2034 p h) (sat_cons (step2036 p h) (sat_cons (step73 p h) (sat_cons (step1749 p h) (sat_nil p)))))
def c3128 : List Lit := [(1636, true), (123, false), (1618, false), (160, true), (114, true), (109, true)]
theorem step3128 (p : Nat → Bool) (h : Constraints p) : clause p c3128 = true :=
  Snake9.LocalRup.prove_clause [c1226, c2333, c2331, c1196, c1190, c1191, c1195, c2608, c1223, c93, c2603] c3128 (by decide) p (sat_cons (step1226 p h) (sat_cons (step2333 p h) (sat_cons (step2331 p h) (sat_cons (step1196 p h) (sat_cons (step1190 p h) (sat_cons (step1191 p h) (sat_cons (step1195 p h) (sat_cons (step2608 p h) (sat_cons (step1223 p h) (sat_cons (step93 p h) (sat_cons (step2603 p h) (sat_nil p))))))))))))
def c3129 : List Lit := [(27, true), (1591, true), (30, false)]
theorem step3129 (p : Nat → Bool) (h : Constraints p) : clause p c3129 = true :=
  Snake9.LocalRup.prove_clause [c1142, c1139, c1140, c1144, c1913, c1136] c3129 (by decide) p (sat_cons (step1142 p h) (sat_cons (step1139 p h) (sat_cons (step1140 p h) (sat_cons (step1144 p h) (sat_cons (step1913 p h) (sat_cons (step1136 p h) (sat_nil p)))))))
def c3130 : List Lit := [(123, true), (107, true), (1811, true)]
theorem step3130 (p : Nat → Bool) (h : Constraints p) : clause p c3130 = true :=
  Snake9.LocalRup.prove_clause [c1602, c1584, c1586, c1599, c1590, c1592, c2373, c1587, c2177, c833] c3130 (by decide) p (sat_cons (step1602 p h) (sat_cons (step1584 p h) (sat_cons (step1586 p h) (sat_cons (step1599 p h) (sat_cons (step1590 p h) (sat_cons (step1592 p h) (sat_cons (step2373 p h) (sat_cons (step1587 p h) (sat_cons (step2177 p h) (sat_cons (step833 p h) (sat_nil p)))))))))))
def c3131 : List Lit := [(128, false), (125, false), (46, false), (1811, true)]
theorem step3131 (p : Nat → Bool) (h : Constraints p) : clause p c3131 = true :=
  Snake9.LocalRup.prove_clause [c823, c822, c1592, c1585, c1599] c3131 (by decide) p (sat_cons (step823 p h) (sat_cons (step822 p h) (sat_cons (step1592 p h) (sat_cons (step1585 p h) (sat_cons (step1599 p h) (sat_nil p))))))
def c3132 : List Lit := [(125, false), (46, false), (1811, true)]
theorem step3132 (p : Nat → Bool) (h : Constraints p) : clause p c3132 = true :=
  Snake9.LocalRup.prove_clause [c1596, c3131, c1587, c1590, c1593, c1599, c821, c1585] c3132 (by decide) p (sat_cons (step1596 p h) (sat_cons (step3131 p h) (sat_cons (step1587 p h) (sat_cons (step1590 p h) (sat_cons (step1593 p h) (sat_cons (step1599 p h) (sat_cons (step821 p h) (sat_cons (step1585 p h) (sat_nil p)))))))))
def c3133 : List Lit := [(1623, true), (37, false), (46, false), (30, true), (1618, false)]
theorem step3133 (p : Nat → Bool) (h : Constraints p) : clause p c3133 = true :=
  Snake9.LocalRup.prove_clause [c1197, c1195, c1188, c1189, c113] c3133 (by decide) p (sat_cons (step1197 p h) (sat_cons (step1195 p h) (sat_cons (step1188 p h) (sat_cons (step1189 p h) (sat_cons (step113 p h) (sat_nil p))))))
def c3134 : List Lit := [(123, true), (97, false), (108, false), (1811, true)]
theorem step3134 (p : Nat → Bool) (h : Constraints p) : clause p c3134 = true :=
  Snake9.LocalRup.prove_clause [c1584, c3130, c1599, c671, c1590, c1587] c3134 (by decide) p (sat_cons (step1584 p h) (sat_cons (step3130 p h) (sat_cons (step1599 p h) (sat_cons (step671 p h) (sat_cons (step1590 p h) (sat_cons (step1587 p h) (sat_nil p)))))))
def c3135 : List Lit := [(104, false), (92, false), (107, true), (125, true), (97, false)]
theorem step3135 (p : Nat → Bool) (h : Constraints p) : clause p c3135 = true :=
  Snake9.LocalRup.prove_clause [c493, c2142] c3135 (by decide) p (sat_cons (step493 p h) (sat_cons (step2142 p h) (sat_nil p)))
def c3136 : List Lit := [(1725, true), (1660, true), (54, true), (123, false), (108, false)]
theorem step3136 (p : Nat → Bool) (h : Constraints p) : clause p c3136 = true :=
  Snake9.LocalRup.prove_clause [c1399, c3040, c1369, c1370, c3103, c1897, c587, c2587, c2677] c3136 (by decide) p (sat_cons (step1399 p h) (sat_cons (step3040 p h) (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step3103 p h) (sat_cons (step1897 p h) (sat_cons (step587 p h) (sat_cons (step2587 p h) (sat_cons (step2677 p h) (sat_nil p))))))))))
def c3137 : List Lit := [(104, false), (92, false), (107, true), (97, false), (1817, true)]
theorem step3137 (p : Nat → Bool) (h : Constraints p) : clause p c3137 = true :=
  Snake9.LocalRup.prove_clause [c2234, c2884, c3135, c1587, c3007, c1590] c3137 (by decide) p (sat_cons (step2234 p h) (sat_cons (step2884 p h) (sat_cons (step3135 p h) (sat_cons (step1587 p h) (sat_cons (step3007 p h) (sat_cons (step1590 p h) (sat_nil p)))))))
def c3138 : List Lit := [(87, true), (1736, true), (123, false)]
theorem step3138 (p : Nat → Bool) (h : Constraints p) : clause p c3138 = true :=
  Snake9.LocalRup.prove_clause [c1426, c2523, c1424, c320, c338, c2589, c2024, c297, c913, c1017, c916, c1018, c917, c1026, c919, c1028, c956, c1047, c1007, c1091, c2200] c3138 (by decide) p (sat_cons (step1426 p h) (sat_cons (step2523 p h) (sat_cons (step1424 p h) (sat_cons (step320 p h) (sat_cons (step338 p h) (sat_cons (step2589 p h) (sat_cons (step2024 p h) (sat_cons (step297 p h) (sat_cons (step913 p h) (sat_cons (step1017 p h) (sat_cons (step916 p h) (sat_cons (step1018 p h) (sat_cons (step917 p h) (sat_cons (step1026 p h) (sat_cons (step919 p h) (sat_cons (step1028 p h) (sat_cons (step956 p h) (sat_cons (step1047 p h) (sat_cons (step1007 p h) (sat_cons (step1091 p h) (sat_cons (step2200 p h) (sat_nil p))))))))))))))))))))))
def c3139 : List Lit := [(1659, false), (1670, true), (1692, true), (7, true), (114, true), (109, true), (123, false)]
theorem step3139 (p : Nat → Bool) (h : Constraints p) : clause p c3139 = true :=
  Snake9.LocalRup.prove_clause [c2024, c913, c916, c917, c919, c2186, c949, c946, c943, c940, c1099, c1896, c2293, c1291, c1298, c1349, c3128, c1176, c1915] c3139 (by decide) p (sat_cons (step2024 p h) (sat_cons (step913 p h) (sat_cons (step916 p h) (sat_cons (step917 p h) (sat_cons (step919 p h) (sat_cons (step2186 p h) (sat_cons (step949 p h) (sat_cons (step946 p h) (sat_cons (step943 p h) (sat_cons (step940 p h) (sat_cons (step1099 p h) (sat_cons (step1896 p h) (sat_cons (step2293 p h) (sat_cons (step1291 p h) (sat_cons (step1298 p h) (sat_cons (step1349 p h) (sat_cons (step3128 p h) (sat_cons (step1176 p h) (sat_cons (step1915 p h) (sat_nil p))))))))))))))))))))
def c3140 : List Lit := [(104, false), (125, true), (108, false), (92, false), (97, false)]
theorem step3140 (p : Nat → Bool) (h : Constraints p) : clause p c3140 = true :=
  Snake9.LocalRup.prove_clause [c669, c3135] c3140 (by decide) p (sat_cons (step669 p h) (sat_cons (step3135 p h) (sat_nil p)))
def c3141 : List Lit := [(1805, false), (111, false), (123, false), (1811, true)]
theorem step3141 (p : Nat → Bool) (h : Constraints p) : clause p c3141 = true :=
  Snake9.LocalRup.prove_clause [c1596, c1590, c1593, c1599, c1585, c796, c2166, c2168, c1814] c3141 (by decide) p (sat_cons (step1596 p h) (sat_cons (step1590 p h) (sat_cons (step1593 p h) (sat_cons (step1599 p h) (sat_cons (step1585 p h) (sat_cons (step796 p h) (sat_cons (step2166 p h) (sat_cons (step2168 p h) (sat_cons (step1814 p h) (sat_nil p))))))))))
def c3142 : List Lit := [(1731, false), (1744, false), (1760, true), (123, false)]
theorem step3142 (p : Nat → Bool) (h : Constraints p) : clause p c3142 = true :=
  Snake9.LocalRup.prove_clause [c2860, c1485, c1458, c1427, c1428, c1453, c1423, c1493, c2389, c3101, c2274] c3142 (by decide) p (sat_cons (step2860 p h) (sat_cons (step1485 p h) (sat_cons (step1458 p h) (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step1453 p h) (sat_cons (step1423 p h) (sat_cons (step1493 p h) (sat_cons (step2389 p h) (sat_cons (step3101 p h) (sat_cons (step2274 p h) (sat_nil p))))))))))))
def c3143 : List Lit := [(1735, true), (80, false), (1728, true), (123, false), (108, false)]
theorem step3143 (p : Nat → Bool) (h : Constraints p) : clause p c3143 = true :=
  Snake9.LocalRup.prove_clause [c1425, c1427, c3080, c1423, c1419, c1420, c3102] c3143 (by decide) p (sat_cons (step1425 p h) (sat_cons (step1427 p h) (sat_cons (step3080 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step3102 p h) (sat_nil p))))))))
def c3144 : List Lit := [(85, false), (1661, true), (1726, true), (72, true), (80, false), (1732, true), (87, false), (123, false)]
theorem step3144 (p : Nat → Bool) (h : Constraints p) : clause p c3144 = true :=
  Snake9.LocalRup.prove_clause [c1400, c320, c330, c3082, c2586, c2024, c1404, c1396, c913, c1375, c1377, c1385, c916, c1373, c2390, c917, c2369, c919, c995, c956, c1000, c2192] c3144 (by decide) p (sat_cons (step1400 p h) (sat_cons (step320 p h) (sat_cons (step330 p h) (sat_cons (step3082 p h) (sat_cons (step2586 p h) (sat_cons (step2024 p h) (sat_cons (step1404 p h) (sat_cons (step1396 p h) (sat_cons (step913 p h) (sat_cons (step1375 p h) (sat_cons (step1377 p h) (sat_cons (step1385 p h) (sat_cons (step916 p h) (sat_cons (step1373 p h) (sat_cons (step2390 p h) (sat_cons (step917 p h) (sat_cons (step2369 p h) (sat_cons (step919 p h) (sat_cons (step995 p h) (sat_cons (step956 p h) (sat_cons (step1000 p h) (sat_cons (step2192 p h) (sat_nil p)))))))))))))))))))))))
def c3145 : List Lit := [(1731, true), (122, true), (73, false), (1811, true)]
theorem step3145 (p : Nat → Bool) (h : Constraints p) : clause p c3145 = true :=
  Snake9.LocalRup.prove_clause [c3081, c2410, c1938, c2166, c1599, c1585] c3145 (by decide) p (sat_cons (step3081 p h) (sat_cons (step2410 p h) (sat_cons (step1938 p h) (sat_cons (step2166 p h) (sat_cons (step1599 p h) (sat_cons (step1585 p h) (sat_nil p)))))))
def c3146 : List Lit := [(1744, false), (1735, false), (1760, true), (80, false), (123, false)]
theorem step3146 (p : Nat → Bool) (h : Constraints p) : clause p c3146 = true :=
  Snake9.LocalRup.prove_clause [c2860, c1485, c1458, c1453, c3101, c1493] c3146 (by decide) p (sat_cons (step2860 p h) (sat_cons (step1485 p h) (sat_cons (step1458 p h) (sat_cons (step1453 p h) (sat_cons (step3101 p h) (sat_cons (step1493 p h) (sat_nil p)))))))
def c3147 : List Lit := [(1711, true), (62, true), (373, true), (1661, true), (1731, true), (87, false)]
theorem step3147 (p : Nat → Bool) (h : Constraints p) : clause p c3147 = true :=
  Snake9.LocalRup.prove_clause [c1375, c1377, c1373, c2369, c3023, c2727] c3147 (by decide) p (sat_cons (step1375 p h) (sat_cons (step1377 p h) (sat_cons (step1373 p h) (sat_cons (step2369 p h) (sat_cons (step3023 p h) (sat_cons (step2727 p h) (sat_nil p)))))))
def c3148 : List Lit := [(63, false), (1707, true), (1731, true)]
theorem step3148 (p : Nat → Bool) (h : Constraints p) : clause p c3148 = true :=
  Snake9.LocalRup.prove_clause [c3023, c2727] c3148 (by decide) p (sat_cons (step3023 p h) (sat_cons (step2727 p h) (sat_nil p)))
def c3149 : List Lit := [(1776, false), (1790, true), (1829, true), (108, true), (97, false), (1783, false)]
theorem step3149 (p : Nat → Bool) (h : Constraints p) : clause p c3149 = true :=
  Snake9.LocalRup.prove_clause [c1556, c1557, c2875, c1641, c1539, c1532, c1537, c2882] c3149 (by decide) p (sat_cons (step1556 p h) (sat_cons (step1557 p h) (sat_cons (step2875 p h) (sat_cons (step1641 p h) (sat_cons (step1539 p h) (sat_cons (step1532 p h) (sat_cons (step1537 p h) (sat_cons (step2882 p h) (sat_nil p)))))))))
def c3150 : List Lit := [(101, false), (66, false), (102, true), (97, false), (87, false)]
theorem step3150 (p : Nat → Bool) (h : Constraints p) : clause p c3150 = true :=
  Snake9.LocalRup.prove_clause [c1967, c431] c3150 (by decide) p (sat_cons (step1967 p h) (sat_cons (step431 p h) (sat_nil p)))
def c3151 : List Lit := [(1810, true), (66, false), (97, false)]
theorem step3151 (p : Nat → Bool) (h : Constraints p) : clause p c3151 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1598, c1590, c1592, c2373, c1585, c1587, c833, c659, c2177] c3151 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1598 p h) (sat_cons (step1590 p h) (sat_cons (step1592 p h) (sat_cons (step2373 p h) (sat_cons (step1585 p h) (sat_cons (step1587 p h) (sat_cons (step833 p h) (sat_cons (step659 p h) (sat_cons (step2177 p h) (sat_nil p)))))))))))
def c3152 : List Lit := [(1807, true), (125, true), (107, true)]
theorem step3152 (p : Nat → Bool) (h : Constraints p) : clause p c3152 = true :=
  Snake9.LocalRup.prove_clause [c1590, c2373, c1587, c2177] c3152 (by decide) p (sat_cons (step1590 p h) (sat_cons (step2373 p h) (sat_cons (step1587 p h) (sat_cons (step2177 p h) (sat_nil p)))))
def c3153 : List Lit := [(58, true), (107, true), (1707, true)]
theorem step3153 (p : Nat → Bool) (h : Constraints p) : clause p c3153 = true :=
  Snake9.LocalRup.prove_clause [c1370, c1369, c2091, c2090, c1777] c3153 (by decide) p (sat_cons (step1370 p h) (sat_cons (step1369 p h) (sat_cons (step2091 p h) (sat_cons (step2090 p h) (sat_cons (step1777 p h) (sat_nil p))))))
def c3154 : List Lit := [(1817, true), (118, true), (127, false), (123, false), (1807, false), (125, true)]
theorem step3154 (p : Nat → Bool) (h : Constraints p) : clause p c3154 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1612, c2255, c2010, c2374, c1573, c2398] c3154 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1612 p h) (sat_cons (step2255 p h) (sat_cons (step2010 p h) (sat_cons (step2374 p h) (sat_cons (step1573 p h) (sat_cons (step2398 p h) (sat_nil p))))))))
def c3155 : List Lit := [(93, true), (1652, false), (1691, true), (87, false), (1635, false)]
theorem step3155 (p : Nat → Bool) (h : Constraints p) : clause p c3155 = true :=
  Snake9.LocalRup.prove_clause [c2709, c1291, c3056, c1340, c2793, c2202, c2371] c3155 (by decide) p (sat_cons (step2709 p h) (sat_cons (step1291 p h) (sat_cons (step3056 p h) (sat_cons (step1340 p h) (sat_cons (step2793 p h) (sat_cons (step2202 p h) (sat_cons (step2371 p h) (sat_nil p))))))))
def c3156 : List Lit := [(72, true), (1731, true), (80, true), (1725, true)]
theorem step3156 (p : Nat → Bool) (h : Constraints p) : clause p c3156 = true :=
  Snake9.LocalRup.prove_clause [c1420, c2359, c1384, c2599, c1385, c295, c1955, c1387, c1373, c1392, c1375, c1403] c3156 (by decide) p (sat_cons (step1420 p h) (sat_cons (step2359 p h) (sat_cons (step1384 p h) (sat_cons (step2599 p h) (sat_cons (step1385 p h) (sat_cons (step295 p h) (sat_cons (step1955 p h) (sat_cons (step1387 p h) (sat_cons (step1373 p h) (sat_cons (step1392 p h) (sat_cons (step1375 p h) (sat_cons (step1403 p h) (sat_nil p)))))))))))))
def c3157 : List Lit := [(1810, true), (1731, true)]
theorem step3157 (p : Nat → Bool) (h : Constraints p) : clause p c3157 = true :=
  Snake9.LocalRup.prove_clause [c1595, c2630, c1592, c1988] c3157 (by decide) p (sat_cons (step1595 p h) (sat_cons (step2630 p h) (sat_cons (step1592 p h) (sat_cons (step1988 p h) (sat_nil p)))))
def c3158 : List Lit := [(1807, true), (1731, true)]
theorem step3158 (p : Nat → Bool) (h : Constraints p) : clause p c3158 = true :=
  Snake9.LocalRup.prove_clause [c1419, c1590, c1592, c2373, c1587, c1988, c2171, c829] c3158 (by decide) p (sat_cons (step1419 p h) (sat_cons (step1590 p h) (sat_cons (step1592 p h) (sat_cons (step2373 p h) (sat_cons (step1587 p h) (sat_cons (step1988 p h) (sat_cons (step2171 p h) (sat_cons (step829 p h) (sat_nil p)))))))))
def c3159 : List Lit := [(1780, false), (1790, true), (96, true), (87, false)]
theorem step3159 (p : Nat → Bool) (h : Constraints p) : clause p c3159 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1526, c1553, c1543, c1544, c1557, c1536, c1529, c1527, c1520, c2645] c3159 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1526 p h) (sat_cons (step1553 p h) (sat_cons (step1543 p h) (sat_cons (step1544 p h) (sat_cons (step1557 p h) (sat_cons (step1536 p h) (sat_cons (step1529 p h) (sat_cons (step1527 p h) (sat_cons (step1520 p h) (sat_cons (step2645 p h) (sat_nil p))))))))))))
end B112E050
