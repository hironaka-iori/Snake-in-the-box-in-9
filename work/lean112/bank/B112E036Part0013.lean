import B112E036Part0012
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2477 : List Lit := [(1724, false), (1849, true), (1741, false), (1807, false), (1735, false), (73, false)]
theorem step2477 (p : Nat → Bool) (h : Constraints p) : clause p c2477 = true :=
  Snake9.LocalRup.prove_clause [c2468, c2469, c2279, c2316] c2477 (by decide) p (sat_cons (step2468 p h) (sat_cons (step2469 p h) (sat_cons (step2279 p h) (sat_cons (step2316 p h) (sat_nil p)))))
def c2478 : List Lit := [(1850, true), (1807, false), (92, true), (1725, false), (1735, false)]
theorem step2478 (p : Nat → Bool) (h : Constraints p) : clause p c2478 = true :=
  Snake9.LocalRup.prove_clause [c2399, c1335, c1337, c1346, c1367, c1554, c1561, c1368, c1347, c1338, c1340, c1336, c1333, c2466, c2436, c2279, c2457, c1498, c2267, c2032, c531, c529, c1388] c2478 (by decide) p (sat_cons (step2399 p h) (sat_cons (step1335 p h) (sat_cons (step1337 p h) (sat_cons (step1346 p h) (sat_cons (step1367 p h) (sat_cons (step1554 p h) (sat_cons (step1561 p h) (sat_cons (step1368 p h) (sat_cons (step1347 p h) (sat_cons (step1338 p h) (sat_cons (step1340 p h) (sat_cons (step1336 p h) (sat_cons (step1333 p h) (sat_cons (step2466 p h) (sat_cons (step2436 p h) (sat_cons (step2279 p h) (sat_cons (step2457 p h) (sat_cons (step1498 p h) (sat_cons (step2267 p h) (sat_cons (step2032 p h) (sat_cons (step531 p h) (sat_cons (step529 p h) (sat_cons (step1388 p h) (sat_nil p))))))))))))))))))))))))
def c2479 : List Lit := [(1707, true), (1659, true), (66, false), (27, false), (1635, false), (35, false), (52, true)]
theorem step2479 (p : Nat → Bool) (h : Constraints p) : clause p c2479 = true :=
  Snake9.LocalRup.prove_clause [c1280, c1281, c318, c2369] c2479 (by decide) p (sat_cons (step1280 p h) (sat_cons (step1281 p h) (sat_cons (step318 p h) (sat_cons (step2369 p h) (sat_nil p)))))
def c2480 : List Lit := [(1641, false), (39, true), (1671, true), (58, false), (37, true), (34, true)]
theorem step2480 (p : Nat → Bool) (h : Constraints p) : clause p c2480 = true :=
  Snake9.LocalRup.prove_clause [c1108, c2475, c1224, c1995, c1201, c1230, c2373, c2443, c1109] c2480 (by decide) p (sat_cons (step1108 p h) (sat_cons (step2475 p h) (sat_cons (step1224 p h) (sat_cons (step1995 p h) (sat_cons (step1201 p h) (sat_cons (step1230 p h) (sat_cons (step2373 p h) (sat_cons (step2443 p h) (sat_cons (step1109 p h) (sat_nil p))))))))))
def c2481 : List Lit := [(1670, true), (39, true), (58, false), (37, true), (34, true), (1640, false)]
theorem step2481 (p : Nat → Bool) (h : Constraints p) : clause p c2481 = true :=
  Snake9.LocalRup.prove_clause [c1108, c2475, c1994, c1229, c1223, c2443, c1197, c1109, c2373] c2481 (by decide) p (sat_cons (step1108 p h) (sat_cons (step2475 p h) (sat_cons (step1994 p h) (sat_cons (step1229 p h) (sat_cons (step1223 p h) (sat_cons (step2443 p h) (sat_cons (step1197 p h) (sat_cons (step1109 p h) (sat_cons (step2373 p h) (sat_nil p))))))))))
def c2482 : List Lit := [(1624, false), (1611, false), (1671, true), (58, false), (37, true), (1640, false)]
theorem step2482 (p : Nat → Bool) (h : Constraints p) : clause p c2482 = true :=
  Snake9.LocalRup.prove_clause [c1108, c1113, c1994, c1235, c1143, c1147, c1230, c1114, c1197, c1109, c2373] c2482 (by decide) p (sat_cons (step1108 p h) (sat_cons (step1113 p h) (sat_cons (step1994 p h) (sat_cons (step1235 p h) (sat_cons (step1143 p h) (sat_cons (step1147 p h) (sat_cons (step1230 p h) (sat_cons (step1114 p h) (sat_cons (step1197 p h) (sat_cons (step1109 p h) (sat_cons (step2373 p h) (sat_nil p))))))))))))
def c2483 : List Lit := [(1601, true), (1550, false)]
theorem step2483 (p : Nat → Bool) (h : Constraints p) : clause p c2483 = true :=
  Snake9.LocalRup.prove_clause [c1003, c1033, c1989, c1083, c1037, c1716, c1006, c997] c2483 (by decide) p (sat_cons (step1003 p h) (sat_cons (step1033 p h) (sat_cons (step1989 p h) (sat_cons (step1083 p h) (sat_cons (step1037 p h) (sat_cons (step1716 p h) (sat_cons (step1006 p h) (sat_cons (step997 p h) (sat_nil p)))))))))
def c2484 : List Lit := [(1565, true), (2, true), (8, false), (1549, false)]
theorem step2484 (p : Nat → Bool) (h : Constraints p) : clause p c2484 = true :=
  Snake9.LocalRup.prove_clause [c997, c1005, c1037, c1034, c1008, c1018, c998, c1011, c2055, c2412, c1796] c2484 (by decide) p (sat_cons (step997 p h) (sat_cons (step1005 p h) (sat_cons (step1037 p h) (sat_cons (step1034 p h) (sat_cons (step1008 p h) (sat_cons (step1018 p h) (sat_cons (step998 p h) (sat_cons (step1011 p h) (sat_cons (step2055 p h) (sat_cons (step2412 p h) (sat_cons (step1796 p h) (sat_nil p))))))))))))
def c2485 : List Lit := [(1555, true), (4, false), (8, false)]
theorem step2485 (p : Nat → Bool) (h : Constraints p) : clause p c2485 = true :=
  Snake9.LocalRup.prove_clause [c1011, c2055, c2412, c1796] c2485 (by decide) p (sat_cons (step1011 p h) (sat_cons (step2055 p h) (sat_cons (step2412 p h) (sat_cons (step1796 p h) (sat_nil p)))))
def c2486 : List Lit := [(32, true), (1619, false), (38, false), (101, false), (1629, true), (1612, true), (52, false)]
theorem step2486 (p : Nat → Bool) (h : Constraints p) : clause p c2486 = true :=
  Snake9.LocalRup.prove_clause [c1105, c1106, c1112, c139, c1138, c2434, c1127] c2486 (by decide) p (sat_cons (step1105 p h) (sat_cons (step1106 p h) (sat_cons (step1112 p h) (sat_cons (step139 p h) (sat_cons (step1138 p h) (sat_cons (step2434 p h) (sat_cons (step1127 p h) (sat_nil p))))))))
def c2487 : List Lit := [(39, true), (38, false), (37, false), (101, false), (1629, true), (1612, true), (52, false)]
theorem step2487 (p : Nat → Bool) (h : Constraints p) : clause p c2487 = true :=
  Snake9.LocalRup.prove_clause [c1134, c1119, c1128, c2486, c136, c2455, c99, c2434, c1130, c1120, c2451, c188, c1841] c2487 (by decide) p (sat_cons (step1134 p h) (sat_cons (step1119 p h) (sat_cons (step1128 p h) (sat_cons (step2486 p h) (sat_cons (step136 p h) (sat_cons (step2455 p h) (sat_cons (step99 p h) (sat_cons (step2434 p h) (sat_cons (step1130 p h) (sat_cons (step1120 p h) (sat_cons (step2451 p h) (sat_cons (step188 p h) (sat_cons (step1841 p h) (sat_nil p))))))))))))))
def c2488 : List Lit := [(38, true), (101, false), (1629, true), (1616, true), (52, false)]
theorem step2488 (p : Nat → Bool) (h : Constraints p) : clause p c2488 = true :=
  Snake9.LocalRup.prove_clause [c1111, c1107, c1109, c1110, c1113, c1138, c1104, c1105, c1125, c99, c134, c2434, c1127, c1118, c2451, c188, c1841] c2488 (by decide) p (sat_cons (step1111 p h) (sat_cons (step1107 p h) (sat_cons (step1109 p h) (sat_cons (step1110 p h) (sat_cons (step1113 p h) (sat_cons (step1138 p h) (sat_cons (step1104 p h) (sat_cons (step1105 p h) (sat_cons (step1125 p h) (sat_cons (step99 p h) (sat_cons (step134 p h) (sat_cons (step2434 p h) (sat_cons (step1127 p h) (sat_cons (step1118 p h) (sat_cons (step2451 p h) (sat_cons (step188 p h) (sat_cons (step1841 p h) (sat_nil p))))))))))))))))))
def c2489 : List Lit := [(1624, true), (1621, false), (31, true), (33, false), (32, false), (101, false)]
theorem step2489 (p : Nat → Bool) (h : Constraints p) : clause p c2489 = true :=
  Snake9.LocalRup.prove_clause [c1125, c1127, c1118, c2451, c188, c1841] c2489 (by decide) p (sat_cons (step1125 p h) (sat_cons (step1127 p h) (sat_cons (step1118 p h) (sat_cons (step2451 p h) (sat_cons (step188 p h) (sat_cons (step1841 p h) (sat_nil p)))))))
def c2490 : List Lit := [(1818, true), (105, false), (1800, false), (112, true), (1773, true)]
theorem step2490 (p : Nat → Bool) (h : Constraints p) : clause p c2490 = true :=
  Snake9.LocalRup.prove_clause [c1389, c1724, c1390, c1487, c1483, c2079, c1784] c2490 (by decide) p (sat_cons (step1389 p h) (sat_cons (step1724 p h) (sat_cons (step1390 p h) (sat_cons (step1487 p h) (sat_cons (step1483 p h) (sat_cons (step2079 p h) (sat_cons (step1784 p h) (sat_nil p))))))))
def c2491 : List Lit := [(1564, true), (2, true)]
theorem step2491 (p : Nat → Bool) (h : Constraints p) : clause p c2491 = true :=
  Snake9.LocalRup.prove_clause [c997, c1004, c1033, c1029, c1007, c1005, c1018, c998, c999, c2485] c2491 (by decide) p (sat_cons (step997 p h) (sat_cons (step1004 p h) (sat_cons (step1033 p h) (sat_cons (step1029 p h) (sat_cons (step1007 p h) (sat_cons (step1005 p h) (sat_cons (step1018 p h) (sat_cons (step998 p h) (sat_cons (step999 p h) (sat_cons (step2485 p h) (sat_nil p)))))))))))
def c2492 : List Lit := [(1818, true), (1796, false), (1800, false), (1773, true)]
theorem step2492 (p : Nat → Bool) (h : Constraints p) : clause p c2492 = true :=
  Snake9.LocalRup.prove_clause [c1389, c1724, c1390, c1487, c1483, c1450, c1784, c1728] c2492 (by decide) p (sat_cons (step1389 p h) (sat_cons (step1724 p h) (sat_cons (step1390 p h) (sat_cons (step1487 p h) (sat_cons (step1483 p h) (sat_cons (step1450 p h) (sat_cons (step1784 p h) (sat_cons (step1728 p h) (sat_nil p)))))))))
def c2493 : List Lit := [(1771, true), (37, false), (100, false)]
theorem step2493 (p : Nat → Bool) (h : Constraints p) : clause p c2493 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1387, c2113, c571] c2493 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step2113 p h) (sat_cons (step571 p h) (sat_nil p)))))
def c2494 : List Lit := [(116, false), (112, false), (118, false), (1798, true)]
theorem step2494 (p : Nat → Bool) (h : Constraints p) : clause p c2494 = true :=
  Snake9.LocalRup.prove_clause [c712, c711, c1443] c2494 (by decide) p (sat_cons (step712 p h) (sat_cons (step711 p h) (sat_cons (step1443 p h) (sat_nil p))))
def c2495 : List Lit := [(1785, true), (103, true), (110, true), (94, true), (106, true), (101, false)]
theorem step2495 (p : Nat → Bool) (h : Constraints p) : clause p c2495 = true :=
  Snake9.LocalRup.prove_clause [c1401, c1404, c1412, c1410, c1402, c1405, c624, c1928] c2495 (by decide) p (sat_cons (step1401 p h) (sat_cons (step1404 p h) (sat_cons (step1412 p h) (sat_cons (step1410 p h) (sat_cons (step1402 p h) (sat_cons (step1405 p h) (sat_cons (step624 p h) (sat_cons (step1928 p h) (sat_nil p)))))))))
def c2496 : List Lit := [(105, false), (110, true), (94, true), (101, false)]
theorem step2496 (p : Nat → Bool) (h : Constraints p) : clause p c2496 = true :=
  Snake9.LocalRup.prove_clause [c1928, c1927, c1638] c2496 (by decide) p (sat_cons (step1928 p h) (sat_cons (step1927 p h) (sat_cons (step1638 p h) (sat_nil p))))
def c2497 : List Lit := [(112, false), (115, false), (95, false), (120, true), (89, true)]
theorem step2497 (p : Nat → Bool) (h : Constraints p) : clause p c2497 = true :=
  Snake9.LocalRup.prove_clause [c1939, c1940, c700] c2497 (by decide) p (sat_cons (step1939 p h) (sat_cons (step1940 p h) (sat_cons (step700 p h) (sat_nil p))))
def c2498 : List Lit := [(1818, true), (112, true), (100, false), (119, false), (101, false)]
theorem step2498 (p : Nat → Bool) (h : Constraints p) : clause p c2498 = true :=
  Snake9.LocalRup.prove_clause [c2094, c1724, c1487, c1483, c1784, c728, c1728, c1440, c1450] c2498 (by decide) p (sat_cons (step2094 p h) (sat_cons (step1724 p h) (sat_cons (step1487 p h) (sat_cons (step1483 p h) (sat_cons (step1784 p h) (sat_cons (step728 p h) (sat_cons (step1728 p h) (sat_cons (step1440 p h) (sat_cons (step1450 p h) (sat_nil p))))))))))
def c2499 : List Lit := [(64, true), (66, true), (58, true), (56, true), (1712, true), (393, true)]
theorem step2499 (p : Nat → Bool) (h : Constraints p) : clause p c2499 = true :=
  Snake9.LocalRup.prove_clause [c1291, c910, c902, c901, c908, c906, c904, c1282, c317, c1750, c1872, c1880, c340] c2499 (by decide) p (sat_cons (step1291 p h) (sat_cons (step910 p h) (sat_cons (step902 p h) (sat_cons (step901 p h) (sat_cons (step908 p h) (sat_cons (step906 p h) (sat_cons (step904 p h) (sat_cons (step1282 p h) (sat_cons (step317 p h) (sat_cons (step1750 p h) (sat_cons (step1872 p h) (sat_cons (step1880 p h) (sat_cons (step340 p h) (sat_nil p))))))))))))))
def c2500 : List Lit := [(56, true), (57, true), (61, true), (1653, true)]
theorem step2500 (p : Nat → Bool) (h : Constraints p) : clause p c2500 = true :=
  Snake9.LocalRup.prove_clause [c1169, c1175, c1186, c1166, c1183, c1176, c1168, c1171, c1742] c2500 (by decide) p (sat_cons (step1169 p h) (sat_cons (step1175 p h) (sat_cons (step1186 p h) (sat_cons (step1166 p h) (sat_cons (step1183 p h) (sat_cons (step1176 p h) (sat_cons (step1168 p h) (sat_cons (step1171 p h) (sat_cons (step1742 p h) (sat_nil p))))))))))
def c2501 : List Lit := [(1600, true)]
theorem step2501 (p : Nat → Bool) (h : Constraints p) : clause p c2501 = true :=
  Snake9.LocalRup.prove_clause [c1988, c2491, c1716, c1078, c1024, c1028, c2444, c1004, c996] c2501 (by decide) p (sat_cons (step1988 p h) (sat_cons (step2491 p h) (sat_cons (step1716 p h) (sat_cons (step1078 p h) (sat_cons (step1024 p h) (sat_cons (step1028 p h) (sat_cons (step2444 p h) (sat_cons (step1004 p h) (sat_cons (step996 p h) (sat_nil p))))))))))
def c2502 : List Lit := [(1652, true), (57, true), (61, true)]
theorem step2502 (p : Nat → Bool) (h : Constraints p) : clause p c2502 = true :=
  Snake9.LocalRup.prove_clause [c1169, c1175, c1179, c1182, c1176, c1167, c1171, c1742] c2502 (by decide) p (sat_cons (step1169 p h) (sat_cons (step1175 p h) (sat_cons (step1179 p h) (sat_cons (step1182 p h) (sat_cons (step1176 p h) (sat_cons (step1167 p h) (sat_cons (step1171 p h) (sat_cons (step1742 p h) (sat_nil p)))))))))
def c2503 : List Lit := [(32, false), (1623, true), (52, false)]
theorem step2503 (p : Nat → Bool) (h : Constraints p) : clause p c2503 = true :=
  Snake9.LocalRup.prove_clause [c1126, c1118, c1124, c1122, c187, c137, c2124] c2503 (by decide) p (sat_cons (step1126 p h) (sat_cons (step1118 p h) (sat_cons (step1124 p h) (sat_cons (step1122 p h) (sat_cons (step187 p h) (sat_cons (step137 p h) (sat_cons (step2124 p h) (sat_nil p))))))))
def c2504 : List Lit := [(1628, true), (58, true), (52, false), (57, false), (1615, false)]
theorem step2504 (p : Nat → Bool) (h : Constraints p) : clause p c2504 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1137, c1115, c1124, c1122, c2503, c1106, c245, c140, c1855] c2504 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1137 p h) (sat_cons (step1115 p h) (sat_cons (step1124 p h) (sat_cons (step1122 p h) (sat_cons (step2503 p h) (sat_cons (step1106 p h) (sat_cons (step245 p h) (sat_cons (step140 p h) (sat_cons (step1855 p h) (sat_nil p)))))))))))
def c2505 : List Lit := [(1635, true), (49, false), (45, false)]
theorem step2505 (p : Nat → Bool) (h : Constraints p) : clause p c2505 = true :=
  Snake9.LocalRup.prove_clause [c1152, c1153, c227] c2505 (by decide) p (sat_cons (step1152 p h) (sat_cons (step1153 p h) (sat_cons (step227 p h) (sat_nil p))))
def c2506 : List Lit := [(1816, true), (1807, false), (119, false), (1810, false)]
theorem step2506 (p : Nat → Bool) (h : Constraints p) : clause p c2506 = true :=
  Snake9.LocalRup.prove_clause [c1477, c2244, c1446, c1438] c2506 (by decide) p (sat_cons (step1477 p h) (sat_cons (step2244 p h) (sat_cons (step1446 p h) (sat_cons (step1438 p h) (sat_nil p)))))
def c2507 : List Lit := [(102, false), (44, false), (105, false), (1774, false), (1791, true), (95, false), (115, false)]
theorem step2507 (p : Nat → Bool) (h : Constraints p) : clause p c2507 = true :=
  Snake9.LocalRup.prove_clause [c2299, c1396, c1430, c1407, c2128, c615, c1434, c1405, c1399, c536, c535, c1388] c2507 (by decide) p (sat_cons (step2299 p h) (sat_cons (step1396 p h) (sat_cons (step1430 p h) (sat_cons (step1407 p h) (sat_cons (step2128 p h) (sat_cons (step615 p h) (sat_cons (step1434 p h) (sat_cons (step1405 p h) (sat_cons (step1399 p h) (sat_cons (step536 p h) (sat_cons (step535 p h) (sat_cons (step1388 p h) (sat_nil p)))))))))))))
def c2508 : List Lit := [(96, false), (1782, true), (95, false), (115, false), (97, false), (117, false)]
theorem step2508 (p : Nat → Bool) (h : Constraints p) : clause p c2508 = true :=
  Snake9.LocalRup.prove_clause [c562, c535, c1405] c2508 (by decide) p (sat_cons (step562 p h) (sat_cons (step535 p h) (sat_cons (step1405 p h) (sat_nil p))))
def c2509 : List Lit := [(1741, true), (102, true), (105, false), (103, false)]
theorem step2509 (p : Nat → Bool) (h : Constraints p) : clause p c2509 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1335, c635, c493, c1929] c2509 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step635 p h) (sat_cons (step493 p h) (sat_cons (step1929 p h) (sat_nil p))))))
def c2510 : List Lit := [(1658, true), (63, false), (56, true), (1635, false)]
theorem step2510 (p : Nat → Bool) (h : Constraints p) : clause p c2510 = true :=
  Snake9.LocalRup.prove_clause [c1873, c2019, c1160, c1193, c1197, c2271, c1161, c302, c1155] c2510 (by decide) p (sat_cons (step1873 p h) (sat_cons (step2019 p h) (sat_cons (step1160 p h) (sat_cons (step1193 p h) (sat_cons (step1197 p h) (sat_cons (step2271 p h) (sat_cons (step1161 p h) (sat_cons (step302 p h) (sat_cons (step1155 p h) (sat_nil p))))))))))
def c2511 : List Lit := [(1796, false), (1725, false), (1790, false), (114, true), (1741, false), (1807, false), (1735, false), (1853, true)]
theorem step2511 (p : Nat → Bool) (h : Constraints p) : clause p c2511 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1337, c1346, c1367, c1557, c1514, c1487, c1449, c1450, c1482, c1483, c1442, c1513, c1467, c1564, c1453, c1368, c1770, c2268, c1347, c1624, c1340, c1333] c2511 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1337 p h) (sat_cons (step1346 p h) (sat_cons (step1367 p h) (sat_cons (step1557 p h) (sat_cons (step1514 p h) (sat_cons (step1487 p h) (sat_cons (step1449 p h) (sat_cons (step1450 p h) (sat_cons (step1482 p h) (sat_cons (step1483 p h) (sat_cons (step1442 p h) (sat_cons (step1513 p h) (sat_cons (step1467 p h) (sat_cons (step1564 p h) (sat_cons (step1453 p h) (sat_cons (step1368 p h) (sat_cons (step1770 p h) (sat_cons (step2268 p h) (sat_cons (step1347 p h) (sat_cons (step1624 p h) (sat_cons (step1340 p h) (sat_cons (step1333 p h) (sat_nil p))))))))))))))))))))))))
def c2512 : List Lit := [(1735, true), (122, false), (105, false)]
theorem step2512 (p : Nat → Bool) (h : Constraints p) : clause p c2512 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1702, c1323, c622] c2512 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1702 p h) (sat_cons (step1323 p h) (sat_cons (step622 p h) (sat_nil p)))))
def c2513 : List Lit := [(89, true), (88, false), (1735, false), (1779, true), (1758, true), (91, true)]
theorem step2513 (p : Nat → Bool) (h : Constraints p) : clause p c2513 = true :=
  Snake9.LocalRup.prove_clause [c2132, c1361, c1346, c1337, c1334, c1335, c1739] c2513 (by decide) p (sat_cons (step2132 p h) (sat_cons (step1361 p h) (sat_cons (step1346 p h) (sat_cons (step1337 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step1739 p h) (sat_nil p))))))))
def c2514 : List Lit := [(88, false), (1735, false), (1779, true), (1758, true), (112, false), (91, true)]
theorem step2514 (p : Nat → Bool) (h : Constraints p) : clause p c2514 = true :=
  Snake9.LocalRup.prove_clause [c2513, c442, c437, c1335, c1283, c1337, c1286, c1346, c2003, c1361] c2514 (by decide) p (sat_cons (step2513 p h) (sat_cons (step442 p h) (sat_cons (step437 p h) (sat_cons (step1335 p h) (sat_cons (step1283 p h) (sat_cons (step1337 p h) (sat_cons (step1286 p h) (sat_cons (step1346 p h) (sat_cons (step2003 p h) (sat_cons (step1361 p h) (sat_nil p)))))))))))
def c2515 : List Lit := [(1736, true), (80, true), (81, false), (103, false)]
theorem step2515 (p : Nat → Bool) (h : Constraints p) : clause p c2515 = true :=
  Snake9.LocalRup.prove_clause [c1323, c1332, c1331, c1324, c1325, c391] c2515 (by decide) p (sat_cons (step1323 p h) (sat_cons (step1332 p h) (sat_cons (step1331 p h) (sat_cons (step1324 p h) (sat_cons (step1325 p h) (sat_cons (step391 p h) (sat_nil p)))))))
def c2516 : List Lit := [(46, false), (64, false), (47, false), (38, true), (1631, true), (1621, false), (1611, false)]
theorem step2516 (p : Nat → Bool) (h : Constraints p) : clause p c2516 = true :=
  Snake9.LocalRup.prove_clause [c211, c214, c1109, c1118, c1114, c1127, c1147] c2516 (by decide) p (sat_cons (step211 p h) (sat_cons (step214 p h) (sat_cons (step1109 p h) (sat_cons (step1118 p h) (sat_cons (step1114 p h) (sat_cons (step1127 p h) (sat_cons (step1147 p h) (sat_nil p))))))))
def c2517 : List Lit := [(1635, false), (1629, false), (1692, true)]
theorem step2517 (p : Nat → Bool) (h : Constraints p) : clause p c2517 = true :=
  Snake9.LocalRup.prove_clause [c2501, c1247, c1222, c1994, c1160, c1161, c1993, c1156, c1221, c2099, c1253] c2517 (by decide) p (sat_cons (step2501 p h) (sat_cons (step1247 p h) (sat_cons (step1222 p h) (sat_cons (step1994 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1993 p h) (sat_cons (step1156 p h) (sat_cons (step1221 p h) (sat_cons (step2099 p h) (sat_cons (step1253 p h) (sat_nil p))))))))))))
def c2518 : List Lit := [(39, false), (1635, true), (38, false)]
theorem step2518 (p : Nat → Bool) (h : Constraints p) : clause p c2518 = true :=
  Snake9.LocalRup.prove_clause [c1152, c2104, c174, c1835] c2518 (by decide) p (sat_cons (step1152 p h) (sat_cons (step2104 p h) (sat_cons (step174 p h) (sat_cons (step1835 p h) (sat_nil p)))))
def c2519 : List Lit := [(1613, false), (1619, false), (47, false), (50, false), (1631, true), (44, true), (32, true)]
theorem step2519 (p : Nat → Bool) (h : Constraints p) : clause p c2519 = true :=
  Snake9.LocalRup.prove_clause [c1122, c1127, c1147, c1105, c1113, c1144, c1128, c1123, c1116, c2338, c1106] c2519 (by decide) p (sat_cons (step1122 p h) (sat_cons (step1127 p h) (sat_cons (step1147 p h) (sat_cons (step1105 p h) (sat_cons (step1113 p h) (sat_cons (step1144 p h) (sat_cons (step1128 p h) (sat_cons (step1123 p h) (sat_cons (step1116 p h) (sat_cons (step2338 p h) (sat_cons (step1106 p h) (sat_nil p))))))))))))
def c2520 : List Lit := [(1713, true), (64, true), (50, false), (70, true)]
theorem step2520 (p : Nat → Bool) (h : Constraints p) : clause p c2520 = true :=
  Snake9.LocalRup.prove_clause [c1280, c1283, c1292, c1282, c1290, c1872, c337, c1285] c2520 (by decide) p (sat_cons (step1280 p h) (sat_cons (step1283 p h) (sat_cons (step1292 p h) (sat_cons (step1282 p h) (sat_cons (step1290 p h) (sat_cons (step1872 p h) (sat_cons (step337 p h) (sat_cons (step1285 p h) (sat_nil p)))))))))
def c2521 : List Lit := [(37, true), (34, false), (1614, true), (1631, true), (1619, false), (52, false), (32, true), (1635, true)]
theorem step2521 (p : Nat → Bool) (h : Constraints p) : clause p c2521 = true :=
  Snake9.LocalRup.prove_clause [c1153, c1152, c1108, c1109, c2519, c141] c2521 (by decide) p (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step1108 p h) (sat_cons (step1109 p h) (sat_cons (step2519 p h) (sat_cons (step141 p h) (sat_nil p)))))))
def c2522 : List Lit := [(1656, true), (32, true), (1635, true), (1749, false), (35, false), (92, false), (1693, true), (1832, false)]
theorem step2522 (p : Nat → Bool) (h : Constraints p) : clause p c2522 = true :=
  Snake9.LocalRup.prove_clause [c1105, c1112, c1153, c1152, c2331, c1686, c1188, c1681, c1993, c2019, c2027, c2120, c2003, c1158, c1362, c1155, c1156, c1558, c151, c2028, c2099, c283, c2013, c1119, c1170, c1254, c1253, c1172, c2001, c2000, c1181, c1139, c1146, c1167, c1114, c247, c1855, c2521, c208, c1120, c1129, c1130, c2105, c1122, c1107, c141] c2522 (by decide) p (sat_cons (step1105 p h) (sat_cons (step1112 p h) (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step2331 p h) (sat_cons (step1686 p h) (sat_cons (step1188 p h) (sat_cons (step1681 p h) (sat_cons (step1993 p h) (sat_cons (step2019 p h) (sat_cons (step2027 p h) (sat_cons (step2120 p h) (sat_cons (step2003 p h) (sat_cons (step1158 p h) (sat_cons (step1362 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1558 p h) (sat_cons (step151 p h) (sat_cons (step2028 p h) (sat_cons (step2099 p h) (sat_cons (step283 p h) (sat_cons (step2013 p h) (sat_cons (step1119 p h) (sat_cons (step1170 p h) (sat_cons (step1254 p h) (sat_cons (step1253 p h) (sat_cons (step1172 p h) (sat_cons (step2001 p h) (sat_cons (step2000 p h) (sat_cons (step1181 p h) (sat_cons (step1139 p h) (sat_cons (step1146 p h) (sat_cons (step1167 p h) (sat_cons (step1114 p h) (sat_cons (step247 p h) (sat_cons (step1855 p h) (sat_cons (step2521 p h) (sat_cons (step208 p h) (sat_cons (step1120 p h) (sat_cons (step1129 p h) (sat_cons (step1130 p h) (sat_cons (step2105 p h) (sat_cons (step1122 p h) (sat_cons (step1107 p h) (sat_cons (step141 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c2523 : List Lit := [(1601, false), (1656, false), (1611, false), (1635, true), (1749, false), (1693, true), (1832, false)]
theorem step2523 (p : Nat → Bool) (h : Constraints p) : clause p c2523 = true :=
  Snake9.LocalRup.prove_clause [c1686, c1112, c1137, c1215, c1153, c1152, c2331, c1254, c1252, c1228, c2012, c1146, c1566, c1114, c1368, c2004, c1750, c211, c214, c1108, c1109, c1113, c2518, c1143, c1120, c1129] c2523 (by decide) p (sat_cons (step1686 p h) (sat_cons (step1112 p h) (sat_cons (step1137 p h) (sat_cons (step1215 p h) (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step2331 p h) (sat_cons (step1254 p h) (sat_cons (step1252 p h) (sat_cons (step1228 p h) (sat_cons (step2012 p h) (sat_cons (step1146 p h) (sat_cons (step1566 p h) (sat_cons (step1114 p h) (sat_cons (step1368 p h) (sat_cons (step2004 p h) (sat_cons (step1750 p h) (sat_cons (step211 p h) (sat_cons (step214 p h) (sat_cons (step1108 p h) (sat_cons (step1109 p h) (sat_cons (step1113 p h) (sat_cons (step2518 p h) (sat_cons (step1143 p h) (sat_cons (step1120 p h) (sat_cons (step1129 p h) (sat_nil p)))))))))))))))))))))))))))
def c2524 : List Lit := [(1613, false), (1619, false), (1630, true), (32, true), (1635, true)]
theorem step2524 (p : Nat → Bool) (h : Constraints p) : clause p c2524 = true :=
  Snake9.LocalRup.prove_clause [c1686, c1146, c1105, c1153, c1152, c1113, c1116, c1143, c1106, c1127, c2338, c1121] c2524 (by decide) p (sat_cons (step1686 p h) (sat_cons (step1146 p h) (sat_cons (step1105 p h) (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step1113 p h) (sat_cons (step1116 p h) (sat_cons (step1143 p h) (sat_cons (step1106 p h) (sat_cons (step1127 p h) (sat_cons (step2338 p h) (sat_cons (step1121 p h) (sat_nil p)))))))))))))
def c2525 : List Lit := [(1620, false), (1630, true), (32, true), (1635, true)]
theorem step2525 (p : Nat → Bool) (h : Constraints p) : clause p c2525 = true :=
  Snake9.LocalRup.prove_clause [c1105, c1112, c1139, c1153, c1152, c1129, c1130, c1143, c1121, c1115, c2338, c1106] c2525 (by decide) p (sat_cons (step1105 p h) (sat_cons (step1112 p h) (sat_cons (step1139 p h) (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step1129 p h) (sat_cons (step1130 p h) (sat_cons (step1143 p h) (sat_cons (step1121 p h) (sat_cons (step1115 p h) (sat_cons (step2338 p h) (sat_cons (step1106 p h) (sat_nil p)))))))))))))
def c2526 : List Lit := [(39, true), (1630, true), (32, true), (1635, true)]
theorem step2526 (p : Nat → Bool) (h : Constraints p) : clause p c2526 = true :=
  Snake9.LocalRup.prove_clause [c2525, c1153, c1152, c2331, c1119, c1120, c2524, c208, c1108] c2526 (by decide) p (sat_cons (step2525 p h) (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step2331 p h) (sat_cons (step1119 p h) (sat_cons (step1120 p h) (sat_cons (step2524 p h) (sat_cons (step208 p h) (sat_cons (step1108 p h) (sat_nil p))))))))))
def c2527 : List Lit := [(39, false), (1601, true), (1635, true), (35, false), (92, false)]
theorem step2527 (p : Nat → Bool) (h : Constraints p) : clause p c2527 = true :=
  Snake9.LocalRup.prove_clause [c1153, c1152, c2104, c146, c1849, c2335, c226] c2527 (by decide) p (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step2104 p h) (sat_cons (step146 p h) (sat_cons (step1849 p h) (sat_cons (step2335 p h) (sat_cons (step226 p h) (sat_nil p))))))))
def c2528 : List Lit := [(32, true), (1635, true), (1749, false), (35, false), (92, false), (1693, true), (1832, false)]
theorem step2528 (p : Nat → Bool) (h : Constraints p) : clause p c2528 = true :=
  Snake9.LocalRup.prove_clause [c2501, c1248, c1105, c2522, c2523, c2099, c2527, c2526, c1229, c1228, c2040, c1247, c1281, c2013, c1288, c1558, c2003, c1362] c2528 (by decide) p (sat_cons (step2501 p h) (sat_cons (step1248 p h) (sat_cons (step1105 p h) (sat_cons (step2522 p h) (sat_cons (step2523 p h) (sat_cons (step2099 p h) (sat_cons (step2527 p h) (sat_cons (step2526 p h) (sat_cons (step1229 p h) (sat_cons (step1228 p h) (sat_cons (step2040 p h) (sat_cons (step1247 p h) (sat_cons (step1281 p h) (sat_cons (step2013 p h) (sat_cons (step1288 p h) (sat_cons (step1558 p h) (sat_cons (step2003 p h) (sat_cons (step1362 p h) (sat_nil p)))))))))))))))))))
def c2529 : List Lit := [(1630, false), (54, true), (1693, true)]
theorem step2529 (p : Nat → Bool) (h : Constraints p) : clause p c2529 = true :=
  Snake9.LocalRup.prove_clause [c2501, c1155, c1158, c1993, c1248, c1229, c1228, c1994, c1254, c1159, c2099, c1157] c2529 (by decide) p (sat_cons (step2501 p h) (sat_cons (step1155 p h) (sat_cons (step1158 p h) (sat_cons (step1993 p h) (sat_cons (step1248 p h) (sat_cons (step1229 p h) (sat_cons (step1228 p h) (sat_cons (step1994 p h) (sat_cons (step1254 p h) (sat_cons (step1159 p h) (sat_cons (step2099 p h) (sat_cons (step1157 p h) (sat_nil p)))))))))))))
def c2530 : List Lit := [(1601, true), (4, true), (50, false)]
theorem step2530 (p : Nat → Bool) (h : Constraints p) : clause p c2530 = true :=
  Snake9.LocalRup.prove_clause [c996, c1989, c2037, c2335, c1037, c1018, c1011, c1734, c1008, c1005, c998, c1033, c1716, c1083] c2530 (by decide) p (sat_cons (step996 p h) (sat_cons (step1989 p h) (sat_cons (step2037 p h) (sat_cons (step2335 p h) (sat_cons (step1037 p h) (sat_cons (step1018 p h) (sat_cons (step1011 p h) (sat_cons (step1734 p h) (sat_cons (step1008 p h) (sat_cons (step1005 p h) (sat_cons (step998 p h) (sat_cons (step1033 p h) (sat_cons (step1716 p h) (sat_cons (step1083 p h) (sat_nil p)))))))))))))))
def c2531 : List Lit := [(1635, true), (1749, false), (35, false), (92, false), (1693, true), (1832, false)]
theorem step2531 (p : Nat → Bool) (h : Constraints p) : clause p c2531 = true :=
  Snake9.LocalRup.prove_clause [c1152, c1153, c2331, c2528, c150, c149, c144, c1155, c1119, c1158, c1993, c2529, c2530, c2523, c1104, c2338, c1121, c1127, c1133, c1215, c1252, c2012, c1566, c1368, c2004, c1750, c211, c214, c1108, c1120, c1110, c2105] c2531 (by decide) p (sat_cons (step1152 p h) (sat_cons (step1153 p h) (sat_cons (step2331 p h) (sat_cons (step2528 p h) (sat_cons (step150 p h) (sat_cons (step149 p h) (sat_cons (step144 p h) (sat_cons (step1155 p h) (sat_cons (step1119 p h) (sat_cons (step1158 p h) (sat_cons (step1993 p h) (sat_cons (step2529 p h) (sat_cons (step2530 p h) (sat_cons (step2523 p h) (sat_cons (step1104 p h) (sat_cons (step2338 p h) (sat_cons (step1121 p h) (sat_cons (step1127 p h) (sat_cons (step1133 p h) (sat_cons (step1215 p h) (sat_cons (step1252 p h) (sat_cons (step2012 p h) (sat_cons (step1566 p h) (sat_cons (step1368 p h) (sat_cons (step2004 p h) (sat_cons (step1750 p h) (sat_cons (step211 p h) (sat_cons (step214 p h) (sat_cons (step1108 p h) (sat_cons (step1120 p h) (sat_cons (step1110 p h) (sat_cons (step2105 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c2532 : List Lit := [(1621, true), (33, false), (32, false), (122, false), (105, false)]
theorem step2532 (p : Nat → Bool) (h : Constraints p) : clause p c2532 = true :=
  Snake9.LocalRup.prove_clause [c1121, c1122, c196, c616, c133, c1843] c2532 (by decide) p (sat_cons (step1121 p h) (sat_cons (step1122 p h) (sat_cons (step196 p h) (sat_cons (step616 p h) (sat_cons (step133 p h) (sat_cons (step1843 p h) (sat_nil p)))))))
def c2533 : List Lit := [(33, true), (1629, true), (39, true), (32, false), (35, false)]
theorem step2533 (p : Nat → Bool) (h : Constraints p) : clause p c2533 = true :=
  Snake9.LocalRup.prove_clause [c1104, c2455, c1112, c110, c112, c1138, c1712] c2533 (by decide) p (sat_cons (step1104 p h) (sat_cons (step2455 p h) (sat_cons (step1112 p h) (sat_cons (step110 p h) (sat_cons (step112 p h) (sat_cons (step1138 p h) (sat_cons (step1712 p h) (sat_nil p))))))))
def c2534 : List Lit := [(32, true), (1628, true), (122, false), (105, false)]
theorem step2534 (p : Nat → Bool) (h : Constraints p) : clause p c2534 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1115, c1105, c1106, c1112, c1113, c1137, c1107, c1124, c1121, c1122, c196, c616, c138, c1843] c2534 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1115 p h) (sat_cons (step1105 p h) (sat_cons (step1106 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step1137 p h) (sat_cons (step1107 p h) (sat_cons (step1124 p h) (sat_cons (step1121 p h) (sat_cons (step1122 p h) (sat_cons (step196 p h) (sat_cons (step616 p h) (sat_cons (step138 p h) (sat_cons (step1843 p h) (sat_nil p))))))))))))))))
def c2535 : List Lit := [(1611, false), (32, false), (1628, true)]
theorem step2535 (p : Nat → Bool) (h : Constraints p) : clause p c2535 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1112, c1113, c1137, c1108, c1126, c2107, c1118, c102] c2535 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step1137 p h) (sat_cons (step1108 p h) (sat_cons (step1126 p h) (sat_cons (step2107 p h) (sat_cons (step1118 p h) (sat_cons (step102 p h) (sat_nil p))))))))))
def c2536 : List Lit := [(46, false), (1708, true), (52, true), (50, true), (41, false), (37, false), (1659, true)]
theorem step2536 (p : Nat → Bool) (h : Constraints p) : clause p c2536 = true :=
  Snake9.LocalRup.prove_clause [c209, c208, c1282, c1154, c2414] c2536 (by decide) p (sat_cons (step209 p h) (sat_cons (step208 p h) (sat_cons (step1282 p h) (sat_cons (step1154 p h) (sat_cons (step2414 p h) (sat_nil p))))))
def c2537 : List Lit := [(44, true), (1630, true), (1620, false), (1635, true)]
theorem step2537 (p : Nat → Bool) (h : Constraints p) : clause p c2537 = true :=
  Snake9.LocalRup.prove_clause [c1135, c1131, c1153, c1152, c1122, c1123, c1130, c2338, c1139, c1104, c1112] c2537 (by decide) p (sat_cons (step1135 p h) (sat_cons (step1131 p h) (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step1122 p h) (sat_cons (step1123 p h) (sat_cons (step1130 p h) (sat_cons (step2338 p h) (sat_cons (step1139 p h) (sat_cons (step1104 p h) (sat_cons (step1112 p h) (sat_nil p))))))))))))
def c2538 : List Lit := [(1630, true), (1624, false), (39, true), (44, false), (1613, false), (1635, true)]
theorem step2538 (p : Nat → Bool) (h : Constraints p) : clause p c2538 = true :=
  Snake9.LocalRup.prove_clause [c1119, c1110, c1153, c1152, c2526, c1143, c1139, c2105, c1113, c1128, c1120, c1104, c100, c2451, c187, c1841] c2538 (by decide) p (sat_cons (step1119 p h) (sat_cons (step1110 p h) (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step2526 p h) (sat_cons (step1143 p h) (sat_cons (step1139 p h) (sat_cons (step2105 p h) (sat_cons (step1113 p h) (sat_cons (step1128 p h) (sat_cons (step1120 p h) (sat_cons (step1104 p h) (sat_cons (step100 p h) (sat_cons (step2451 p h) (sat_cons (step187 p h) (sat_cons (step1841 p h) (sat_nil p)))))))))))))))))
def c2539 : List Lit := [(1631, false), (1693, true)]
theorem step2539 (p : Nat → Bool) (h : Constraints p) : clause p c2539 = true :=
  Snake9.LocalRup.prove_clause [c2501, c1248, c2001, c1234, c1254, c1993, c2099, c1158, c1156] c2539 (by decide) p (sat_cons (step2501 p h) (sat_cons (step1248 p h) (sat_cons (step2001 p h) (sat_cons (step1234 p h) (sat_cons (step1254 p h) (sat_cons (step1993 p h) (sat_cons (step2099 p h) (sat_cons (step1158 p h) (sat_cons (step1156 p h) (sat_nil p))))))))))
def c2540 : List Lit := [(39, false), (110, false), (1635, true)]
theorem step2540 (p : Nat → Bool) (h : Constraints p) : clause p c2540 = true :=
  Snake9.LocalRup.prove_clause [c1153, c1152, c2104, c2020, c1849] c2540 (by decide) p (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step2104 p h) (sat_cons (step2020 p h) (sat_cons (step1849 p h) (sat_nil p))))))
end B112E036
