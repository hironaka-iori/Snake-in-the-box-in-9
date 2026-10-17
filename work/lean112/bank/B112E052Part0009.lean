import B112E052Part0008
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2566 : List Lit := [(35, true), (55, true), (1585, false), (44, false), (1625, true), (1681, true), (122, false), (20, false), (54, true)]
theorem step2566 (p : Nat → Bool) (h : Constraints p) : clause p c2566 = true :=
  Snake9.TreeRup.prove_clause [c2564, c2212, c1044, c1048, c1051, c1055, c1083, c2407, c1132, c1102, c1100, c1096, c1093, c1130, c1127, c1113, c1109, c1108, c2397, c1037, c1036, c1035, c17, c1038, c1033, c1248, c1251, c2037, c1325, c1500, c1390, c1393, c1418, c1347, c1349, c2178, c1374, c1444, c1445, c1367, c1508, c1423, c1419, c2075, c1330, c1396, c1407, c1409, c214, c2039, c1388, c1405, c1401, c1252, c1254, c273, c1250, c1247, c2276, c2205, c216, c5, c2565, c1361, c195, c168, c1359, c2253, c137] c2566 (by decide) p (sat_cons (step2564 p h) (sat_cons (step2212 p h) (sat_cons (step1044 p h) (sat_cons (step1048 p h) (sat_cons (step1051 p h) (sat_cons (step1055 p h) (sat_cons (step1083 p h) (sat_cons (step2407 p h) (sat_cons (step1132 p h) (sat_cons (step1102 p h) (sat_cons (step1100 p h) (sat_cons (step1096 p h) (sat_cons (step1093 p h) (sat_cons (step1130 p h) (sat_cons (step1127 p h) (sat_cons (step1113 p h) (sat_cons (step1109 p h) (sat_cons (step1108 p h) (sat_cons (step2397 p h) (sat_cons (step1037 p h) (sat_cons (step1036 p h) (sat_cons (step1035 p h) (sat_cons (step17 p h) (sat_cons (step1038 p h) (sat_cons (step1033 p h) (sat_cons (step1248 p h) (sat_cons (step1251 p h) (sat_cons (step2037 p h) (sat_cons (step1325 p h) (sat_cons (step1500 p h) (sat_cons (step1390 p h) (sat_cons (step1393 p h) (sat_cons (step1418 p h) (sat_cons (step1347 p h) (sat_cons (step1349 p h) (sat_cons (step2178 p h) (sat_cons (step1374 p h) (sat_cons (step1444 p h) (sat_cons (step1445 p h) (sat_cons (step1367 p h) (sat_cons (step1508 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step2075 p h) (sat_cons (step1330 p h) (sat_cons (step1396 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step214 p h) (sat_cons (step2039 p h) (sat_cons (step1388 p h) (sat_cons (step1405 p h) (sat_cons (step1401 p h) (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step273 p h) (sat_cons (step1250 p h) (sat_cons (step1247 p h) (sat_cons (step2276 p h) (sat_cons (step2205 p h) (sat_cons (step216 p h) (sat_cons (step5 p h) (sat_cons (step2565 p h) (sat_cons (step1361 p h) (sat_cons (step195 p h) (sat_cons (step168 p h) (sat_cons (step1359 p h) (sat_cons (step2253 p h) (sat_cons (step137 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2567 : List Lit := [(44, false), (1625, true), (1681, true), (122, false), (20, false), (1571, false), (54, true), (94, true)]
theorem step2567 (p : Nat → Bool) (h : Constraints p) : clause p c2567 = true :=
  Snake9.LocalRup.prove_clause [c1371, c2563, c2172, c1304, c2564, c2212, c1044, c1048, c1051, c1055, c1083, c2407, c1130, c1127, c1112, c1111, c1110, c248, c2566, c1931, c193, c194, c2538, c2242, c1357, c1361, c135, c1365, c1343, c1374, c1351] c2567 (by decide) p (sat_cons (step1371 p h) (sat_cons (step2563 p h) (sat_cons (step2172 p h) (sat_cons (step1304 p h) (sat_cons (step2564 p h) (sat_cons (step2212 p h) (sat_cons (step1044 p h) (sat_cons (step1048 p h) (sat_cons (step1051 p h) (sat_cons (step1055 p h) (sat_cons (step1083 p h) (sat_cons (step2407 p h) (sat_cons (step1130 p h) (sat_cons (step1127 p h) (sat_cons (step1112 p h) (sat_cons (step1111 p h) (sat_cons (step1110 p h) (sat_cons (step248 p h) (sat_cons (step2566 p h) (sat_cons (step1931 p h) (sat_cons (step193 p h) (sat_cons (step194 p h) (sat_cons (step2538 p h) (sat_cons (step2242 p h) (sat_cons (step1357 p h) (sat_cons (step1361 p h) (sat_cons (step135 p h) (sat_cons (step1365 p h) (sat_cons (step1343 p h) (sat_cons (step1374 p h) (sat_cons (step1351 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2568 : List Lit := [(41, true), (45, false), (42, false), (44, true)]
theorem step2568 (p : Nat → Bool) (h : Constraints p) : clause p c2568 = true :=
  Snake9.LocalRup.prove_clause [c2250, c2248, c1933] c2568 (by decide) p (sat_cons (step2250 p h) (sat_cons (step2248 p h) (sat_cons (step1933 p h) (sat_nil p))))
def c2569 : List Lit := [(38, true), (1611, true)]
theorem step2569 (p : Nat → Bool) (h : Constraints p) : clause p c2569 = true :=
  Snake9.LocalRup.prove_clause [c1351, c1343, c1349, c1346, c2244, c2245, c1930] c2569 (by decide) p (sat_cons (step1351 p h) (sat_cons (step1343 p h) (sat_cons (step1349 p h) (sat_cons (step1346 p h) (sat_cons (step2244 p h) (sat_cons (step2245 p h) (sat_cons (step1930 p h) (sat_nil p))))))))
def c2570 : List Lit := [(47, true), (45, false), (42, false)]
theorem step2570 (p : Nat → Bool) (h : Constraints p) : clause p c2570 = true :=
  Snake9.LocalRup.prove_clause [c2254, c2256, c1933] c2570 (by decide) p (sat_cons (step2254 p h) (sat_cons (step2256 p h) (sat_cons (step1933 p h) (sat_nil p))))
def c2571 : List Lit := [(1572, true), (54, false), (95, false), (87, false)]
theorem step2571 (p : Nat → Bool) (h : Constraints p) : clause p c2571 = true :=
  Snake9.LocalRup.prove_clause [c2099, c2191, c2219, c539] c2571 (by decide) p (sat_cons (step2099 p h) (sat_cons (step2191 p h) (sat_cons (step2219 p h) (sat_cons (step539 p h) (sat_nil p)))))
def c2572 : List Lit := [(1580, true), (44, true), (1577, false), (101, true)]
theorem step2572 (p : Nat → Bool) (h : Constraints p) : clause p c2572 = true :=
  Snake9.LocalRup.prove_clause [c2172, c1294, c2232, c2493] c2572 (by decide) p (sat_cons (step2172 p h) (sat_cons (step1294 p h) (sat_cons (step2232 p h) (sat_cons (step2493 p h) (sat_nil p)))))
def c2573 : List Lit := [(1647, true), (7, false), (101, true), (122, false)]
theorem step2573 (p : Nat → Bool) (h : Constraints p) : clause p c2573 = true :=
  Snake9.LocalRup.prove_clause [c1415, c1418, c1407, c1409, c1395, c1405, c1401, c1387, c273, c371, c2279] c2573 (by decide) p (sat_cons (step1415 p h) (sat_cons (step1418 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1395 p h) (sat_cons (step1405 p h) (sat_cons (step1401 p h) (sat_cons (step1387 p h) (sat_cons (step273 p h) (sat_cons (step371 p h) (sat_cons (step2279 p h) (sat_nil p))))))))))))
def c2574 : List Lit := [(92, false), (54, false), (1573, true), (146, true), (14, true), (20, true), (95, false)]
theorem step2574 (p : Nat → Bool) (h : Constraints p) : clause p c2574 = true :=
  Snake9.LocalRup.prove_clause [c556, c539, c1276, c60, c1281, c2215, c1272] c2574 (by decide) p (sat_cons (step556 p h) (sat_cons (step539 p h) (sat_cons (step1276 p h) (sat_cons (step60 p h) (sat_cons (step1281 p h) (sat_cons (step2215 p h) (sat_cons (step1272 p h) (sat_nil p))))))))
def c2575 : List Lit := [(15, false), (1576, true), (1581, true), (28, true), (14, true)]
theorem step2575 (p : Nat → Bool) (h : Constraints p) : clause p c2575 = true :=
  Snake9.LocalRup.prove_clause [c2214, c2492, c1290, c1295, c1285, c1286, c97] c2575 (by decide) p (sat_cons (step2214 p h) (sat_cons (step2492 p h) (sat_cons (step1290 p h) (sat_cons (step1295 p h) (sat_cons (step1285 p h) (sat_cons (step1286 p h) (sat_cons (step97 p h) (sat_nil p))))))))
def c2576 : List Lit := [(1572, true), (1569, false), (95, false), (87, false)]
theorem step2576 (p : Nat → Bool) (h : Constraints p) : clause p c2576 = true :=
  Snake9.LocalRup.prove_clause [c2099, c1280, c2562, c1271] c2576 (by decide) p (sat_cons (step2099 p h) (sat_cons (step1280 p h) (sat_cons (step2562 p h) (sat_cons (step1271 p h) (sat_nil p)))))
def c2577 : List Lit := [(1573, true), (15, true), (20, true), (95, false), (87, false)]
theorem step2577 (p : Nat → Bool) (h : Constraints p) : clause p c2577 = true :=
  Snake9.LocalRup.prove_clause [c1272, c1274, c1283, c1281, c1273, c1276, c481, c2216, c71] c2577 (by decide) p (sat_cons (step1272 p h) (sat_cons (step1274 p h) (sat_cons (step1283 p h) (sat_cons (step1281 p h) (sat_cons (step1273 p h) (sat_cons (step1276 p h) (sat_cons (step481 p h) (sat_cons (step2216 p h) (sat_cons (step71 p h) (sat_nil p))))))))))
def c2578 : List Lit := [(34, true), (35, false), (122, false)]
theorem step2578 (p : Nat → Bool) (h : Constraints p) : clause p c2578 = true :=
  Snake9.LocalRup.prove_clause [c2243, c2242, c1931] c2578 (by decide) p (sat_cons (step2243 p h) (sat_cons (step2242 p h) (sat_cons (step1931 p h) (sat_nil p))))
def c2579 : List Lit := [(33, false), (1620, true), (35, false), (122, false)]
theorem step2579 (p : Nat → Bool) (h : Constraints p) : clause p c2579 = true :=
  Snake9.LocalRup.prove_clause [c2578, c2530, c135] c2579 (by decide) p (sat_cons (step2578 p h) (sat_cons (step2530 p h) (sat_cons (step135 p h) (sat_nil p))))
def c2580 : List Lit := [(17, false), (18, false), (88, true), (95, false)]
theorem step2580 (p : Nat → Bool) (h : Constraints p) : clause p c2580 = true :=
  Snake9.LocalRup.prove_clause [c2216, c71] c2580 (by decide) p (sat_cons (step2216 p h) (sat_cons (step71 p h) (sat_nil p)))
def c2581 : List Lit := [(1569, true), (54, false), (95, false)]
theorem step2581 (p : Nat → Bool) (h : Constraints p) : clause p c2581 = true :=
  Snake9.LocalRup.prove_clause [c1275, c2171, c539] c2581 (by decide) p (sat_cons (step1275 p h) (sat_cons (step2171 p h) (sat_cons (step539 p h) (sat_nil p))))
def c2582 : List Lit := [(1812, true), (1763, false), (1767, false), (1788, false), (1783, false), (110, true), (113, false), (35, false)]
theorem step2582 (p : Nat → Bool) (h : Constraints p) : clause p c2582 = true :=
  Snake9.LocalRup.prove_clause [c1702, c1708, c1719, c1773, c1812, c1806, c1720, c2526, c1709, c1704] c2582 (by decide) p (sat_cons (step1702 p h) (sat_cons (step1708 p h) (sat_cons (step1719 p h) (sat_cons (step1773 p h) (sat_cons (step1812 p h) (sat_cons (step1806 p h) (sat_cons (step1720 p h) (sat_cons (step2526 p h) (sat_cons (step1709 p h) (sat_cons (step1704 p h) (sat_nil p)))))))))))
def c2583 : List Lit := [(1759, true), (100, false), (101, true), (87, false)]
theorem step2583 (p : Nat → Bool) (h : Constraints p) : clause p c2583 = true :=
  Snake9.LocalRup.prove_clause [c1685, c1686, c634, c522, c2341] c2583 (by decide) p (sat_cons (step1685 p h) (sat_cons (step1686 p h) (sat_cons (step634 p h) (sat_cons (step522 p h) (sat_cons (step2341 p h) (sat_nil p))))))
def c2584 : List Lit := [(106, true), (101, true), (87, false), (100, false)]
theorem step2584 (p : Nat → Bool) (h : Constraints p) : clause p c2584 = true :=
  Snake9.LocalRup.prove_clause [c2339, c2338, c1961] c2584 (by decide) p (sat_cons (step2339 p h) (sat_cons (step2338 p h) (sat_cons (step1961 p h) (sat_nil p))))
def c2585 : List Lit := [(1733, true), (95, true), (90, true), (87, false), (103, false), (108, false)]
theorem step2585 (p : Nat → Bool) (h : Constraints p) : clause p c2585 = true :=
  Snake9.LocalRup.prove_clause [c1599, c1597, c1606, c1608, c1601, c1598, c580, c443, c2327] c2585 (by decide) p (sat_cons (step1599 p h) (sat_cons (step1597 p h) (sat_cons (step1606 p h) (sat_cons (step1608 p h) (sat_cons (step1601 p h) (sat_cons (step1598 p h) (sat_cons (step580 p h) (sat_cons (step443 p h) (sat_cons (step2327 p h) (sat_nil p))))))))))
def c2586 : List Lit := [(20, true), (1572, true), (1730, true), (114, false), (94, false)]
theorem step2586 (p : Nat → Bool) (h : Constraints p) : clause p c2586 = true :=
  Snake9.LocalRup.prove_clause [c1278, c1274, c1276, c1280, c2079, c1272, c2220, c59] c2586 (by decide) p (sat_cons (step1278 p h) (sat_cons (step1274 p h) (sat_cons (step1276 p h) (sat_cons (step1280 p h) (sat_cons (step2079 p h) (sat_cons (step1272 p h) (sat_cons (step2220 p h) (sat_cons (step59 p h) (sat_nil p)))))))))
def c2587 : List Lit := [(56, true), (1649, true), (50, false), (46, true), (86, false)]
theorem step2587 (p : Nat → Bool) (h : Constraints p) : clause p c2587 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1395, c1420, c1412, c1402, c1403, c1409, c217, c1424, c1389, c1398] c2587 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1395 p h) (sat_cons (step1420 p h) (sat_cons (step1412 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step1409 p h) (sat_cons (step217 p h) (sat_cons (step1424 p h) (sat_cons (step1389 p h) (sat_cons (step1398 p h) (sat_nil p))))))))))))
def c2588 : List Lit := [(1649, true), (50, false), (65, false), (96, false), (46, true), (106, true), (86, false)]
theorem step2588 (p : Nat → Bool) (h : Constraints p) : clause p c2588 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1395, c1420, c2587, c265, c2286, c284, c1404, c1407, c1410, c1424, c1401, c1398, c217, c1389] c2588 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1395 p h) (sat_cons (step1420 p h) (sat_cons (step2587 p h) (sat_cons (step265 p h) (sat_cons (step2286 p h) (sat_cons (step284 p h) (sat_cons (step1404 p h) (sat_cons (step1407 p h) (sat_cons (step1410 p h) (sat_cons (step1424 p h) (sat_cons (step1401 p h) (sat_cons (step1398 p h) (sat_cons (step217 p h) (sat_cons (step1389 p h) (sat_nil p))))))))))))))))
def c2589 : List Lit := [(44, false), (122, false), (1626, true), (7, false), (1607, false)]
theorem step2589 (p : Nat → Bool) (h : Constraints p) : clause p c2589 = true :=
  Snake9.LocalRup.prove_clause [c182, c184, c185, c1347, c1357, c1361, c1352, c1365, c1378] c2589 (by decide) p (sat_cons (step182 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step1347 p h) (sat_cons (step1357 p h) (sat_cons (step1361 p h) (sat_cons (step1352 p h) (sat_cons (step1365 p h) (sat_cons (step1378 p h) (sat_nil p))))))))))
def c2590 : List Lit := [(42, true), (1617, false), (1626, true), (3, false), (30, true), (20, false)]
theorem step2590 (p : Nat → Bool) (h : Constraints p) : clause p c2590 = true :=
  Snake9.LocalRup.prove_clause [c1344, c1351, c1375, c1368, c1357, c1359, c1365, c157, c1378, c1354, c1352, c1345, c1346, c150, c2244] c2590 (by decide) p (sat_cons (step1344 p h) (sat_cons (step1351 p h) (sat_cons (step1375 p h) (sat_cons (step1368 p h) (sat_cons (step1357 p h) (sat_cons (step1359 p h) (sat_cons (step1365 p h) (sat_cons (step157 p h) (sat_cons (step1378 p h) (sat_cons (step1354 p h) (sat_cons (step1352 p h) (sat_cons (step1345 p h) (sat_cons (step1346 p h) (sat_cons (step150 p h) (sat_cons (step2244 p h) (sat_nil p))))))))))))))))
def c2591 : List Lit := [(1763, false), (1810, true), (106, true), (1769, false), (122, true)]
theorem step2591 (p : Nat → Bool) (h : Constraints p) : clause p c2591 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1758, c1764, c1804, c1705, c1718, c1719, c1798, c1708, c1765, c1700, c1761, c1759, c1752, c2198] c2591 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1758 p h) (sat_cons (step1764 p h) (sat_cons (step1804 p h) (sat_cons (step1705 p h) (sat_cons (step1718 p h) (sat_cons (step1719 p h) (sat_cons (step1798 p h) (sat_cons (step1708 p h) (sat_cons (step1765 p h) (sat_cons (step1700 p h) (sat_cons (step1761 p h) (sat_cons (step1759 p h) (sat_cons (step1752 p h) (sat_cons (step2198 p h) (sat_nil p))))))))))))))))
def c2592 : List Lit := [(1796, true), (103, false), (106, true), (122, true)]
theorem step2592 (p : Nat → Bool) (h : Constraints p) : clause p c2592 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1761, c1759, c1752, c2198] c2592 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1761 p h) (sat_cons (step1759 p h) (sat_cons (step1752 p h) (sat_cons (step2198 p h) (sat_nil p))))))
def c2593 : List Lit := [(1787, true), (113, false), (35, false)]
theorem step2593 (p : Nat → Bool) (h : Constraints p) : clause p c2593 = true :=
  Snake9.LocalRup.prove_clause [c1742, c1744, c1740, c1737, c835] c2593 (by decide) p (sat_cons (step1742 p h) (sat_cons (step1744 p h) (sat_cons (step1740 p h) (sat_cons (step1737 p h) (sat_cons (step835 p h) (sat_nil p))))))
def c2594 : List Lit := [(1810, true), (106, true), (1787, false), (1769, false), (122, true)]
theorem step2594 (p : Nat → Bool) (h : Constraints p) : clause p c2594 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1758, c1769, c1705, c1713, c1792, c1770, c1798, c2592, c1714, c1700, c1708] c2594 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1758 p h) (sat_cons (step1769 p h) (sat_cons (step1705 p h) (sat_cons (step1713 p h) (sat_cons (step1792 p h) (sat_cons (step1770 p h) (sat_cons (step1798 p h) (sat_cons (step2592 p h) (sat_cons (step1714 p h) (sat_cons (step1700 p h) (sat_cons (step1708 p h) (sat_nil p)))))))))))))
def c2595 : List Lit := [(1586, true), (1578, false), (1569, false), (1580, false), (33, false)]
theorem step2595 (p : Nat → Bool) (h : Constraints p) : clause p c2595 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1305, c1309, c1295, c1280, c1285, c1286, c1272, c33, c2229, c2230, c1926] c2595 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1305 p h) (sat_cons (step1309 p h) (sat_cons (step1295 p h) (sat_cons (step1280 p h) (sat_cons (step1285 p h) (sat_cons (step1286 p h) (sat_cons (step1272 p h) (sat_cons (step33 p h) (sat_cons (step2229 p h) (sat_cons (step2230 p h) (sat_cons (step1926 p h) (sat_nil p)))))))))))))
def c2596 : List Lit := [(15, false), (25, false), (1576, true), (1581, true), (28, true), (33, false)]
theorem step2596 (p : Nat → Bool) (h : Constraints p) : clause p c2596 = true :=
  Snake9.LocalRup.prove_clause [c2575, c33] c2596 (by decide) p (sat_cons (step2575 p h) (sat_cons (step33 p h) (sat_nil p)))
def c2597 : List Lit := [(91, false), (94, false), (85, true)]
theorem step2597 (p : Nat → Bool) (h : Constraints p) : clause p c2597 = true :=
  Snake9.LocalRup.prove_clause [c2328, c2327, c1967] c2597 (by decide) p (sat_cons (step2328 p h) (sat_cons (step2327 p h) (sat_cons (step1967 p h) (sat_nil p))))
def c2598 : List Lit := [(99, false), (100, false), (107, false), (95, false), (87, false)]
theorem step2598 (p : Nat → Bool) (h : Constraints p) : clause p c2598 = true :=
  Snake9.LocalRup.prove_clause [c503, c720, c634, c690, c2334] c2598 (by decide) p (sat_cons (step503 p h) (sat_cons (step720 p h) (sat_cons (step634 p h) (sat_cons (step690 p h) (sat_cons (step2334 p h) (sat_nil p))))))
def c2599 : List Lit := [(1720, true), (1712, true)]
theorem step2599 (p : Nat → Bool) (h : Constraints p) : clause p c2599 = true :=
  Snake9.LocalRup.prove_clause [c2119, c2078, c1535, c1536, c2121, c1550, c2306, c330] c2599 (by decide) p (sat_cons (step2119 p h) (sat_cons (step2078 p h) (sat_cons (step1535 p h) (sat_cons (step1536 p h) (sat_cons (step2121 p h) (sat_cons (step1550 p h) (sat_cons (step2306 p h) (sat_cons (step330 p h) (sat_nil p)))))))))
def c2600 : List Lit := [(1747, true), (1732, false), (90, true)]
theorem step2600 (p : Nat → Bool) (h : Constraints p) : clause p c2600 = true :=
  Snake9.LocalRup.prove_clause [c2453, c2535, c1621, c2168, c1593, c1643, c2599] c2600 (by decide) p (sat_cons (step2453 p h) (sat_cons (step2535 p h) (sat_cons (step1621 p h) (sat_cons (step2168 p h) (sat_cons (step1593 p h) (sat_cons (step1643 p h) (sat_cons (step2599 p h) (sat_nil p))))))))
def c2601 : List Lit := [(79, true), (1712, true)]
theorem step2601 (p : Nat → Bool) (h : Constraints p) : clause p c2601 = true :=
  Snake9.LocalRup.prove_clause [c2078, c1536, c1535, c2121, c1550, c2306, c330] c2601 (by decide) p (sat_cons (step2078 p h) (sat_cons (step1536 p h) (sat_cons (step1535 p h) (sat_cons (step2121 p h) (sat_cons (step1550 p h) (sat_cons (step2306 p h) (sat_cons (step330 p h) (sat_nil p))))))))
def c2602 : List Lit := [(1705, true), (1712, true)]
theorem step2602 (p : Nat → Bool) (h : Constraints p) : clause p c2602 = true :=
  Snake9.LocalRup.prove_clause [c2601, c2078, c1535, c1561, c1557, c1549, c1550, c392, c373, c2058, c1546, c1548, c2212, c1554, c1044, c1565, c1048, c1540, c1051, c1532, c1055, c2122, c1083, c1137, c2421, c1240, c1181, c1183, c1179, c1158, c1167, c1155, c1163, c1149, c1162, c1147, c433, c353, c2309] c2602 (by decide) p (sat_cons (step2601 p h) (sat_cons (step2078 p h) (sat_cons (step1535 p h) (sat_cons (step1561 p h) (sat_cons (step1557 p h) (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step392 p h) (sat_cons (step373 p h) (sat_cons (step2058 p h) (sat_cons (step1546 p h) (sat_cons (step1548 p h) (sat_cons (step2212 p h) (sat_cons (step1554 p h) (sat_cons (step1044 p h) (sat_cons (step1565 p h) (sat_cons (step1048 p h) (sat_cons (step1540 p h) (sat_cons (step1051 p h) (sat_cons (step1532 p h) (sat_cons (step1055 p h) (sat_cons (step2122 p h) (sat_cons (step1083 p h) (sat_cons (step1137 p h) (sat_cons (step2421 p h) (sat_cons (step1240 p h) (sat_cons (step1181 p h) (sat_cons (step1183 p h) (sat_cons (step1179 p h) (sat_cons (step1158 p h) (sat_cons (step1167 p h) (sat_cons (step1155 p h) (sat_cons (step1163 p h) (sat_cons (step1149 p h) (sat_cons (step1162 p h) (sat_cons (step1147 p h) (sat_cons (step433 p h) (sat_cons (step353 p h) (sat_cons (step2309 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c2603 : List Lit := [(1572, true), (1569, false), (88, true), (95, false)]
theorem step2603 (p : Nat → Bool) (h : Constraints p) : clause p c2603 = true :=
  Snake9.LocalRup.prove_clause [c1280, c2099, c1271, c2216] c2603 (by decide) p (sat_cons (step1280 p h) (sat_cons (step2099 p h) (sat_cons (step1271 p h) (sat_cons (step2216 p h) (sat_nil p)))))
def c2604 : List Lit := [(1712, true), (1565, true)]
theorem step2604 (p : Nat → Bool) (h : Constraints p) : clause p c2604 = true :=
  Snake9.LocalRup.prove_clause [c1561, c2078, c2601, c2602, c1553, c1535, c1536, c1552, c1555, c1565, c1546, c1547, c1540, c392, c2061, c372, c1532, c1551, c2212, c2122, c1044, c1048, c1051, c2396, c1055, c2397, c1042, c1083, c1037, c1038, c1041, c1137, c1036, c1032, c2421, c1035, c1031, c1240, c17, c1181, c1179, c1167, c1163, c1162, c433, c2308, c406, c2030, c2210, c11, c2034, c2204, c1270, c1250, c1255, c1247, c349, c2202] c2604 (by decide) p (sat_cons (step1561 p h) (sat_cons (step2078 p h) (sat_cons (step2601 p h) (sat_cons (step2602 p h) (sat_cons (step1553 p h) (sat_cons (step1535 p h) (sat_cons (step1536 p h) (sat_cons (step1552 p h) (sat_cons (step1555 p h) (sat_cons (step1565 p h) (sat_cons (step1546 p h) (sat_cons (step1547 p h) (sat_cons (step1540 p h) (sat_cons (step392 p h) (sat_cons (step2061 p h) (sat_cons (step372 p h) (sat_cons (step1532 p h) (sat_cons (step1551 p h) (sat_cons (step2212 p h) (sat_cons (step2122 p h) (sat_cons (step1044 p h) (sat_cons (step1048 p h) (sat_cons (step1051 p h) (sat_cons (step2396 p h) (sat_cons (step1055 p h) (sat_cons (step2397 p h) (sat_cons (step1042 p h) (sat_cons (step1083 p h) (sat_cons (step1037 p h) (sat_cons (step1038 p h) (sat_cons (step1041 p h) (sat_cons (step1137 p h) (sat_cons (step1036 p h) (sat_cons (step1032 p h) (sat_cons (step2421 p h) (sat_cons (step1035 p h) (sat_cons (step1031 p h) (sat_cons (step1240 p h) (sat_cons (step17 p h) (sat_cons (step1181 p h) (sat_cons (step1179 p h) (sat_cons (step1167 p h) (sat_cons (step1163 p h) (sat_cons (step1162 p h) (sat_cons (step433 p h) (sat_cons (step2308 p h) (sat_cons (step406 p h) (sat_cons (step2030 p h) (sat_cons (step2210 p h) (sat_cons (step11 p h) (sat_cons (step2034 p h) (sat_cons (step2204 p h) (sat_cons (step1270 p h) (sat_cons (step1250 p h) (sat_cons (step1255 p h) (sat_cons (step1247 p h) (sat_cons (step349 p h) (sat_cons (step2202 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2605 : List Lit := [(8, true), (1564, true), (7, true)]
theorem step2605 (p : Nat → Bool) (h : Constraints p) : clause p c2605 = true :=
  Snake9.LocalRup.prove_clause [c2212, c1044, c1048, c1051, c2397, c1037, c1036, c1035, c17, c1038, c1032, c1031, c2030, c11, c2034, c2204, c1269, c1250, c1252] c2605 (by decide) p (sat_cons (step2212 p h) (sat_cons (step1044 p h) (sat_cons (step1048 p h) (sat_cons (step1051 p h) (sat_cons (step2397 p h) (sat_cons (step1037 p h) (sat_cons (step1036 p h) (sat_cons (step1035 p h) (sat_cons (step17 p h) (sat_cons (step1038 p h) (sat_cons (step1032 p h) (sat_cons (step1031 p h) (sat_cons (step2030 p h) (sat_cons (step11 p h) (sat_cons (step2034 p h) (sat_cons (step2204 p h) (sat_cons (step1269 p h) (sat_cons (step1250 p h) (sat_cons (step1252 p h) (sat_nil p))))))))))))))))))))
def c2606 : List Lit := [(53, false), (87, false), (1697, true), (57, true), (68, false), (88, true)]
theorem step2606 (p : Nat → Bool) (h : Constraints p) : clause p c2606 = true :=
  Snake9.LocalRup.prove_clause [c2500, c231, c2263] c2606 (by decide) p (sat_cons (step2500 p h) (sat_cons (step231 p h) (sat_cons (step2263 p h) (sat_nil p))))
def c2607 : List Lit := [(53, false), (56, false), (1697, true), (88, true), (57, true), (68, false)]
theorem step2607 (p : Nat → Bool) (h : Constraints p) : clause p c2607 = true :=
  Snake9.LocalRup.prove_clause [c2500, c229, c2263] c2607 (by decide) p (sat_cons (step2500 p h) (sat_cons (step229 p h) (sat_cons (step2263 p h) (sat_nil p))))
def c2608 : List Lit := [(1812, true), (113, false), (1764, false), (1796, false), (114, true)]
theorem step2608 (p : Nat → Bool) (h : Constraints p) : clause p c2608 = true :=
  Snake9.LocalRup.prove_clause [c1722, c1736, c1744, c1770, c1806, c1800, c1723, c1775, c1705, c1747, c1745, c1702, c1738, c1740, c854] c2608 (by decide) p (sat_cons (step1722 p h) (sat_cons (step1736 p h) (sat_cons (step1744 p h) (sat_cons (step1770 p h) (sat_cons (step1806 p h) (sat_cons (step1800 p h) (sat_cons (step1723 p h) (sat_cons (step1775 p h) (sat_cons (step1705 p h) (sat_cons (step1747 p h) (sat_cons (step1745 p h) (sat_cons (step1702 p h) (sat_cons (step1738 p h) (sat_cons (step1740 p h) (sat_cons (step854 p h) (sat_nil p))))))))))))))))
def c2609 : List Lit := [(62, false), (79, false), (81, false), (437, true), (71, false)]
theorem step2609 (p : Nat → Bool) (h : Constraints p) : clause p c2609 = true :=
  Snake9.LocalRup.prove_clause [c1183, c1158, c1155, c1149, c1147, c1181, c1179, c1167, c1163, c1162, c382, c384, c353, c2309, c2310, c433, c1957] c2609 (by decide) p (sat_cons (step1183 p h) (sat_cons (step1158 p h) (sat_cons (step1155 p h) (sat_cons (step1149 p h) (sat_cons (step1147 p h) (sat_cons (step1181 p h) (sat_cons (step1179 p h) (sat_cons (step1167 p h) (sat_cons (step1163 p h) (sat_cons (step1162 p h) (sat_cons (step382 p h) (sat_cons (step384 p h) (sat_cons (step353 p h) (sat_cons (step2309 p h) (sat_cons (step2310 p h) (sat_cons (step433 p h) (sat_cons (step1957 p h) (sat_nil p))))))))))))))))))
def c2610 : List Lit := [(77, true), (8, false), (81, false), (202, true), (1704, true)]
theorem step2610 (p : Nat → Bool) (h : Constraints p) : clause p c2610 = true :=
  Snake9.LocalRup.prove_clause [c353, c1548, c2310, c406] c2610 (by decide) p (sat_cons (step353 p h) (sat_cons (step1548 p h) (sat_cons (step2310 p h) (sat_cons (step406 p h) (sat_nil p)))))
def c2611 : List Lit := [(63, true), (1649, true), (62, true), (186, true)]
theorem step2611 (p : Nat → Bool) (h : Constraints p) : clause p c2611 = true :=
  Snake9.LocalRup.prove_clause [c1417, c1406, c267, c1408, c1411, c1420, c1401, c1395, c2275, c2277, c1387, c1937] c2611 (by decide) p (sat_cons (step1417 p h) (sat_cons (step1406 p h) (sat_cons (step267 p h) (sat_cons (step1408 p h) (sat_cons (step1411 p h) (sat_cons (step1420 p h) (sat_cons (step1401 p h) (sat_cons (step1395 p h) (sat_cons (step2275 p h) (sat_cons (step2277 p h) (sat_cons (step1387 p h) (sat_cons (step1937 p h) (sat_nil p)))))))))))))
def c2612 : List Lit := [(1607, false), (1624, true)]
theorem step2612 (p : Nat → Bool) (h : Constraints p) : clause p c2612 = true :=
  Snake9.LocalRup.prove_clause [c1376, c1351, c1352, c1373, c1347, c2519] c2612 (by decide) p (sat_cons (step1376 p h) (sat_cons (step1351 p h) (sat_cons (step1352 p h) (sat_cons (step1373 p h) (sat_cons (step1347 p h) (sat_cons (step2519 p h) (sat_nil p)))))))
def c2613 : List Lit := [(1769, false), (1776, true), (88, false)]
theorem step2613 (p : Nat → Bool) (h : Constraints p) : clause p c2613 = true :=
  Snake9.LocalRup.prove_clause [c1714, c1705, c1708, c1718, c1699, c1691, c1693, c1689, c2540, c1685, c690] c2613 (by decide) p (sat_cons (step1714 p h) (sat_cons (step1705 p h) (sat_cons (step1708 p h) (sat_cons (step1718 p h) (sat_cons (step1699 p h) (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step1689 p h) (sat_cons (step2540 p h) (sat_cons (step1685 p h) (sat_cons (step690 p h) (sat_nil p))))))))))))
def c2614 : List Lit := [(1678, true), (1609, false), (1585, false)]
theorem step2614 (p : Nat → Bool) (h : Constraints p) : clause p c2614 = true :=
  Snake9.LocalRup.prove_clause [c2045, c2446, c1490, c1325, c1443, c2037, c2076, c1251, c1248] c2614 (by decide) p (sat_cons (step2045 p h) (sat_cons (step2446 p h) (sat_cons (step1490 p h) (sat_cons (step1325 p h) (sat_cons (step1443 p h) (sat_cons (step2037 p h) (sat_cons (step2076 p h) (sat_cons (step1251 p h) (sat_cons (step1248 p h) (sat_nil p))))))))))
def c2615 : List Lit := [(1647, true), (71, false), (101, true), (7, false)]
theorem step2615 (p : Nat → Bool) (h : Constraints p) : clause p c2615 = true :=
  Snake9.LocalRup.prove_clause [c1415, c1418, c1407, c1409, c1395, c1405, c1401, c1387, c367, c2279, c273] c2615 (by decide) p (sat_cons (step1415 p h) (sat_cons (step1418 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1395 p h) (sat_cons (step1405 p h) (sat_cons (step1401 p h) (sat_cons (step1387 p h) (sat_cons (step367 p h) (sat_cons (step2279 p h) (sat_cons (step273 p h) (sat_nil p))))))))))))
def c2616 : List Lit := [(46, false), (1802, true), (1783, false), (124, false), (103, false)]
theorem step2616 (p : Nat → Bool) (h : Constraints p) : clause p c2616 = true :=
  Snake9.LocalRup.prove_clause [c939, c938, c937, c1753, c1750, c1739, c1759, c1745, c1775] c2616 (by decide) p (sat_cons (step939 p h) (sat_cons (step938 p h) (sat_cons (step937 p h) (sat_cons (step1753 p h) (sat_cons (step1750 p h) (sat_cons (step1739 p h) (sat_cons (step1759 p h) (sat_cons (step1745 p h) (sat_cons (step1775 p h) (sat_nil p))))))))))
def c2617 : List Lit := [(1812, false), (77, true), (78, true), (1741, false), (71, true), (1657, false)]
theorem step2617 (p : Nat → Bool) (h : Constraints p) : clause p c2617 = true :=
  Snake9.LocalRup.prove_clause [c1535, c1538, c1550, c1546, c1555, c1566, c1655, c2437, c2466, c1894, c1886, c1663, c2467, c1571, c1567, c1483, c1539, c1558, c1556, c2426, c1537, c1548, c1551, c2187] c2617 (by decide) p (sat_cons (step1535 p h) (sat_cons (step1538 p h) (sat_cons (step1550 p h) (sat_cons (step1546 p h) (sat_cons (step1555 p h) (sat_cons (step1566 p h) (sat_cons (step1655 p h) (sat_cons (step2437 p h) (sat_cons (step2466 p h) (sat_cons (step1894 p h) (sat_cons (step1886 p h) (sat_cons (step1663 p h) (sat_cons (step2467 p h) (sat_cons (step1571 p h) (sat_cons (step1567 p h) (sat_cons (step1483 p h) (sat_cons (step1539 p h) (sat_cons (step1558 p h) (sat_cons (step1556 p h) (sat_cons (step2426 p h) (sat_cons (step1537 p h) (sat_cons (step1548 p h) (sat_cons (step1551 p h) (sat_cons (step2187 p h) (sat_nil p)))))))))))))))))))))))))
def c2618 : List Lit := [(99, true), (86, false), (103, false), (102, true), (101, true), (1765, true), (1760, true)]
theorem step2618 (p : Nat → Bool) (h : Constraints p) : clause p c2618 = true :=
  Snake9.LocalRup.prove_clause [c1685, c1687, c1695, c1690, c756, c519, c2339] c2618 (by decide) p (sat_cons (step1685 p h) (sat_cons (step1687 p h) (sat_cons (step1695 p h) (sat_cons (step1690 p h) (sat_cons (step756 p h) (sat_cons (step519 p h) (sat_cons (step2339 p h) (sat_nil p))))))))
def c2619 : List Lit := [(1571, true), (88, true)]
theorem step2619 (p : Nat → Bool) (h : Constraints p) : clause p c2619 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1279, c1274, c1275, c1271, c70, c2216] c2619 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1279 p h) (sat_cons (step1274 p h) (sat_cons (step1275 p h) (sat_cons (step1271 p h) (sat_cons (step70 p h) (sat_cons (step2216 p h) (sat_nil p))))))))
def c2620 : List Lit := [(1624, true), (122, false)]
theorem step2620 (p : Nat → Bool) (h : Constraints p) : clause p c2620 = true :=
  Snake9.LocalRup.prove_clause [c1370, c2178, c2612, c1347, c1343, c2579] c2620 (by decide) p (sat_cons (step1370 p h) (sat_cons (step2178 p h) (sat_cons (step2612 p h) (sat_cons (step1347 p h) (sat_cons (step1343 p h) (sat_cons (step2579 p h) (sat_nil p)))))))
def c2621 : List Lit := [(1763, true), (87, false), (101, true)]
theorem step2621 (p : Nat → Bool) (h : Constraints p) : clause p c2621 = true :=
  Snake9.LocalRup.prove_clause [c1691, c1693, c1689, c2583] c2621 (by decide) p (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step1689 p h) (sat_cons (step2583 p h) (sat_nil p)))))
def c2622 : List Lit := [(1713, true), (79, false), (68, true), (122, false)]
theorem step2622 (p : Nat → Bool) (h : Constraints p) : clause p c2622 = true :=
  Snake9.LocalRup.prove_clause [c2159, c1536, c1538, c1570, c1566, c1539, c2158, c1537] c2622 (by decide) p (sat_cons (step2159 p h) (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1570 p h) (sat_cons (step1566 p h) (sat_cons (step1539 p h) (sat_cons (step2158 p h) (sat_cons (step1537 p h) (sat_nil p)))))))))
def c2623 : List Lit := [(101, true), (107, false), (1764, true), (98, true), (89, true), (88, true)]
theorem step2623 (p : Nat → Bool) (h : Constraints p) : clause p c2623 = true :=
  Snake9.LocalRup.prove_clause [c1692, c2341, c1689, c1694, c1690, c1685, c725, c2334] c2623 (by decide) p (sat_cons (step1692 p h) (sat_cons (step2341 p h) (sat_cons (step1689 p h) (sat_cons (step1694 p h) (sat_cons (step1690 p h) (sat_cons (step1685 p h) (sat_cons (step725 p h) (sat_cons (step2334 p h) (sat_nil p)))))))))
def c2624 : List Lit := [(107, false), (1764, true), (101, false), (122, false)]
theorem step2624 (p : Nat → Bool) (h : Constraints p) : clause p c2624 = true :=
  Snake9.LocalRup.prove_clause [c693, c692, c1689, c1685, c1694] c2624 (by decide) p (sat_cons (step693 p h) (sat_cons (step692 p h) (sat_cons (step1689 p h) (sat_cons (step1685 p h) (sat_cons (step1694 p h) (sat_nil p))))))
def c2625 : List Lit := [(36, false), (39, false), (33, false), (108, false)]
theorem step2625 (p : Nat → Bool) (h : Constraints p) : clause p c2625 = true :=
  Snake9.LocalRup.prove_clause [c124, c150, c2246] c2625 (by decide) p (sat_cons (step124 p h) (sat_cons (step150 p h) (sat_cons (step2246 p h) (sat_nil p))))
def c2626 : List Lit := [(1617, false), (1613, false), (1682, true), (1647, false), (1585, false), (44, false), (122, false)]
theorem step2626 (p : Nat → Bool) (h : Constraints p) : clause p c2626 = true :=
  Snake9.LocalRup.prove_clause [c2045, c1494, c1462, c1382, c1363, c1381, c1365, c1457, c1357, c1501, c184, c1325, c1248, c2037, c1251] c2626 (by decide) p (sat_cons (step2045 p h) (sat_cons (step1494 p h) (sat_cons (step1462 p h) (sat_cons (step1382 p h) (sat_cons (step1363 p h) (sat_cons (step1381 p h) (sat_cons (step1365 p h) (sat_cons (step1457 p h) (sat_cons (step1357 p h) (sat_cons (step1501 p h) (sat_cons (step184 p h) (sat_cons (step1325 p h) (sat_cons (step1248 p h) (sat_cons (step2037 p h) (sat_cons (step1251 p h) (sat_nil p))))))))))))))))
def c2627 : List Lit := [(1613, false), (1682, true), (122, false), (1647, false), (1585, false), (44, false)]
theorem step2627 (p : Nat → Bool) (h : Constraints p) : clause p c2627 = true :=
  Snake9.LocalRup.prove_clause [c2626, c1361, c195, c185, c1357, c1248, c1364, c1251, c1381, c2037, c1457, c1325, c1501] c2627 (by decide) p (sat_cons (step2626 p h) (sat_cons (step1361 p h) (sat_cons (step195 p h) (sat_cons (step185 p h) (sat_cons (step1357 p h) (sat_cons (step1248 p h) (sat_cons (step1364 p h) (sat_cons (step1251 p h) (sat_cons (step1381 p h) (sat_cons (step2037 p h) (sat_cons (step1457 p h) (sat_cons (step1325 p h) (sat_cons (step1501 p h) (sat_nil p))))))))))))))
def c2628 : List Lit := [(46, true), (52, true), (1649, true), (1641, false), (88, true)]
theorem step2628 (p : Nat → Bool) (h : Constraints p) : clause p c2628 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1424, c1398, c1388, c1389, c1395, c1396, c1420, c1390, c1391, c1410, c211, c1402, c2266, c259] c2628 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1424 p h) (sat_cons (step1398 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1395 p h) (sat_cons (step1396 p h) (sat_cons (step1420 p h) (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step1410 p h) (sat_cons (step211 p h) (sat_cons (step1402 p h) (sat_cons (step2266 p h) (sat_cons (step259 p h) (sat_nil p))))))))))))))))
def c2629 : List Lit := [(1648, false), (1625, false), (1585, false), (44, false), (122, false), (1660, true), (1607, false), (1682, true)]
theorem step2629 (p : Nat → Bool) (h : Constraints p) : clause p c2629 = true :=
  Snake9.LocalRup.prove_clause [c1458, c1452, c2589, c1501, c1248, c1325, c1251, c2037] c2629 (by decide) p (sat_cons (step1458 p h) (sat_cons (step1452 p h) (sat_cons (step2589 p h) (sat_cons (step1501 p h) (sat_cons (step1248 p h) (sat_cons (step1325 p h) (sat_cons (step1251 p h) (sat_cons (step2037 p h) (sat_nil p)))))))))
end B112E052
