import B112E089Part0006
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2460 : List Lit := [(27, false), (34, false), (151, true), (26, true), (31, false)]
theorem step2460 (p : Nat → Bool) (h : Constraints p) : clause p c2460 = true :=
  Snake9.LocalRup.prove_clause [c163, c202] c2460 (by decide) p (sat_cons (step163 p h) (sat_cons (step202 p h) (sat_nil p)))
def c2461 : List Lit := [(76, false), (113, false), (74, false), (32, false), (237, true), (63, true)]
theorem step2461 (p : Nat → Bool) (h : Constraints p) : clause p c2461 = true :=
  Snake9.LocalRup.prove_clause [c695, c688, c2389] c2461 (by decide) p (sat_cons (step695 p h) (sat_cons (step688 p h) (sat_cons (step2389 p h) (sat_nil p))))
def c2462 : List Lit := [(49, false), (1594, true), (14, false), (73, false), (51, true)]
theorem step2462 (p : Nat → Bool) (h : Constraints p) : clause p c2462 = true :=
  Snake9.LocalRup.prove_clause [c327, c329, c1461, c1466, c1471] c2462 (by decide) p (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step1461 p h) (sat_cons (step1466 p h) (sat_cons (step1471 p h) (sat_nil p))))))
def c2463 : List Lit := [(34, true), (1570, true), (156, true), (39, true), (23, true)]
theorem step2463 (p : Nat → Bool) (h : Constraints p) : clause p c2463 = true :=
  Snake9.LocalRup.prove_clause [c1418, c2137, c1423, c1413] c2463 (by decide) p (sat_cons (step1418 p h) (sat_cons (step2137 p h) (sat_cons (step1423 p h) (sat_cons (step1413 p h) (sat_nil p)))))
def c2464 : List Lit := [(1577, true), (50, true), (41, true), (169, true), (68, true)]
theorem step2464 (p : Nat → Bool) (h : Constraints p) : clause p c2464 = true :=
  Snake9.LocalRup.prove_clause [c1428, c1438, c1436, c1429, c1430, c300, c301, c2229, c280] c2464 (by decide) p (sat_cons (step1428 p h) (sat_cons (step1438 p h) (sat_cons (step1436 p h) (sat_cons (step1429 p h) (sat_cons (step1430 p h) (sat_cons (step300 p h) (sat_cons (step301 p h) (sat_cons (step2229 p h) (sat_cons (step280 p h) (sat_nil p))))))))))
def c2465 : List Lit := [(1760, true), (103, true), (1717, false), (487, true)]
theorem step2465 (p : Nat → Bool) (h : Constraints p) : clause p c2465 = true :=
  Snake9.LocalRup.prove_clause [c2431, c2293, c1772, c1291, c1250, c1248, c1242, c1240, c1289, c1284, c1281, c1272, c1266, c1252, c1236, c1227, c1857, c1780, c1788, c2095, c2093, c1768, c2115, c1776, c1758, c1766, c1750, c1751, c2456] c2465 (by decide) p (sat_cons (step2431 p h) (sat_cons (step2293 p h) (sat_cons (step1772 p h) (sat_cons (step1291 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1242 p h) (sat_cons (step1240 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1857 p h) (sat_cons (step1780 p h) (sat_cons (step1788 p h) (sat_cons (step2095 p h) (sat_cons (step2093 p h) (sat_cons (step1768 p h) (sat_cons (step2115 p h) (sat_cons (step1776 p h) (sat_cons (step1758 p h) (sat_cons (step1766 p h) (sat_cons (step1750 p h) (sat_cons (step1751 p h) (sat_cons (step2456 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2466 : List Lit := [(1508, true), (129, true), (2, true), (6, false), (24, false)]
theorem step2466 (p : Nat → Bool) (h : Constraints p) : clause p c2466 = true :=
  Snake9.LocalRup.prove_clause [c1310, c2119, c1304, c31] c2466 (by decide) p (sat_cons (step1310 p h) (sat_cons (step2119 p h) (sat_cons (step1304 p h) (sat_cons (step31 p h) (sat_nil p)))))
def c2467 : List Lit := [(273, true), (14, true), (16, true), (1543, true), (10, false)]
theorem step2467 (p : Nat → Bool) (h : Constraints p) : clause p c2467 = true :=
  Snake9.LocalRup.prove_clause [c1380, c1056, c1058, c1052, c1043, c1049, c1041, c83, c1341, c2183, c1350, c1351, c60, c1377, c1342, c145, c1361, c1353] c2467 (by decide) p (sat_cons (step1380 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1052 p h) (sat_cons (step1043 p h) (sat_cons (step1049 p h) (sat_cons (step1041 p h) (sat_cons (step83 p h) (sat_cons (step1341 p h) (sat_cons (step2183 p h) (sat_cons (step1350 p h) (sat_cons (step1351 p h) (sat_cons (step60 p h) (sat_cons (step1377 p h) (sat_cons (step1342 p h) (sat_cons (step145 p h) (sat_cons (step1361 p h) (sat_cons (step1353 p h) (sat_nil p)))))))))))))))))))
def c2468 : List Lit := [(22, false), (26, false), (1538, true), (10, false)]
theorem step2468 (p : Nat → Bool) (h : Constraints p) : clause p c2468 = true :=
  Snake9.LocalRup.prove_clause [c146, c145, c1357, c1353, c1362] c2468 (by decide) p (sat_cons (step146 p h) (sat_cons (step145 p h) (sat_cons (step1357 p h) (sat_cons (step1353 p h) (sat_cons (step1362 p h) (sat_nil p))))))
def c2469 : List Lit := [(1537, true), (153, true), (1528, true)]
theorem step2469 (p : Nat → Bool) (h : Constraints p) : clause p c2469 = true :=
  Snake9.LocalRup.prove_clause [c1359, c1361, c1356, c1353, c2412] c2469 (by decide) p (sat_cons (step1359 p h) (sat_cons (step1361 p h) (sat_cons (step1356 p h) (sat_cons (step1353 p h) (sat_cons (step2412 p h) (sat_nil p))))))
def c2470 : List Lit := [(1599, true), (1660, true), (57, true), (60, false), (22, false)]
theorem step2470 (p : Nat → Bool) (h : Constraints p) : clause p c2470 = true :=
  Snake9.LocalRup.prove_clause [c2134, c1480, c1615, c442, c1623, c1617] c2470 (by decide) p (sat_cons (step2134 p h) (sat_cons (step1480 p h) (sat_cons (step1615 p h) (sat_cons (step442 p h) (sat_cons (step1623 p h) (sat_cons (step1617 p h) (sat_nil p)))))))
def c2471 : List Lit := [(35, false), (28, false), (27, true)]
theorem step2471 (p : Nat → Bool) (h : Constraints p) : clause p c2471 = true :=
  Snake9.LocalRup.prove_clause [c2212, c2213, c1964] c2471 (by decide) p (sat_cons (step2212 p h) (sat_cons (step2213 p h) (sat_cons (step1964 p h) (sat_nil p))))
def c2472 : List Lit := [(25, false), (1544, true), (27, true), (65, true), (139, true), (149, true), (153, true), (14, true)]
theorem step2472 (p : Nat → Bool) (h : Constraints p) : clause p c2472 = true :=
  Snake9.LocalRup.prove_clause [c1340, c1357, c1359, c1381, c1349, c2412, c2107, c1358] c2472 (by decide) p (sat_cons (step1340 p h) (sat_cons (step1357 p h) (sat_cons (step1359 p h) (sat_cons (step1381 p h) (sat_cons (step1349 p h) (sat_cons (step2412 p h) (sat_cons (step2107 p h) (sat_cons (step1358 p h) (sat_nil p)))))))))
def c2473 : List Lit := [(1544, true), (27, true), (65, true), (139, true), (149, true), (153, true), (14, true)]
theorem step2473 (p : Nat → Bool) (h : Constraints p) : clause p c2473 = true :=
  Snake9.LocalRup.prove_clause [c1357, c1340, c1347, c1374, c2472, c1353, c1363, c1362, c1358, c1378, c2413, c1348] c2473 (by decide) p (sat_cons (step1357 p h) (sat_cons (step1340 p h) (sat_cons (step1347 p h) (sat_cons (step1374 p h) (sat_cons (step2472 p h) (sat_cons (step1353 p h) (sat_cons (step1363 p h) (sat_cons (step1362 p h) (sat_cons (step1358 p h) (sat_cons (step1378 p h) (sat_cons (step2413 p h) (sat_cons (step1348 p h) (sat_nil p)))))))))))))
def c2474 : List Lit := [(53, false), (81, false), (54, true), (43, false), (205, true), (75, true)]
theorem step2474 (p : Nat → Bool) (h : Constraints p) : clause p c2474 = true :=
  Snake9.LocalRup.prove_clause [c2227, c244, c252, c2268] c2474 (by decide) p (sat_cons (step2227 p h) (sat_cons (step244 p h) (sat_cons (step252 p h) (sat_cons (step2268 p h) (sat_nil p)))))
def c2475 : List Lit := [(1519, true), (8, true)]
theorem step2475 (p : Nat → Bool) (h : Constraints p) : clause p c2475 = true :=
  Snake9.LocalRup.prove_clause [c1304, c1307, c1332, c2438, c1329, c1308, c1310, c1315, c1320, c1306, c2448, c1313, c18, c23] c2475 (by decide) p (sat_cons (step1304 p h) (sat_cons (step1307 p h) (sat_cons (step1332 p h) (sat_cons (step2438 p h) (sat_cons (step1329 p h) (sat_cons (step1308 p h) (sat_cons (step1310 p h) (sat_cons (step1315 p h) (sat_cons (step1320 p h) (sat_cons (step1306 p h) (sat_cons (step2448 p h) (sat_cons (step1313 p h) (sat_cons (step18 p h) (sat_cons (step23 p h) (sat_nil p)))))))))))))))
def c2476 : List Lit := [(1719, true), (1761, true), (1745, false), (487, true), (103, true), (44, false)]
theorem step2476 (p : Nat → Bool) (h : Constraints p) : clause p c2476 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1284, c1281, c1272, c1266, c1291, c1764, c1772, c2293, c1767, c1768, c2088, c2092, c1828, c1788, c1858] c2476 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1291 p h) (sat_cons (step1764 p h) (sat_cons (step1772 p h) (sat_cons (step2293 p h) (sat_cons (step1767 p h) (sat_cons (step1768 p h) (sat_cons (step2088 p h) (sat_cons (step2092 p h) (sat_cons (step1828 p h) (sat_cons (step1788 p h) (sat_cons (step1858 p h) (sat_nil p)))))))))))))))))
def c2477 : List Lit := [(1761, true), (1745, false), (1713, false), (487, true), (103, true), (44, false)]
theorem step2477 (p : Nat → Bool) (h : Constraints p) : clause p c2477 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1289, c1284, c1281, c1272, c1266, c1291, c1764, c2293, c1863, c1785, c1774, c2476, c1773, c1789, c1784, c2092, c1858, c1769, c1828, c2088] c2477 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1291 p h) (sat_cons (step1764 p h) (sat_cons (step2293 p h) (sat_cons (step1863 p h) (sat_cons (step1785 p h) (sat_cons (step1774 p h) (sat_cons (step2476 p h) (sat_cons (step1773 p h) (sat_cons (step1789 p h) (sat_cons (step1784 p h) (sat_cons (step2092 p h) (sat_cons (step1858 p h) (sat_cons (step1769 p h) (sat_cons (step1828 p h) (sat_cons (step2088 p h) (sat_nil p))))))))))))))))))))))
def c2478 : List Lit := [(1722, false), (1720, true), (1746, false), (1762, true), (1713, false), (487, true), (106, true), (44, false)]
theorem step2478 (p : Nat → Bool) (h : Constraints p) : clause p c2478 = true :=
  Snake9.LocalRup.prove_clause [c1825, c1864, c1289, c1284, c1281, c1272, c1266, c1291, c1789, c1784, c2092, c1859, c1769, c1829, c2088] c2478 (by decide) p (sat_cons (step1825 p h) (sat_cons (step1864 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1291 p h) (sat_cons (step1789 p h) (sat_cons (step1784 p h) (sat_cons (step2092 p h) (sat_cons (step1859 p h) (sat_cons (step1769 p h) (sat_cons (step1829 p h) (sat_cons (step2088 p h) (sat_nil p))))))))))))))))
def c2479 : List Lit := [(1746, false), (1762, true), (1713, false), (487, true), (103, true), (44, false)]
theorem step2479 (p : Nat → Bool) (h : Constraints p) : clause p c2479 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1284, c1281, c1272, c1266, c1291, c1764, c1772, c2293, c1825, c1864, c1785, c1774, c2478, c1773, c1767, c1768, c2088, c2092, c1829, c1788, c1859] c2479 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1291 p h) (sat_cons (step1764 p h) (sat_cons (step1772 p h) (sat_cons (step2293 p h) (sat_cons (step1825 p h) (sat_cons (step1864 p h) (sat_cons (step1785 p h) (sat_cons (step1774 p h) (sat_cons (step2478 p h) (sat_cons (step1773 p h) (sat_cons (step1767 p h) (sat_cons (step1768 p h) (sat_cons (step2088 p h) (sat_cons (step2092 p h) (sat_cons (step1829 p h) (sat_cons (step1788 p h) (sat_cons (step1859 p h) (sat_nil p)))))))))))))))))))))))
def c2480 : List Lit := [(1761, true), (1713, false), (487, true), (103, true), (44, false)]
theorem step2480 (p : Nat → Bool) (h : Constraints p) : clause p c2480 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1291, c2293, c1863, c2477, c1785, c1817, c1819, c2162, c1815, c1812, c921, c1766, c1775, c1776, c1789, c1768, c2092] c2480 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1291 p h) (sat_cons (step2293 p h) (sat_cons (step1863 p h) (sat_cons (step2477 p h) (sat_cons (step1785 p h) (sat_cons (step1817 p h) (sat_cons (step1819 p h) (sat_cons (step2162 p h) (sat_cons (step1815 p h) (sat_cons (step1812 p h) (sat_cons (step921 p h) (sat_cons (step1766 p h) (sat_cons (step1775 p h) (sat_cons (step1776 p h) (sat_cons (step1789 p h) (sat_cons (step1768 p h) (sat_cons (step2092 p h) (sat_nil p)))))))))))))))))))
def c2481 : List Lit := [(75, true), (120, false), (1660, false), (74, false), (1699, true), (1650, false)]
theorem step2481 (p : Nat → Bool) (h : Constraints p) : clause p c2481 = true :=
  Snake9.LocalRup.prove_clause [c1609, c1634, c1716, c2161, c1648, c1649, c2145, c711, c1722, c1612, c1639] c2481 (by decide) p (sat_cons (step1609 p h) (sat_cons (step1634 p h) (sat_cons (step1716 p h) (sat_cons (step2161 p h) (sat_cons (step1648 p h) (sat_cons (step1649 p h) (sat_cons (step2145 p h) (sat_cons (step711 p h) (sat_cons (step1722 p h) (sat_cons (step1612 p h) (sat_cons (step1639 p h) (sat_nil p))))))))))))
def c2482 : List Lit := [(120, false), (1660, false), (1650, false), (74, false), (1699, true)]
theorem step2482 (p : Nat → Bool) (h : Constraints p) : clause p c2482 = true :=
  Snake9.LocalRup.prove_clause [c2481, c710, c715, c1612, c1647, c1639, c2145, c1722] c2482 (by decide) p (sat_cons (step2481 p h) (sat_cons (step710 p h) (sat_cons (step715 p h) (sat_cons (step1612 p h) (sat_cons (step1647 p h) (sat_cons (step1639 p h) (sat_cons (step2145 p h) (sat_cons (step1722 p h) (sat_nil p)))))))))
def c2483 : List Lit := [(1746, true), (72, false), (120, true), (243, true)]
theorem step2483 (p : Nat → Bool) (h : Constraints p) : clause p c2483 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1822, c2453, c1820, c2087, c1813, c2310, c1814, c938, c968] c2483 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1822 p h) (sat_cons (step2453 p h) (sat_cons (step1820 p h) (sat_cons (step2087 p h) (sat_cons (step1813 p h) (sat_cons (step2310 p h) (sat_cons (step1814 p h) (sat_cons (step938 p h) (sat_cons (step968 p h) (sat_nil p)))))))))))
def c2484 : List Lit := [(1670, true), (74, true), (67, false), (200, true), (65, true)]
theorem step2484 (p : Nat → Bool) (h : Constraints p) : clause p c2484 = true :=
  Snake9.LocalRup.prove_clause [c1647, c1648, c2130] c2484 (by decide) p (sat_cons (step1647 p h) (sat_cons (step1648 p h) (sat_cons (step2130 p h) (sat_nil p))))
def c2485 : List Lit := [(1762, true), (120, true), (1713, false), (487, true), (103, true), (44, false)]
theorem step2485 (p : Nat → Bool) (h : Constraints p) : clause p c2485 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1819, c1289, c1284, c1281, c1270, c1268, c1279, c1277, c1274, c1291, c2293, c2479, c1822, c1820, c1813, c1814, c1815, c2139, c968, c1803, c957, c1828, c921, c1864, c1766, c1785, c1775, c1776, c1789, c1768, c2092] c2485 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1819 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1270 p h) (sat_cons (step1268 p h) (sat_cons (step1279 p h) (sat_cons (step1277 p h) (sat_cons (step1274 p h) (sat_cons (step1291 p h) (sat_cons (step2293 p h) (sat_cons (step2479 p h) (sat_cons (step1822 p h) (sat_cons (step1820 p h) (sat_cons (step1813 p h) (sat_cons (step1814 p h) (sat_cons (step1815 p h) (sat_cons (step2139 p h) (sat_cons (step968 p h) (sat_cons (step1803 p h) (sat_cons (step957 p h) (sat_cons (step1828 p h) (sat_cons (step921 p h) (sat_cons (step1864 p h) (sat_cons (step1766 p h) (sat_cons (step1785 p h) (sat_cons (step1775 p h) (sat_cons (step1776 p h) (sat_cons (step1789 p h) (sat_cons (step1768 p h) (sat_cons (step2092 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c2486 : List Lit := [(1660, true), (74, true), (193, true), (73, true)]
theorem step2486 (p : Nat → Bool) (h : Constraints p) : clause p c2486 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1621, c1623, c1619, c1614, c641, c640, c2001] c2486 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1621 p h) (sat_cons (step1623 p h) (sat_cons (step1619 p h) (sat_cons (step1614 p h) (sat_cons (step641 p h) (sat_cons (step640 p h) (sat_cons (step2001 p h) (sat_nil p)))))))))
def c2487 : List Lit := [(107, false), (1751, true), (112, false), (120, false), (68, true), (485, true)]
theorem step2487 (p : Nat → Bool) (h : Constraints p) : clause p c2487 = true :=
  Snake9.LocalRup.prove_clause [c1286, c1262, c1259, c1258, c1284, c1281, c1272, c1266, c897, c1797, c2090, c2116, c1832, c916, c2397] c2487 (by decide) p (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1259 p h) (sat_cons (step1258 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step897 p h) (sat_cons (step1797 p h) (sat_cons (step2090 p h) (sat_cons (step2116 p h) (sat_cons (step1832 p h) (sat_cons (step916 p h) (sat_cons (step2397 p h) (sat_nil p))))))))))))))))
def c2488 : List Lit := [(115, false), (111, false), (68, true), (67, false), (239, true)]
theorem step2488 (p : Nat → Bool) (h : Constraints p) : clause p c2488 = true :=
  Snake9.LocalRup.prove_clause [c917, c907] c2488 (by decide) p (sat_cons (step917 p h) (sat_cons (step907 p h) (sat_nil p)))
def c2489 : List Lit := [(1745, true), (102, false)]
theorem step2489 (p : Nat → Bool) (h : Constraints p) : clause p c2489 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1819, c2162, c1815, c1812, c921] c2489 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1819 p h) (sat_cons (step2162 p h) (sat_cons (step1815 p h) (sat_cons (step1812 p h) (sat_cons (step921 p h) (sat_nil p)))))))
def c2490 : List Lit := [(122, false), (119, false), (102, false), (123, false), (246, true)]
theorem step2490 (p : Nat → Bool) (h : Constraints p) : clause p c2490 = true :=
  Snake9.LocalRup.prove_clause [c968, c921, c957] c2490 (by decide) p (sat_cons (step968 p h) (sat_cons (step921 p h) (sat_cons (step957 p h) (sat_nil p))))
def c2491 : List Lit := [(117, false), (111, false), (107, false), (241, true)]
theorem step2491 (p : Nat → Bool) (h : Constraints p) : clause p c2491 = true :=
  Snake9.LocalRup.prove_clause [c927, c884] c2491 (by decide) p (sat_cons (step927 p h) (sat_cons (step884 p h) (sat_nil p)))
def c2492 : List Lit := [(1601, true), (111, false), (68, true), (67, false), (54, true), (185, true)]
theorem step2492 (p : Nat → Bool) (h : Constraints p) : clause p c2492 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1486, c1484, c1477, c1478, c1479, c464, c416, c472] c2492 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1486 p h) (sat_cons (step1484 p h) (sat_cons (step1477 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step464 p h) (sat_cons (step416 p h) (sat_cons (step472 p h) (sat_nil p))))))))))
def c2493 : List Lit := [(76, false), (123, false), (74, true), (66, false), (200, true), (65, true)]
theorem step2493 (p : Nat → Bool) (h : Constraints p) : clause p c2493 = true :=
  Snake9.LocalRup.prove_clause [c749, c750] c2493 (by decide) p (sat_cons (step749 p h) (sat_cons (step750 p h) (sat_nil p)))
def c2494 : List Lit := [(1572, true), (43, false), (45, false)]
theorem step2494 (p : Nat → Bool) (h : Constraints p) : clause p c2494 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1428, c270] c2494 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step270 p h) (sat_nil p))))
def c2495 : List Lit := [(1601, true), (68, true), (66, false), (54, true), (185, true)]
theorem step2495 (p : Nat → Bool) (h : Constraints p) : clause p c2495 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1486, c1484, c1477, c1478, c1479, c416, c473, c428] c2495 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1486 p h) (sat_cons (step1484 p h) (sat_cons (step1477 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step416 p h) (sat_cons (step473 p h) (sat_cons (step428 p h) (sat_nil p))))))))))
def c2496 : List Lit := [(1739, true), (115, true), (113, true), (107, false), (241, true)]
theorem step2496 (p : Nat → Bool) (h : Constraints p) : clause p c2496 = true :=
  Snake9.LocalRup.prove_clause [c1801, c1797, c1807, c1809, c1802, c1799, c927, c884] c2496 (by decide) p (sat_cons (step1801 p h) (sat_cons (step1797 p h) (sat_cons (step1807 p h) (sat_cons (step1809 p h) (sat_cons (step1802 p h) (sat_cons (step1799 p h) (sat_cons (step927 p h) (sat_cons (step884 p h) (sat_nil p)))))))))
def c2497 : List Lit := [(115, false), (1746, true), (123, false), (68, true), (239, true)]
theorem step2497 (p : Nat → Bool) (h : Constraints p) : clause p c2497 = true :=
  Snake9.LocalRup.prove_clause [c916, c966, c967, c1812, c1815, c1820] c2497 (by decide) p (sat_cons (step916 p h) (sat_cons (step966 p h) (sat_cons (step967 p h) (sat_cons (step1812 p h) (sat_cons (step1815 p h) (sat_cons (step1820 p h) (sat_nil p)))))))
def c2498 : List Lit := [(115, false), (122, false), (123, false), (68, true), (239, true)]
theorem step2498 (p : Nat → Bool) (h : Constraints p) : clause p c2498 = true :=
  Snake9.LocalRup.prove_clause [c916, c967] c2498 (by decide) p (sat_cons (step916 p h) (sat_cons (step967 p h) (sat_nil p)))
def c2499 : List Lit := [(115, false), (1751, true), (123, false), (68, true), (67, false), (239, true)]
theorem step2499 (p : Nat → Bool) (h : Constraints p) : clause p c2499 = true :=
  Snake9.LocalRup.prove_clause [c2488, c2497, c1798, c1829, c1805] c2499 (by decide) p (sat_cons (step2488 p h) (sat_cons (step2497 p h) (sat_cons (step1798 p h) (sat_cons (step1829 p h) (sat_cons (step1805 p h) (sat_nil p))))))
def c2500 : List Lit := [(93, true), (98, false), (222, true), (123, true)]
theorem step2500 (p : Nat → Bool) (h : Constraints p) : clause p c2500 = true :=
  Snake9.LocalRup.prove_clause [c835, c836, c2291, c2007] c2500 (by decide) p (sat_cons (step835 p h) (sat_cons (step836 p h) (sat_cons (step2291 p h) (sat_cons (step2007 p h) (sat_nil p)))))
def c2501 : List Lit := [(1572, false), (1590, false), (1616, true), (103, false), (45, true), (158, true), (171, true), (75, false)]
theorem step2501 (p : Nat → Bool) (h : Constraints p) : clause p c2501 = true :=
  Snake9.LocalRup.prove_clause [c2099, c1467, c1493, c1541, c1448, c1430, c1436, c1437, c1447, c1452, c1432, c1534, c2101, c1498, c2094, c1470, c1461] c2501 (by decide) p (sat_cons (step2099 p h) (sat_cons (step1467 p h) (sat_cons (step1493 p h) (sat_cons (step1541 p h) (sat_cons (step1448 p h) (sat_cons (step1430 p h) (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step1447 p h) (sat_cons (step1452 p h) (sat_cons (step1432 p h) (sat_cons (step1534 p h) (sat_cons (step2101 p h) (sat_cons (step1498 p h) (sat_cons (step2094 p h) (sat_cons (step1470 p h) (sat_cons (step1461 p h) (sat_nil p))))))))))))))))))
def c2502 : List Lit := [(1572, true), (54, false), (43, false)]
theorem step2502 (p : Nat → Bool) (h : Constraints p) : clause p c2502 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1428, c271] c2502 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step271 p h) (sat_nil p))))
def c2503 : List Lit := [(54, true), (1601, true), (185, true), (66, false), (67, false)]
theorem step2503 (p : Nat → Bool) (h : Constraints p) : clause p c2503 = true :=
  Snake9.LocalRup.prove_clause [c1476, c2495, c1484, c621, c1478] c2503 (by decide) p (sat_cons (step1476 p h) (sat_cons (step2495 p h) (sat_cons (step1484 p h) (sat_cons (step621 p h) (sat_cons (step1478 p h) (sat_nil p))))))
def c2504 : List Lit := [(1577, false), (1600, false), (75, false), (158, true), (1616, true)]
theorem step2504 (p : Nat → Bool) (h : Constraints p) : clause p c2504 = true :=
  Snake9.LocalRup.prove_clause [c1489, c1541, c2099, c1447, c1452, c1534, c2101, c1494, c2155] c2504 (by decide) p (sat_cons (step1489 p h) (sat_cons (step1541 p h) (sat_cons (step2099 p h) (sat_cons (step1447 p h) (sat_cons (step1452 p h) (sat_cons (step1534 p h) (sat_cons (step2101 p h) (sat_cons (step1494 p h) (sat_cons (step2155 p h) (sat_nil p))))))))))
def c2505 : List Lit := [(51, true), (1593, true), (103, false)]
theorem step2505 (p : Nat → Bool) (h : Constraints p) : clause p c2505 = true :=
  Snake9.LocalRup.prove_clause [c1468, c1464, c1466, c1470, c1461, c1462, c339, c2141, c318] c2505 (by decide) p (sat_cons (step1468 p h) (sat_cons (step1464 p h) (sat_cons (step1466 p h) (sat_cons (step1470 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step339 p h) (sat_cons (step2141 p h) (sat_cons (step318 p h) (sat_nil p))))))))))
def c2506 : List Lit := [(1572, true), (53, true), (175, false), (54, false)]
theorem step2506 (p : Nat → Bool) (h : Constraints p) : clause p c2506 = true :=
  Snake9.LocalRup.prove_clause [c1129, c1132, c1134, c2336, c1147, c1142, c1138, c353, c1428, c2502, c361, c379] c2506 (by decide) p (sat_cons (step1129 p h) (sat_cons (step1132 p h) (sat_cons (step1134 p h) (sat_cons (step2336 p h) (sat_cons (step1147 p h) (sat_cons (step1142 p h) (sat_cons (step1138 p h) (sat_cons (step353 p h) (sat_cons (step1428 p h) (sat_cons (step2502 p h) (sat_cons (step361 p h) (sat_cons (step379 p h) (sat_nil p)))))))))))))
def c2507 : List Lit := [(52, false), (43, false), (1593, true), (175, false), (54, false)]
theorem step2507 (p : Nat → Bool) (h : Constraints p) : clause p c2507 = true :=
  Snake9.LocalRup.prove_clause [c2332, c353, c362, c373, c1462, c2399, c1470, c1465] c2507 (by decide) p (sat_cons (step2332 p h) (sat_cons (step353 p h) (sat_cons (step362 p h) (sat_cons (step373 p h) (sat_cons (step1462 p h) (sat_cons (step2399 p h) (sat_cons (step1470 p h) (sat_cons (step1465 p h) (sat_nil p)))))))))
def c2508 : List Lit := [(112, false), (62, true), (120, true), (41, false), (237, true), (56, false)]
theorem step2508 (p : Nat → Bool) (h : Constraints p) : clause p c2508 = true :=
  Snake9.LocalRup.prove_clause [c2300, c2299, c2008, c514, c906] c2508 (by decide) p (sat_cons (step2300 p h) (sat_cons (step2299 p h) (sat_cons (step2008 p h) (sat_cons (step514 p h) (sat_cons (step906 p h) (sat_nil p))))))
def c2509 : List Lit := [(113, false), (112, true), (41, false), (237, true), (56, false)]
theorem step2509 (p : Nat → Bool) (h : Constraints p) : clause p c2509 = true :=
  Snake9.LocalRup.prove_clause [c514, c905] c2509 (by decide) p (sat_cons (step514 p h) (sat_cons (step905 p h) (sat_nil p)))
def c2510 : List Lit := [(1553, true), (1527, false), (6, false), (153, true), (1519, false), (275, true), (41, false)]
theorem step2510 (p : Nat → Bool) (h : Constraints p) : clause p c2510 = true :=
  Snake9.LocalRup.prove_clause [c1345, c1371, c1063, c1035, c1034, c1033, c1061, c1058, c1043, c1040, c1056, c1052, c1049, c1406, c1394, c2410, c1380, c2416, c1351, c34, c30, c2182, c1313, c2466, c83, c1334, c1341, c1321, c2136] c2510 (by decide) p (sat_cons (step1345 p h) (sat_cons (step1371 p h) (sat_cons (step1063 p h) (sat_cons (step1035 p h) (sat_cons (step1034 p h) (sat_cons (step1033 p h) (sat_cons (step1061 p h) (sat_cons (step1058 p h) (sat_cons (step1043 p h) (sat_cons (step1040 p h) (sat_cons (step1056 p h) (sat_cons (step1052 p h) (sat_cons (step1049 p h) (sat_cons (step1406 p h) (sat_cons (step1394 p h) (sat_cons (step2410 p h) (sat_cons (step1380 p h) (sat_cons (step2416 p h) (sat_cons (step1351 p h) (sat_cons (step34 p h) (sat_cons (step30 p h) (sat_cons (step2182 p h) (sat_cons (step1313 p h) (sat_cons (step2466 p h) (sat_cons (step83 p h) (sat_cons (step1334 p h) (sat_cons (step1341 p h) (sat_cons (step1321 p h) (sat_cons (step2136 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2511 : List Lit := [(1688, true), (1680, false), (1670, false)]
theorem step2511 (p : Nat → Bool) (h : Constraints p) : clause p c2511 = true :=
  Snake9.LocalRup.prove_clause [c1667, c1655, c1681, c1685, c1670, c1656, c2097, c1651] c2511 (by decide) p (sat_cons (step1667 p h) (sat_cons (step1655 p h) (sat_cons (step1681 p h) (sat_cons (step1685 p h) (sat_cons (step1670 p h) (sat_cons (step1656 p h) (sat_cons (step2097 p h) (sat_cons (step1651 p h) (sat_nil p)))))))))
def c2512 : List Lit := [(1660, true), (57, false), (61, false), (49, true), (197, true), (69, true)]
theorem step2512 (p : Nat → Bool) (h : Constraints p) : clause p c2512 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1625, c1623, c1616, c1617, c2449, c463] c2512 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1625 p h) (sat_cons (step1623 p h) (sat_cons (step1616 p h) (sat_cons (step1617 p h) (sat_cons (step2449 p h) (sat_cons (step463 p h) (sat_nil p))))))))
def c2513 : List Lit := [(455, true), (91, false), (1727, true), (1709, false), (49, true)]
theorem step2513 (p : Nat → Bool) (h : Constraints p) : clause p c2513 = true :=
  Snake9.LocalRup.prove_clause [c1758, c1784, c1250, c1252, c1248, c1234, c1236, c1242, c1231, c1227, c1240, c1241, c1230, c2454, c1772, c1773, c1788, c1767, c1768, c2095, c1759, c2093, c1753, c2293, c846, c840, c789] c2513 (by decide) p (sat_cons (step1758 p h) (sat_cons (step1784 p h) (sat_cons (step1250 p h) (sat_cons (step1252 p h) (sat_cons (step1248 p h) (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1242 p h) (sat_cons (step1231 p h) (sat_cons (step1227 p h) (sat_cons (step1240 p h) (sat_cons (step1241 p h) (sat_cons (step1230 p h) (sat_cons (step2454 p h) (sat_cons (step1772 p h) (sat_cons (step1773 p h) (sat_cons (step1788 p h) (sat_cons (step1767 p h) (sat_cons (step1768 p h) (sat_cons (step2095 p h) (sat_cons (step1759 p h) (sat_cons (step2093 p h) (sat_cons (step1753 p h) (sat_cons (step2293 p h) (sat_cons (step846 p h) (sat_cons (step840 p h) (sat_cons (step789 p h) (sat_nil p))))))))))))))))))))))))))))
def c2514 : List Lit := [(1714, true), (103, false), (91, false), (1722, true), (96, true), (49, true)]
theorem step2514 (p : Nat → Bool) (h : Constraints p) : clause p c2514 = true :=
  Snake9.LocalRup.prove_clause [c1750, c1761, c1759, c1752, c1753, c846, c862, c1241, c1242, c1248, c2351, c1234, c1236, c1231, c1227, c1230, c817, c840, c807, c789, c1765, c1767, c1773] c2514 (by decide) p (sat_cons (step1750 p h) (sat_cons (step1761 p h) (sat_cons (step1759 p h) (sat_cons (step1752 p h) (sat_cons (step1753 p h) (sat_cons (step846 p h) (sat_cons (step862 p h) (sat_cons (step1241 p h) (sat_cons (step1242 p h) (sat_cons (step1248 p h) (sat_cons (step2351 p h) (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1231 p h) (sat_cons (step1227 p h) (sat_cons (step1230 p h) (sat_cons (step817 p h) (sat_cons (step840 p h) (sat_cons (step807 p h) (sat_cons (step789 p h) (sat_cons (step1765 p h) (sat_cons (step1767 p h) (sat_cons (step1773 p h) (sat_nil p))))))))))))))))))))))))
def c2515 : List Lit := [(1726, true), (218, true), (97, false), (1713, false), (44, false)]
theorem step2515 (p : Nat → Bool) (h : Constraints p) : clause p c2515 = true :=
  Snake9.LocalRup.prove_clause [c1787, c1783, c2095, c1770, c831, c1768] c2515 (by decide) p (sat_cons (step1787 p h) (sat_cons (step1783 p h) (sat_cons (step2095 p h) (sat_cons (step1770 p h) (sat_cons (step831 p h) (sat_cons (step1768 p h) (sat_nil p)))))))
def c2516 : List Lit := [(1714, false), (107, true), (1761, true), (120, true)]
theorem step2516 (p : Nat → Bool) (h : Constraints p) : clause p c2516 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1767, c1770, c1863, c1811, c1819, c1788, c1789, c1858, c1773, c1825, c2403, c1828, c1765, c1822, c1820, c2296, c1803, c1813, c1814, c1815, c928, c1801, c966, c921, c933] c2516 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1767 p h) (sat_cons (step1770 p h) (sat_cons (step1863 p h) (sat_cons (step1811 p h) (sat_cons (step1819 p h) (sat_cons (step1788 p h) (sat_cons (step1789 p h) (sat_cons (step1858 p h) (sat_cons (step1773 p h) (sat_cons (step1825 p h) (sat_cons (step2403 p h) (sat_cons (step1828 p h) (sat_cons (step1765 p h) (sat_cons (step1822 p h) (sat_cons (step1820 p h) (sat_cons (step2296 p h) (sat_cons (step1803 p h) (sat_cons (step1813 p h) (sat_cons (step1814 p h) (sat_cons (step1815 p h) (sat_cons (step928 p h) (sat_cons (step1801 p h) (sat_cons (step966 p h) (sat_cons (step921 p h) (sat_cons (step933 p h) (sat_nil p)))))))))))))))))))))))))))
def c2517 : List Lit := [(1750, true), (107, false), (120, true)]
theorem step2517 (p : Nat → Bool) (h : Constraints p) : clause p c2517 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1819, c2152, c2403, c1828, c1798, c884, c1803, c1800] c2517 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1819 p h) (sat_cons (step2152 p h) (sat_cons (step2403 p h) (sat_cons (step1828 p h) (sat_cons (step1798 p h) (sat_cons (step884 p h) (sat_cons (step1803 p h) (sat_cons (step1800 p h) (sat_nil p))))))))))
def c2518 : List Lit := [(1714, false), (1737, false), (1727, true), (1761, true), (120, true)]
theorem step2518 (p : Nat → Bool) (h : Constraints p) : clause p c2518 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1787, c1788, c1853, c1772, c1829, c1765, c1822, c1820, c1813, c1814, c1815, c968, c2490, c921, c1274, c938, c1277, c1268, c2357, c1270] c2518 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1787 p h) (sat_cons (step1788 p h) (sat_cons (step1853 p h) (sat_cons (step1772 p h) (sat_cons (step1829 p h) (sat_cons (step1765 p h) (sat_cons (step1822 p h) (sat_cons (step1820 p h) (sat_cons (step1813 p h) (sat_cons (step1814 p h) (sat_cons (step1815 p h) (sat_cons (step968 p h) (sat_cons (step2490 p h) (sat_cons (step921 p h) (sat_cons (step1274 p h) (sat_cons (step938 p h) (sat_cons (step1277 p h) (sat_cons (step1268 p h) (sat_cons (step2357 p h) (sat_cons (step1270 p h) (sat_nil p))))))))))))))))))))))
def c2519 : List Lit := [(102, false), (122, false), (123, false), (119, false)]
theorem step2519 (p : Nat → Bool) (h : Constraints p) : clause p c2519 = true :=
  Snake9.LocalRup.prove_clause [c968, c2490, c921, c1274, c938, c1277, c1268, c2357, c1270] c2519 (by decide) p (sat_cons (step968 p h) (sat_cons (step2490 p h) (sat_cons (step921 p h) (sat_cons (step1274 p h) (sat_cons (step938 p h) (sat_cons (step1277 p h) (sat_cons (step1268 p h) (sat_cons (step2357 p h) (sat_cons (step1270 p h) (sat_nil p))))))))))
def c2520 : List Lit := [(1746, true), (97, true), (98, false), (1722, true), (120, true)]
theorem step2520 (p : Nat → Bool) (h : Constraints p) : clause p c2520 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1822, c1820, c1813, c1814, c1815, c2519, c1765, c1773, c1768, c867, c2143] c2520 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1822 p h) (sat_cons (step1820 p h) (sat_cons (step1813 p h) (sat_cons (step1814 p h) (sat_cons (step1815 p h) (sat_cons (step2519 p h) (sat_cons (step1765 p h) (sat_cons (step1773 p h) (sat_cons (step1768 p h) (sat_cons (step867 p h) (sat_cons (step2143 p h) (sat_nil p)))))))))))))
def c2521 : List Lit := [(1709, true), (101, true), (116, true), (102, false)]
theorem step2521 (p : Nat → Bool) (h : Constraints p) : clause p c2521 = true :=
  Snake9.LocalRup.prove_clause [c1750, c1751, c2456, c809, c1227, c854, c1236, c1239, c2351, c1243, c1248] c2521 (by decide) p (sat_cons (step1750 p h) (sat_cons (step1751 p h) (sat_cons (step2456 p h) (sat_cons (step809 p h) (sat_cons (step1227 p h) (sat_cons (step854 p h) (sat_cons (step1236 p h) (sat_cons (step1239 p h) (sat_cons (step2351 p h) (sat_cons (step1243 p h) (sat_cons (step1248 p h) (sat_nil p))))))))))))
def c2522 : List Lit := [(124, true), (116, true), (122, false), (119, false)]
theorem step2522 (p : Nat → Bool) (h : Constraints p) : clause p c2522 = true :=
  Snake9.LocalRup.prove_clause [c938, c957, c1268, c1274, c1270, c1277, c2357] c2522 (by decide) p (sat_cons (step938 p h) (sat_cons (step957 p h) (sat_cons (step1268 p h) (sat_cons (step1274 p h) (sat_cons (step1270 p h) (sat_cons (step1277 p h) (sat_cons (step2357 p h) (sat_nil p))))))))
def c2523 : List Lit := [(110, true), (109, true), (111, false), (235, true), (115, true)]
theorem step2523 (p : Nat → Bool) (h : Constraints p) : clause p c2523 = true :=
  Snake9.LocalRup.prove_clause [c890, c893, c2303, c1992] c2523 (by decide) p (sat_cons (step890 p h) (sat_cons (step893 p h) (sat_cons (step2303 p h) (sat_cons (step1992 p h) (sat_nil p)))))
end B112E089
