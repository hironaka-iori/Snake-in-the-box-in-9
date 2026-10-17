import B112E052Part0047
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c5062 : List Lit := [(35, true), (3, false), (1624, true)]
theorem step5062 (p : Nat → Bool) (h : Constraints p) : clause p c5062 = true :=
  Snake9.LocalRup.prove_clause [c5061, c1376, c1350, c1347, c1348, c1349, c158, c1373, c1358, c1364] c5062 (by decide) p (sat_cons (step5061 p h) (sat_cons (step1376 p h) (sat_cons (step1350 p h) (sat_cons (step1347 p h) (sat_cons (step1348 p h) (sat_cons (step1349 p h) (sat_cons (step158 p h) (sat_cons (step1373 p h) (sat_cons (step1358 p h) (sat_cons (step1364 p h) (sat_nil p)))))))))))
def c5063 : List Lit := [(3, false), (1624, true)]
theorem step5063 (p : Nat → Bool) (h : Constraints p) : clause p c5063 = true :=
  Snake9.LocalRup.prove_clause [c5061, c2612, c1343, c1370, c1367, c5062, c2519, c2691, c1373, c1349, c1346, c158, c1358, c1359, c1365, c192, c1361] c5063 (by decide) p (sat_cons (step5061 p h) (sat_cons (step2612 p h) (sat_cons (step1343 p h) (sat_cons (step1370 p h) (sat_cons (step1367 p h) (sat_cons (step5062 p h) (sat_cons (step2519 p h) (sat_cons (step2691 p h) (sat_cons (step1373 p h) (sat_cons (step1349 p h) (sat_cons (step1346 p h) (sat_cons (step158 p h) (sat_cons (step1358 p h) (sat_cons (step1359 p h) (sat_cons (step1365 p h) (sat_cons (step192 p h) (sat_cons (step1361 p h) (sat_nil p))))))))))))))))))
def c5064 : List Lit := [(8, true), (1565, true), (1543, false), (7, true)]
theorem step5064 (p : Nat → Bool) (h : Constraints p) : clause p c5064 = true :=
  Snake9.LocalRup.prove_clause [c2212, c1044, c1048, c1051, c2397, c1037, c1036, c1035, c17, c1038, c1032, c1031, c2030, c11, c2034, c2204, c1270, c1250, c1255] c5064 (by decide) p (sat_cons (step2212 p h) (sat_cons (step1044 p h) (sat_cons (step1048 p h) (sat_cons (step1051 p h) (sat_cons (step2397 p h) (sat_cons (step1037 p h) (sat_cons (step1036 p h) (sat_cons (step1035 p h) (sat_cons (step17 p h) (sat_cons (step1038 p h) (sat_cons (step1032 p h) (sat_cons (step1031 p h) (sat_cons (step2030 p h) (sat_cons (step11 p h) (sat_cons (step2034 p h) (sat_cons (step2204 p h) (sat_cons (step1270 p h) (sat_cons (step1250 p h) (sat_cons (step1255 p h) (sat_nil p))))))))))))))))))))
def c5065 : List Lit := [(1624, true), (1548, true)]
theorem step5065 (p : Nat → Bool) (h : Constraints p) : clause p c5065 = true :=
  Snake9.LocalRup.prove_clause [c4858, c5063, c1248, c1247, c1254] c5065 (by decide) p (sat_cons (step4858 p h) (sat_cons (step5063 p h) (sat_cons (step1248 p h) (sat_cons (step1247 p h) (sat_cons (step1254 p h) (sat_nil p))))))
def c5066 : List Lit := [(1597, false), (1641, false), (1814, false), (1624, false), (1712, false), (90, false)]
theorem step5066 (p : Nat → Bool) (h : Constraints p) : clause p c5066 = true :=
  Snake9.LocalRup.prove_clause [c5049, c1407, c1415, c1444, c1850, c2470, c1500, c1499, c1445, c2469, c1416, c1419, c1856, c1410, c1393, c1395, c1402, c1390, c1391, c1387, c259, c2513, c3196, c1585, c5053, c2630] c5066 (by decide) p (sat_cons (step5049 p h) (sat_cons (step1407 p h) (sat_cons (step1415 p h) (sat_cons (step1444 p h) (sat_cons (step1850 p h) (sat_cons (step2470 p h) (sat_cons (step1500 p h) (sat_cons (step1499 p h) (sat_cons (step1445 p h) (sat_cons (step2469 p h) (sat_cons (step1416 p h) (sat_cons (step1419 p h) (sat_cons (step1856 p h) (sat_cons (step1410 p h) (sat_cons (step1393 p h) (sat_cons (step1395 p h) (sat_cons (step1402 p h) (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step1387 p h) (sat_cons (step259 p h) (sat_cons (step2513 p h) (sat_cons (step3196 p h) (sat_cons (step1585 p h) (sat_cons (step5053 p h) (sat_cons (step2630 p h) (sat_nil p)))))))))))))))))))))))))))
def c5067 : List Lit := [(1648, true), (1748, true), (1641, false), (1712, false), (90, false)]
theorem step5067 (p : Nat → Bool) (h : Constraints p) : clause p c5067 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1416, c1419, c1410, c1393, c1395, c1402, c1390, c1391, c1387, c259, c2513, c3196, c1585, c5053, c2630] c5067 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1416 p h) (sat_cons (step1419 p h) (sat_cons (step1410 p h) (sat_cons (step1393 p h) (sat_cons (step1395 p h) (sat_cons (step1402 p h) (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step1387 p h) (sat_cons (step259 p h) (sat_cons (step2513 p h) (sat_cons (step3196 p h) (sat_cons (step1585 p h) (sat_cons (step5053 p h) (sat_cons (step2630 p h) (sat_nil p)))))))))))))))))
def c5068 : List Lit := [(1644, true), (1748, true), (62, true), (1562, true), (77, true)]
theorem step5068 (p : Nat → Bool) (h : Constraints p) : clause p c5068 = true :=
  Snake9.LocalRup.prove_clause [c1405, c2037, c1251, c1248, c1264, c2034, c2030, c1408, c1410, c1406, c1402, c5059, c2676, c2129, c1548, c1533, c5060, c1540, c2531, c2056, c1658, c1567, c2677, c1558, c1535, c1536, c1550, c4878, c373] c5068 (by decide) p (sat_cons (step1405 p h) (sat_cons (step2037 p h) (sat_cons (step1251 p h) (sat_cons (step1248 p h) (sat_cons (step1264 p h) (sat_cons (step2034 p h) (sat_cons (step2030 p h) (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1406 p h) (sat_cons (step1402 p h) (sat_cons (step5059 p h) (sat_cons (step2676 p h) (sat_cons (step2129 p h) (sat_cons (step1548 p h) (sat_cons (step1533 p h) (sat_cons (step5060 p h) (sat_cons (step1540 p h) (sat_cons (step2531 p h) (sat_cons (step2056 p h) (sat_cons (step1658 p h) (sat_cons (step1567 p h) (sat_cons (step2677 p h) (sat_cons (step1558 p h) (sat_cons (step1535 p h) (sat_cons (step1536 p h) (sat_cons (step1550 p h) (sat_cons (step4878 p h) (sat_cons (step373 p h) (sat_nil p))))))))))))))))))))))))))))))
def c5069 : List Lit := [(1796, true), (80, true), (46, false), (122, true)]
theorem step5069 (p : Nat → Bool) (h : Constraints p) : clause p c5069 = true :=
  Snake9.LocalRup.prove_clause [c2781, c3324] c5069 (by decide) p (sat_cons (step2781 p h) (sat_cons (step3324 p h) (sat_nil p)))
def c5070 : List Lit := [(1647, true), (1749, true), (1712, false), (90, false)]
theorem step5070 (p : Nat → Bool) (h : Constraints p) : clause p c5070 = true :=
  Snake9.LocalRup.prove_clause [c1418, c2494, c3168, c5054, c1393, c2956, c1587, c1391, c490] c5070 (by decide) p (sat_cons (step1418 p h) (sat_cons (step2494 p h) (sat_cons (step3168 p h) (sat_cons (step5054 p h) (sat_cons (step1393 p h) (sat_cons (step2956 p h) (sat_cons (step1587 p h) (sat_cons (step1391 p h) (sat_cons (step490 p h) (sat_nil p))))))))))
def c5071 : List Lit := [(1800, true), (122, true), (80, true)]
theorem step5071 (p : Nat → Bool) (h : Constraints p) : clause p c5071 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1758, c1765, c1769, c1761, c1759, c1742, c1752, c1739, c4814] c5071 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1758 p h) (sat_cons (step1765 p h) (sat_cons (step1769 p h) (sat_cons (step1761 p h) (sat_cons (step1759 p h) (sat_cons (step1742 p h) (sat_cons (step1752 p h) (sat_cons (step1739 p h) (sat_cons (step4814 p h) (sat_nil p)))))))))))
def c5072 : List Lit := [(1799, true), (80, true)]
theorem step5072 (p : Nat → Bool) (h : Constraints p) : clause p c5072 = true :=
  Snake9.LocalRup.prove_clause [c1764, c1768, c1756, c1758, c1742, c1750, c1739, c4814] c5072 (by decide) p (sat_cons (step1764 p h) (sat_cons (step1768 p h) (sat_cons (step1756 p h) (sat_cons (step1758 p h) (sat_cons (step1742 p h) (sat_cons (step1750 p h) (sat_cons (step1739 p h) (sat_cons (step4814 p h) (sat_nil p)))))))))
def c5073 : List Lit := [(1795, true), (124, false), (46, false)]
theorem step5073 (p : Nat → Bool) (h : Constraints p) : clause p c5073 = true :=
  Snake9.LocalRup.prove_clause [c1756, c1758, c1753, c1750, c942] c5073 (by decide) p (sat_cons (step1756 p h) (sat_cons (step1758 p h) (sat_cons (step1753 p h) (sat_cons (step1750 p h) (sat_cons (step942 p h) (sat_nil p))))))
def c5074 : List Lit := [(94, false), (102, false), (51, false), (53, false), (54, false)]
theorem step5074 (p : Nat → Bool) (h : Constraints p) : clause p c5074 = true :=
  Snake9.LocalRup.prove_clause [c557, c246, c2656] c5074 (by decide) p (sat_cons (step557 p h) (sat_cons (step246 p h) (sat_cons (step2656 p h) (sat_nil p))))
def c5075 : List Lit := [(1801, true), (105, true), (1796, true), (122, true)]
theorem step5075 (p : Nat → Bool) (h : Constraints p) : clause p c5075 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1759, c1753, c2108, c1754, c2384, c1758, c1774, c4104, c1747, c1737, c1738, c1745, c881, c1740] c5075 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1759 p h) (sat_cons (step1753 p h) (sat_cons (step2108 p h) (sat_cons (step1754 p h) (sat_cons (step2384 p h) (sat_cons (step1758 p h) (sat_cons (step1774 p h) (sat_cons (step4104 p h) (sat_cons (step1747 p h) (sat_cons (step1737 p h) (sat_cons (step1738 p h) (sat_cons (step1745 p h) (sat_cons (step881 p h) (sat_cons (step1740 p h) (sat_nil p))))))))))))))))
def c5076 : List Lit := [(123, false), (120, false), (8, false), (1793, true), (1697, false), (1714, true)]
theorem step5076 (p : Nat → Bool) (h : Constraints p) : clause p c5076 = true :=
  Snake9.LocalRup.prove_clause [c4814, c410, c408, c2654] c5076 (by decide) p (sat_cons (step4814 p h) (sat_cons (step410 p h) (sat_cons (step408 p h) (sat_cons (step2654 p h) (sat_nil p)))))
def c5077 : List Lit := [(122, true), (127, false), (1796, true), (46, false), (96, false)]
theorem step5077 (p : Nat → Bool) (h : Constraints p) : clause p c5077 = true :=
  Snake9.LocalRup.prove_clause [c2807, c2781, c2108, c1972, c2388] c5077 (by decide) p (sat_cons (step2807 p h) (sat_cons (step2781 p h) (sat_cons (step2108 p h) (sat_cons (step1972 p h) (sat_cons (step2388 p h) (sat_nil p))))))
def c5078 : List Lit := [(122, false), (1779, true), (1761, false), (1770, false), (101, false), (90, false)]
theorem step5078 (p : Nat → Bool) (h : Constraints p) : clause p c5078 = true :=
  Snake9.LocalRup.prove_clause [c686, c689, c1685, c1699, c1694, c1709, c1725] c5078 (by decide) p (sat_cons (step686 p h) (sat_cons (step689 p h) (sat_cons (step1685 p h) (sat_cons (step1699 p h) (sat_cons (step1694 p h) (sat_cons (step1709 p h) (sat_cons (step1725 p h) (sat_nil p))))))))
def c5079 : List Lit := [(1796, true), (122, true), (46, false), (96, false)]
theorem step5079 (p : Nat → Bool) (h : Constraints p) : clause p c5079 = true :=
  Snake9.LocalRup.prove_clause [c1751, c5077, c1759, c1753] c5079 (by decide) p (sat_cons (step1751 p h) (sat_cons (step5077 p h) (sat_cons (step1759 p h) (sat_cons (step1753 p h) (sat_nil p)))))
def c5080 : List Lit := [(1681, true), (1586, false), (30, true), (1647, false), (46, false)]
theorem step5080 (p : Nat → Bool) (h : Constraints p) : clause p c5080 = true :=
  Snake9.LocalRup.prove_clause [c2046, c1344, c2612, c1444, c1351, c1508, c1500, c1326, c1451, c2037, c2838, c1374, c1251, c1253, c1345, c1248, c1247, c4853, c2701, c2691] c5080 (by decide) p (sat_cons (step2046 p h) (sat_cons (step1344 p h) (sat_cons (step2612 p h) (sat_cons (step1444 p h) (sat_cons (step1351 p h) (sat_cons (step1508 p h) (sat_cons (step1500 p h) (sat_cons (step1326 p h) (sat_cons (step1451 p h) (sat_cons (step2037 p h) (sat_cons (step2838 p h) (sat_cons (step1374 p h) (sat_cons (step1251 p h) (sat_cons (step1253 p h) (sat_cons (step1345 p h) (sat_cons (step1248 p h) (sat_cons (step1247 p h) (sat_cons (step4853 p h) (sat_cons (step2701 p h) (sat_cons (step2691 p h) (sat_nil p)))))))))))))))))))))
def c5081 : List Lit := [(1625, true), (37, false), (30, true), (46, false)]
theorem step5081 (p : Nat → Bool) (h : Constraints p) : clause p c5081 = true :=
  Snake9.LocalRup.prove_clause [c1344, c2838, c1345, c152, c151, c1358, c1346, c1364, c1352, c1377] c5081 (by decide) p (sat_cons (step1344 p h) (sat_cons (step2838 p h) (sat_cons (step1345 p h) (sat_cons (step152 p h) (sat_cons (step151 p h) (sat_cons (step1358 p h) (sat_cons (step1346 p h) (sat_cons (step1364 p h) (sat_cons (step1352 p h) (sat_cons (step1377 p h) (sat_nil p)))))))))))
def c5082 : List Lit := [(103, false), (106, false), (96, false), (1796, false), (1811, true)]
theorem step5082 (p : Nat → Bool) (h : Constraints p) : clause p c5082 = true :=
  Snake9.LocalRup.prove_clause [c759, c756, c1699, c1689, c2941, c1691] c5082 (by decide) p (sat_cons (step759 p h) (sat_cons (step756 p h) (sat_cons (step1699 p h) (sat_cons (step1689 p h) (sat_cons (step2941 p h) (sat_cons (step1691 p h) (sat_nil p)))))))
def c5083 : List Lit := [(106, false), (96, false), (1796, false), (1768, true), (1811, true)]
theorem step5083 (p : Nat → Bool) (h : Constraints p) : clause p c5083 = true :=
  Snake9.LocalRup.prove_clause [c5082, c1700, c1701, c2941, c757, c1691, c1689] c5083 (by decide) p (sat_cons (step5082 p h) (sat_cons (step1700 p h) (sat_cons (step1701 p h) (sat_cons (step2941 p h) (sat_cons (step757 p h) (sat_cons (step1691 p h) (sat_cons (step1689 p h) (sat_nil p))))))))
def c5084 : List Lit := [(44, true), (1585, true), (88, true), (101, true)]
theorem step5084 (p : Nat → Bool) (h : Constraints p) : clause p c5084 = true :=
  Snake9.LocalRup.prove_clause [c2423, c1282, c2619, c1304, c2634, c2547, c1274, c1275, c1273, c70, c2216] c5084 (by decide) p (sat_cons (step2423 p h) (sat_cons (step1282 p h) (sat_cons (step2619 p h) (sat_cons (step1304 p h) (sat_cons (step2634 p h) (sat_cons (step2547 p h) (sat_cons (step1274 p h) (sat_cons (step1275 p h) (sat_cons (step1273 p h) (sat_cons (step70 p h) (sat_cons (step2216 p h) (sat_nil p))))))))))))
def c5085 : List Lit := [(114, false), (92, false), (102, false), (1572, true), (87, true), (88, true)]
theorem step5085 (p : Nat → Bool) (h : Constraints p) : clause p c5085 = true :=
  Snake9.LocalRup.prove_clause [c551, c571, c1275, c2084, c1280, c1271] c5085 (by decide) p (sat_cons (step551 p h) (sat_cons (step571 p h) (sat_cons (step1275 p h) (sat_cons (step2084 p h) (sat_cons (step1280 p h) (sat_cons (step1271 p h) (sat_nil p)))))))
def c5086 : List Lit := [(17, false), (20, false), (88, true)]
theorem step5086 (p : Nat → Bool) (h : Constraints p) : clause p c5086 = true :=
  Snake9.LocalRup.prove_clause [c2216, c2217, c1921] c5086 (by decide) p (sat_cons (step2216 p h) (sat_cons (step2217 p h) (sat_cons (step1921 p h) (sat_nil p))))
def c5087 : List Lit := [(95, false), (92, false), (102, false), (1572, true), (88, true)]
theorem step5087 (p : Nat → Bool) (h : Constraints p) : clause p c5087 = true :=
  Snake9.LocalRup.prove_clause [c549, c2603, c1275] c5087 (by decide) p (sat_cons (step549 p h) (sat_cons (step2603 p h) (sat_cons (step1275 p h) (sat_nil p))))
def c5088 : List Lit := [(18, true), (1572, true), (88, true)]
theorem step5088 (p : Nat → Bool) (h : Constraints p) : clause p c5088 = true :=
  Snake9.LocalRup.prove_clause [c1278, c1275, c1276, c1280, c5086, c1271] c5088 (by decide) p (sat_cons (step1278 p h) (sat_cons (step1275 p h) (sat_cons (step1276 p h) (sat_cons (step1280 p h) (sat_cons (step5086 p h) (sat_cons (step1271 p h) (sat_nil p)))))))
def c5089 : List Lit := [(1567, true), (92, false), (1585, true), (88, true)]
theorem step5089 (p : Nat → Bool) (h : Constraints p) : clause p c5089 = true :=
  Snake9.LocalRup.prove_clause [c2423, c5088, c2619, c1304, c1271, c1272, c2216, c2196, c2213, c53] c5089 (by decide) p (sat_cons (step2423 p h) (sat_cons (step5088 p h) (sat_cons (step2619 p h) (sat_cons (step1304 p h) (sat_cons (step1271 p h) (sat_cons (step1272 p h) (sat_cons (step2216 p h) (sat_cons (step2196 p h) (sat_cons (step2213 p h) (sat_cons (step53 p h) (sat_nil p)))))))))))
def c5090 : List Lit := [(1802, false), (1771, false), (106, true), (1836, true), (1722, false), (101, true), (1730, false), (91, true), (1584, false)]
theorem step5090 (p : Nat → Bool) (h : Constraints p) : clause p c5090 = true :=
  Snake9.LocalRup.prove_clause [c1713, c1596, c1606, c2787, c1869, c1800, c1793, c1718, c1868, c1876, c2777, c2470, c1598, c4637, c1609, c2545] c5090 (by decide) p (sat_cons (step1713 p h) (sat_cons (step1596 p h) (sat_cons (step1606 p h) (sat_cons (step2787 p h) (sat_cons (step1869 p h) (sat_cons (step1800 p h) (sat_cons (step1793 p h) (sat_cons (step1718 p h) (sat_cons (step1868 p h) (sat_cons (step1876 p h) (sat_cons (step2777 p h) (sat_cons (step2470 p h) (sat_cons (step1598 p h) (sat_cons (step4637 p h) (sat_cons (step1609 p h) (sat_cons (step2545 p h) (sat_nil p)))))))))))))))))
def c5091 : List Lit := [(1751, true), (1734, false), (1722, false)]
theorem step5091 (p : Nat → Bool) (h : Constraints p) : clause p c5091 = true :=
  Snake9.LocalRup.prove_clause [c2457, c2545, c1633, c2599, c1595] c5091 (by decide) p (sat_cons (step2457 p h) (sat_cons (step2545 p h) (sat_cons (step1633 p h) (sat_cons (step2599 p h) (sat_cons (step1595 p h) (sat_nil p))))))
def c5092 : List Lit := [(1796, true), (1811, true), (106, false), (122, true), (100, false), (99, false)]
theorem step5092 (p : Nat → Bool) (h : Constraints p) : clause p c5092 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1758, c1764, c1811, c1759, c1753, c1754, c758, c2134, c1686, c1710, c1714, c1724, c1799, c1694, c5075, c1688, c726] c5092 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1758 p h) (sat_cons (step1764 p h) (sat_cons (step1811 p h) (sat_cons (step1759 p h) (sat_cons (step1753 p h) (sat_cons (step1754 p h) (sat_cons (step758 p h) (sat_cons (step2134 p h) (sat_cons (step1686 p h) (sat_cons (step1710 p h) (sat_cons (step1714 p h) (sat_cons (step1724 p h) (sat_cons (step1799 p h) (sat_cons (step1694 p h) (sat_cons (step5075 p h) (sat_cons (step1688 p h) (sat_cons (step726 p h) (sat_nil p)))))))))))))))))))
def c5093 : List Lit := [(1768, false), (1796, false), (1811, true)]
theorem step5093 (p : Nat → Bool) (h : Constraints p) : clause p c5093 = true :=
  Snake9.LocalRup.prove_clause [c1765, c1805, c1715, c1711, c1710, c1702, c1714, c2917, c1799, c1770] c5093 (by decide) p (sat_cons (step1765 p h) (sat_cons (step1805 p h) (sat_cons (step1715 p h) (sat_cons (step1711 p h) (sat_cons (step1710 p h) (sat_cons (step1702 p h) (sat_cons (step1714 p h) (sat_cons (step2917 p h) (sat_cons (step1799 p h) (sat_cons (step1770 p h) (sat_nil p)))))))))))
def c5094 : List Lit := [(1767, true), (106, false), (100, false)]
theorem step5094 (p : Nat → Bool) (h : Constraints p) : clause p c5094 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1700, c762] c5094 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1700 p h) (sat_cons (step762 p h) (sat_nil p))))
def c5095 : List Lit := [(1811, true), (1796, false), (1767, false), (106, false)]
theorem step5095 (p : Nat → Bool) (h : Constraints p) : clause p c5095 = true :=
  Snake9.LocalRup.prove_clause [c5093, c2941, c5083, c1693, c1686] c5095 (by decide) p (sat_cons (step5093 p h) (sat_cons (step2941 p h) (sat_cons (step5083 p h) (sat_cons (step1693 p h) (sat_cons (step1686 p h) (sat_nil p))))))
def c5096 : List Lit := [(121, true), (120, false), (123, false)]
theorem step5096 (p : Nat → Bool) (h : Constraints p) : clause p c5096 = true :=
  Snake9.LocalRup.prove_clause [c2374, c2372, c1988] c5096 (by decide) p (sat_cons (step2374 p h) (sat_cons (step2372 p h) (sat_cons (step1988 p h) (sat_nil p))))
def c5097 : List Lit := [(97, true), (231, true), (105, true), (103, true), (107, true), (102, false)]
theorem step5097 (p : Nat → Bool) (h : Constraints p) : clause p c5097 = true :=
  Snake9.LocalRup.prove_clause [c2342, c2344, c717, c1968] c5097 (by decide) p (sat_cons (step2342 p h) (sat_cons (step2344 p h) (sat_cons (step717 p h) (sat_cons (step1968 p h) (sat_nil p)))))
def c5098 : List Lit := [(92, false), (1734, true), (90, true), (114, false), (102, false)]
theorem step5098 (p : Nat → Bool) (h : Constraints p) : clause p c5098 = true :=
  Snake9.LocalRup.prove_clause [c567, c2080, c1598, c1609] c5098 (by decide) p (sat_cons (step567 p h) (sat_cons (step2080 p h) (sat_cons (step1598 p h) (sat_cons (step1609 p h) (sat_nil p)))))
def c5099 : List Lit := [(92, true), (231, true), (116, true), (105, true), (114, false), (118, false), (103, true), (107, true), (102, false)]
theorem step5099 (p : Nat → Bool) (h : Constraints p) : clause p c5099 = true :=
  Snake9.LocalRup.prove_clause [c2343, c2365, c717, c866] c5099 (by decide) p (sat_cons (step2343 p h) (sat_cons (step2365 p h) (sat_cons (step717 p h) (sat_cons (step866 p h) (sat_nil p)))))
def c5100 : List Lit := [(1749, true), (1734, false), (1712, false)]
theorem step5100 (p : Nat → Bool) (h : Constraints p) : clause p c5100 = true :=
  Snake9.LocalRup.prove_clause [c1613, c1645, c1652, c1618, c2062, c1590] c5100 (by decide) p (sat_cons (step1613 p h) (sat_cons (step1645 p h) (sat_cons (step1652 p h) (sat_cons (step1618 p h) (sat_cons (step2062 p h) (sat_cons (step1590 p h) (sat_nil p)))))))
def c5101 : List Lit := [(114, false), (1712, false), (146, true), (176, true), (182, true), (1730, false), (94, true), (53, true), (17, true), (1721, false), (92, false), (1624, false), (102, false), (1811, false)]
theorem step5101 (p : Nat → Bool) (h : Constraints p) : clause p c5101 = true :=
  Snake9.LocalRup.prove_clause [c567, c561, c551, c1596, c4518, c2723, c1606, c1446, c2046, c3350, c1501, c1859, c2471] c5101 (by decide) p (sat_cons (step567 p h) (sat_cons (step561 p h) (sat_cons (step551 p h) (sat_cons (step1596 p h) (sat_cons (step4518 p h) (sat_cons (step2723 p h) (sat_cons (step1606 p h) (sat_cons (step1446 p h) (sat_cons (step2046 p h) (sat_cons (step3350 p h) (sat_cons (step1501 p h) (sat_cons (step1859 p h) (sat_cons (step2471 p h) (sat_nil p))))))))))))))
def c5102 : List Lit := [(1813, true), (1802, false), (114, true), (113, false), (90, false), (1768, false), (1796, false)]
theorem step5102 (p : Nat → Bool) (h : Constraints p) : clause p c5102 = true :=
  Snake9.LocalRup.prove_clause [c1710, c1714, c1801, c1807, c1780, c1715, c4948, c1711, c1702] c5102 (by decide) p (sat_cons (step1710 p h) (sat_cons (step1714 p h) (sat_cons (step1801 p h) (sat_cons (step1807 p h) (sat_cons (step1780 p h) (sat_cons (step1715 p h) (sat_cons (step4948 p h) (sat_cons (step1711 p h) (sat_cons (step1702 p h) (sat_nil p))))))))))
def c5103 : List Lit := [(90, false), (92, false), (1836, true), (1624, false), (103, true), (89, true), (107, true), (1763, true), (1811, false), (1796, false), (100, false)]
theorem step5103 (p : Nat → Bool) (h : Constraints p) : clause p c5103 = true :=
  Snake9.TreeRup.prove_clause [c1701, c1693, c1685, c1691, c1688, c2124, c2097, c684, c2322, c1585, c2341, c2325, c508, c642, c639, c485, c495, c2342, c5097, c1391, c1968, c1197, c1601, c1200, c1603, c1206, c1207, c1235, c1238, c2421, c1135, c1137, c1130, c1081, c1083, c1127, c1079, c1055, c1112, c1113, c1068, c1051, c1111, c1109, c1061, c1048, c1110, c1108, c1060, c1044, c2212, c3973, c3196, c5101, c1738, c1747, c1775, c5102, c1855, c1861, c2470, c2956, c3350, c1587, c1606, c2192, c1596, c1445, c544, c1500, c2723, c2046] c5103 (by decide) p (sat_cons (step1701 p h) (sat_cons (step1693 p h) (sat_cons (step1685 p h) (sat_cons (step1691 p h) (sat_cons (step1688 p h) (sat_cons (step2124 p h) (sat_cons (step2097 p h) (sat_cons (step684 p h) (sat_cons (step2322 p h) (sat_cons (step1585 p h) (sat_cons (step2341 p h) (sat_cons (step2325 p h) (sat_cons (step508 p h) (sat_cons (step642 p h) (sat_cons (step639 p h) (sat_cons (step485 p h) (sat_cons (step495 p h) (sat_cons (step2342 p h) (sat_cons (step5097 p h) (sat_cons (step1391 p h) (sat_cons (step1968 p h) (sat_cons (step1197 p h) (sat_cons (step1601 p h) (sat_cons (step1200 p h) (sat_cons (step1603 p h) (sat_cons (step1206 p h) (sat_cons (step1207 p h) (sat_cons (step1235 p h) (sat_cons (step1238 p h) (sat_cons (step2421 p h) (sat_cons (step1135 p h) (sat_cons (step1137 p h) (sat_cons (step1130 p h) (sat_cons (step1081 p h) (sat_cons (step1083 p h) (sat_cons (step1127 p h) (sat_cons (step1079 p h) (sat_cons (step1055 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step1068 p h) (sat_cons (step1051 p h) (sat_cons (step1111 p h) (sat_cons (step1109 p h) (sat_cons (step1061 p h) (sat_cons (step1048 p h) (sat_cons (step1110 p h) (sat_cons (step1108 p h) (sat_cons (step1060 p h) (sat_cons (step1044 p h) (sat_cons (step2212 p h) (sat_cons (step3973 p h) (sat_cons (step3196 p h) (sat_cons (step5101 p h) (sat_cons (step1738 p h) (sat_cons (step1747 p h) (sat_cons (step1775 p h) (sat_cons (step5102 p h) (sat_cons (step1855 p h) (sat_cons (step1861 p h) (sat_cons (step2470 p h) (sat_cons (step2956 p h) (sat_cons (step3350 p h) (sat_cons (step1587 p h) (sat_cons (step1606 p h) (sat_cons (step2192 p h) (sat_cons (step1596 p h) (sat_cons (step1445 p h) (sat_cons (step544 p h) (sat_cons (step1500 p h) (sat_cons (step2723 p h) (sat_cons (step2046 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c5104 : List Lit := [(94, true), (1733, true), (90, true), (92, false), (102, false)]
theorem step5104 (p : Nat → Bool) (h : Constraints p) : clause p c5104 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1606, c1600, c1601, c1608, c565, c1598] c5104 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1606 p h) (sat_cons (step1600 p h) (sat_cons (step1601 p h) (sat_cons (step1608 p h) (sat_cons (step565 p h) (sat_cons (step1598 p h) (sat_nil p))))))))
def c5105 : List Lit := [(1733, true), (90, true), (102, false), (92, false)]
theorem step5105 (p : Nat → Bool) (h : Constraints p) : clause p c5105 = true :=
  Snake9.LocalRup.prove_clause [c5104, c568, c563, c1599, c1598, c1608] c5105 (by decide) p (sat_cons (step5104 p h) (sat_cons (step568 p h) (sat_cons (step563 p h) (sat_cons (step1599 p h) (sat_cons (step1598 p h) (sat_cons (step1608 p h) (sat_nil p)))))))
def c5106 : List Lit := [(1748, true), (1712, false), (1733, false)]
theorem step5106 (p : Nat → Bool) (h : Constraints p) : clause p c5106 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1644, c1651, c1617, c2062, c1590] c5106 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1644 p h) (sat_cons (step1651 p h) (sat_cons (step1617 p h) (sat_cons (step2062 p h) (sat_cons (step1590 p h) (sat_nil p)))))))
def c5107 : List Lit := [(1572, true), (88, true), (1734, true), (90, true), (92, false), (102, false)]
theorem step5107 (p : Nat → Bool) (h : Constraints p) : clause p c5107 = true :=
  Snake9.LocalRup.prove_clause [c5088, c5087, c544, c547, c1598, c1601, c1609] c5107 (by decide) p (sat_cons (step5088 p h) (sat_cons (step5087 p h) (sat_cons (step544 p h) (sat_cons (step547 p h) (sat_cons (step1598 p h) (sat_cons (step1601 p h) (sat_cons (step1609 p h) (sat_nil p))))))))
def c5108 : List Lit := [(91, false), (1721, true), (96, false)]
theorem step5108 (p : Nat → Bool) (h : Constraints p) : clause p c5108 = true :=
  Snake9.LocalRup.prove_clause [c1586, c4866, c574] c5108 (by decide) p (sat_cons (step1586 p h) (sat_cons (step4866 p h) (sat_cons (step574 p h) (sat_nil p))))
def c5109 : List Lit := [(1586, false), (1648, false), (1633, false), (1682, true), (1643, false), (30, true)]
theorem step5109 (p : Nat → Bool) (h : Constraints p) : clause p c5109 = true :=
  Snake9.LocalRup.prove_clause [c1344, c2612, c1445, c1509, c1351, c2046, c1326, c1501, c2037, c1446, c1452, c1251, c1253, c1424, c2838, c1374, c1248, c1247, c1396, c1345, c4853, c1388, c2691, c2701] c5109 (by decide) p (sat_cons (step1344 p h) (sat_cons (step2612 p h) (sat_cons (step1445 p h) (sat_cons (step1509 p h) (sat_cons (step1351 p h) (sat_cons (step2046 p h) (sat_cons (step1326 p h) (sat_cons (step1501 p h) (sat_cons (step2037 p h) (sat_cons (step1446 p h) (sat_cons (step1452 p h) (sat_cons (step1251 p h) (sat_cons (step1253 p h) (sat_cons (step1424 p h) (sat_cons (step2838 p h) (sat_cons (step1374 p h) (sat_cons (step1248 p h) (sat_cons (step1247 p h) (sat_cons (step1396 p h) (sat_cons (step1345 p h) (sat_cons (step4853 p h) (sat_cons (step1388 p h) (sat_cons (step2691 p h) (sat_cons (step2701 p h) (sat_nil p)))))))))))))))))))))))))
def c5110 : List Lit := [(1681, true), (1649, false), (1634, false), (1659, false), (1643, false), (1584, false), (30, true)]
theorem step5110 (p : Nat → Bool) (h : Constraints p) : clause p c5110 = true :=
  Snake9.LocalRup.prove_clause [c2044, c1344, c2612, c1351, c1486, c1493, c1447, c1453, c1324, c1429, c2838, c1374, c2037, c1397, c1345, c1251, c1253, c1388, c1248, c1247, c4853, c2701, c2691] c5110 (by decide) p (sat_cons (step2044 p h) (sat_cons (step1344 p h) (sat_cons (step2612 p h) (sat_cons (step1351 p h) (sat_cons (step1486 p h) (sat_cons (step1493 p h) (sat_cons (step1447 p h) (sat_cons (step1453 p h) (sat_cons (step1324 p h) (sat_cons (step1429 p h) (sat_cons (step2838 p h) (sat_cons (step1374 p h) (sat_cons (step2037 p h) (sat_cons (step1397 p h) (sat_cons (step1345 p h) (sat_cons (step1251 p h) (sat_cons (step1253 p h) (sat_cons (step1388 p h) (sat_cons (step1248 p h) (sat_cons (step1247 p h) (sat_cons (step4853 p h) (sat_cons (step2701 p h) (sat_cons (step2691 p h) (sat_nil p))))))))))))))))))))))))
def c5111 : List Lit := [(1634, false), (1681, true), (1643, false), (30, true), (1584, false)]
theorem step5111 (p : Nat → Bool) (h : Constraints p) : clause p c5111 = true :=
  Snake9.LocalRup.prove_clause [c1344, c2612, c1394, c1424, c1446, c5110] c5111 (by decide) p (sat_cons (step1344 p h) (sat_cons (step2612 p h) (sat_cons (step1394 p h) (sat_cons (step1424 p h) (sat_cons (step1446 p h) (sat_cons (step5110 p h) (sat_nil p)))))))
def c5112 : List Lit := [(1571, true), (99, false), (53, false)]
theorem step5112 (p : Nat → Bool) (h : Constraints p) : clause p c5112 = true :=
  Snake9.LocalRup.prove_clause [c1279, c2619, c1271, c478] c5112 (by decide) p (sat_cons (step1279 p h) (sat_cons (step2619 p h) (sat_cons (step1271 p h) (sat_cons (step478 p h) (sat_nil p)))))
def c5113 : List Lit := [(44, true), (33, false), (1625, true), (1607, false)]
theorem step5113 (p : Nat → Bool) (h : Constraints p) : clause p c5113 = true :=
  Snake9.LocalRup.prove_clause [c1351, c1374, c2691, c1347, c1352, c1377, c1363, c1364, c1361, c1358, c2252, c137] c5113 (by decide) p (sat_cons (step1351 p h) (sat_cons (step1374 p h) (sat_cons (step2691 p h) (sat_cons (step1347 p h) (sat_cons (step1352 p h) (sat_cons (step1377 p h) (sat_cons (step1363 p h) (sat_cons (step1364 p h) (sat_cons (step1361 p h) (sat_cons (step1358 p h) (sat_cons (step2252 p h) (sat_cons (step137 p h) (sat_nil p)))))))))))))
def c5114 : List Lit := [(35, true), (1625, true), (30, true)]
theorem step5114 (p : Nat → Bool) (h : Constraints p) : clause p c5114 = true :=
  Snake9.LocalRup.prove_clause [c1344, c2838, c1345, c5113, c4853, c2212, c1044, c1048, c1051, c1055, c1083, c2407, c1132, c1102, c1100, c1095, c1094, c4604, c1347, c1352, c4654, c1377, c197, c198, c1364, c1934, c1358, c2253, c137] c5114 (by decide) p (sat_cons (step1344 p h) (sat_cons (step2838 p h) (sat_cons (step1345 p h) (sat_cons (step5113 p h) (sat_cons (step4853 p h) (sat_cons (step2212 p h) (sat_cons (step1044 p h) (sat_cons (step1048 p h) (sat_cons (step1051 p h) (sat_cons (step1055 p h) (sat_cons (step1083 p h) (sat_cons (step2407 p h) (sat_cons (step1132 p h) (sat_cons (step1102 p h) (sat_cons (step1100 p h) (sat_cons (step1095 p h) (sat_cons (step1094 p h) (sat_cons (step4604 p h) (sat_cons (step1347 p h) (sat_cons (step1352 p h) (sat_cons (step4654 p h) (sat_cons (step1377 p h) (sat_cons (step197 p h) (sat_cons (step198 p h) (sat_cons (step1364 p h) (sat_cons (step1934 p h) (sat_cons (step1358 p h) (sat_cons (step2253 p h) (sat_cons (step137 p h) (sat_nil p))))))))))))))))))))))))))))))
def c5115 : List Lit := [(1763, false), (1812, true), (113, false), (108, true), (35, false), (1796, false), (124, false), (46, false)]
theorem step5115 (p : Nat → Bool) (h : Constraints p) : clause p c5115 = true :=
  Snake9.LocalRup.prove_clause [c2593, c1770, c1806, c1703, c1705, c1718, c1719, c1800, c1706, c1708, c1775, c1704, c1700, c1743, c833, c937, c1741] c5115 (by decide) p (sat_cons (step2593 p h) (sat_cons (step1770 p h) (sat_cons (step1806 p h) (sat_cons (step1703 p h) (sat_cons (step1705 p h) (sat_cons (step1718 p h) (sat_cons (step1719 p h) (sat_cons (step1800 p h) (sat_cons (step1706 p h) (sat_cons (step1708 p h) (sat_cons (step1775 p h) (sat_cons (step1704 p h) (sat_cons (step1700 p h) (sat_cons (step1743 p h) (sat_cons (step833 p h) (sat_cons (step937 p h) (sat_cons (step1741 p h) (sat_nil p))))))))))))))))))
def c5116 : List Lit := [(103, false), (99, false), (102, false), (1803, true), (113, false), (252, true), (122, true), (124, false), (35, false), (46, false)]
theorem step5116 (p : Nat → Bool) (h : Constraints p) : clause p c5116 = true :=
  Snake9.LocalRup.prove_clause [c2593, c1772, c938, c939, c2769, c937, c1752, c955, c1753, c726, c2384, c1762, c1776, c1743, c2525, c1741, c881] c5116 (by decide) p (sat_cons (step2593 p h) (sat_cons (step1772 p h) (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step2769 p h) (sat_cons (step937 p h) (sat_cons (step1752 p h) (sat_cons (step955 p h) (sat_cons (step1753 p h) (sat_cons (step726 p h) (sat_cons (step2384 p h) (sat_cons (step1762 p h) (sat_cons (step1776 p h) (sat_cons (step1743 p h) (sat_cons (step2525 p h) (sat_cons (step1741 p h) (sat_cons (step881 p h) (sat_nil p))))))))))))))))))
def c5117 : List Lit := [(1812, true), (113, false), (252, true), (108, true), (122, true), (124, false), (35, false), (46, false)]
theorem step5117 (p : Nat → Bool) (h : Constraints p) : clause p c5117 = true :=
  Snake9.LocalRup.prove_clause [c2781, c2593, c1770, c1703, c1705, c1713, c1794, c1806, c5115, c1715, c1691, c1693, c1688, c1685, c5116, c1700, c1709, c1708, c1704, c1714, c833, c832, c1800, c1740, c1737, c1775, c1745] c5117 (by decide) p (sat_cons (step2781 p h) (sat_cons (step2593 p h) (sat_cons (step1770 p h) (sat_cons (step1703 p h) (sat_cons (step1705 p h) (sat_cons (step1713 p h) (sat_cons (step1794 p h) (sat_cons (step1806 p h) (sat_cons (step5115 p h) (sat_cons (step1715 p h) (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step1688 p h) (sat_cons (step1685 p h) (sat_cons (step5116 p h) (sat_cons (step1700 p h) (sat_cons (step1709 p h) (sat_cons (step1708 p h) (sat_cons (step1704 p h) (sat_cons (step1714 p h) (sat_cons (step833 p h) (sat_cons (step832 p h) (sat_cons (step1800 p h) (sat_cons (step1740 p h) (sat_cons (step1737 p h) (sat_cons (step1775 p h) (sat_cons (step1745 p h) (sat_nil p))))))))))))))))))))))))))))
def c5118 : List Lit := [(118, true), (1788, true), (113, false), (246, true), (248, true), (108, true), (122, true), (124, false), (35, false), (46, false)]
theorem step5118 (p : Nat → Bool) (h : Constraints p) : clause p c5118 = true :=
  Snake9.LocalRup.prove_clause [c1743, c1740, c1741, c1745, c940, c1737, c898, c832, c2374, c909] c5118 (by decide) p (sat_cons (step1743 p h) (sat_cons (step1740 p h) (sat_cons (step1741 p h) (sat_cons (step1745 p h) (sat_cons (step940 p h) (sat_cons (step1737 p h) (sat_cons (step898 p h) (sat_cons (step832 p h) (sat_cons (step2374 p h) (sat_cons (step909 p h) (sat_nil p)))))))))))
def c5119 : List Lit := [(1788, true), (113, false), (46, false), (246, true), (248, true), (108, true), (122, true), (124, false), (35, false)]
theorem step5119 (p : Nat → Bool) (h : Constraints p) : clause p c5119 = true :=
  Snake9.LocalRup.prove_clause [c5118, c835, c833, c1737, c909, c1745, c1739, c940, c2374, c898] c5119 (by decide) p (sat_cons (step5118 p h) (sat_cons (step835 p h) (sat_cons (step833 p h) (sat_cons (step1737 p h) (sat_cons (step909 p h) (sat_cons (step1745 p h) (sat_cons (step1739 p h) (sat_cons (step940 p h) (sat_cons (step2374 p h) (sat_cons (step898 p h) (sat_nil p)))))))))))
def c5120 : List Lit := [(120, false), (121, true), (246, true), (108, true), (124, false), (46, false)]
theorem step5120 (p : Nat → Bool) (h : Constraints p) : clause p c5120 = true :=
  Snake9.LocalRup.prove_clause [c940, c2374, c898] c5120 (by decide) p (sat_cons (step940 p h) (sat_cons (step2374 p h) (sat_cons (step898 p h) (sat_nil p))))
def c5121 : List Lit := [(42, true), (34, true), (168, true), (1620, true)]
theorem step5121 (p : Nat → Bool) (h : Constraints p) : clause p c5121 = true :=
  Snake9.LocalRup.prove_clause [c1357, c168, c1365, c2253, c1361] c5121 (by decide) p (sat_cons (step1357 p h) (sat_cons (step168 p h) (sat_cons (step1365 p h) (sat_cons (step2253 p h) (sat_cons (step1361 p h) (sat_nil p))))))
def c5122 : List Lit := [(1813, false), (1712, false), (1599, false), (1624, false)]
theorem step5122 (p : Nat → Bool) (h : Constraints p) : clause p c5122 = true :=
  Snake9.LocalRup.prove_clause [c5049, c1443, c1515, c2470, c1849, c2471, c1516, c1444, c1855, c4656] c5122 (by decide) p (sat_cons (step5049 p h) (sat_cons (step1443 p h) (sat_cons (step1515 p h) (sat_cons (step2470 p h) (sat_cons (step1849 p h) (sat_cons (step2471 p h) (sat_cons (step1516 p h) (sat_cons (step1444 p h) (sat_cons (step1855 p h) (sat_cons (step4656 p h) (sat_nil p)))))))))))
def c5123 : List Lit := [(118, false), (1599, false), (1802, false), (113, false), (252, true), (108, true), (122, true), (124, false), (35, false), (46, false), (1624, false)]
theorem step5123 (p : Nat → Bool) (h : Constraints p) : clause p c5123 = true :=
  Snake9.LocalRup.prove_clause [c826, c833, c1535, c1704, c2078, c1706, c1714, c5122, c1801, c1807, c1715, c1719, c1709, c1691, c1693, c1700, c1688, c1685, c5116] c5123 (by decide) p (sat_cons (step826 p h) (sat_cons (step833 p h) (sat_cons (step1535 p h) (sat_cons (step1704 p h) (sat_cons (step2078 p h) (sat_cons (step1706 p h) (sat_cons (step1714 p h) (sat_cons (step5122 p h) (sat_cons (step1801 p h) (sat_cons (step1807 p h) (sat_cons (step1715 p h) (sat_cons (step1719 p h) (sat_cons (step1709 p h) (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step1700 p h) (sat_cons (step1688 p h) (sat_cons (step1685 p h) (sat_cons (step5116 p h) (sat_nil p))))))))))))))))))))
def c5124 : List Lit := [(1770, false), (1777, true), (1813, true), (113, false), (252, true), (122, true), (124, false), (35, false), (46, false)]
theorem step5124 (p : Nat → Bool) (h : Constraints p) : clause p c5124 = true :=
  Snake9.LocalRup.prove_clause [c1715, c1706, c1709, c1714, c1719, c1700, c1801, c1691, c1693, c1688, c1685, c5116] c5124 (by decide) p (sat_cons (step1715 p h) (sat_cons (step1706 p h) (sat_cons (step1709 p h) (sat_cons (step1714 p h) (sat_cons (step1719 p h) (sat_cons (step1700 p h) (sat_cons (step1801 p h) (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step1688 p h) (sat_cons (step1685 p h) (sat_cons (step5116 p h) (sat_nil p)))))))))))))
def c5125 : List Lit := [(103, false), (1783, false), (1804, true), (118, true), (122, true), (124, false), (46, false)]
theorem step5125 (p : Nat → Bool) (h : Constraints p) : clause p c5125 = true :=
  Snake9.LocalRup.prove_clause [c938, c939, c937, c1752, c1753, c1741, c1762, c1746, c1781] c5125 (by decide) p (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step937 p h) (sat_cons (step1752 p h) (sat_cons (step1753 p h) (sat_cons (step1741 p h) (sat_cons (step1762 p h) (sat_cons (step1746 p h) (sat_cons (step1781 p h) (sat_nil p))))))))))
end B112E052
