import B112E089Part0005
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2396 : List Lit := [(1758, true), (1737, false)]
theorem step2396 (p : Nat → Bool) (h : Constraints p) : clause p c2396 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1841, c1845, c1828, c1778, c1817, c1819, c2162, c1772, c1815, c1812, c921, c1765] c2396 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1841 p h) (sat_cons (step1845 p h) (sat_cons (step1828 p h) (sat_cons (step1778 p h) (sat_cons (step1817 p h) (sat_cons (step1819 p h) (sat_cons (step2162 p h) (sat_cons (step1772 p h) (sat_cons (step1815 p h) (sat_cons (step1812 p h) (sat_cons (step921 p h) (sat_cons (step1765 p h) (sat_nil p))))))))))))))
def c2397 : List Lit := [(1745, true), (124, false)]
theorem step2397 (p : Nat → Bool) (h : Constraints p) : clause p c2397 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1819, c2162, c1815, c1812, c2010] c2397 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1819 p h) (sat_cons (step2162 p h) (sat_cons (step1815 p h) (sat_cons (step1812 p h) (sat_cons (step2010 p h) (sat_nil p)))))))
def c2398 : List Lit := [(1725, true), (43, true), (220, true)]
theorem step2398 (p : Nat → Bool) (h : Constraints p) : clause p c2398 = true :=
  Snake9.LocalRup.prove_clause [c1778, c1782, c1772, c1758, c1765, c1750, c1751, c809, c830] c2398 (by decide) p (sat_cons (step1778 p h) (sat_cons (step1782 p h) (sat_cons (step1772 p h) (sat_cons (step1758 p h) (sat_cons (step1765 p h) (sat_cons (step1750 p h) (sat_cons (step1751 p h) (sat_cons (step809 p h) (sat_cons (step830 p h) (sat_nil p))))))))))
def c2399 : List Lit := [(55, true), (46, true), (50, false), (174, true)]
theorem step2399 (p : Nat → Bool) (h : Constraints p) : clause p c2399 = true :=
  Snake9.LocalRup.prove_clause [c351, c350, c2221, c1979] c2399 (by decide) p (sat_cons (step351 p h) (sat_cons (step350 p h) (sat_cons (step2221 p h) (sat_cons (step1979 p h) (sat_nil p)))))
def c2400 : List Lit := [(487, true), (1726, true), (1737, true), (49, true)]
theorem step2400 (p : Nat → Bool) (h : Constraints p) : clause p c2400 = true :=
  Snake9.LocalRup.prove_clause [c1779, c1289, c1291, c1284, c1250, c1281, c1248, c1272, c1242, c1266, c1241, c2088, c1767, c1770, c1773, c1783, c1764, c1765, c1756, c862, c1753, c848] c2400 (by decide) p (sat_cons (step1779 p h) (sat_cons (step1289 p h) (sat_cons (step1291 p h) (sat_cons (step1284 p h) (sat_cons (step1250 p h) (sat_cons (step1281 p h) (sat_cons (step1248 p h) (sat_cons (step1272 p h) (sat_cons (step1242 p h) (sat_cons (step1266 p h) (sat_cons (step1241 p h) (sat_cons (step2088 p h) (sat_cons (step1767 p h) (sat_cons (step1770 p h) (sat_cons (step1773 p h) (sat_cons (step1783 p h) (sat_cons (step1764 p h) (sat_cons (step1765 p h) (sat_cons (step1756 p h) (sat_cons (step862 p h) (sat_cons (step1753 p h) (sat_cons (step848 p h) (sat_nil p)))))))))))))))))))))))
def c2401 : List Lit := [(1719, false), (1726, true), (220, true), (43, true)]
theorem step2401 (p : Nat → Bool) (h : Constraints p) : clause p c2401 = true :=
  Snake9.LocalRup.prove_clause [c1779, c1770, c1773, c1783, c1765, c1758, c1750, c1751, c830, c809] c2401 (by decide) p (sat_cons (step1779 p h) (sat_cons (step1770 p h) (sat_cons (step1773 p h) (sat_cons (step1783 p h) (sat_cons (step1765 p h) (sat_cons (step1758 p h) (sat_cons (step1750 p h) (sat_cons (step1751 p h) (sat_cons (step830 p h) (sat_cons (step809 p h) (sat_nil p)))))))))))
def c2402 : List Lit := [(109, false), (90, false), (237, true), (107, false), (113, false)]
theorem step2402 (p : Nat → Bool) (h : Constraints p) : clause p c2402 = true :=
  Snake9.LocalRup.prove_clause [c873, c871, c904] c2402 (by decide) p (sat_cons (step873 p h) (sat_cons (step871 p h) (sat_cons (step904 p h) (sat_nil p))))
def c2403 : List Lit := [(1750, true), (120, true), (110, true)]
theorem step2403 (p : Nat → Bool) (h : Constraints p) : clause p c2403 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1819, c1825, c1828, c1822, c1820, c1803, c1813, c1814, c1800, c928, c925] c2403 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1819 p h) (sat_cons (step1825 p h) (sat_cons (step1828 p h) (sat_cons (step1822 p h) (sat_cons (step1820 p h) (sat_cons (step1803 p h) (sat_cons (step1813 p h) (sat_cons (step1814 p h) (sat_cons (step1800 p h) (sat_cons (step928 p h) (sat_cons (step925 p h) (sat_nil p)))))))))))))
def c2404 : List Lit := [(1717, true), (101, false), (99, false)]
theorem step2404 (p : Nat → Bool) (h : Constraints p) : clause p c2404 = true :=
  Snake9.LocalRup.prove_clause [c1764, c1765, c848] c2404 (by decide) p (sat_cons (step1764 p h) (sat_cons (step1765 p h) (sat_cons (step848 p h) (sat_nil p))))
def c2405 : List Lit := [(1602, false), (1616, true), (75, false), (158, true)]
theorem step2405 (p : Nat → Bool) (h : Constraints p) : clause p c2405 = true :=
  Snake9.LocalRup.prove_clause [c2099, c1445, c1520, c1491, c1527, c1496, c1450, c2155, c2101] c2405 (by decide) p (sat_cons (step2099 p h) (sat_cons (step1445 p h) (sat_cons (step1520 p h) (sat_cons (step1491 p h) (sat_cons (step1527 p h) (sat_cons (step1496 p h) (sat_cons (step1450 p h) (sat_cons (step2155 p h) (sat_cons (step2101 p h) (sat_nil p))))))))))
def c2406 : List Lit := [(1616, true), (1576, false), (1601, false), (75, false), (158, true)]
theorem step2406 (p : Nat → Bool) (h : Constraints p) : clause p c2406 = true :=
  Snake9.LocalRup.prove_clause [c2099, c1446, c1490, c1534, c1527, c1451, c1495, c2101, c2155] c2406 (by decide) p (sat_cons (step2099 p h) (sat_cons (step1446 p h) (sat_cons (step1490 p h) (sat_cons (step1534 p h) (sat_cons (step1527 p h) (sat_cons (step1451 p h) (sat_cons (step1495 p h) (sat_cons (step2101 p h) (sat_cons (step2155 p h) (sat_nil p))))))))))
def c2407 : List Lit := [(1606, true), (56, true), (1601, false), (1598, false), (45, false), (174, true)]
theorem step2407 (p : Nat → Bool) (h : Constraints p) : clause p c2407 = true :=
  Snake9.LocalRup.prove_clause [c1491, c1495, c1487, c1467, c1469, c1477, c1465, c1461, c1462, c380, c351, c318] c2407 (by decide) p (sat_cons (step1491 p h) (sat_cons (step1495 p h) (sat_cons (step1487 p h) (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_cons (step1477 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step380 p h) (sat_cons (step351 p h) (sat_cons (step318 p h) (sat_nil p)))))))))))))
def c2408 : List Lit := [(1687, true), (1680, false)]
theorem step2408 (p : Nat → Bool) (h : Constraints p) : clause p c2408 = true :=
  Snake9.LocalRup.prove_clause [c1667, c1676, c1680, c1670, c1653, c2097, c1651] c2408 (by decide) p (sat_cons (step1667 p h) (sat_cons (step1676 p h) (sat_cons (step1680 p h) (sat_cons (step1670 p h) (sat_cons (step1653 p h) (sat_cons (step2097 p h) (sat_cons (step1651 p h) (sat_nil p))))))))
def c2409 : List Lit := [(1542, true), (27, true), (153, true)]
theorem step2409 (p : Nat → Bool) (h : Constraints p) : clause p c2409 = true :=
  Snake9.LocalRup.prove_clause [c1357, c1359, c1368, c1372, c1360, c1362, c1345, c1358, c1353, c1343, c2131] c2409 (by decide) p (sat_cons (step1357 p h) (sat_cons (step1359 p h) (sat_cons (step1368 p h) (sat_cons (step1372 p h) (sat_cons (step1360 p h) (sat_cons (step1362 p h) (sat_cons (step1345 p h) (sat_cons (step1358 p h) (sat_cons (step1353 p h) (sat_cons (step1343 p h) (sat_cons (step2131 p h) (sat_nil p))))))))))))
def c2410 : List Lit := [(1527, false), (1538, false), (1553, true), (275, true)]
theorem step2410 (p : Nat → Bool) (h : Constraints p) : clause p c2410 = true :=
  Snake9.LocalRup.prove_clause [c2364, c1378, c1063, c1035, c1034, c1033, c2128, c1061, c1058, c1043, c1040, c1345, c1348, c1373, c1340, c1394, c2136, c1329, c1318] c2410 (by decide) p (sat_cons (step2364 p h) (sat_cons (step1378 p h) (sat_cons (step1063 p h) (sat_cons (step1035 p h) (sat_cons (step1034 p h) (sat_cons (step1033 p h) (sat_cons (step2128 p h) (sat_cons (step1061 p h) (sat_cons (step1058 p h) (sat_cons (step1043 p h) (sat_cons (step1040 p h) (sat_cons (step1345 p h) (sat_cons (step1348 p h) (sat_cons (step1373 p h) (sat_cons (step1340 p h) (sat_cons (step1394 p h) (sat_cons (step2136 p h) (sat_cons (step1329 p h) (sat_cons (step1318 p h) (sat_nil p))))))))))))))))))))
def c2411 : List Lit := [(24, true), (1543, true), (1538, true), (153, true)]
theorem step2411 (p : Nat → Bool) (h : Constraints p) : clause p c2411 = true :=
  Snake9.LocalRup.prove_clause [c1364, c1354, c1355, c1361, c1362, c1377, c1356, c1346, c174, c2131, c106, c1344] c2411 (by decide) p (sat_cons (step1364 p h) (sat_cons (step1354 p h) (sat_cons (step1355 p h) (sat_cons (step1361 p h) (sat_cons (step1362 p h) (sat_cons (step1377 p h) (sat_cons (step1356 p h) (sat_cons (step1346 p h) (sat_cons (step174 p h) (sat_cons (step2131 p h) (sat_cons (step106 p h) (sat_cons (step1344 p h) (sat_nil p)))))))))))))
def c2412 : List Lit := [(25, false), (29, false), (1528, true), (153, true)]
theorem step2412 (p : Nat → Bool) (h : Constraints p) : clause p c2412 = true :=
  Snake9.LocalRup.prove_clause [c174, c2131, c106, c1344] c2412 (by decide) p (sat_cons (step174 p h) (sat_cons (step2131 p h) (sat_cons (step106 p h) (sat_cons (step1344 p h) (sat_nil p)))))
def c2413 : List Lit := [(29, false), (1527, true), (153, true)]
theorem step2413 (p : Nat → Bool) (h : Constraints p) : clause p c2413 = true :=
  Snake9.LocalRup.prove_clause [c1343, c1342, c174, c104] c2413 (by decide) p (sat_cons (step1343 p h) (sat_cons (step1342 p h) (sat_cons (step174 p h) (sat_cons (step104 p h) (sat_nil p)))))
def c2414 : List Lit := [(79, false), (1520, true), (92, true), (203, true)]
theorem step2414 (p : Nat → Bool) (h : Constraints p) : clause p c2414 = true :=
  Snake9.LocalRup.prove_clause [c764, c2112] c2414 (by decide) p (sat_cons (step764 p h) (sat_cons (step2112 p h) (sat_nil p)))
def c2415 : List Lit := [(24, false), (1651, true), (63, false), (113, false)]
theorem step2415 (p : Nat → Bool) (h : Constraints p) : clause p c2415 = true :=
  Snake9.LocalRup.prove_clause [c510, c509, c1608] c2415 (by decide) p (sat_cons (step510 p h) (sat_cons (step509 p h) (sat_cons (step1608 p h) (sat_nil p))))
def c2416 : List Lit := [(24, true), (153, true), (1553, true), (1538, true), (275, true)]
theorem step2416 (p : Nat → Bool) (h : Constraints p) : clause p c2416 = true :=
  Snake9.LocalRup.prove_clause [c2364, c1364, c1063, c1035, c1034, c1033, c2128, c1061, c1058, c1043, c1040, c1354, c2411, c1355, c1361, c1362, c1394, c1381, c1356, c1329, c2412, c1318, c1349, c2136, c1340] c2416 (by decide) p (sat_cons (step2364 p h) (sat_cons (step1364 p h) (sat_cons (step1063 p h) (sat_cons (step1035 p h) (sat_cons (step1034 p h) (sat_cons (step1033 p h) (sat_cons (step2128 p h) (sat_cons (step1061 p h) (sat_cons (step1058 p h) (sat_cons (step1043 p h) (sat_cons (step1040 p h) (sat_cons (step1354 p h) (sat_cons (step2411 p h) (sat_cons (step1355 p h) (sat_cons (step1361 p h) (sat_cons (step1362 p h) (sat_cons (step1394 p h) (sat_cons (step1381 p h) (sat_cons (step1356 p h) (sat_cons (step1329 p h) (sat_cons (step2412 p h) (sat_cons (step1318 p h) (sat_cons (step1349 p h) (sat_cons (step2136 p h) (sat_cons (step1340 p h) (sat_nil p))))))))))))))))))))))))))
def c2417 : List Lit := [(1615, true), (1568, false), (1598, false), (56, true)]
theorem step2417 (p : Nat → Bool) (h : Constraints p) : clause p c2417 = true :=
  Snake9.LocalRup.prove_clause [c1445, c1475, c1484, c1490, c1526, c1519, c1446, c1491, c1495, c1487, c1467, c1477, c1464, c2157] c2417 (by decide) p (sat_cons (step1445 p h) (sat_cons (step1475 p h) (sat_cons (step1484 p h) (sat_cons (step1490 p h) (sat_cons (step1526 p h) (sat_cons (step1519 p h) (sat_cons (step1446 p h) (sat_cons (step1491 p h) (sat_cons (step1495 p h) (sat_cons (step1487 p h) (sat_cons (step1467 p h) (sat_cons (step1477 p h) (sat_cons (step1464 p h) (sat_cons (step2157 p h) (sat_nil p)))))))))))))))
def c2418 : List Lit := [(1606, true), (1576, true), (1598, false), (56, true)]
theorem step2418 (p : Nat → Bool) (h : Constraints p) : clause p c2418 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1484, c1491, c1495, c1487, c1467, c1477, c1464, c2157] c2418 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1484 p h) (sat_cons (step1491 p h) (sat_cons (step1495 p h) (sat_cons (step1487 p h) (sat_cons (step1467 p h) (sat_cons (step1477 p h) (sat_cons (step1464 p h) (sat_cons (step2157 p h) (sat_nil p))))))))))
def c2419 : List Lit := [(1760, true), (1749, false), (241, true), (455, true), (103, true), (1576, true), (111, false)]
theorem step2419 (p : Nat → Bool) (h : Constraints p) : clause p c2419 = true :=
  Snake9.LocalRup.prove_clause [c1764, c1772, c2293, c1435, c1428, c1427, c1433, c1430, c270, c1431, c1857, c2160, c1780, c1788, c927, c1774, c2092, c884, c1769] c2419 (by decide) p (sat_cons (step1764 p h) (sat_cons (step1772 p h) (sat_cons (step2293 p h) (sat_cons (step1435 p h) (sat_cons (step1428 p h) (sat_cons (step1427 p h) (sat_cons (step1433 p h) (sat_cons (step1430 p h) (sat_cons (step270 p h) (sat_cons (step1431 p h) (sat_cons (step1857 p h) (sat_cons (step2160 p h) (sat_cons (step1780 p h) (sat_cons (step1788 p h) (sat_cons (step927 p h) (sat_cons (step1774 p h) (sat_cons (step2092 p h) (sat_cons (step884 p h) (sat_cons (step1769 p h) (sat_nil p))))))))))))))))))))
def c2420 : List Lit := [(69, true), (62, true), (68, false), (1667, true), (1657, false), (45, false)]
theorem step2420 (p : Nat → Bool) (h : Constraints p) : clause p c2420 = true :=
  Snake9.LocalRup.prove_clause [c2147, c1612, c1640, c1626, c1614, c1616, c1623, c615, c613, c1644, c1608, c1613] c2420 (by decide) p (sat_cons (step2147 p h) (sat_cons (step1612 p h) (sat_cons (step1640 p h) (sat_cons (step1626 p h) (sat_cons (step1614 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step615 p h) (sat_cons (step613 p h) (sat_cons (step1644 p h) (sat_cons (step1608 p h) (sat_cons (step1613 p h) (sat_nil p)))))))))))))
def c2421 : List Lit := [(74, true), (23, true), (52, true), (51, false), (40, true), (32, false)]
theorem step2421 (p : Nat → Bool) (h : Constraints p) : clause p c2421 = true :=
  Snake9.LocalRup.prove_clause [c357, c189, c1129, c1093, c1132, c1094, c1134, c1100, c1152, c1123, c2337] c2421 (by decide) p (sat_cons (step357 p h) (sat_cons (step189 p h) (sat_cons (step1129 p h) (sat_cons (step1093 p h) (sat_cons (step1132 p h) (sat_cons (step1094 p h) (sat_cons (step1134 p h) (sat_cons (step1100 p h) (sat_cons (step1152 p h) (sat_cons (step1123 p h) (sat_cons (step2337 p h) (sat_nil p))))))))))))
def c2422 : List Lit := [(155, true), (30, true), (31, false), (34, false)]
theorem step2422 (p : Nat → Bool) (h : Constraints p) : clause p c2422 = true :=
  Snake9.LocalRup.prove_clause [c182, c180, c1964] c2422 (by decide) p (sat_cons (step182 p h) (sat_cons (step180 p h) (sat_cons (step1964 p h) (sat_nil p))))
def c2423 : List Lit := [(13, true), (135, true), (1513, true), (14, true)]
theorem step2423 (p : Nat → Bool) (h : Constraints p) : clause p c2423 = true :=
  Snake9.LocalRup.prove_clause [c2178, c1317, c65] c2423 (by decide) p (sat_cons (step2178 p h) (sat_cons (step1317 p h) (sat_cons (step65 p h) (sat_nil p))))
def c2424 : List Lit := [(79, true), (1691, true), (1671, false), (85, true), (211, true), (1680, false)]
theorem step2424 (p : Nat → Bool) (h : Constraints p) : clause p c2424 = true :=
  Snake9.LocalRup.prove_clause [c1651, c2272, c1659, c783, c1692, c1663, c1673] c2424 (by decide) p (sat_cons (step1651 p h) (sat_cons (step2272 p h) (sat_cons (step1659 p h) (sat_cons (step783 p h) (sat_cons (step1692 p h) (sat_cons (step1663 p h) (sat_cons (step1673 p h) (sat_nil p))))))))
def c2425 : List Lit := [(1542, true), (153, true), (25, false), (1529, false)]
theorem step2425 (p : Nat → Bool) (h : Constraints p) : clause p c2425 = true :=
  Snake9.LocalRup.prove_clause [c1376, c1372, c1346, c1359, c2412, c1356] c2425 (by decide) p (sat_cons (step1376 p h) (sat_cons (step1372 p h) (sat_cons (step1346 p h) (sat_cons (step1359 p h) (sat_cons (step2412 p h) (sat_cons (step1356 p h) (sat_nil p)))))))
def c2426 : List Lit := [(27, false), (26, true), (151, true), (1569, true), (39, true)]
theorem step2426 (p : Nat → Bool) (h : Constraints p) : clause p c2426 = true :=
  Snake9.LocalRup.prove_clause [c2117, c163] c2426 (by decide) p (sat_cons (step2117 p h) (sat_cons (step163 p h) (sat_nil p)))
def c2427 : List Lit := [(74, true), (25, false), (52, true), (51, false), (40, true), (31, false), (32, false), (34, false)]
theorem step2427 (p : Nat → Bool) (h : Constraints p) : clause p c2427 = true :=
  Snake9.LocalRup.prove_clause [c357, c2421, c1129, c2194, c1132, c1134, c1152, c1155, c2337, c2338, c1123, c1088, c1100, c1084, c1095, c1080, c2422, c1077, c2207, c1076, c174] c2427 (by decide) p (sat_cons (step357 p h) (sat_cons (step2421 p h) (sat_cons (step1129 p h) (sat_cons (step2194 p h) (sat_cons (step1132 p h) (sat_cons (step1134 p h) (sat_cons (step1152 p h) (sat_cons (step1155 p h) (sat_cons (step2337 p h) (sat_cons (step2338 p h) (sat_cons (step1123 p h) (sat_cons (step1088 p h) (sat_cons (step1100 p h) (sat_cons (step1084 p h) (sat_cons (step1095 p h) (sat_cons (step1080 p h) (sat_cons (step2422 p h) (sat_cons (step1077 p h) (sat_cons (step2207 p h) (sat_cons (step1076 p h) (sat_cons (step174 p h) (sat_nil p))))))))))))))))))))))
def c2428 : List Lit := [(1507, true), (1576, true)]
theorem step2428 (p : Nat → Bool) (h : Constraints p) : clause p c2428 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1428, c1427, c1433, c1430, c270, c1307, c1309, c2128, c1304, c1305, c1033, c28, c7, c1034, c49, c1035, c1038, c2320, c1045, c1058] c2428 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1428 p h) (sat_cons (step1427 p h) (sat_cons (step1433 p h) (sat_cons (step1430 p h) (sat_cons (step270 p h) (sat_cons (step1307 p h) (sat_cons (step1309 p h) (sat_cons (step2128 p h) (sat_cons (step1304 p h) (sat_cons (step1305 p h) (sat_cons (step1033 p h) (sat_cons (step28 p h) (sat_cons (step7 p h) (sat_cons (step1034 p h) (sat_cons (step49 p h) (sat_cons (step1035 p h) (sat_cons (step1038 p h) (sat_cons (step2320 p h) (sat_cons (step1045 p h) (sat_cons (step1058 p h) (sat_nil p))))))))))))))))))))))
def c2429 : List Lit := [(74, false), (1671, true), (51, false), (32, false)]
theorem step2429 (p : Nat → Bool) (h : Constraints p) : clause p c2429 = true :=
  Snake9.LocalRup.prove_clause [c684, c683, c1649] c2429 (by decide) p (sat_cons (step684 p h) (sat_cons (step683 p h) (sat_cons (step1649 p h) (sat_nil p))))
def c2430 : List Lit := [(69, false), (193, true), (75, true), (74, true), (1592, true), (57, true)]
theorem step2430 (p : Nat → Bool) (h : Constraints p) : clause p c2430 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1465, c1469, c1461, c1462, c318, c2141, c338, c641, c640, c645, c2250] c2430 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1465 p h) (sat_cons (step1469 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step318 p h) (sat_cons (step2141 p h) (sat_cons (step338 p h) (sat_cons (step641 p h) (sat_cons (step640 p h) (sat_cons (step645 p h) (sat_cons (step2250 p h) (sat_nil p)))))))))))))
def c2431 : List Lit := [(1749, true)]
theorem step2431 (p : Nat → Bool) (h : Constraints p) : clause p c2431 = true :=
  Snake9.LocalRup.prove_clause [c1824, c1827, c2138, c1803] c2431 (by decide) p (sat_cons (step1824 p h) (sat_cons (step1827 p h) (sat_cons (step2138 p h) (sat_cons (step1803 p h) (sat_nil p)))))
def c2432 : List Lit := [(1757, true)]
theorem step2432 (p : Nat → Bool) (h : Constraints p) : clause p c2432 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1840] c2432 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1840 p h) (sat_nil p)))
def c2433 : List Lit := [(35, true), (28, true), (34, false), (31, false)]
theorem step2433 (p : Nat → Bool) (h : Constraints p) : clause p c2433 = true :=
  Snake9.LocalRup.prove_clause [c181, c200, c1095, c1097, c2326, c1098] c2433 (by decide) p (sat_cons (step181 p h) (sat_cons (step200 p h) (sat_cons (step1095 p h) (sat_cons (step1097 p h) (sat_cons (step2326 p h) (sat_cons (step1098 p h) (sat_nil p)))))))
def c2434 : List Lit := [(1650, true), (188, true), (68, true), (43, true), (41, false)]
theorem step2434 (p : Nat → Bool) (h : Constraints p) : clause p c2434 = true :=
  Snake9.LocalRup.prove_clause [c1606, c1607, c540, c518] c2434 (by decide) p (sat_cons (step1606 p h) (sat_cons (step1607 p h) (sat_cons (step540 p h) (sat_cons (step518 p h) (sat_nil p)))))
def c2435 : List Lit := [(1737, true), (66, false), (67, false), (62, true), (120, true), (41, false)]
theorem step2435 (p : Nat → Bool) (h : Constraints p) : clause p c2435 = true :=
  Snake9.LocalRup.prove_clause [c1803, c1805, c1801, c1797, c1798, c907, c627, c520, c917, c2389, c1258, c1257, c2352] c2435 (by decide) p (sat_cons (step1803 p h) (sat_cons (step1805 p h) (sat_cons (step1801 p h) (sat_cons (step1797 p h) (sat_cons (step1798 p h) (sat_cons (step907 p h) (sat_cons (step627 p h) (sat_cons (step520 p h) (sat_cons (step917 p h) (sat_cons (step2389 p h) (sat_cons (step1258 p h) (sat_cons (step1257 p h) (sat_cons (step2352 p h) (sat_nil p))))))))))))))
def c2436 : List Lit := [(113, false), (237, true), (66, false), (62, true), (120, true), (41, false)]
theorem step2436 (p : Nat → Bool) (h : Constraints p) : clause p c2436 = true :=
  Snake9.LocalRup.prove_clause [c520, c2389] c2436 (by decide) p (sat_cons (step520 p h) (sat_cons (step2389 p h) (sat_nil p)))
def c2437 : List Lit := [(115, true), (1752, true), (120, true), (1733, false)]
theorem step2437 (p : Nat → Bool) (h : Constraints p) : clause p c2437 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1819, c1836, c1807, c1801, c1802, c1806, c1833, c1822, c1820, c1813, c1814, c1815, c928, c968, c926, c937, c1266, c1268, c2355] c2437 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1819 p h) (sat_cons (step1836 p h) (sat_cons (step1807 p h) (sat_cons (step1801 p h) (sat_cons (step1802 p h) (sat_cons (step1806 p h) (sat_cons (step1833 p h) (sat_cons (step1822 p h) (sat_cons (step1820 p h) (sat_cons (step1813 p h) (sat_cons (step1814 p h) (sat_cons (step1815 p h) (sat_cons (step928 p h) (sat_cons (step968 p h) (sat_cons (step926 p h) (sat_cons (step937 p h) (sat_cons (step1266 p h) (sat_cons (step1268 p h) (sat_cons (step2355 p h) (sat_nil p)))))))))))))))))))))
def c2438 : List Lit := [(1512, false), (1519, true)]
theorem step2438 (p : Nat → Bool) (h : Constraints p) : clause p c2438 = true :=
  Snake9.LocalRup.prove_clause [c1326, c1318, c1321, c1329, c1313, c1307, c1309, c1304, c1305, c7, c18, c23] c2438 (by decide) p (sat_cons (step1326 p h) (sat_cons (step1318 p h) (sat_cons (step1321 p h) (sat_cons (step1329 p h) (sat_cons (step1313 p h) (sat_cons (step1307 p h) (sat_cons (step1309 p h) (sat_cons (step1304 p h) (sat_cons (step1305 p h) (sat_cons (step7 p h) (sat_cons (step18 p h) (sat_cons (step23 p h) (sat_nil p)))))))))))))
def c2439 : List Lit := [(153, true), (25, false), (1537, false), (29, false), (1553, true)]
theorem step2439 (p : Nat → Bool) (h : Constraints p) : clause p c2439 = true :=
  Snake9.LocalRup.prove_clause [c2364, c1381, c2131, c2412, c1346, c1349, c1377, c1340, c1394, c1332, c1308, c2438, c1315, c1316, c2136, c67, c1040, c63, c1043, c2170, c2319, c1054, c1048, c74, c8, c10, c1306] c2439 (by decide) p (sat_cons (step2364 p h) (sat_cons (step1381 p h) (sat_cons (step2131 p h) (sat_cons (step2412 p h) (sat_cons (step1346 p h) (sat_cons (step1349 p h) (sat_cons (step1377 p h) (sat_cons (step1340 p h) (sat_cons (step1394 p h) (sat_cons (step1332 p h) (sat_cons (step1308 p h) (sat_cons (step2438 p h) (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step2136 p h) (sat_cons (step67 p h) (sat_cons (step1040 p h) (sat_cons (step63 p h) (sat_cons (step1043 p h) (sat_cons (step2170 p h) (sat_cons (step2319 p h) (sat_cons (step1054 p h) (sat_cons (step1048 p h) (sat_cons (step74 p h) (sat_cons (step8 p h) (sat_cons (step10 p h) (sat_cons (step1306 p h) (sat_nil p))))))))))))))))))))))))))))
def c2440 : List Lit := [(1508, false), (1512, false), (14, false), (139, true), (1537, false), (1553, true)]
theorem step2440 (p : Nat → Bool) (h : Constraints p) : clause p c2440 = true :=
  Snake9.LocalRup.prove_clause [c1318, c1367, c1406, c1334, c1333, c1321, c1401, c1312, c1372, c1347, c1339, c82, c86] c2440 (by decide) p (sat_cons (step1318 p h) (sat_cons (step1367 p h) (sat_cons (step1406 p h) (sat_cons (step1334 p h) (sat_cons (step1333 p h) (sat_cons (step1321 p h) (sat_cons (step1401 p h) (sat_cons (step1312 p h) (sat_cons (step1372 p h) (sat_cons (step1347 p h) (sat_cons (step1339 p h) (sat_cons (step82 p h) (sat_cons (step86 p h) (sat_nil p))))))))))))))
def c2441 : List Lit := [(15, false), (13, true), (6, true), (2, false), (3, false), (14, false), (1516, true), (133, true), (135, true), (139, true)]
theorem step2441 (p : Nat → Bool) (h : Constraints p) : clause p c2441 = true :=
  Snake9.LocalRup.prove_clause [c83, c82, c2182, c86, c56, c1312, c3, c1322, c66, c1317] c2441 (by decide) p (sat_cons (step83 p h) (sat_cons (step82 p h) (sat_cons (step2182 p h) (sat_cons (step86 p h) (sat_cons (step56 p h) (sat_cons (step1312 p h) (sat_cons (step3 p h) (sat_cons (step1322 p h) (sat_cons (step66 p h) (sat_cons (step1317 p h) (sat_nil p)))))))))))
def c2442 : List Lit := [(2, false), (3, false), (1530, true), (14, false), (129, true), (133, true), (135, true), (139, true), (1537, false), (1553, true)]
theorem step2442 (p : Nat → Bool) (h : Constraints p) : clause p c2442 = true :=
  Snake9.LocalRup.prove_clause [c2136, c2440, c1308, c1367, c1406, c2128, c1331, c2122, c1306, c1954, c10, c2441, c2181, c1339, c54, c1347, c1348, c1372, c1343, c1401, c2121] c2442 (by decide) p (sat_cons (step2136 p h) (sat_cons (step2440 p h) (sat_cons (step1308 p h) (sat_cons (step1367 p h) (sat_cons (step1406 p h) (sat_cons (step2128 p h) (sat_cons (step1331 p h) (sat_cons (step2122 p h) (sat_cons (step1306 p h) (sat_cons (step1954 p h) (sat_cons (step10 p h) (sat_cons (step2441 p h) (sat_cons (step2181 p h) (sat_cons (step1339 p h) (sat_cons (step54 p h) (sat_cons (step1347 p h) (sat_cons (step1348 p h) (sat_cons (step1372 p h) (sat_cons (step1343 p h) (sat_cons (step1401 p h) (sat_cons (step2121 p h) (sat_nil p))))))))))))))))))))))
def c2443 : List Lit := [(18, false), (6, true), (2, false), (148, true), (24, false), (25, false)]
theorem step2443 (p : Nat → Bool) (h : Constraints p) : clause p c2443 = true :=
  Snake9.LocalRup.prove_clause [c118, c96, c136] c2443 (by decide) p (sat_cons (step118 p h) (sat_cons (step96 p h) (sat_cons (step136 p h) (sat_nil p))))
def c2444 : List Lit := [(18, true), (14, true), (139, true), (146, true), (25, false), (1531, true), (29, false)]
theorem step2444 (p : Nat → Bool) (h : Constraints p) : clause p c2444 = true :=
  Snake9.LocalRup.prove_clause [c1340, c1349, c1343, c1344, c1351, c106, c1341, c2103, c82, c145, c2184] c2444 (by decide) p (sat_cons (step1340 p h) (sat_cons (step1349 p h) (sat_cons (step1343 p h) (sat_cons (step1344 p h) (sat_cons (step1351 p h) (sat_cons (step106 p h) (sat_cons (step1341 p h) (sat_cons (step2103 p h) (sat_cons (step82 p h) (sat_cons (step145 p h) (sat_cons (step2184 p h) (sat_nil p))))))))))))
def c2445 : List Lit := [(2, false), (9, false), (18, false), (148, true), (24, false), (25, false)]
theorem step2445 (p : Nat → Bool) (h : Constraints p) : clause p c2445 = true :=
  Snake9.LocalRup.prove_clause [c2443, c29] c2445 (by decide) p (sat_cons (step2443 p h) (sat_cons (step29 p h) (sat_nil p)))
def c2446 : List Lit := [(6, false), (2, true), (9, false), (14, true), (129, true), (139, true), (24, false), (1537, false), (1553, true)]
theorem step2446 (p : Nat → Bool) (h : Constraints p) : clause p c2446 = true :=
  Snake9.LocalRup.prove_clause [c1340, c1347, c1372, c1401, c1336, c1311, c31, c1304, c1306, c1310, c24, c1332, c52, c1394, c83, c1377, c1341, c1350] c2446 (by decide) p (sat_cons (step1340 p h) (sat_cons (step1347 p h) (sat_cons (step1372 p h) (sat_cons (step1401 p h) (sat_cons (step1336 p h) (sat_cons (step1311 p h) (sat_cons (step31 p h) (sat_cons (step1304 p h) (sat_cons (step1306 p h) (sat_cons (step1310 p h) (sat_cons (step24 p h) (sat_cons (step1332 p h) (sat_cons (step52 p h) (sat_cons (step1394 p h) (sat_cons (step83 p h) (sat_cons (step1377 p h) (sat_cons (step1341 p h) (sat_cons (step1350 p h) (sat_nil p)))))))))))))))))))
def c2447 : List Lit := [(5, false), (1508, true), (3, false), (13, false)]
theorem step2447 (p : Nat → Bool) (h : Constraints p) : clause p c2447 = true :=
  Snake9.LocalRup.prove_clause [c8, c13, c1310, c1304] c2447 (by decide) p (sat_cons (step8 p h) (sat_cons (step13 p h) (sat_cons (step1310 p h) (sat_cons (step1304 p h) (sat_nil p)))))
def c2448 : List Lit := [(1508, true), (3, false), (13, false)]
theorem step2448 (p : Nat → Bool) (h : Constraints p) : clause p c2448 = true :=
  Snake9.LocalRup.prove_clause [c1308, c2447, c1305, c1306, c1310, c10] c2448 (by decide) p (sat_cons (step1308 p h) (sat_cons (step2447 p h) (sat_cons (step1305 p h) (sat_cons (step1306 p h) (sat_cons (step1310 p h) (sat_cons (step10 p h) (sat_nil p)))))))
def c2449 : List Lit := [(1657, true), (60, true), (57, false), (197, true), (49, true)]
theorem step2449 (p : Nat → Bool) (h : Constraints p) : clause p c2449 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1618, c680, c651] c2449 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1618 p h) (sat_cons (step680 p h) (sat_cons (step651 p h) (sat_nil p)))))
def c2450 : List Lit := [(1657, true), (57, false), (39, false), (197, true), (49, true)]
theorem step2450 (p : Nat → Bool) (h : Constraints p) : clause p c2450 = true :=
  Snake9.LocalRup.prove_clause [c1617, c2449, c449] c2450 (by decide) p (sat_cons (step1617 p h) (sat_cons (step2449 p h) (sat_cons (step449 p h) (sat_nil p))))
def c2451 : List Lit := [(69, false), (67, true), (75, true), (74, false), (32, false), (1657, true), (49, true), (197, true)]
theorem step2451 (p : Nat → Bool) (h : Constraints p) : clause p c2451 = true :=
  Snake9.LocalRup.prove_clause [c1618, c1617, c691, c654, c2264, c678] c2451 (by decide) p (sat_cons (step1618 p h) (sat_cons (step1617 p h) (sat_cons (step691 p h) (sat_cons (step654 p h) (sat_cons (step2264 p h) (sat_cons (step678 p h) (sat_nil p)))))))
def c2452 : List Lit := [(1759, true), (1745, false), (487, true), (1725, false), (49, true)]
theorem step2452 (p : Nat → Bool) (h : Constraints p) : clause p c2452 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1851, c1846, c2400, c1828] c2452 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1851 p h) (sat_cons (step1846 p h) (sat_cons (step2400 p h) (sat_cons (step1828 p h) (sat_nil p))))))
def c2453 : List Lit := [(1746, true), (72, false), (121, true), (120, true)]
theorem step2453 (p : Nat → Bool) (h : Constraints p) : clause p c2453 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1822, c2087, c1820, c1813, c1814, c1815, c968, c953] c2453 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1822 p h) (sat_cons (step2087 p h) (sat_cons (step1820 p h) (sat_cons (step1813 p h) (sat_cons (step1814 p h) (sat_cons (step1815 p h) (sat_cons (step968 p h) (sat_cons (step953 p h) (sat_nil p))))))))))
def c2454 : List Lit := [(1717, true), (227, true), (91, false), (49, true)]
theorem step2454 (p : Nat → Bool) (h : Constraints p) : clause p c2454 = true :=
  Snake9.LocalRup.prove_clause [c1764, c1765, c862, c847] c2454 (by decide) p (sat_cons (step1764 p h) (sat_cons (step1765 p h) (sat_cons (step862 p h) (sat_cons (step847 p h) (sat_nil p)))))
def c2455 : List Lit := [(99, false), (90, true), (1717, true), (223, true)]
theorem step2455 (p : Nat → Bool) (h : Constraints p) : clause p c2455 = true :=
  Snake9.LocalRup.prove_clause [c2404, c840] c2455 (by decide) p (sat_cons (step2404 p h) (sat_cons (step840 p h) (sat_nil p)))
def c2456 : List Lit := [(94, false), (96, false), (102, false), (218, true)]
theorem step2456 (p : Nat → Bool) (h : Constraints p) : clause p c2456 = true :=
  Snake9.LocalRup.prove_clause [c809, c817] c2456 (by decide) p (sat_cons (step809 p h) (sat_cons (step817 p h) (sat_nil p)))
def c2457 : List Lit := [(1614, true), (1568, false), (42, true), (43, false)]
theorem step2457 (p : Nat → Bool) (h : Constraints p) : clause p c2457 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1435, c1446, c1532, c1525, c1447, c1489, c1438, c1436, c1483, c1429, c1430, c1476, c274] c2457 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1435 p h) (sat_cons (step1446 p h) (sat_cons (step1532 p h) (sat_cons (step1525 p h) (sat_cons (step1447 p h) (sat_cons (step1489 p h) (sat_cons (step1438 p h) (sat_cons (step1436 p h) (sat_cons (step1483 p h) (sat_cons (step1429 p h) (sat_cons (step1430 p h) (sat_cons (step1476 p h) (sat_cons (step274 p h) (sat_nil p)))))))))))))))
def c2458 : List Lit := [(120, true), (62, true), (113, false), (237, true), (107, true)]
theorem step2458 (p : Nat → Bool) (h : Constraints p) : clause p c2458 = true :=
  Snake9.LocalRup.prove_clause [c2389, c2300, c904, c1984, c2294] c2458 (by decide) p (sat_cons (step2389 p h) (sat_cons (step2300 p h) (sat_cons (step904 p h) (sat_cons (step1984 p h) (sat_cons (step2294 p h) (sat_nil p))))))
def c2459 : List Lit := [(21, false), (1528, true), (29, false), (25, false)]
theorem step2459 (p : Nat → Bool) (h : Constraints p) : clause p c2459 = true :=
  Snake9.LocalRup.prove_clause [c106, c105, c1344] c2459 (by decide) p (sat_cons (step106 p h) (sat_cons (step105 p h) (sat_cons (step1344 p h) (sat_nil p))))
end B112E089
