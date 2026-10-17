import B112E052Part0006
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2438 : List Lit := [(1658, false), (1678, true)]
theorem step2438 (p : Nat → Bool) (h : Constraints p) : clause p c2438 = true :=
  Snake9.LocalRup.prove_clause [c2070, c1475] c2438 (by decide) p (sat_cons (step2070 p h) (sat_cons (step1475 p h) (sat_nil p)))
def c2439 : List Lit := [(1659, false), (1679, true)]
theorem step2439 (p : Nat → Bool) (h : Constraints p) : clause p c2439 = true :=
  Snake9.LocalRup.prove_clause [c2070, c1476] c2439 (by decide) p (sat_cons (step2070 p h) (sat_cons (step1476 p h) (sat_nil p)))
def c2440 : List Lit := [(1660, false), (1680, true)]
theorem step2440 (p : Nat → Bool) (h : Constraints p) : clause p c2440 = true :=
  Snake9.LocalRup.prove_clause [c2070, c1477] c2440 (by decide) p (sat_cons (step2070 p h) (sat_cons (step1477 p h) (sat_nil p)))
def c2441 : List Lit := [(1661, false), (1681, true)]
theorem step2441 (p : Nat → Bool) (h : Constraints p) : clause p c2441 = true :=
  Snake9.LocalRup.prove_clause [c2070, c1478] c2441 (by decide) p (sat_cons (step2070 p h) (sat_cons (step1478 p h) (sat_nil p)))
def c2442 : List Lit := [(1662, false), (1682, true)]
theorem step2442 (p : Nat → Bool) (h : Constraints p) : clause p c2442 = true :=
  Snake9.LocalRup.prove_clause [c2070, c1479] c2442 (by decide) p (sat_cons (step2070 p h) (sat_cons (step1479 p h) (sat_nil p)))
def c2443 : List Lit := [(1663, false), (1683, true)]
theorem step2443 (p : Nat → Bool) (h : Constraints p) : clause p c2443 = true :=
  Snake9.LocalRup.prove_clause [c2070, c1480] c2443 (by decide) p (sat_cons (step2070 p h) (sat_cons (step1480 p h) (sat_nil p)))
def c2444 : List Lit := [(1595, false), (1676, true)]
theorem step2444 (p : Nat → Bool) (h : Constraints p) : clause p c2444 = true :=
  Snake9.LocalRup.prove_clause [c2067, c1481] c2444 (by decide) p (sat_cons (step2067 p h) (sat_cons (step1481 p h) (sat_nil p)))
def c2445 : List Lit := [(1596, false), (1677, true)]
theorem step2445 (p : Nat → Bool) (h : Constraints p) : clause p c2445 = true :=
  Snake9.LocalRup.prove_clause [c2067, c1489] c2445 (by decide) p (sat_cons (step2067 p h) (sat_cons (step1489 p h) (sat_nil p)))
def c2446 : List Lit := [(1597, false), (1678, true)]
theorem step2446 (p : Nat → Bool) (h : Constraints p) : clause p c2446 = true :=
  Snake9.LocalRup.prove_clause [c2067, c1497] c2446 (by decide) p (sat_cons (step2067 p h) (sat_cons (step1497 p h) (sat_nil p)))
def c2447 : List Lit := [(1598, false), (1679, true)]
theorem step2447 (p : Nat → Bool) (h : Constraints p) : clause p c2447 = true :=
  Snake9.LocalRup.prove_clause [c2067, c1506] c2447 (by decide) p (sat_cons (step2067 p h) (sat_cons (step1506 p h) (sat_nil p)))
def c2448 : List Lit := [(1599, false), (1680, true)]
theorem step2448 (p : Nat → Bool) (h : Constraints p) : clause p c2448 = true :=
  Snake9.LocalRup.prove_clause [c2067, c1514] c2448 (by decide) p (sat_cons (step2067 p h) (sat_cons (step1514 p h) (sat_nil p)))
def c2449 : List Lit := [(1600, false), (1681, true)]
theorem step2449 (p : Nat → Bool) (h : Constraints p) : clause p c2449 = true :=
  Snake9.LocalRup.prove_clause [c2067, c1522] c2449 (by decide) p (sat_cons (step2067 p h) (sat_cons (step1522 p h) (sat_nil p)))
def c2450 : List Lit := [(1601, false), (1682, true)]
theorem step2450 (p : Nat → Bool) (h : Constraints p) : clause p c2450 = true :=
  Snake9.LocalRup.prove_clause [c2067, c1529] c2450 (by decide) p (sat_cons (step2067 p h) (sat_cons (step1529 p h) (sat_nil p)))
def c2451 : List Lit := [(1736, false), (1745, true)]
theorem step2451 (p : Nat → Bool) (h : Constraints p) : clause p c2451 = true :=
  Snake9.LocalRup.prove_clause [c2050, c1634] c2451 (by decide) p (sat_cons (step2050 p h) (sat_cons (step1634 p h) (sat_nil p)))
def c2452 : List Lit := [(1737, false), (1746, true)]
theorem step2452 (p : Nat → Bool) (h : Constraints p) : clause p c2452 = true :=
  Snake9.LocalRup.prove_clause [c2050, c1635] c2452 (by decide) p (sat_cons (step2050 p h) (sat_cons (step1635 p h) (sat_nil p)))
def c2453 : List Lit := [(1738, false), (1747, true)]
theorem step2453 (p : Nat → Bool) (h : Constraints p) : clause p c2453 = true :=
  Snake9.LocalRup.prove_clause [c2050, c1636] c2453 (by decide) p (sat_cons (step2050 p h) (sat_cons (step1636 p h) (sat_nil p)))
def c2454 : List Lit := [(1739, false), (1748, true)]
theorem step2454 (p : Nat → Bool) (h : Constraints p) : clause p c2454 = true :=
  Snake9.LocalRup.prove_clause [c2050, c1637] c2454 (by decide) p (sat_cons (step2050 p h) (sat_cons (step1637 p h) (sat_nil p)))
def c2455 : List Lit := [(1740, false), (1749, true)]
theorem step2455 (p : Nat → Bool) (h : Constraints p) : clause p c2455 = true :=
  Snake9.LocalRup.prove_clause [c2050, c1638] c2455 (by decide) p (sat_cons (step2050 p h) (sat_cons (step1638 p h) (sat_nil p)))
def c2456 : List Lit := [(1741, false), (1750, true)]
theorem step2456 (p : Nat → Bool) (h : Constraints p) : clause p c2456 = true :=
  Snake9.LocalRup.prove_clause [c2050, c1639] c2456 (by decide) p (sat_cons (step2050 p h) (sat_cons (step1639 p h) (sat_nil p)))
def c2457 : List Lit := [(1742, false), (1751, true)]
theorem step2457 (p : Nat → Bool) (h : Constraints p) : clause p c2457 = true :=
  Snake9.LocalRup.prove_clause [c2050, c1640] c2457 (by decide) p (sat_cons (step2050 p h) (sat_cons (step1640 p h) (sat_nil p)))
def c2458 : List Lit := [(1745, true), (1712, false)]
theorem step2458 (p : Nat → Bool) (h : Constraints p) : clause p c2458 = true :=
  Snake9.LocalRup.prove_clause [c2063, c1641] c2458 (by decide) p (sat_cons (step2063 p h) (sat_cons (step1641 p h) (sat_nil p)))
def c2459 : List Lit := [(1713, false), (1746, true)]
theorem step2459 (p : Nat → Bool) (h : Constraints p) : clause p c2459 = true :=
  Snake9.LocalRup.prove_clause [c2063, c1649] c2459 (by decide) p (sat_cons (step2063 p h) (sat_cons (step1649 p h) (sat_nil p)))
def c2460 : List Lit := [(1714, false), (1747, true)]
theorem step2460 (p : Nat → Bool) (h : Constraints p) : clause p c2460 = true :=
  Snake9.LocalRup.prove_clause [c2063, c1657] c2460 (by decide) p (sat_cons (step2063 p h) (sat_cons (step1657 p h) (sat_nil p)))
def c2461 : List Lit := [(1715, false), (1748, true)]
theorem step2461 (p : Nat → Bool) (h : Constraints p) : clause p c2461 = true :=
  Snake9.LocalRup.prove_clause [c2063, c1666] c2461 (by decide) p (sat_cons (step2063 p h) (sat_cons (step1666 p h) (sat_nil p)))
def c2462 : List Lit := [(1717, false), (1750, true)]
theorem step2462 (p : Nat → Bool) (h : Constraints p) : clause p c2462 = true :=
  Snake9.LocalRup.prove_clause [c2063, c1679] c2462 (by decide) p (sat_cons (step2063 p h) (sat_cons (step1679 p h) (sat_nil p)))
def c2463 : List Lit := [(1754, false), (1813, false)]
theorem step2463 (p : Nat → Bool) (h : Constraints p) : clause p c2463 = true :=
  Snake9.LocalRup.prove_clause [c2072, c1902] c2463 (by decide) p (sat_cons (step2072 p h) (sat_cons (step1902 p h) (sat_nil p)))
def c2464 : List Lit := [(1755, false), (1812, false)]
theorem step2464 (p : Nat → Bool) (h : Constraints p) : clause p c2464 = true :=
  Snake9.LocalRup.prove_clause [c2072, c1905] c2464 (by decide) p (sat_cons (step2072 p h) (sat_cons (step1905 p h) (sat_nil p)))
def c2465 : List Lit := [(1676, false), (1840, false)]
theorem step2465 (p : Nat → Bool) (h : Constraints p) : clause p c2465 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1907] c2465 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1907 p h) (sat_nil p)))
def c2466 : List Lit := [(1677, false), (1839, false)]
theorem step2466 (p : Nat → Bool) (h : Constraints p) : clause p c2466 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1908] c2466 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1908 p h) (sat_nil p)))
def c2467 : List Lit := [(1678, false), (1838, false)]
theorem step2467 (p : Nat → Bool) (h : Constraints p) : clause p c2467 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1909] c2467 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1909 p h) (sat_nil p)))
def c2468 : List Lit := [(1679, false), (1837, false)]
theorem step2468 (p : Nat → Bool) (h : Constraints p) : clause p c2468 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1910] c2468 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1910 p h) (sat_nil p)))
def c2469 : List Lit := [(1680, false), (1836, false)]
theorem step2469 (p : Nat → Bool) (h : Constraints p) : clause p c2469 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1911] c2469 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1911 p h) (sat_nil p)))
def c2470 : List Lit := [(1681, false), (1835, false)]
theorem step2470 (p : Nat → Bool) (h : Constraints p) : clause p c2470 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1912] c2470 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1912 p h) (sat_nil p)))
def c2471 : List Lit := [(1682, false), (1834, false)]
theorem step2471 (p : Nat → Bool) (h : Constraints p) : clause p c2471 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1913] c2471 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1913 p h) (sat_nil p)))
def c2472 : List Lit := [(1683, false), (1833, false)]
theorem step2472 (p : Nat → Bool) (h : Constraints p) : clause p c2472 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1914] c2472 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1914 p h) (sat_nil p)))
def c2473 : List Lit := [(1684, false), (1832, false)]
theorem step2473 (p : Nat → Bool) (h : Constraints p) : clause p c2473 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1915] c2473 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1915 p h) (sat_nil p)))
def c2474 : List Lit := [(1685, false), (1831, false)]
theorem step2474 (p : Nat → Bool) (h : Constraints p) : clause p c2474 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1916] c2474 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1916 p h) (sat_nil p)))
def c2475 : List Lit := [(1686, false), (1830, false)]
theorem step2475 (p : Nat → Bool) (h : Constraints p) : clause p c2475 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1917] c2475 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1917 p h) (sat_nil p)))
def c2476 : List Lit := [(1687, false), (1829, false)]
theorem step2476 (p : Nat → Bool) (h : Constraints p) : clause p c2476 = true :=
  Snake9.LocalRup.prove_clause [c1919, c1918] c2476 (by decide) p (sat_cons (step1919 p h) (sat_cons (step1918 p h) (sat_nil p)))
def c2477 : List Lit := [(71, false), (1789, true), (114, true), (113, false), (122, false)]
theorem step2477 (p : Nat → Bool) (h : Constraints p) : clause p c2477 = true :=
  Snake9.LocalRup.prove_clause [c846, c847, c1738, c1740, c1748] c2477 (by decide) p (sat_cons (step846 p h) (sat_cons (step847 p h) (sat_cons (step1738 p h) (sat_cons (step1740 p h) (sat_cons (step1748 p h) (sat_nil p))))))
def c2478 : List Lit := [(1738, true), (94, true), (114, false), (90, true), (1719, false)]
theorem step2478 (p : Nat → Bool) (h : Constraints p) : clause p c2478 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1600, c1605, c1590, c1617, c1621, c1606, c1608, c1591, c1601, c1598, c1585, c1586, c566, c440, c2328] c2478 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1600 p h) (sat_cons (step1605 p h) (sat_cons (step1590 p h) (sat_cons (step1617 p h) (sat_cons (step1621 p h) (sat_cons (step1606 p h) (sat_cons (step1608 p h) (sat_cons (step1591 p h) (sat_cons (step1601 p h) (sat_cons (step1598 p h) (sat_cons (step1585 p h) (sat_cons (step1586 p h) (sat_cons (step566 p h) (sat_cons (step440 p h) (sat_cons (step2328 p h) (sat_nil p)))))))))))))))))
def c2479 : List Lit := [(1730, false), (1739, true), (92, true), (87, true), (1719, false)]
theorem step2479 (p : Nat → Bool) (h : Constraints p) : clause p c2479 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1591, c1622, c1603, c1606, c1626, c1596, c1592, c2328, c2326, c1587, c1958] c2479 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1591 p h) (sat_cons (step1622 p h) (sat_cons (step1603 p h) (sat_cons (step1606 p h) (sat_cons (step1626 p h) (sat_cons (step1596 p h) (sat_cons (step1592 p h) (sat_cons (step2328 p h) (sat_cons (step2326 p h) (sat_cons (step1587 p h) (sat_cons (step1958 p h) (sat_nil p)))))))))))))
def c2480 : List Lit := [(1573, true), (95, false), (15, true), (18, true), (90, false)]
theorem step2480 (p : Nat → Bool) (h : Constraints p) : clause p c2480 = true :=
  Snake9.LocalRup.prove_clause [c1272, c1275, c1283, c1281, c1273, c1276, c484, c72, c2216] c2480 (by decide) p (sat_cons (step1272 p h) (sat_cons (step1275 p h) (sat_cons (step1283 p h) (sat_cons (step1281 p h) (sat_cons (step1273 p h) (sat_cons (step1276 p h) (sat_cons (step484 p h) (sat_cons (step72 p h) (sat_cons (step2216 p h) (sat_nil p))))))))))
def c2481 : List Lit := [(17, false), (20, false), (95, false), (90, false)]
theorem step2481 (p : Nat → Bool) (h : Constraints p) : clause p c2481 = true :=
  Snake9.LocalRup.prove_clause [c484, c72, c2216] c2481 (by decide) p (sat_cons (step484 p h) (sat_cons (step72 p h) (sat_cons (step2216 p h) (sat_nil p))))
def c2482 : List Lit := [(1769, true), (114, false), (92, true), (94, false)]
theorem step2482 (p : Nat → Bool) (h : Constraints p) : clause p c2482 = true :=
  Snake9.LocalRup.prove_clause [c1702, c1703, c791, c864, c2367] c2482 (by decide) p (sat_cons (step1702 p h) (sat_cons (step1703 p h) (sat_cons (step791 p h) (sat_cons (step864 p h) (sat_cons (step2367 p h) (sat_nil p))))))
def c2483 : List Lit := [(102, false), (107, false), (105, true), (94, false), (92, true)]
theorem step2483 (p : Nat → Bool) (h : Constraints p) : clause p c2483 = true :=
  Snake9.LocalRup.prove_clause [c712, c2343] c2483 (by decide) p (sat_cons (step712 p h) (sat_cons (step2343 p h) (sat_nil p)))
def c2484 : List Lit := [(1597, true), (1572, false), (1569, false), (17, true), (101, true), (122, false)]
theorem step2484 (p : Nat → Bool) (h : Constraints p) : clause p c2484 = true :=
  Snake9.LocalRup.prove_clause [c2046, c2195, c2424, c1309, c1283, c2172, c1273, c2232, c2196] c2484 (by decide) p (sat_cons (step2046 p h) (sat_cons (step2195 p h) (sat_cons (step2424 p h) (sat_cons (step1309 p h) (sat_cons (step1283 p h) (sat_cons (step2172 p h) (sat_cons (step1273 p h) (sat_cons (step2232 p h) (sat_cons (step2196 p h) (sat_nil p))))))))))
def c2485 : List Lit := [(1569, false), (17, true), (1597, true), (101, true), (122, false)]
theorem step2485 (p : Nat → Bool) (h : Constraints p) : clause p c2485 = true :=
  Snake9.LocalRup.prove_clause [c1271, c1280, c2484] c2485 (by decide) p (sat_cons (step1271 p h) (sat_cons (step1280 p h) (sat_cons (step2484 p h) (sat_nil p))))
def c2486 : List Lit := [(1647, true), (92, true)]
theorem step2486 (p : Nat → Bool) (h : Constraints p) : clause p c2486 = true :=
  Snake9.LocalRup.prove_clause [c1415, c1418, c1409, c1393, c1395, c1402, c1390, c1391, c1387, c259, c2269, c211] c2486 (by decide) p (sat_cons (step1415 p h) (sat_cons (step1418 p h) (sat_cons (step1409 p h) (sat_cons (step1393 p h) (sat_cons (step1395 p h) (sat_cons (step1402 p h) (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step1387 p h) (sat_cons (step259 p h) (sat_cons (step2269 p h) (sat_cons (step211 p h) (sat_nil p)))))))))))))
def c2487 : List Lit := [(1624, true), (3, false), (7, false), (44, true), (20, false)]
theorem step2487 (p : Nat → Bool) (h : Constraints p) : clause p c2487 = true :=
  Snake9.LocalRup.prove_clause [c2076, c1346, c1347, c156, c2243, c2245, c2244, c1930, c1343, c1351, c1373, c1363, c1364, c1361, c1358, c138] c2487 (by decide) p (sat_cons (step2076 p h) (sat_cons (step1346 p h) (sat_cons (step1347 p h) (sat_cons (step156 p h) (sat_cons (step2243 p h) (sat_cons (step2245 p h) (sat_cons (step2244 p h) (sat_cons (step1930 p h) (sat_cons (step1343 p h) (sat_cons (step1351 p h) (sat_cons (step1373 p h) (sat_cons (step1363 p h) (sat_cons (step1364 p h) (sat_cons (step1361 p h) (sat_cons (step1358 p h) (sat_cons (step138 p h) (sat_nil p)))))))))))))))))
def c2488 : List Lit := [(1801, true), (117, true), (1783, false), (118, true), (123, false)]
theorem step2488 (p : Nat → Bool) (h : Constraints p) : clause p c2488 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1745, c1778, c1774, c1746, c1756, c1741, c1753, c1754, c952, c953, c2388] c2488 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1745 p h) (sat_cons (step1778 p h) (sat_cons (step1774 p h) (sat_cons (step1746 p h) (sat_cons (step1756 p h) (sat_cons (step1741 p h) (sat_cons (step1753 p h) (sat_cons (step1754 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step2388 p h) (sat_nil p)))))))))))))
def c2489 : List Lit := [(24, false), (17, true), (1586, true), (1577, false), (26, false), (27, false)]
theorem step2489 (p : Nat → Bool) (h : Constraints p) : clause p c2489 = true :=
  Snake9.LocalRup.prove_clause [c100, c98, c1285, c1273, c1294, c1282, c1309] c2489 (by decide) p (sat_cons (step100 p h) (sat_cons (step98 p h) (sat_cons (step1285 p h) (sat_cons (step1273 p h) (sat_cons (step1294 p h) (sat_cons (step1282 p h) (sat_cons (step1309 p h) (sat_nil p))))))))
def c2490 : List Lit := [(17, true), (1586, true), (1577, false), (26, false), (27, false)]
theorem step2490 (p : Nat → Bool) (h : Constraints p) : clause p c2490 = true :=
  Snake9.LocalRup.prove_clause [c1271, c1279, c1305, c1297, c2489, c1286, c1287, c1294, c99, c1309, c1273, c1282] c2490 (by decide) p (sat_cons (step1271 p h) (sat_cons (step1279 p h) (sat_cons (step1305 p h) (sat_cons (step1297 p h) (sat_cons (step2489 p h) (sat_cons (step1286 p h) (sat_cons (step1287 p h) (sat_cons (step1294 p h) (sat_cons (step99 p h) (sat_cons (step1309 p h) (sat_cons (step1273 p h) (sat_cons (step1282 p h) (sat_nil p)))))))))))))
def c2491 : List Lit := [(20, false), (17, false), (29, true), (22, true), (38, true)]
theorem step2491 (p : Nat → Bool) (h : Constraints p) : clause p c2491 = true :=
  Snake9.LocalRup.prove_clause [c2223, c2222, c1921] c2491 (by decide) p (sat_cons (step2223 p h) (sat_cons (step2222 p h) (sat_cons (step1921 p h) (sat_nil p))))
def c2492 : List Lit := [(15, false), (1576, true), (26, false), (27, false)]
theorem step2492 (p : Nat → Bool) (h : Constraints p) : clause p c2492 = true :=
  Snake9.LocalRup.prove_clause [c99, c98, c1287] c2492 (by decide) p (sat_cons (step99 p h) (sat_cons (step98 p h) (sat_cons (step1287 p h) (sat_nil p))))
def c2493 : List Lit := [(1575, true), (26, false), (27, false)]
theorem step2493 (p : Nat → Bool) (h : Constraints p) : clause p c2493 = true :=
  Snake9.LocalRup.prove_clause [c1285, c1286, c100] c2493 (by decide) p (sat_cons (step1285 p h) (sat_cons (step1286 p h) (sat_cons (step100 p h) (sat_nil p))))
def c2494 : List Lit := [(1732, true), (1647, true)]
theorem step2494 (p : Nat → Bool) (h : Constraints p) : clause p c2494 = true :=
  Snake9.LocalRup.prove_clause [c1418, c1395, c1387, c1393, c1390, c1391, c1415, c1409, c1402, c259, c211, c2271, c246, c1600, c2486, c1603, c1605, c1601, c1596, c553] c2494 (by decide) p (sat_cons (step1418 p h) (sat_cons (step1395 p h) (sat_cons (step1387 p h) (sat_cons (step1393 p h) (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step1415 p h) (sat_cons (step1409 p h) (sat_cons (step1402 p h) (sat_cons (step259 p h) (sat_cons (step211 p h) (sat_cons (step2271 p h) (sat_cons (step246 p h) (sat_cons (step1600 p h) (sat_cons (step2486 p h) (sat_cons (step1603 p h) (sat_cons (step1605 p h) (sat_cons (step1601 p h) (sat_cons (step1596 p h) (sat_cons (step553 p h) (sat_nil p)))))))))))))))))))))
def c2495 : List Lit := [(60, false), (51, false), (62, false), (86, false)]
theorem step2495 (p : Nat → Bool) (h : Constraints p) : clause p c2495 = true :=
  Snake9.LocalRup.prove_clause [c273, c217, c2276] c2495 (by decide) p (sat_cons (step273 p h) (sat_cons (step217 p h) (sat_cons (step2276 p h) (sat_nil p))))
def c2496 : List Lit := [(51, false), (62, false), (88, true), (53, false), (86, false), (87, false), (54, false), (1640, true)]
theorem step2496 (p : Nat → Bool) (h : Constraints p) : clause p c2496 = true :=
  Snake9.LocalRup.prove_clause [c211, c2495, c1403, c259, c230, c2266] c2496 (by decide) p (sat_cons (step211 p h) (sat_cons (step2495 p h) (sat_cons (step1403 p h) (sat_cons (step259 p h) (sat_cons (step230 p h) (sat_cons (step2266 p h) (sat_nil p)))))))
def c2497 : List Lit := [(91, false), (92, true), (1721, true)]
theorem step2497 (p : Nat → Bool) (h : Constraints p) : clause p c2497 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1585, c2328, c440] c2497 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1585 p h) (sat_cons (step2328 p h) (sat_cons (step440 p h) (sat_nil p)))))
def c2498 : List Lit := [(99, true), (107, true), (1769, false), (98, true), (89, true), (1778, true)]
theorem step2498 (p : Nat → Bool) (h : Constraints p) : clause p c2498 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1708, c1724, c1696, c1685, c1687, c1693, c1694, c1720, c1689, c1711, c2340, c1701, c756] c2498 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1708 p h) (sat_cons (step1724 p h) (sat_cons (step1696 p h) (sat_cons (step1685 p h) (sat_cons (step1687 p h) (sat_cons (step1693 p h) (sat_cons (step1694 p h) (sat_cons (step1720 p h) (sat_cons (step1689 p h) (sat_cons (step1711 p h) (sat_cons (step2340 p h) (sat_cons (step1701 p h) (sat_cons (step756 p h) (sat_nil p)))))))))))))))
def c2499 : List Lit := [(79, false), (67, true), (56, false), (63, false), (62, false), (1720, true), (1715, true), (1562, true)]
theorem step2499 (p : Nat → Bool) (h : Constraints p) : clause p c2499 = true :=
  Snake9.LocalRup.prove_clause [c2037, c1251, c1248, c1264, c2034, c2030, c370, c368, c369, c1584, c1546, c1550, c404, c1555, c2282, c1575, c284, c1534, c367, c1544, c1535] c2499 (by decide) p (sat_cons (step2037 p h) (sat_cons (step1251 p h) (sat_cons (step1248 p h) (sat_cons (step1264 p h) (sat_cons (step2034 p h) (sat_cons (step2030 p h) (sat_cons (step370 p h) (sat_cons (step368 p h) (sat_cons (step369 p h) (sat_cons (step1584 p h) (sat_cons (step1546 p h) (sat_cons (step1550 p h) (sat_cons (step404 p h) (sat_cons (step1555 p h) (sat_cons (step2282 p h) (sat_cons (step1575 p h) (sat_cons (step284 p h) (sat_cons (step1534 p h) (sat_cons (step367 p h) (sat_cons (step1544 p h) (sat_cons (step1535 p h) (sat_nil p))))))))))))))))))))))
def c2500 : List Lit := [(1697, true), (69, false), (53, false)]
theorem step2500 (p : Nat → Bool) (h : Constraints p) : clause p c2500 = true :=
  Snake9.LocalRup.prove_clause [c1535, c1536, c317] c2500 (by decide) p (sat_cons (step1535 p h) (sat_cons (step1536 p h) (sat_cons (step317 p h) (sat_nil p))))
def c2501 : List Lit := [(72, false), (80, true), (56, false), (3, false)]
theorem step2501 (p : Nat → Bool) (h : Constraints p) : clause p c2501 = true :=
  Snake9.LocalRup.prove_clause [c348, c2299] c2501 (by decide) p (sat_cons (step348 p h) (sat_cons (step2299 p h) (sat_nil p)))
end B112E052
