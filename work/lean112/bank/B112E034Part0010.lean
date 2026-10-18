import B112E034Part0009
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2419 : List Lit := [(99, false), (93, true), (1604, false), (86, true), (89, true), (123, false), (109, false), (122, false), (126, false), (95, false), (1829, false), (97, false), (1804, true), (119, false), (107, false), (114, true), (117, false)]
theorem step2419 (p : Nat → Bool) (h : Constraints p) : clause p c2419 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1439, c783, c476, c1570, c748, c754, c2416, c1417, c2340, c1934, c2176, c1697, c1488, c2163, c2184, c2264, c2162, c1483, c2406, c1440, c1435, c2061, c462] c2419 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1439 p h) (sat_cons (step783 p h) (sat_cons (step476 p h) (sat_cons (step1570 p h) (sat_cons (step748 p h) (sat_cons (step754 p h) (sat_cons (step2416 p h) (sat_cons (step1417 p h) (sat_cons (step2340 p h) (sat_cons (step1934 p h) (sat_cons (step2176 p h) (sat_cons (step1697 p h) (sat_cons (step1488 p h) (sat_cons (step2163 p h) (sat_cons (step2184 p h) (sat_cons (step2264 p h) (sat_cons (step2162 p h) (sat_cons (step1483 p h) (sat_cons (step2406 p h) (sat_cons (step1440 p h) (sat_cons (step1435 p h) (sat_cons (step2061 p h) (sat_cons (step462 p h) (sat_nil p)))))))))))))))))))))))))
def c2420 : List Lit := [(1804, true), (119, false), (1797, false), (1830, true), (107, false), (113, true), (114, true), (117, false)]
theorem step2420 (p : Nat → Bool) (h : Constraints p) : clause p c2420 = true :=
  Snake9.LocalRup.prove_clause [c2384, c1554, c1563, c2255, c1621, c2400, c2381, c1572, c2401, c2413, c1556, c1566, c1607, c1608, c1620, c1625, c2239, c1584, c1533, c1904, c2411, c1573, c1577, c1529, c1521, c2412, c2190, c1526, c2105, c1537, c1510, c1928, c1902, c1507, c1508, c474, c2338, c2080, c2418, c1433, c1439, c2419, c2076, c506, c1520, c464, c2069, c529, c521, c1374, c2415, c1570, c748, c754, c2416, c1417, c2417, c1934] c2420 (by decide) p (sat_cons (step2384 p h) (sat_cons (step1554 p h) (sat_cons (step1563 p h) (sat_cons (step2255 p h) (sat_cons (step1621 p h) (sat_cons (step2400 p h) (sat_cons (step2381 p h) (sat_cons (step1572 p h) (sat_cons (step2401 p h) (sat_cons (step2413 p h) (sat_cons (step1556 p h) (sat_cons (step1566 p h) (sat_cons (step1607 p h) (sat_cons (step1608 p h) (sat_cons (step1620 p h) (sat_cons (step1625 p h) (sat_cons (step2239 p h) (sat_cons (step1584 p h) (sat_cons (step1533 p h) (sat_cons (step1904 p h) (sat_cons (step2411 p h) (sat_cons (step1573 p h) (sat_cons (step1577 p h) (sat_cons (step1529 p h) (sat_cons (step1521 p h) (sat_cons (step2412 p h) (sat_cons (step2190 p h) (sat_cons (step1526 p h) (sat_cons (step2105 p h) (sat_cons (step1537 p h) (sat_cons (step1510 p h) (sat_cons (step1928 p h) (sat_cons (step1902 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step474 p h) (sat_cons (step2338 p h) (sat_cons (step2080 p h) (sat_cons (step2418 p h) (sat_cons (step1433 p h) (sat_cons (step1439 p h) (sat_cons (step2419 p h) (sat_cons (step2076 p h) (sat_cons (step506 p h) (sat_cons (step1520 p h) (sat_cons (step464 p h) (sat_cons (step2069 p h) (sat_cons (step529 p h) (sat_cons (step521 p h) (sat_cons (step1374 p h) (sat_cons (step2415 p h) (sat_cons (step1570 p h) (sat_cons (step748 p h) (sat_cons (step754 p h) (sat_cons (step2416 p h) (sat_cons (step1417 p h) (sat_cons (step2417 p h) (sat_cons (step1934 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2421 : List Lit := [(68, false), (105, false), (1788, true)]
theorem step2421 (p : Nat → Bool) (h : Constraints p) : clause p c2421 = true :=
  Snake9.LocalRup.prove_clause [c1533, c1529, c2411, c529, c530, c1520] c2421 (by decide) p (sat_cons (step1533 p h) (sat_cons (step1529 p h) (sat_cons (step2411 p h) (sat_cons (step529 p h) (sat_cons (step530 p h) (sat_cons (step1520 p h) (sat_nil p)))))))
def c2422 : List Lit := [(1682, true), (1659, false)]
theorem step2422 (p : Nat → Bool) (h : Constraints p) : clause p c2422 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1325] c2422 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1325 p h) (sat_nil p)))
def c2423 : List Lit := [(1683, true), (1660, false)]
theorem step2423 (p : Nat → Bool) (h : Constraints p) : clause p c2423 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1326] c2423 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1326 p h) (sat_nil p)))
def c2424 : List Lit := [(1661, false), (1684, true)]
theorem step2424 (p : Nat → Bool) (h : Constraints p) : clause p c2424 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1327] c2424 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1327 p h) (sat_nil p)))
def c2425 : List Lit := [(1662, false), (1685, true)]
theorem step2425 (p : Nat → Bool) (h : Constraints p) : clause p c2425 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1328] c2425 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1328 p h) (sat_nil p)))
def c2426 : List Lit := [(1663, false), (1686, true)]
theorem step2426 (p : Nat → Bool) (h : Constraints p) : clause p c2426 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1329] c2426 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1329 p h) (sat_nil p)))
def c2427 : List Lit := [(1664, false), (1687, true)]
theorem step2427 (p : Nat → Bool) (h : Constraints p) : clause p c2427 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1330] c2427 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1330 p h) (sat_nil p)))
def c2428 : List Lit := [(1665, false), (1688, true)]
theorem step2428 (p : Nat → Bool) (h : Constraints p) : clause p c2428 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1331] c2428 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1331 p h) (sat_nil p)))
def c2429 : List Lit := [(1666, false), (1689, true)]
theorem step2429 (p : Nat → Bool) (h : Constraints p) : clause p c2429 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1332] c2429 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1332 p h) (sat_nil p)))
def c2430 : List Lit := [(1685, true), (1644, false), (1622, false)]
theorem step2430 (p : Nat → Bool) (h : Constraints p) : clause p c2430 = true :=
  Snake9.LocalRup.prove_clause [c2263, c2207] c2430 (by decide) p (sat_cons (step2263 p h) (sat_cons (step2207 p h) (sat_nil p)))
def c2431 : List Lit := [(1788, true), (104, true), (94, false), (117, false)]
theorem step2431 (p : Nat → Bool) (h : Constraints p) : clause p c2431 = true :=
  Snake9.LocalRup.prove_clause [c1533, c2411, c1529, c464, c1520] c2431 (by decide) p (sat_cons (step1533 p h) (sat_cons (step2411 p h) (sat_cons (step1529 p h) (sat_cons (step464 p h) (sat_cons (step1520 p h) (sat_nil p))))))
def c2432 : List Lit := [(1781, false), (104, true), (94, false), (1789, true), (117, false)]
theorem step2432 (p : Nat → Bool) (h : Constraints p) : clause p c2432 = true :=
  Snake9.LocalRup.prove_clause [c1518, c1534, c1530, c1527, c1520, c1538, c464, c1512, c1505] c2432 (by decide) p (sat_cons (step1518 p h) (sat_cons (step1534 p h) (sat_cons (step1530 p h) (sat_cons (step1527 p h) (sat_cons (step1520 p h) (sat_cons (step1538 p h) (sat_cons (step464 p h) (sat_cons (step1512 p h) (sat_cons (step1505 p h) (sat_nil p))))))))))
def c2433 : List Lit := [(1738, true), (93, true), (98, false), (100, false), (97, false)]
theorem step2433 (p : Nat → Bool) (h : Constraints p) : clause p c2433 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1439, c2301, c488] c2433 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1439 p h) (sat_cons (step2301 p h) (sat_cons (step488 p h) (sat_nil p)))))
def c2434 : List Lit := [(1714, true), (115, true), (1641, true), (125, false), (117, false)]
theorem step2434 (p : Nat → Bool) (h : Constraints p) : clause p c2434 = true :=
  Snake9.LocalRup.prove_clause [c2249, c2238, c2319, c1887] c2434 (by decide) p (sat_cons (step2249 p h) (sat_cons (step2238 p h) (sat_cons (step2319 p h) (sat_cons (step1887 p h) (sat_nil p)))))
def c2435 : List Lit := [(1779, true), (1776, true), (117, false)]
theorem step2435 (p : Nat → Bool) (h : Constraints p) : clause p c2435 = true :=
  Snake9.LocalRup.prove_clause [c2412, c1505, c1946, c1513, c1848, c1507] c2435 (by decide) p (sat_cons (step2412 p h) (sat_cons (step1505 p h) (sat_cons (step1946 p h) (sat_cons (step1513 p h) (sat_cons (step1848 p h) (sat_cons (step1507 p h) (sat_nil p)))))))
def c2436 : List Lit := [(101, false), (98, false), (1780, true), (115, false), (125, false), (126, false), (114, true), (117, false)]
theorem step2436 (p : Nat → Bool) (h : Constraints p) : clause p c2436 = true :=
  Snake9.LocalRup.prove_clause [c506, c826, c827, c1520, c2109, c838] c2436 (by decide) p (sat_cons (step506 p h) (sat_cons (step826 p h) (sat_cons (step827 p h) (sat_cons (step1520 p h) (sat_cons (step2109 p h) (sat_cons (step838 p h) (sat_nil p)))))))
def c2437 : List Lit := [(1777, true), (95, true), (89, false), (86, false), (109, false)]
theorem step2437 (p : Nat → Bool) (h : Constraints p) : clause p c2437 = true :=
  Snake9.LocalRup.prove_clause [c2347, c1516, c1914] c2437 (by decide) p (sat_cons (step2347 p h) (sat_cons (step1516 p h) (sat_cons (step1914 p h) (sat_nil p))))
def c2438 : List Lit := [(1737, false), (1725, false), (1747, true)]
theorem step2438 (p : Nat → Bool) (h : Constraints p) : clause p c2438 = true :=
  Snake9.LocalRup.prove_clause [c1425, c1459, c1441, c1445, c1464, c1431, c1426, c1908] c2438 (by decide) p (sat_cons (step1425 p h) (sat_cons (step1459 p h) (sat_cons (step1441 p h) (sat_cons (step1445 p h) (sat_cons (step1464 p h) (sat_cons (step1431 p h) (sat_cons (step1426 p h) (sat_cons (step1908 p h) (sat_nil p)))))))))
def c2439 : List Lit := [(86, true), (1725, false), (1747, true)]
theorem step2439 (p : Nat → Bool) (h : Constraints p) : clause p c2439 = true :=
  Snake9.LocalRup.prove_clause [c1425, c1459, c1448, c1430, c1432, c1444, c1908, c1464, c1426] c2439 (by decide) p (sat_cons (step1425 p h) (sat_cons (step1459 p h) (sat_cons (step1448 p h) (sat_cons (step1430 p h) (sat_cons (step1432 p h) (sat_cons (step1444 p h) (sat_cons (step1908 p h) (sat_cons (step1464 p h) (sat_cons (step1426 p h) (sat_nil p))))))))))
def c2440 : List Lit := [(1714, true), (77, false), (73, true), (107, false), (93, false)]
theorem step2440 (p : Nat → Bool) (h : Constraints p) : clause p c2440 = true :=
  Snake9.LocalRup.prove_clause [c1389, c1392, c1394, c1390, c1386, c687, c296, c336, c2042] c2440 (by decide) p (sat_cons (step1389 p h) (sat_cons (step1392 p h) (sat_cons (step1394 p h) (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step687 p h) (sat_cons (step296 p h) (sat_cons (step336 p h) (sat_cons (step2042 p h) (sat_nil p))))))))))
def c2441 : List Lit := [(1706, true), (62, true), (105, false)]
theorem step2441 (p : Nat → Bool) (h : Constraints p) : clause p c2441 = true :=
  Snake9.LocalRup.prove_clause [c1371, c1382, c1380, c1373, c1374, c1375, c283, c2024, c2271] c2441 (by decide) p (sat_cons (step1371 p h) (sat_cons (step1382 p h) (sat_cons (step1380 p h) (sat_cons (step1373 p h) (sat_cons (step1374 p h) (sat_cons (step1375 p h) (sat_cons (step283 p h) (sat_cons (step2024 p h) (sat_cons (step2271 p h) (sat_nil p))))))))))
def c2442 : List Lit := [(58, true), (1644, true), (93, false)]
theorem step2442 (p : Nat → Bool) (h : Constraints p) : clause p c2442 = true :=
  Snake9.LocalRup.prove_clause [c1264, c1259, c1857, c1256, c1257, c1258, c1261, c244, c2022, c1267, c259, c1252] c2442 (by decide) p (sat_cons (step1264 p h) (sat_cons (step1259 p h) (sat_cons (step1857 p h) (sat_cons (step1256 p h) (sat_cons (step1257 p h) (sat_cons (step1258 p h) (sat_cons (step1261 p h) (sat_cons (step244 p h) (sat_cons (step2022 p h) (sat_cons (step1267 p h) (sat_cons (step259 p h) (sat_cons (step1252 p h) (sat_nil p)))))))))))))
def c2443 : List Lit := [(70, false), (77, false), (58, false), (52, false), (89, false), (107, false)]
theorem step2443 (p : Nat → Bool) (h : Constraints p) : clause p c2443 = true :=
  Snake9.LocalRup.prove_clause [c570, c294, c330, c2034] c2443 (by decide) p (sat_cons (step570 p h) (sat_cons (step294 p h) (sat_cons (step330 p h) (sat_cons (step2034 p h) (sat_nil p)))))
def c2444 : List Lit := [(1789, true), (1783, false), (89, false), (86, false), (109, false), (117, false)]
theorem step2444 (p : Nat → Bool) (h : Constraints p) : clause p c2444 = true :=
  Snake9.LocalRup.prove_clause [c2347, c1542, c2362, c1511, c2241, c1913, c1509, c1916] c2444 (by decide) p (sat_cons (step2347 p h) (sat_cons (step1542 p h) (sat_cons (step2362 p h) (sat_cons (step1511 p h) (sat_cons (step2241 p h) (sat_cons (step1913 p h) (sat_cons (step1509 p h) (sat_cons (step1916 p h) (sat_nil p)))))))))
def c2445 : List Lit := [(74, false), (75, true), (70, false), (107, false), (93, false)]
theorem step2445 (p : Nat → Bool) (h : Constraints p) : clause p c2445 = true :=
  Snake9.LocalRup.prove_clause [c687, c296, c2042] c2445 (by decide) p (sat_cons (step687 p h) (sat_cons (step296 p h) (sat_cons (step2042 p h) (sat_nil p))))
def c2446 : List Lit := [(74, true), (1714, true), (1712, true), (117, false), (92, false)]
theorem step2446 (p : Nat → Bool) (h : Constraints p) : clause p c2446 = true :=
  Snake9.LocalRup.prove_clause [c2184, c1390, c662] c2446 (by decide) p (sat_cons (step2184 p h) (sat_cons (step1390 p h) (sat_cons (step662 p h) (sat_nil p))))
def c2447 : List Lit := [(74, false), (58, false), (88, true), (107, false), (93, false)]
theorem step2447 (p : Nat → Bool) (h : Constraints p) : clause p c2447 = true :=
  Snake9.LocalRup.prove_clause [c687, c254, c2067] c2447 (by decide) p (sat_cons (step687 p h) (sat_cons (step254 p h) (sat_cons (step2067 p h) (sat_nil p))))
def c2448 : List Lit := [(75, true), (73, false), (117, false)]
theorem step2448 (p : Nat → Bool) (h : Constraints p) : clause p c2448 = true :=
  Snake9.LocalRup.prove_clause [c2040, c2041, c1746] c2448 (by decide) p (sat_cons (step2040 p h) (sat_cons (step2041 p h) (sat_cons (step1746 p h) (sat_nil p))))
def c2449 : List Lit := [(1644, false), (1686, true), (1623, false)]
theorem step2449 (p : Nat → Bool) (h : Constraints p) : clause p c2449 = true :=
  Snake9.LocalRup.prove_clause [c2426, c1313, c1275, c1280, c1312, c1244, c1337, c1241, c2195] c2449 (by decide) p (sat_cons (step2426 p h) (sat_cons (step1313 p h) (sat_cons (step1275 p h) (sat_cons (step1280 p h) (sat_cons (step1312 p h) (sat_cons (step1244 p h) (sat_cons (step1337 p h) (sat_cons (step1241 p h) (sat_cons (step2195 p h) (sat_nil p))))))))))
def c2450 : List Lit := [(1812, true), (110, true), (126, true), (122, true), (117, false)]
theorem step2450 (p : Nat → Bool) (h : Constraints p) : clause p c2450 = true :=
  Snake9.LocalRup.prove_clause [c1571, c1577, c1581, c1584, c1578, c1568, c2280, c1573, c840] c2450 (by decide) p (sat_cons (step1571 p h) (sat_cons (step1577 p h) (sat_cons (step1581 p h) (sat_cons (step1584 p h) (sat_cons (step1578 p h) (sat_cons (step1568 p h) (sat_cons (step2280 p h) (sat_cons (step1573 p h) (sat_cons (step840 p h) (sat_nil p))))))))))
def c2451 : List Lit := [(1706, true), (58, false), (62, true)]
theorem step2451 (p : Nat → Bool) (h : Constraints p) : clause p c2451 = true :=
  Snake9.LocalRup.prove_clause [c1371, c1382, c1380, c1373, c1374, c1375, c283, c280, c2029] c2451 (by decide) p (sat_cons (step1371 p h) (sat_cons (step1382 p h) (sat_cons (step1380 p h) (sat_cons (step1373 p h) (sat_cons (step1374 p h) (sat_cons (step1375 p h) (sat_cons (step283 p h) (sat_cons (step280 p h) (sat_cons (step2029 p h) (sat_nil p))))))))))
def c2452 : List Lit := [(1543, false), (1594, true)]
theorem step2452 (p : Nat → Bool) (h : Constraints p) : clause p c2452 = true :=
  Snake9.LocalRup.prove_clause [c2150, c1826, c2140, c1100, c1825, c1895, c1175, c2268] c2452 (by decide) p (sat_cons (step2150 p h) (sat_cons (step1826 p h) (sat_cons (step2140 p h) (sat_cons (step1100 p h) (sat_cons (step1825 p h) (sat_cons (step1895 p h) (sat_cons (step1175 p h) (sat_cons (step2268 p h) (sat_nil p)))))))))
def c2453 : List Lit := [(15, false), (21, false), (86, false), (117, false), (92, false)]
theorem step2453 (p : Nat → Bool) (h : Constraints p) : clause p c2453 = true :=
  Snake9.LocalRup.prove_clause [c57, c389, c2063, c2064, c1758] c2453 (by decide) p (sat_cons (step57 p h) (sat_cons (step389 p h) (sat_cons (step2063 p h) (sat_cons (step2064 p h) (sat_cons (step1758 p h) (sat_nil p))))))
def c2454 : List Lit := [(1809, false), (1820, true), (1797, false), (113, true), (109, false), (107, false), (117, false)]
theorem step2454 (p : Nat → Bool) (h : Constraints p) : clause p c2454 = true :=
  Snake9.LocalRup.prove_clause [c2244, c1603, c1581, c1585, c1608, c1568, c1569, c1566, c611, c1556, c616, c579, c800, c2089] c2454 (by decide) p (sat_cons (step2244 p h) (sat_cons (step1603 p h) (sat_cons (step1581 p h) (sat_cons (step1585 p h) (sat_cons (step1608 p h) (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step1566 p h) (sat_cons (step611 p h) (sat_cons (step1556 p h) (sat_cons (step616 p h) (sat_cons (step579 p h) (sat_cons (step800 p h) (sat_cons (step2089 p h) (sat_nil p)))))))))))))))
def c2455 : List Lit := [(1775, true), (119, true), (125, false), (1804, true), (109, false), (117, false)]
theorem step2455 (p : Nat → Bool) (h : Constraints p) : clause p c2455 = true :=
  Snake9.LocalRup.prove_clause [c2330, c2258, c1570, c840] c2455 (by decide) p (sat_cons (step2330 p h) (sat_cons (step2258 p h) (sat_cons (step1570 p h) (sat_cons (step840 p h) (sat_nil p)))))
def c2456 : List Lit := [(121, false), (119, true), (125, false), (109, false), (117, false)]
theorem step2456 (p : Nat → Bool) (h : Constraints p) : clause p c2456 = true :=
  Snake9.LocalRup.prove_clause [c840, c2242] c2456 (by decide) p (sat_cons (step840 p h) (sat_cons (step2242 p h) (sat_nil p)))
def c2457 : List Lit := [(1830, true), (1797, false), (113, true), (126, true), (122, true), (109, false), (107, false), (117, false), (92, false)]
theorem step2457 (p : Nat → Bool) (h : Constraints p) : clause p c2457 = true :=
  Snake9.LocalRup.prove_clause [c1571, c1577, c2244, c2255, c1621, c1603, c1588, c2454, c1578, c1573, c669, c2420, c2455, c2456, c1568, c1584, c1602, c1625, c1541, c1537, c2435, c1526] c2457 (by decide) p (sat_cons (step1571 p h) (sat_cons (step1577 p h) (sat_cons (step2244 p h) (sat_cons (step2255 p h) (sat_cons (step1621 p h) (sat_cons (step1603 p h) (sat_cons (step1588 p h) (sat_cons (step2454 p h) (sat_cons (step1578 p h) (sat_cons (step1573 p h) (sat_cons (step669 p h) (sat_cons (step2420 p h) (sat_cons (step2455 p h) (sat_cons (step2456 p h) (sat_cons (step1568 p h) (sat_cons (step1584 p h) (sat_cons (step1602 p h) (sat_cons (step1625 p h) (sat_cons (step1541 p h) (sat_cons (step1537 p h) (sat_cons (step2435 p h) (sat_cons (step1526 p h) (sat_nil p)))))))))))))))))))))))
def c2458 : List Lit := [(1737, false), (119, true), (120, false), (1748, true), (114, true), (1761, true), (74, true), (86, true), (1706, false)]
theorem step2458 (p : Nat → Bool) (h : Constraints p) : clause p c2458 = true :=
  Snake9.LocalRup.prove_clause [c1849, c2185, c1498, c1417, c1418, c1409, c2049, c2204, c355, c1390, c1386, c1395] c2458 (by decide) p (sat_cons (step1849 p h) (sat_cons (step2185 p h) (sat_cons (step1498 p h) (sat_cons (step1417 p h) (sat_cons (step1418 p h) (sat_cons (step1409 p h) (sat_cons (step2049 p h) (sat_cons (step2204 p h) (sat_cons (step355 p h) (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step1395 p h) (sat_nil p)))))))))))))
def c2459 : List Lit := [(97, false), (108, true), (89, false), (120, false), (88, true), (92, false)]
theorem step2459 (p : Nat → Bool) (h : Constraints p) : clause p c2459 = true :=
  Snake9.LocalRup.prove_clause [c489, c403, c2058] c2459 (by decide) p (sat_cons (step489 p h) (sat_cons (step403 p h) (sat_cons (step2058 p h) (sat_nil p))))
def c2460 : List Lit := [(1737, false), (1748, true), (114, true), (1761, true), (74, true), (86, true), (1706, false), (58, false), (117, false)]
theorem step2460 (p : Nat → Bool) (h : Constraints p) : clause p c2460 = true :=
  Snake9.LocalRup.prove_clause [c1849, c2185, c1498, c1418, c1409, c2204, c1390, c1395, c1385, c1386, c2251, c330] c2460 (by decide) p (sat_cons (step1849 p h) (sat_cons (step2185 p h) (sat_cons (step1498 p h) (sat_cons (step1418 p h) (sat_cons (step1409 p h) (sat_cons (step2204 p h) (sat_cons (step1390 p h) (sat_cons (step1395 p h) (sat_cons (step1385 p h) (sat_cons (step1386 p h) (sat_cons (step2251 p h) (sat_cons (step330 p h) (sat_nil p)))))))))))))
def c2461 : List Lit := [(1760, true), (89, false), (1720, false), (114, true), (74, true), (86, true), (1706, false), (58, false), (52, false), (107, false)]
theorem step2461 (p : Nat → Bool) (h : Constraints p) : clause p c2461 = true :=
  Snake9.LocalRup.prove_clause [c2200, c1497, c1492, c1409, c2439, c1418, c2204, c2443, c1390, c1386, c1395] c2461 (by decide) p (sat_cons (step2200 p h) (sat_cons (step1497 p h) (sat_cons (step1492 p h) (sat_cons (step1409 p h) (sat_cons (step2439 p h) (sat_cons (step1418 p h) (sat_cons (step2204 p h) (sat_cons (step2443 p h) (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step1395 p h) (sat_nil p))))))))))))
def c2462 : List Lit := [(1714, true), (74, true), (117, false), (92, false)]
theorem step2462 (p : Nat → Bool) (h : Constraints p) : clause p c2462 = true :=
  Snake9.LocalRup.prove_clause [c1392, c2446] c2462 (by decide) p (sat_cons (step1392 p h) (sat_cons (step2446 p h) (sat_nil p)))
def c2463 : List Lit := [(1737, false), (1761, true), (74, true), (86, true), (1706, false), (58, false), (117, false), (92, false)]
theorem step2463 (p : Nat → Bool) (h : Constraints p) : clause p c2463 = true :=
  Snake9.LocalRup.prove_clause [c2462, c1408, c1493, c1849, c2185, c2460, c1498, c1418, c662, c1409, c1390, c1395, c1385, c1386, c2251, c330] c2463 (by decide) p (sat_cons (step2462 p h) (sat_cons (step1408 p h) (sat_cons (step1493 p h) (sat_cons (step1849 p h) (sat_cons (step2185 p h) (sat_cons (step2460 p h) (sat_cons (step1498 p h) (sat_cons (step1418 p h) (sat_cons (step662 p h) (sat_cons (step1409 p h) (sat_cons (step1390 p h) (sat_cons (step1395 p h) (sat_cons (step1385 p h) (sat_cons (step1386 p h) (sat_cons (step2251 p h) (sat_cons (step330 p h) (sat_nil p)))))))))))))))))
def c2464 : List Lit := [(1788, true), (1775, false), (117, false)]
theorem step2464 (p : Nat → Bool) (h : Constraints p) : clause p c2464 = true :=
  Snake9.LocalRup.prove_clause [c1541, c1537, c2435, c1526] c2464 (by decide) p (sat_cons (step1541 p h) (sat_cons (step1537 p h) (sat_cons (step2435 p h) (sat_cons (step1526 p h) (sat_nil p)))))
def c2465 : List Lit := [(1745, true)]
theorem step2465 (p : Nat → Bool) (h : Constraints p) : clause p c2465 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1457, c1444, c1423, c1431, c1908] c2465 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1457 p h) (sat_cons (step1444 p h) (sat_cons (step1423 p h) (sat_cons (step1431 p h) (sat_cons (step1908 p h) (sat_nil p)))))))
def c2466 : List Lit := [(1755, true)]
theorem step2466 (p : Nat → Bool) (h : Constraints p) : clause p c2466 = true :=
  Snake9.LocalRup.prove_clause [c2465, c2166] c2466 (by decide) p (sat_cons (step2465 p h) (sat_cons (step2166 p h) (sat_nil p)))
def c2467 : List Lit := [(36, false), (35, false), (20, true), (117, false), (92, false)]
theorem step2467 (p : Nat → Bool) (h : Constraints p) : clause p c2467 = true :=
  Snake9.LocalRup.prove_clause [c656, c158, c1993] c2467 (by decide) p (sat_cons (step656 p h) (sat_cons (step158 p h) (sat_cons (step1993 p h) (sat_nil p))))
def c2468 : List Lit := [(1738, false), (1758, true)]
theorem step2468 (p : Nat → Bool) (h : Constraints p) : clause p c2468 = true :=
  Snake9.LocalRup.prove_clause [c2169, c2218, c1884, c1480, c1418, c2162, c2194] c2468 (by decide) p (sat_cons (step2169 p h) (sat_cons (step2218 p h) (sat_cons (step1884 p h) (sat_cons (step1480 p h) (sat_cons (step1418 p h) (sat_cons (step2162 p h) (sat_cons (step2194 p h) (sat_nil p))))))))
def c2469 : List Lit := [(1817, true), (119, false), (42, false), (115, false), (37, false), (117, true)]
theorem step2469 (p : Nat → Bool) (h : Constraints p) : clause p c2469 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1560, c1595, c1580, c1586, c1575, c2395, c1572, c1573, c1574, c686, c1579, c1559, c1600, c1561] c2469 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1560 p h) (sat_cons (step1595 p h) (sat_cons (step1580 p h) (sat_cons (step1586 p h) (sat_cons (step1575 p h) (sat_cons (step2395 p h) (sat_cons (step1572 p h) (sat_cons (step1573 p h) (sat_cons (step1574 p h) (sat_cons (step686 p h) (sat_cons (step1579 p h) (sat_cons (step1559 p h) (sat_cons (step1600 p h) (sat_cons (step1561 p h) (sat_nil p))))))))))))))))
def c2470 : List Lit := [(1790, true), (107, true), (101, false), (29, false), (1771, false), (1775, false), (86, false), (92, false)]
theorem step2470 (p : Nat → Bool) (h : Constraints p) : clause p c2470 = true :=
  Snake9.LocalRup.prove_clause [c1522, c1524, c1547, c2197, c1514, c1523, c2226, c2347, c1527, c1513, c1543] c2470 (by decide) p (sat_cons (step1522 p h) (sat_cons (step1524 p h) (sat_cons (step1547 p h) (sat_cons (step2197 p h) (sat_cons (step1514 p h) (sat_cons (step1523 p h) (sat_cons (step2226 p h) (sat_cons (step2347 p h) (sat_cons (step1527 p h) (sat_cons (step1513 p h) (sat_cons (step1543 p h) (sat_nil p))))))))))))
def c2471 : List Lit := [(1758, true), (120, false), (43, false), (108, true), (91, true), (86, false), (1735, false), (92, false)]
theorem step2471 (p : Nat → Bool) (h : Constraints p) : clause p c2471 = true :=
  Snake9.LocalRup.prove_clause [c1436, c2169, c2468, c1883, c1439, c400, c2057, c767, c763, c2049, c1417, c1419, c2438, c2194, c1480, c2162] c2471 (by decide) p (sat_cons (step1436 p h) (sat_cons (step2169 p h) (sat_cons (step2468 p h) (sat_cons (step1883 p h) (sat_cons (step1439 p h) (sat_cons (step400 p h) (sat_cons (step2057 p h) (sat_cons (step767 p h) (sat_cons (step763 p h) (sat_cons (step2049 p h) (sat_cons (step1417 p h) (sat_cons (step1419 p h) (sat_cons (step2438 p h) (sat_cons (step2194 p h) (sat_cons (step1480 p h) (sat_cons (step2162 p h) (sat_nil p)))))))))))))))))
def c2472 : List Lit := [(128, true), (119, true), (1811, true), (114, true)]
theorem step2472 (p : Nat → Bool) (h : Constraints p) : clause p c2472 = true :=
  Snake9.LocalRup.prove_clause [c1580, c2354, c1574, c1577, c1583, c1568, c1945, c2101] c2472 (by decide) p (sat_cons (step1580 p h) (sat_cons (step2354 p h) (sat_cons (step1574 p h) (sat_cons (step1577 p h) (sat_cons (step1583 p h) (sat_cons (step1568 p h) (sat_cons (step1945 p h) (sat_cons (step2101 p h) (sat_nil p)))))))))
def c2473 : List Lit := [(120, true), (1817, true), (110, false), (1797, false), (35, false)]
theorem step2473 (p : Nat → Bool) (h : Constraints p) : clause p c2473 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1595, c1586, c1569, c1570, c1582, c601, c1600, c1555, c1563] c2473 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1595 p h) (sat_cons (step1586 p h) (sat_cons (step1569 p h) (sat_cons (step1570 p h) (sat_cons (step1582 p h) (sat_cons (step601 p h) (sat_cons (step1600 p h) (sat_cons (step1555 p h) (sat_cons (step1563 p h) (sat_nil p)))))))))))
def c2474 : List Lit := [(1634, true), (46, true), (49, true), (51, true)]
theorem step2474 (p : Nat → Bool) (h : Constraints p) : clause p c2474 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1241, c1250, c1248, c1240, c1243, c2011, c2010, c1736] c2474 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1241 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1240 p h) (sat_cons (step1243 p h) (sat_cons (step2011 p h) (sat_cons (step2010 p h) (sat_cons (step1736 p h) (sat_nil p))))))))))
def c2475 : List Lit := [(89, false), (108, true), (107, false), (91, true), (86, false), (92, false)]
theorem step2475 (p : Nat → Bool) (h : Constraints p) : clause p c2475 = true :=
  Snake9.LocalRup.prove_clause [c417, c400, c2059] c2475 (by decide) p (sat_cons (step417 p h) (sat_cons (step400 p h) (sat_cons (step2059 p h) (sat_nil p))))
def c2476 : List Lit := [(1789, true), (101, false), (29, false), (1771, false), (1775, false), (86, false)]
theorem step2476 (p : Nat → Bool) (h : Constraints p) : clause p c2476 = true :=
  Snake9.LocalRup.prove_clause [c1538, c2233, c2361, c1513] c2476 (by decide) p (sat_cons (step1538 p h) (sat_cons (step2233 p h) (sat_cons (step2361 p h) (sat_cons (step1513 p h) (sat_nil p)))))
def c2477 : List Lit := [(108, true), (120, false), (1778, true), (100, true), (87, true), (89, false), (95, true), (91, true), (86, false)]
theorem step2477 (p : Nat → Bool) (h : Constraints p) : clause p c2477 = true :=
  Snake9.LocalRup.prove_clause [c2059, c2057, c416, c489, c1509, c1506, c1517] c2477 (by decide) p (sat_cons (step2059 p h) (sat_cons (step2057 p h) (sat_cons (step416 p h) (sat_cons (step489 p h) (sat_cons (step1509 p h) (sat_cons (step1506 p h) (sat_cons (step1517 p h) (sat_nil p))))))))
def c2478 : List Lit := [(1644, true), (86, false), (58, true)]
theorem step2478 (p : Nat → Bool) (h : Constraints p) : clause p c2478 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1258, c1264, c1857, c1267, c1259, c1261, c1252, c1257, c211, c259, c237, c2018] c2478 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1258 p h) (sat_cons (step1264 p h) (sat_cons (step1857 p h) (sat_cons (step1267 p h) (sat_cons (step1259 p h) (sat_cons (step1261 p h) (sat_cons (step1252 p h) (sat_cons (step1257 p h) (sat_cons (step211 p h) (sat_cons (step259 p h) (sat_cons (step237 p h) (sat_cons (step2018 p h) (sat_nil p))))))))))))))
def c2479 : List Lit := [(1633, true), (46, false), (49, true), (51, true)]
theorem step2479 (p : Nat → Bool) (h : Constraints p) : clause p c2479 = true :=
  Snake9.LocalRup.prove_clause [c1241, c1245, c1247, c1243, c1239, c1880] c2479 (by decide) p (sat_cons (step1241 p h) (sat_cons (step1245 p h) (sat_cons (step1247 p h) (sat_cons (step1243 p h) (sat_cons (step1239 p h) (sat_cons (step1880 p h) (sat_nil p)))))))
def c2480 : List Lit := [(1817, true), (108, false), (1710, true), (89, false), (110, false), (1797, false), (35, false)]
theorem step2480 (p : Nat → Bool) (h : Constraints p) : clause p c2480 = true :=
  Snake9.LocalRup.prove_clause [c2473, c578, c572, c1555, c1387, c1563, c596, c1600, c1568, c1582] c2480 (by decide) p (sat_cons (step2473 p h) (sat_cons (step578 p h) (sat_cons (step572 p h) (sat_cons (step1555 p h) (sat_cons (step1387 p h) (sat_cons (step1563 p h) (sat_cons (step596 p h) (sat_cons (step1600 p h) (sat_cons (step1568 p h) (sat_cons (step1582 p h) (sat_nil p)))))))))))
def c2481 : List Lit := [(107, true), (1782, true), (1791, true), (1779, false), (89, false), (95, true), (86, false)]
theorem step2481 (p : Nat → Bool) (h : Constraints p) : clause p c2481 = true :=
  Snake9.LocalRup.prove_clause [c1522, c1523, c1527, c2437, c1548] c2481 (by decide) p (sat_cons (step1522 p h) (sat_cons (step1523 p h) (sat_cons (step1527 p h) (sat_cons (step2437 p h) (sat_cons (step1548 p h) (sat_nil p))))))
def c2482 : List Lit := [(1789, true), (1783, false), (1771, false), (1775, false), (86, false)]
theorem step2482 (p : Nat → Bool) (h : Constraints p) : clause p c2482 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1542, c2361, c1513] c2482 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1542 p h) (sat_cons (step2361 p h) (sat_cons (step1513 p h) (sat_nil p)))))
end B112E034
