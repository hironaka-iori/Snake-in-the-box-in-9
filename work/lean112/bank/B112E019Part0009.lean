import B112E019Part0008
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2382 : List Lit := [(1643, true), (210, true)]
theorem step2382 (p : Nat → Bool) (h : Constraints p) : clause p c2382 = true :=
  Snake9.LocalRup.prove_clause [c1490, c1494, c1482, c1484, c1468, c1479, c1480, c1476, c1477, c1465, c463, c1947, c431] c2382 (by decide) p (sat_cons (step1490 p h) (sat_cons (step1494 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1468 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step1465 p h) (sat_cons (step463 p h) (sat_cons (step1947 p h) (sat_cons (step431 p h) (sat_nil p))))))))))))))
def c2383 : List Lit := [(1705, true), (99, false), (1691, false), (1686, false), (118, true), (236, true), (116, false)]
theorem step2383 (p : Nat → Bool) (h : Constraints p) : clause p c2383 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1614, c1637, c1633, c1604, c1916, c1617, c1914, c775, c1609] c2383 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1614 p h) (sat_cons (step1637 p h) (sat_cons (step1633 p h) (sat_cons (step1604 p h) (sat_cons (step1916 p h) (sat_cons (step1617 p h) (sat_cons (step1914 p h) (sat_cons (step775 p h) (sat_cons (step1609 p h) (sat_nil p)))))))))))
def c2384 : List Lit := [(1705, true), (1688, false), (107, true), (118, true), (241, true), (76, false), (48, false), (116, false)]
theorem step2384 (p : Nat → Bool) (h : Constraints p) : clause p c2384 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1603, c1612, c1614, c1637, c1633, c1606, c1615, c1916, c1596, c1613, c2347, c705] c2384 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1603 p h) (sat_cons (step1612 p h) (sat_cons (step1614 p h) (sat_cons (step1637 p h) (sat_cons (step1633 p h) (sat_cons (step1606 p h) (sat_cons (step1615 p h) (sat_cons (step1916 p h) (sat_cons (step1596 p h) (sat_cons (step1613 p h) (sat_cons (step2347 p h) (sat_cons (step705 p h) (sat_nil p))))))))))))))
def c2385 : List Lit := [(1638, false), (1645, true), (100, true), (201, true)]
theorem step2385 (p : Nat → Bool) (h : Constraints p) : clause p c2385 = true :=
  Snake9.LocalRup.prove_clause [c1492, c1483, c1486, c1496, c1477, c1468, c1465, c1466, c385, c403] c2385 (by decide) p (sat_cons (step1492 p h) (sat_cons (step1483 p h) (sat_cons (step1486 p h) (sat_cons (step1496 p h) (sat_cons (step1477 p h) (sat_cons (step1468 p h) (sat_cons (step1465 p h) (sat_cons (step1466 p h) (sat_cons (step385 p h) (sat_cons (step403 p h) (sat_nil p)))))))))))
def c2386 : List Lit := [(1629, true), (1636, true), (100, true), (201, true)]
theorem step2386 (p : Nat → Bool) (h : Constraints p) : clause p c2386 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1466, c402, c403, c1779, c386, c1478] c2386 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1466 p h) (sat_cons (step402 p h) (sat_cons (step403 p h) (sat_cons (step1779 p h) (sat_cons (step386 p h) (sat_cons (step1478 p h) (sat_nil p))))))))
def c2387 : List Lit := [(1736, true), (102, true), (1715, false), (79, true), (82, false), (1622, false), (99, false), (1705, false), (1639, false), (81, true), (100, false), (201, true)]
theorem step2387 (p : Nat → Bool) (h : Constraints p) : clause p c2387 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1468, c1495, c1534, c1714, c1721, c1664, c1535, c1500, c1469, c1467, c588, c404, c1567, c427, c1569, c1559, c1582] c2387 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1468 p h) (sat_cons (step1495 p h) (sat_cons (step1534 p h) (sat_cons (step1714 p h) (sat_cons (step1721 p h) (sat_cons (step1664 p h) (sat_cons (step1535 p h) (sat_cons (step1500 p h) (sat_cons (step1469 p h) (sat_cons (step1467 p h) (sat_cons (step588 p h) (sat_cons (step404 p h) (sat_cons (step1567 p h) (sat_cons (step427 p h) (sat_cons (step1569 p h) (sat_cons (step1559 p h) (sat_cons (step1582 p h) (sat_nil p)))))))))))))))))))
def c2388 : List Lit := [(1543, true), (99, false), (327, true), (46, false)]
theorem step2388 (p : Nat → Bool) (h : Constraints p) : clause p c2388 = true :=
  Snake9.LocalRup.prove_clause [c988, c971, c964, c963, c1874, c986, c983, c975, c974, c1307, c2290, c1294, c1897, c171, c192, c1291] c2388 (by decide) p (sat_cons (step988 p h) (sat_cons (step971 p h) (sat_cons (step964 p h) (sat_cons (step963 p h) (sat_cons (step1874 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step975 p h) (sat_cons (step974 p h) (sat_cons (step1307 p h) (sat_cons (step2290 p h) (sat_cons (step1294 p h) (sat_cons (step1897 p h) (sat_cons (step171 p h) (sat_cons (step192 p h) (sat_cons (step1291 p h) (sat_nil p)))))))))))))))))
def c2389 : List Lit := [(1715, false), (79, true), (82, false), (1736, true), (1622, false), (99, false), (1705, false), (1639, false), (81, true), (100, false), (201, true)]
theorem step2389 (p : Nat → Bool) (h : Constraints p) : clause p c2389 = true :=
  Snake9.LocalRup.prove_clause [c1721, c2387, c1535, c587, c1500, c1467, c1469] c2389 (by decide) p (sat_cons (step1721 p h) (sat_cons (step2387 p h) (sat_cons (step1535 p h) (sat_cons (step587 p h) (sat_cons (step1500 p h) (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_nil p))))))))
def c2390 : List Lit := [(1673, true), (99, false), (100, false)]
theorem step2390 (p : Nat → Bool) (h : Constraints p) : clause p c2390 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1566, c593] c2390 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1566 p h) (sat_cons (step593 p h) (sat_nil p))))
def c2391 : List Lit := [(1557, true), (45, true), (76, false), (46, false), (116, false)]
theorem step2391 (p : Nat → Bool) (h : Constraints p) : clause p c2391 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1331, c2203, c796, c259, c255, c1006, c1005, c2115] c2391 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1331 p h) (sat_cons (step2203 p h) (sat_cons (step796 p h) (sat_cons (step259 p h) (sat_cons (step255 p h) (sat_cons (step1006 p h) (sat_cons (step1005 p h) (sat_cons (step2115 p h) (sat_nil p))))))))))
def c2392 : List Lit := [(1704, true), (109, false), (118, true), (1690, false), (48, false)]
theorem step2392 (p : Nat → Bool) (h : Constraints p) : clause p c2392 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1614, c1632, c1628, c1605, c1615, c1878, c1613] c2392 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1614 p h) (sat_cons (step1632 p h) (sat_cons (step1628 p h) (sat_cons (step1605 p h) (sat_cons (step1615 p h) (sat_cons (step1878 p h) (sat_cons (step1613 p h) (sat_nil p)))))))))
def c2393 : List Lit := [(65, false), (69, false), (1608, true), (109, false), (85, false), (72, false), (187, true), (74, true), (116, false)]
theorem step2393 (p : Nat → Bool) (h : Constraints p) : clause p c2393 = true :=
  Snake9.LocalRup.prove_clause [c298, c325, c1424, c304, c648] c2393 (by decide) p (sat_cons (step298 p h) (sat_cons (step325 p h) (sat_cons (step1424 p h) (sat_cons (step304 p h) (sat_cons (step648 p h) (sat_nil p))))))
def c2394 : List Lit := [(69, false), (109, false), (1687, true), (48, false)]
theorem step2394 (p : Nat → Bool) (h : Constraints p) : clause p c2394 = true :=
  Snake9.LocalRup.prove_clause [c697, c698, c1596] c2394 (by decide) p (sat_cons (step697 p h) (sat_cons (step698 p h) (sat_cons (step1596 p h) (sat_nil p))))
def c2395 : List Lit := [(1542, true)]
theorem step2395 (p : Nat → Bool) (h : Constraints p) : clause p c2395 = true :=
  Snake9.LocalRup.prove_clause [c1302, c1306, c1296, c2192, c1289] c2395 (by decide) p (sat_cons (step1302 p h) (sat_cons (step1306 p h) (sat_cons (step1296 p h) (sat_cons (step2192 p h) (sat_cons (step1289 p h) (sat_nil p))))))
def c2396 : List Lit := [(1573, true)]
theorem step2396 (p : Nat → Bool) (h : Constraints p) : clause p c2396 = true :=
  Snake9.LocalRup.prove_clause [c2395, c1355] c2396 (by decide) p (sat_cons (step2395 p h) (sat_cons (step1355 p h) (sat_nil p)))
def c2397 : List Lit := [(1682, true), (1640, true), (1674, false), (90, true), (99, true)]
theorem step2397 (p : Nat → Bool) (h : Constraints p) : clause p c2397 = true :=
  Snake9.LocalRup.prove_clause [c1483, c1562, c1572, c1579, c2303, c2293, c1583, c1575, c491, c1557, c1564, c1555, c1481, c1922, c434, c1480, c1485, c1477] c2397 (by decide) p (sat_cons (step1483 p h) (sat_cons (step1562 p h) (sat_cons (step1572 p h) (sat_cons (step1579 p h) (sat_cons (step2303 p h) (sat_cons (step2293 p h) (sat_cons (step1583 p h) (sat_cons (step1575 p h) (sat_cons (step491 p h) (sat_cons (step1557 p h) (sat_cons (step1564 p h) (sat_cons (step1555 p h) (sat_cons (step1481 p h) (sat_cons (step1922 p h) (sat_cons (step434 p h) (sat_cons (step1480 p h) (sat_cons (step1485 p h) (sat_cons (step1477 p h) (sat_nil p)))))))))))))))))))
def c2398 : List Lit := [(1574, true), (1565, false)]
theorem step2398 (p : Nat → Bool) (h : Constraints p) : clause p c2398 = true :=
  Snake9.LocalRup.prove_clause [c2395, c1356] c2398 (by decide) p (sat_cons (step2395 p h) (sat_cons (step1356 p h) (sat_nil p)))
def c2399 : List Lit := [(1575, true), (1566, false)]
theorem step2399 (p : Nat → Bool) (h : Constraints p) : clause p c2399 = true :=
  Snake9.LocalRup.prove_clause [c2395, c1357] c2399 (by decide) p (sat_cons (step2395 p h) (sat_cons (step1357 p h) (sat_nil p)))
def c2400 : List Lit := [(1567, false), (1576, true)]
theorem step2400 (p : Nat → Bool) (h : Constraints p) : clause p c2400 = true :=
  Snake9.LocalRup.prove_clause [c2395, c1358] c2400 (by decide) p (sat_cons (step2395 p h) (sat_cons (step1358 p h) (sat_nil p)))
def c2401 : List Lit := [(1568, false), (1577, true)]
theorem step2401 (p : Nat → Bool) (h : Constraints p) : clause p c2401 = true :=
  Snake9.LocalRup.prove_clause [c2395, c1359] c2401 (by decide) p (sat_cons (step2395 p h) (sat_cons (step1359 p h) (sat_nil p)))
def c2402 : List Lit := [(1569, false), (1578, true)]
theorem step2402 (p : Nat → Bool) (h : Constraints p) : clause p c2402 = true :=
  Snake9.LocalRup.prove_clause [c2395, c1360] c2402 (by decide) p (sat_cons (step2395 p h) (sat_cons (step1360 p h) (sat_nil p)))
def c2403 : List Lit := [(1570, false), (1579, true)]
theorem step2403 (p : Nat → Bool) (h : Constraints p) : clause p c2403 = true :=
  Snake9.LocalRup.prove_clause [c2395, c1361] c2403 (by decide) p (sat_cons (step2395 p h) (sat_cons (step1361 p h) (sat_nil p)))
def c2404 : List Lit := [(1591, true), (1517, false)]
theorem step2404 (p : Nat → Bool) (h : Constraints p) : clause p c2404 = true :=
  Snake9.LocalRup.prove_clause [c2396, c1387] c2404 (by decide) p (sat_cons (step2396 p h) (sat_cons (step1387 p h) (sat_nil p)))
def c2405 : List Lit := [(1592, true), (1518, false)]
theorem step2405 (p : Nat → Bool) (h : Constraints p) : clause p c2405 = true :=
  Snake9.LocalRup.prove_clause [c2396, c1395] c2405 (by decide) p (sat_cons (step2396 p h) (sat_cons (step1395 p h) (sat_nil p)))
def c2406 : List Lit := [(1593, true), (1519, false)]
theorem step2406 (p : Nat → Bool) (h : Constraints p) : clause p c2406 = true :=
  Snake9.LocalRup.prove_clause [c2396, c1401] c2406 (by decide) p (sat_cons (step2396 p h) (sat_cons (step1401 p h) (sat_nil p)))
def c2407 : List Lit := [(1520, false), (1594, true)]
theorem step2407 (p : Nat → Bool) (h : Constraints p) : clause p c2407 = true :=
  Snake9.LocalRup.prove_clause [c2396, c1407] c2407 (by decide) p (sat_cons (step2396 p h) (sat_cons (step1407 p h) (sat_nil p)))
def c2408 : List Lit := [(1522, false), (1596, true)]
theorem step2408 (p : Nat → Bool) (h : Constraints p) : clause p c2408 = true :=
  Snake9.LocalRup.prove_clause [c2396, c1416] c2408 (by decide) p (sat_cons (step2396 p h) (sat_cons (step1416 p h) (sat_nil p)))
def c2409 : List Lit := [(1576, true), (33, true), (43, true), (357, true)]
theorem step2409 (p : Nat → Bool) (h : Constraints p) : clause p c2409 = true :=
  Snake9.LocalRup.prove_clause [c1292, c1294, c1027, c988, c971, c964, c963, c1874, c986, c983, c976, c973, c1025, c2267, c1369, c2266, c1311, c1289, c1286, c156, c2184] c2409 (by decide) p (sat_cons (step1292 p h) (sat_cons (step1294 p h) (sat_cons (step1027 p h) (sat_cons (step988 p h) (sat_cons (step971 p h) (sat_cons (step964 p h) (sat_cons (step963 p h) (sat_cons (step1874 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step976 p h) (sat_cons (step973 p h) (sat_cons (step1025 p h) (sat_cons (step2267 p h) (sat_cons (step1369 p h) (sat_cons (step2266 p h) (sat_cons (step1311 p h) (sat_cons (step1289 p h) (sat_cons (step1286 p h) (sat_cons (step156 p h) (sat_cons (step2184 p h) (sat_nil p))))))))))))))))))))))
def c2410 : List Lit := [(1488, true), (3, false), (28, false)]
theorem step2410 (p : Nat → Bool) (h : Constraints p) : clause p c2410 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1203, c1193, c1180, c1185, c1178, c6] c2410 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1203 p h) (sat_cons (step1193 p h) (sat_cons (step1180 p h) (sat_cons (step1185 p h) (sat_cons (step1178 p h) (sat_cons (step6 p h) (sat_nil p))))))))
def c2411 : List Lit := [(63, false), (184, true), (1678, true), (103, true), (98, true), (41, false)]
theorem step2411 (p : Nat → Bool) (h : Constraints p) : clause p c2411 = true :=
  Snake9.LocalRup.prove_clause [c292, c1893, c564, c1564, c1567, c1575] c2411 (by decide) p (sat_cons (step292 p h) (sat_cons (step1893 p h) (sat_cons (step564 p h) (sat_cons (step1564 p h) (sat_cons (step1567 p h) (sat_cons (step1575 p h) (sat_nil p)))))))
def c2412 : List Lit := [(1689, false), (118, true), (1706, true), (48, false), (109, false), (1686, false)]
theorem step2412 (p : Nat → Bool) (h : Constraints p) : clause p c2412 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1614, c1642, c1604, c1638, c1615, c1613, c1878, c1607] c2412 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1614 p h) (sat_cons (step1642 p h) (sat_cons (step1604 p h) (sat_cons (step1638 p h) (sat_cons (step1615 p h) (sat_cons (step1613 p h) (sat_cons (step1878 p h) (sat_cons (step1607 p h) (sat_nil p))))))))))
def c2413 : List Lit := [(66, false), (187, true), (64, false), (65, false), (74, true), (105, true)]
theorem step2413 (p : Nat → Bool) (h : Constraints p) : clause p c2413 = true :=
  Snake9.LocalRup.prove_clause [c304, c305, c296] c2413 (by decide) p (sat_cons (step304 p h) (sat_cons (step305 p h) (sat_cons (step296 p h) (sat_nil p))))
def c2414 : List Lit := [(120, false), (1632, false), (63, true), (87, true), (1656, true), (48, false), (109, false)]
theorem step2414 (p : Nat → Bool) (h : Constraints p) : clause p c2414 = true :=
  Snake9.LocalRup.prove_clause [c699, c702, c323, c1481, c2288, c1483, c1528, c1501] c2414 (by decide) p (sat_cons (step699 p h) (sat_cons (step702 p h) (sat_cons (step323 p h) (sat_cons (step1481 p h) (sat_cons (step2288 p h) (sat_cons (step1483 p h) (sat_cons (step1528 p h) (sat_cons (step1501 p h) (sat_nil p)))))))))
def c2415 : List Lit := [(1641, false), (1656, true), (1616, false), (1607, false), (100, false), (41, false)]
theorem step2415 (p : Nat → Bool) (h : Constraints p) : clause p c2415 = true :=
  Snake9.LocalRup.prove_clause [c1425, c1449, c1528, c1492, c1497, c1535, c1468, c1454, c1466, c1428, c562] c2415 (by decide) p (sat_cons (step1425 p h) (sat_cons (step1449 p h) (sat_cons (step1528 p h) (sat_cons (step1492 p h) (sat_cons (step1497 p h) (sat_cons (step1535 p h) (sat_cons (step1468 p h) (sat_cons (step1454 p h) (sat_cons (step1466 p h) (sat_cons (step1428 p h) (sat_cons (step562 p h) (sat_nil p))))))))))))
def c2416 : List Lit := [(1627, true), (12, true), (67, false), (116, false)]
theorem step2416 (p : Nat → Bool) (h : Constraints p) : clause p c2416 = true :=
  Snake9.LocalRup.prove_clause [c1462, c1463, c377, c1936, c315, c1059, c1041, c1061, c1042, c1063, c1045, c2128] c2416 (by decide) p (sat_cons (step1462 p h) (sat_cons (step1463 p h) (sat_cons (step377 p h) (sat_cons (step1936 p h) (sat_cons (step315 p h) (sat_cons (step1059 p h) (sat_cons (step1041 p h) (sat_cons (step1061 p h) (sat_cons (step1042 p h) (sat_cons (step1063 p h) (sat_cons (step1045 p h) (sat_cons (step2128 p h) (sat_nil p)))))))))))))
def c2417 : List Lit := [(1640, true), (44, false), (116, false), (87, true), (81, false)]
theorem step2417 (p : Nat → Bool) (h : Constraints p) : clause p c2417 = true :=
  Snake9.LocalRup.prove_clause [c1480, c1483, c1485, c1481, c1476, c1477, c642, c461, c391, c469, c431, c442, c487, c1083, c1088, c1086, c1091, c2133] c2417 (by decide) p (sat_cons (step1480 p h) (sat_cons (step1483 p h) (sat_cons (step1485 p h) (sat_cons (step1481 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step642 p h) (sat_cons (step461 p h) (sat_cons (step391 p h) (sat_cons (step469 p h) (sat_cons (step431 p h) (sat_cons (step442 p h) (sat_cons (step487 p h) (sat_cons (step1083 p h) (sat_cons (step1088 p h) (sat_cons (step1086 p h) (sat_cons (step1091 p h) (sat_cons (step2133 p h) (sat_nil p)))))))))))))))))))
def c2418 : List Lit := [(1557, true), (120, false), (45, true), (116, false), (46, false)]
theorem step2418 (p : Nat → Bool) (h : Constraints p) : clause p c2418 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1331, c2203, c803, c255, c1876, c1005, c1006, c2115] c2418 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1331 p h) (sat_cons (step2203 p h) (sat_cons (step803 p h) (sat_cons (step255 p h) (sat_cons (step1876 p h) (sat_cons (step1005 p h) (sat_cons (step1006 p h) (sat_cons (step2115 p h) (sat_nil p))))))))))
def c2419 : List Lit := [(34, false), (27, false), (29, false)]
theorem step2419 (p : Nat → Bool) (h : Constraints p) : clause p c2419 = true :=
  Snake9.LocalRup.prove_clause [c2005, c99] c2419 (by decide) p (sat_cons (step2005 p h) (sat_cons (step99 p h) (sat_nil p)))
def c2420 : List Lit := [(1549, true), (44, false), (1543, true), (107, false), (120, false), (116, false)]
theorem step2420 (p : Nat → Bool) (h : Constraints p) : clause p c2420 = true :=
  Snake9.LocalRup.prove_clause [c1316, c1317, c704, c212, c220, c2356, c991, c2119, c992, c1022, c1002] c2420 (by decide) p (sat_cons (step1316 p h) (sat_cons (step1317 p h) (sat_cons (step704 p h) (sat_cons (step212 p h) (sat_cons (step220 p h) (sat_cons (step2356 p h) (sat_cons (step991 p h) (sat_cons (step2119 p h) (sat_cons (step992 p h) (sat_cons (step1022 p h) (sat_cons (step1002 p h) (sat_nil p))))))))))))
def c2421 : List Lit := [(387, true), (1621, true), (41, false), (112, false), (1622, true)]
theorem step2421 (p : Nat → Bool) (h : Constraints p) : clause p c2421 = true :=
  Snake9.LocalRup.prove_clause [c1068, c1070, c1065, c1047, c2283, c1038, c566, c1036, c292] c2421 (by decide) p (sat_cons (step1068 p h) (sat_cons (step1070 p h) (sat_cons (step1065 p h) (sat_cons (step1047 p h) (sat_cons (step2283 p h) (sat_cons (step1038 p h) (sat_cons (step566 p h) (sat_cons (step1036 p h) (sat_cons (step292 p h) (sat_nil p))))))))))
def c2422 : List Lit := [(1621, true), (63, true), (113, true), (116, false)]
theorem step2422 (p : Nat → Bool) (h : Constraints p) : clause p c2422 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1453, c2288, c1449, c1428, c323, c1050, c1436, c1438, c1423, c1056, c2125, c1433, c1434, c1431, c298, c2127, c1051, c1052, c337, c344, c1061, c2047, c2040, c1059, c377, c1932] c2422 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1453 p h) (sat_cons (step2288 p h) (sat_cons (step1449 p h) (sat_cons (step1428 p h) (sat_cons (step323 p h) (sat_cons (step1050 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1423 p h) (sat_cons (step1056 p h) (sat_cons (step2125 p h) (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step1431 p h) (sat_cons (step298 p h) (sat_cons (step2127 p h) (sat_cons (step1051 p h) (sat_cons (step1052 p h) (sat_cons (step337 p h) (sat_cons (step344 p h) (sat_cons (step1061 p h) (sat_cons (step2047 p h) (sat_cons (step2040 p h) (sat_cons (step1059 p h) (sat_cons (step377 p h) (sat_cons (step1932 p h) (sat_nil p))))))))))))))))))))))))))))
def c2423 : List Lit := [(1607, true), (75, false), (187, true), (107, false), (116, false)]
theorem step2423 (p : Nat → Bool) (h : Constraints p) : clause p c2423 = true :=
  Snake9.LocalRup.prove_clause [c1422, c2323, c354] c2423 (by decide) p (sat_cons (step1422 p h) (sat_cons (step2323 p h) (sat_cons (step354 p h) (sat_nil p))))
def c2424 : List Lit := [(66, false), (75, false), (190, false), (107, false), (116, false)]
theorem step2424 (p : Nat → Bool) (h : Constraints p) : clause p c2424 = true :=
  Snake9.LocalRup.prove_clause [c1050, c1056, c1065, c2128, c1045, c1043, c1040, c323, c651, c319, c354, c304] c2424 (by decide) p (sat_cons (step1050 p h) (sat_cons (step1056 p h) (sat_cons (step1065 p h) (sat_cons (step2128 p h) (sat_cons (step1045 p h) (sat_cons (step1043 p h) (sat_cons (step1040 p h) (sat_cons (step323 p h) (sat_cons (step651 p h) (sat_cons (step319 p h) (sat_cons (step354 p h) (sat_cons (step304 p h) (sat_nil p)))))))))))))
def c2425 : List Lit := [(46, true), (1537, true), (169, true), (69, false), (1554, true), (107, false)]
theorem step2425 (p : Nat → Bool) (h : Constraints p) : clause p c2425 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1317, c1318, c1325, c697, c221, c220, c1319, c172, c212, c1293] c2425 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1317 p h) (sat_cons (step1318 p h) (sat_cons (step1325 p h) (sat_cons (step697 p h) (sat_cons (step221 p h) (sat_cons (step220 p h) (sat_cons (step1319 p h) (sat_cons (step172 p h) (sat_cons (step212 p h) (sat_cons (step1293 p h) (sat_nil p))))))))))))
def c2426 : List Lit := [(44, true), (46, false), (1531, false), (162, true), (172, true), (99, true), (41, false), (1576, true)]
theorem step2426 (p : Nat → Bool) (h : Constraints p) : clause p c2426 = true :=
  Snake9.LocalRup.prove_clause [c1291, c2010, c1294, c171, c1307, c194, c1364, c2260] c2426 (by decide) p (sat_cons (step1291 p h) (sat_cons (step2010 p h) (sat_cons (step1294 p h) (sat_cons (step171 p h) (sat_cons (step1307 p h) (sat_cons (step194 p h) (sat_cons (step1364 p h) (sat_cons (step2260 p h) (sat_nil p)))))))))
def c2427 : List Lit := [(1682, true), (36, false), (1674, false), (99, true), (116, false)]
theorem step2427 (p : Nat → Bool) (h : Constraints p) : clause p c2427 = true :=
  Snake9.LocalRup.prove_clause [c1562, c1572, c1579, c2303, c1583, c1575, c1089, c1557, c1564, c1090, c1554, c1093, c509, c1098, c1918, c1103, c1109, c2145, c1112, c1164, c1114, c1131] c2427 (by decide) p (sat_cons (step1562 p h) (sat_cons (step1572 p h) (sat_cons (step1579 p h) (sat_cons (step2303 p h) (sat_cons (step1583 p h) (sat_cons (step1575 p h) (sat_cons (step1089 p h) (sat_cons (step1557 p h) (sat_cons (step1564 p h) (sat_cons (step1090 p h) (sat_cons (step1554 p h) (sat_cons (step1093 p h) (sat_cons (step509 p h) (sat_cons (step1098 p h) (sat_cons (step1918 p h) (sat_cons (step1103 p h) (sat_cons (step1109 p h) (sat_cons (step2145 p h) (sat_cons (step1112 p h) (sat_cons (step1164 p h) (sat_cons (step1114 p h) (sat_cons (step1131 p h) (sat_nil p)))))))))))))))))))))))
def c2428 : List Lit := [(1561, false), (1621, false), (353, true), (1551, false), (1717, false), (1639, false), (48, true), (1629, false), (116, false)]
theorem step2428 (p : Nat → Bool) (h : Constraints p) : clause p c2428 = true :=
  Snake9.LocalRup.prove_clause [c1316, c1325, c1468, c1495, c1526, c1706, c2166, c2150, c2401, c1348, c1347, c1350, c2400, c1328, c2149, c1318, c2165, c2340, c1715, c1462, c1527, c1471, c1500] c2428 (by decide) p (sat_cons (step1316 p h) (sat_cons (step1325 p h) (sat_cons (step1468 p h) (sat_cons (step1495 p h) (sat_cons (step1526 p h) (sat_cons (step1706 p h) (sat_cons (step2166 p h) (sat_cons (step2150 p h) (sat_cons (step2401 p h) (sat_cons (step1348 p h) (sat_cons (step1347 p h) (sat_cons (step1350 p h) (sat_cons (step2400 p h) (sat_cons (step1328 p h) (sat_cons (step2149 p h) (sat_cons (step1318 p h) (sat_cons (step2165 p h) (sat_cons (step2340 p h) (sat_cons (step1715 p h) (sat_cons (step1462 p h) (sat_cons (step1527 p h) (sat_cons (step1471 p h) (sat_cons (step1500 p h) (sat_nil p))))))))))))))))))))))))
def c2429 : List Lit := [(31, false), (1683, true), (24, false), (94, true), (118, true), (39, false), (38, false), (43, false), (216, true), (213, true), (145, true), (28, true), (86, false), (58, false), (1673, false), (46, false), (99, true)]
theorem step2429 (p : Nat → Bool) (h : Constraints p) : clause p c2429 = true :=
  Snake9.LocalRup.prove_clause [c157, c122, c113, c1564, c101, c1574, c1995, c408, c407, c1588, c455, c503, c1558, c2062, c1556, c517] c2429 (by decide) p (sat_cons (step157 p h) (sat_cons (step122 p h) (sat_cons (step113 p h) (sat_cons (step1564 p h) (sat_cons (step101 p h) (sat_cons (step1574 p h) (sat_cons (step1995 p h) (sat_cons (step408 p h) (sat_cons (step407 p h) (sat_cons (step1588 p h) (sat_cons (step455 p h) (sat_cons (step503 p h) (sat_cons (step1558 p h) (sat_cons (step2062 p h) (sat_cons (step1556 p h) (sat_cons (step517 p h) (sat_nil p)))))))))))))))))
def c2430 : List Lit := [(45, false), (1567, true), (44, false), (41, false), (1559, false)]
theorem step2430 (p : Nat → Bool) (h : Constraints p) : clause p c2430 = true :=
  Snake9.LocalRup.prove_clause [c192, c193, c1317, c1331, c1324, c1336, c1344] c2430 (by decide) p (sat_cons (step192 p h) (sat_cons (step193 p h) (sat_cons (step1317 p h) (sat_cons (step1331 p h) (sat_cons (step1324 p h) (sat_cons (step1336 p h) (sat_cons (step1344 p h) (sat_nil p))))))))
def c2431 : List Lit := [(1566, true), (45, false), (41, false), (172, true), (1561, false)]
theorem step2431 (p : Nat → Bool) (h : Constraints p) : clause p c2431 = true :=
  Snake9.LocalRup.prove_clause [c1343, c2260, c1324, c194, c1317] c2431 (by decide) p (sat_cons (step1343 p h) (sat_cons (step2260 p h) (sat_cons (step1324 p h) (sat_cons (step194 p h) (sat_cons (step1317 p h) (sat_nil p))))))
def c2432 : List Lit := [(1566, true), (117, true), (176, true), (1559, false)]
theorem step2432 (p : Nat → Bool) (h : Constraints p) : clause p c2432 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1340, c1343, c1336, c1324, c1876, c1317] c2432 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1340 p h) (sat_cons (step1343 p h) (sat_cons (step1336 p h) (sat_cons (step1324 p h) (sat_cons (step1876 p h) (sat_cons (step1317 p h) (sat_nil p))))))))
def c2433 : List Lit := [(279, true), (19, false), (15, true), (22, true), (18, true)]
theorem step2433 (p : Nat → Bool) (h : Constraints p) : clause p c2433 = true :=
  Snake9.LocalRup.prove_clause [c938, c939, c937, c936, c90, c84, c1991] c2433 (by decide) p (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step937 p h) (sat_cons (step936 p h) (sat_cons (step90 p h) (sat_cons (step84 p h) (sat_cons (step1991 p h) (sat_nil p))))))))
def c2434 : List Lit := [(327, true), (1681, true), (45, true), (44, false), (1544, true), (212, true), (41, false), (43, true)]
theorem step2434 (p : Nat → Bool) (h : Constraints p) : clause p c2434 = true :=
  Snake9.LocalRup.prove_clause [c986, c2375, c983, c2259, c975, c2320, c974, c160, c171] c2434 (by decide) p (sat_cons (step986 p h) (sat_cons (step2375 p h) (sat_cons (step983 p h) (sat_cons (step2259 p h) (sat_cons (step975 p h) (sat_cons (step2320 p h) (sat_cons (step974 p h) (sat_cons (step160 p h) (sat_cons (step171 p h) (sat_nil p))))))))))
def c2435 : List Lit := [(162, true), (1681, true), (45, true), (44, false), (212, true), (41, false)]
theorem step2435 (p : Nat → Bool) (h : Constraints p) : clause p c2435 = true :=
  Snake9.LocalRup.prove_clause [c2263, c171, c2259, c1762, c2320] c2435 (by decide) p (sat_cons (step2263 p h) (sat_cons (step171 p h) (sat_cons (step2259 p h) (sat_cons (step1762 p h) (sat_cons (step2320 p h) (sat_nil p))))))
def c2436 : List Lit := [(1566, true), (117, true), (41, false), (1559, false)]
theorem step2436 (p : Nat → Bool) (h : Constraints p) : clause p c2436 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1340, c1343, c2432, c1336, c1324, c256, c1006, c1331, c1317, c262, c2115, c194, c1005, c255] c2436 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1340 p h) (sat_cons (step1343 p h) (sat_cons (step2432 p h) (sat_cons (step1336 p h) (sat_cons (step1324 p h) (sat_cons (step256 p h) (sat_cons (step1006 p h) (sat_cons (step1331 p h) (sat_cons (step1317 p h) (sat_cons (step262 p h) (sat_cons (step2115 p h) (sat_cons (step194 p h) (sat_cons (step1005 p h) (sat_cons (step255 p h) (sat_nil p))))))))))))))))
def c2437 : List Lit := [(1703, true), (117, true), (116, true)]
theorem step2437 (p : Nat → Bool) (h : Constraints p) : clause p c2437 = true :=
  Snake9.LocalRup.prove_clause [c1608, c1616, c1623, c1627, c1619, c1617, c1602, c1610, c1611, c1612, c1594, c1595, c829, c846, c715, c836] c2437 (by decide) p (sat_cons (step1608 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step1627 p h) (sat_cons (step1619 p h) (sat_cons (step1617 p h) (sat_cons (step1602 p h) (sat_cons (step1610 p h) (sat_cons (step1611 p h) (sat_cons (step1612 p h) (sat_cons (step1594 p h) (sat_cons (step1595 p h) (sat_cons (step829 p h) (sat_cons (step846 p h) (sat_cons (step715 p h) (sat_cons (step836 p h) (sat_nil p)))))))))))))))))
def c2438 : List Lit := [(1644, true), (210, true), (1627, false)]
theorem step2438 (p : Nat → Bool) (h : Constraints p) : clause p c2438 = true :=
  Snake9.LocalRup.prove_clause [c1470, c1499, c1495, c2277, c1471, c1482, c1465, c1479, c1480, c462] c2438 (by decide) p (sat_cons (step1470 p h) (sat_cons (step1499 p h) (sat_cons (step1495 p h) (sat_cons (step2277 p h) (sat_cons (step1471 p h) (sat_cons (step1482 p h) (sat_cons (step1465 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step462 p h) (sat_nil p)))))))))))
def c2439 : List Lit := [(1644, true), (44, false), (1627, false), (116, false)]
theorem step2439 (p : Nat → Bool) (h : Constraints p) : clause p c2439 = true :=
  Snake9.LocalRup.prove_clause [c1470, c1499, c1495, c2438, c1471, c1482, c1484, c476, c1088, c1465, c1480, c1476, c1477, c1091, c460, c642, c391, c469, c2133, c442, c1086, c1083] c2439 (by decide) p (sat_cons (step1470 p h) (sat_cons (step1499 p h) (sat_cons (step1495 p h) (sat_cons (step2438 p h) (sat_cons (step1471 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step476 p h) (sat_cons (step1088 p h) (sat_cons (step1465 p h) (sat_cons (step1480 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step1091 p h) (sat_cons (step460 p h) (sat_cons (step642 p h) (sat_cons (step391 p h) (sat_cons (step469 p h) (sat_cons (step2133 p h) (sat_cons (step442 p h) (sat_cons (step1086 p h) (sat_cons (step1083 p h) (sat_nil p)))))))))))))))))))))))
def c2440 : List Lit := [(1643, true), (25, true)]
theorem step2440 (p : Nat → Bool) (h : Constraints p) : clause p c2440 = true :=
  Snake9.LocalRup.prove_clause [c1490, c1494, c2382, c1484, c1468, c476, c1088, c1476, c1477, c1465, c1091, c391, c469, c431, c1093, c418, c2134, c1076, c1081, c1077] c2440 (by decide) p (sat_cons (step1490 p h) (sat_cons (step1494 p h) (sat_cons (step2382 p h) (sat_cons (step1484 p h) (sat_cons (step1468 p h) (sat_cons (step476 p h) (sat_cons (step1088 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step1465 p h) (sat_cons (step1091 p h) (sat_cons (step391 p h) (sat_cons (step469 p h) (sat_cons (step431 p h) (sat_cons (step1093 p h) (sat_cons (step418 p h) (sat_cons (step2134 p h) (sat_cons (step1076 p h) (sat_cons (step1081 p h) (sat_cons (step1077 p h) (sat_nil p)))))))))))))))))))))
def c2441 : List Lit := [(1616, true), (75, false), (387, true), (74, false), (12, true)]
theorem step2441 (p : Nat → Bool) (h : Constraints p) : clause p c2441 = true :=
  Snake9.LocalRup.prove_clause [c1070, c1045, c1042, c1041, c1068, c1065, c1054, c1052, c1436, c1438, c1434, c1431, c337, c315, c358] c2441 (by decide) p (sat_cons (step1070 p h) (sat_cons (step1045 p h) (sat_cons (step1042 p h) (sat_cons (step1041 p h) (sat_cons (step1068 p h) (sat_cons (step1065 p h) (sat_cons (step1054 p h) (sat_cons (step1052 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1434 p h) (sat_cons (step1431 p h) (sat_cons (step337 p h) (sat_cons (step315 p h) (sat_cons (step358 p h) (sat_nil p))))))))))))))))
def c2442 : List Lit := [(1702, true), (116, false), (241, true)]
theorem step2442 (p : Nat → Bool) (h : Constraints p) : clause p c2442 = true :=
  Snake9.LocalRup.prove_clause [c1622, c1626, c1614, c1602, c1611, c1612, c1929, c2313] c2442 (by decide) p (sat_cons (step1622 p h) (sat_cons (step1626 p h) (sat_cons (step1614 p h) (sat_cons (step1602 p h) (sat_cons (step1611 p h) (sat_cons (step1612 p h) (sat_cons (step1929 p h) (sat_cons (step2313 p h) (sat_nil p)))))))))
def c2443 : List Lit := [(1566, true), (172, true), (175, true), (41, false), (1559, false)]
theorem step2443 (p : Nat → Bool) (h : Constraints p) : clause p c2443 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1340, c1343, c2260, c2431, c1336, c1324, c255, c1317, c2203] c2443 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1340 p h) (sat_cons (step1343 p h) (sat_cons (step2260 p h) (sat_cons (step2431 p h) (sat_cons (step1336 p h) (sat_cons (step1324 p h) (sat_cons (step255 p h) (sat_cons (step1317 p h) (sat_cons (step2203 p h) (sat_nil p)))))))))))
def c2444 : List Lit := [(341, false), (76, false), (1566, true), (74, false), (1559, false)]
theorem step2444 (p : Nat → Bool) (h : Constraints p) : clause p c2444 = true :=
  Snake9.LocalRup.prove_clause [c1008, c2115, c2117, c1006, c1012, c2432, c1011, c368, c1808] c2444 (by decide) p (sat_cons (step1008 p h) (sat_cons (step2115 p h) (sat_cons (step2117 p h) (sat_cons (step1006 p h) (sat_cons (step1012 p h) (sat_cons (step2432 p h) (sat_cons (step1011 p h) (sat_cons (step368 p h) (sat_cons (step1808 p h) (sat_nil p))))))))))
def c2445 : List Lit := [(44, true), (1551, true), (41, true), (1545, true), (43, true)]
theorem step2445 (p : Nat → Bool) (h : Constraints p) : clause p c2445 = true :=
  Snake9.LocalRup.prove_clause [c1288, c1305, c1293, c2310, c1298, c1309] c2445 (by decide) p (sat_cons (step1288 p h) (sat_cons (step1305 p h) (sat_cons (step1293 p h) (sat_cons (step2310 p h) (sat_cons (step1298 p h) (sat_cons (step1309 p h) (sat_nil p)))))))
end B112E019
