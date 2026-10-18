import B112E052Part0007
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2502 : List Lit := [(80, true), (67, true), (69, false), (56, false), (63, false), (53, false), (1715, true), (3, false)]
theorem step2502 (p : Nat → Bool) (h : Constraints p) : clause p c2502 = true :=
  Snake9.LocalRup.prove_clause [c2500, c2282, c284, c1534, c1544, c1575, c1557, c2501, c1547, c1548, c1554, c320, c318, c1579, c1537, c1545] c2502 (by decide) p (sat_cons (step2500 p h) (sat_cons (step2282 p h) (sat_cons (step284 p h) (sat_cons (step1534 p h) (sat_cons (step1544 p h) (sat_cons (step1575 p h) (sat_cons (step1557 p h) (sat_cons (step2501 p h) (sat_cons (step1547 p h) (sat_cons (step1548 p h) (sat_cons (step1554 p h) (sat_cons (step320 p h) (sat_cons (step318 p h) (sat_cons (step1579 p h) (sat_cons (step1537 p h) (sat_cons (step1545 p h) (sat_nil p)))))))))))))))))
def c2503 : List Lit := [(67, true), (69, false), (56, false), (63, false), (62, false), (53, false), (1720, true), (1715, true), (1562, true)]
theorem step2503 (p : Nat → Bool) (h : Constraints p) : clause p c2503 = true :=
  Snake9.LocalRup.prove_clause [c2500, c2037, c1253, c1247, c1264, c2034, c2030, c2499, c2502, c403, c402, c404, c1549, c1547, c1584, c1555, c2130, c1575, c1534, c1544] c2503 (by decide) p (sat_cons (step2500 p h) (sat_cons (step2037 p h) (sat_cons (step1253 p h) (sat_cons (step1247 p h) (sat_cons (step1264 p h) (sat_cons (step2034 p h) (sat_cons (step2030 p h) (sat_cons (step2499 p h) (sat_cons (step2502 p h) (sat_cons (step403 p h) (sat_cons (step402 p h) (sat_cons (step404 p h) (sat_cons (step1549 p h) (sat_cons (step1547 p h) (sat_cons (step1584 p h) (sat_cons (step1555 p h) (sat_cons (step2130 p h) (sat_cons (step1575 p h) (sat_cons (step1534 p h) (sat_cons (step1544 p h) (sat_nil p)))))))))))))))))))))
def c2504 : List Lit := [(80, false), (1709, true), (1695, false), (67, false), (63, false), (1715, true), (8, false)]
theorem step2504 (p : Nat → Bool) (h : Constraints p) : clause p c2504 = true :=
  Snake9.LocalRup.prove_clause [c403, c402, c1549, c1547, c1558, c1556, c1555, c1548, c1551, c1575, c2055, c1542] c2504 (by decide) p (sat_cons (step403 p h) (sat_cons (step402 p h) (sat_cons (step1549 p h) (sat_cons (step1547 p h) (sat_cons (step1558 p h) (sat_cons (step1556 p h) (sat_cons (step1555 p h) (sat_cons (step1548 p h) (sat_cons (step1551 p h) (sat_cons (step1575 p h) (sat_cons (step2055 p h) (sat_cons (step1542 p h) (sat_nil p)))))))))))))
def c2505 : List Lit := [(77, false), (1698, true), (69, false), (53, false)]
theorem step2505 (p : Nat → Bool) (h : Constraints p) : clause p c2505 = true :=
  Snake9.LocalRup.prove_clause [c320, c318, c1537] c2505 (by decide) p (sat_cons (step320 p h) (sat_cons (step318 p h) (sat_cons (step1537 p h) (sat_nil p))))
def c2506 : List Lit := [(1698, true), (72, true), (1709, true), (79, true), (67, false), (69, false), (53, false)]
theorem step2506 (p : Nat → Bool) (h : Constraints p) : clause p c2506 = true :=
  Snake9.LocalRup.prove_clause [c2505, c1548, c1558, c1550, c2150, c2186, c1537] c2506 (by decide) p (sat_cons (step2505 p h) (sat_cons (step1548 p h) (sat_cons (step1558 p h) (sat_cons (step1550 p h) (sat_cons (step2150 p h) (sat_cons (step2186 p h) (sat_cons (step1537 p h) (sat_nil p))))))))
def c2507 : List Lit := [(84, false), (67, false), (69, false), (56, false), (63, false), (62, false), (53, false), (1715, true), (1562, true)]
theorem step2507 (p : Nat → Bool) (h : Constraints p) : clause p c2507 = true :=
  Snake9.LocalRup.prove_clause [c2500, c2037, c1253, c1247, c1251, c1248, c1264, c2034, c2030, c370, c2130, c1533, c1541, c1572, c2504, c2501, c1547, c2506, c1542, c1575, c1557, c1555, c1548, c1549, c1550, c2310, c2305, c358] c2507 (by decide) p (sat_cons (step2500 p h) (sat_cons (step2037 p h) (sat_cons (step1253 p h) (sat_cons (step1247 p h) (sat_cons (step1251 p h) (sat_cons (step1248 p h) (sat_cons (step1264 p h) (sat_cons (step2034 p h) (sat_cons (step2030 p h) (sat_cons (step370 p h) (sat_cons (step2130 p h) (sat_cons (step1533 p h) (sat_cons (step1541 p h) (sat_cons (step1572 p h) (sat_cons (step2504 p h) (sat_cons (step2501 p h) (sat_cons (step1547 p h) (sat_cons (step2506 p h) (sat_cons (step1542 p h) (sat_cons (step1575 p h) (sat_cons (step1557 p h) (sat_cons (step1555 p h) (sat_cons (step1548 p h) (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step2310 p h) (sat_cons (step2305 p h) (sat_cons (step358 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2508 : List Lit := [(1708, true), (72, true), (80, true), (69, false), (62, false), (7, false)]
theorem step2508 (p : Nat → Bool) (h : Constraints p) : clause p c2508 = true :=
  Snake9.LocalRup.prove_clause [c1547, c1557, c1555, c1548, c1549, c1550, c368, c2310, c2305, c358] c2508 (by decide) p (sat_cons (step1547 p h) (sat_cons (step1557 p h) (sat_cons (step1555 p h) (sat_cons (step1548 p h) (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step368 p h) (sat_cons (step2310 p h) (sat_cons (step2305 p h) (sat_cons (step358 p h) (sat_nil p)))))))))))
def c2509 : List Lit := [(62, false), (88, true), (86, false), (87, false), (1720, true), (1715, true), (54, false), (1562, true), (1648, true)]
theorem step2509 (p : Nat → Bool) (h : Constraints p) : clause p c2509 = true :=
  Snake9.LocalRup.prove_clause [c2192, c1391, c2037, c1253, c1247, c1251, c1248, c1264, c2034, c2030, c1416, c1412, c2496, c1387, c1395, c2100, c1419, c1407, c1409, c1404, c1402, c230, c2263, c2500, c2503, c2507, c1584, c404, c2282, c2501, c284, c1533, c1541, c1572, c2508, c1575, c1542, c2505, c2506, c1548, c369, c1558, c1550] c2509 (by decide) p (sat_cons (step2192 p h) (sat_cons (step1391 p h) (sat_cons (step2037 p h) (sat_cons (step1253 p h) (sat_cons (step1247 p h) (sat_cons (step1251 p h) (sat_cons (step1248 p h) (sat_cons (step1264 p h) (sat_cons (step2034 p h) (sat_cons (step2030 p h) (sat_cons (step1416 p h) (sat_cons (step1412 p h) (sat_cons (step2496 p h) (sat_cons (step1387 p h) (sat_cons (step1395 p h) (sat_cons (step2100 p h) (sat_cons (step1419 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1404 p h) (sat_cons (step1402 p h) (sat_cons (step230 p h) (sat_cons (step2263 p h) (sat_cons (step2500 p h) (sat_cons (step2503 p h) (sat_cons (step2507 p h) (sat_cons (step1584 p h) (sat_cons (step404 p h) (sat_cons (step2282 p h) (sat_cons (step2501 p h) (sat_cons (step284 p h) (sat_cons (step1533 p h) (sat_cons (step1541 p h) (sat_cons (step1572 p h) (sat_cons (step2508 p h) (sat_cons (step1575 p h) (sat_cons (step1542 p h) (sat_cons (step2505 p h) (sat_cons (step2506 p h) (sat_cons (step1548 p h) (sat_cons (step369 p h) (sat_cons (step1558 p h) (sat_cons (step1550 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c2510 : List Lit := [(1720, true), (1715, true), (56, false), (62, false), (63, false), (69, false), (53, false), (1562, true)]
theorem step2510 (p : Nat → Bool) (h : Constraints p) : clause p c2510 = true :=
  Snake9.LocalRup.prove_clause [c2500, c2037, c1253, c1247, c1251, c1248, c1264, c2034, c2030, c2503, c2507, c1584, c404, c2282, c2501, c284, c2508, c1533, c1575, c1541, c1542, c1572, c2505, c2506, c1548, c369, c1558, c1550] c2510 (by decide) p (sat_cons (step2500 p h) (sat_cons (step2037 p h) (sat_cons (step1253 p h) (sat_cons (step1247 p h) (sat_cons (step1251 p h) (sat_cons (step1248 p h) (sat_cons (step1264 p h) (sat_cons (step2034 p h) (sat_cons (step2030 p h) (sat_cons (step2503 p h) (sat_cons (step2507 p h) (sat_cons (step1584 p h) (sat_cons (step404 p h) (sat_cons (step2282 p h) (sat_cons (step2501 p h) (sat_cons (step284 p h) (sat_cons (step2508 p h) (sat_cons (step1533 p h) (sat_cons (step1575 p h) (sat_cons (step1541 p h) (sat_cons (step1542 p h) (sat_cons (step1572 p h) (sat_cons (step2505 p h) (sat_cons (step2506 p h) (sat_cons (step1548 p h) (sat_cons (step369 p h) (sat_cons (step1558 p h) (sat_cons (step1550 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2511 : List Lit := [(1737, true), (87, true), (1724, false), (1719, false)]
theorem step2511 (p : Nat → Bool) (h : Constraints p) : clause p c2511 = true :=
  Snake9.LocalRup.prove_clause [c1624, c1620, c1592, c1602, c1604, c2090, c1587, c1600, c1596, c573] c2511 (by decide) p (sat_cons (step1624 p h) (sat_cons (step1620 p h) (sat_cons (step1592 p h) (sat_cons (step1602 p h) (sat_cons (step1604 p h) (sat_cons (step2090 p h) (sat_cons (step1587 p h) (sat_cons (step1600 p h) (sat_cons (step1596 p h) (sat_cons (step573 p h) (sat_nil p)))))))))))
def c2512 : List Lit := [(1765, true), (104, true), (96, true), (100, true), (92, true), (95, false)]
theorem step2512 (p : Nat → Bool) (h : Constraints p) : clause p c2512 = true :=
  Snake9.LocalRup.prove_clause [c1686, c1689, c1695, c1697, c1690, c1687, c719, c2343] c2512 (by decide) p (sat_cons (step1686 p h) (sat_cons (step1689 p h) (sat_cons (step1695 p h) (sat_cons (step1697 p h) (sat_cons (step1690 p h) (sat_cons (step1687 p h) (sat_cons (step719 p h) (sat_cons (step2343 p h) (sat_nil p)))))))))
def c2513 : List Lit := [(51, false), (57, true), (53, false), (1732, true), (54, false)]
theorem step2513 (p : Nat → Bool) (h : Constraints p) : clause p c2513 = true :=
  Snake9.LocalRup.prove_clause [c1603, c211, c2269, c2271, c246, c1600, c1601, c1605, c553, c1596] c2513 (by decide) p (sat_cons (step1603 p h) (sat_cons (step211 p h) (sat_cons (step2269 p h) (sat_cons (step2271 p h) (sat_cons (step246 p h) (sat_cons (step1600 p h) (sat_cons (step1601 p h) (sat_cons (step1605 p h) (sat_cons (step553 p h) (sat_cons (step1596 p h) (sat_nil p)))))))))))
def c2514 : List Lit := [(57, false), (53, false), (1730, true), (54, false), (1648, true)]
theorem step2514 (p : Nat → Bool) (h : Constraints p) : clause p c2514 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1412, c259, c260, c1936, c2100, c1402, c1403, c1601, c1387, c1410, c246, c1405, c2260, c273] c2514 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1412 p h) (sat_cons (step259 p h) (sat_cons (step260 p h) (sat_cons (step1936 p h) (sat_cons (step2100 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step1601 p h) (sat_cons (step1387 p h) (sat_cons (step1410 p h) (sat_cons (step246 p h) (sat_cons (step1405 p h) (sat_cons (step2260 p h) (sat_cons (step273 p h) (sat_nil p))))))))))))))))
def c2515 : List Lit := [(95, true), (51, false), (57, true), (1732, true), (54, false)]
theorem step2515 (p : Nat → Bool) (h : Constraints p) : clause p c2515 = true :=
  Snake9.LocalRup.prove_clause [c1603, c1599, c1601, c1605, c246, c1596, c2268, c552] c2515 (by decide) p (sat_cons (step1603 p h) (sat_cons (step1599 p h) (sat_cons (step1601 p h) (sat_cons (step1605 p h) (sat_cons (step246 p h) (sat_cons (step1596 p h) (sat_cons (step2268 p h) (sat_cons (step552 p h) (sat_nil p)))))))))
def c2516 : List Lit := [(90, true), (51, false), (57, true), (1732, true), (54, false)]
theorem step2516 (p : Nat → Bool) (h : Constraints p) : clause p c2516 = true :=
  Snake9.LocalRup.prove_clause [c2515, c1607, c1597, c1598, c1605, c553, c1600, c2268, c246] c2516 (by decide) p (sat_cons (step2515 p h) (sat_cons (step1607 p h) (sat_cons (step1597 p h) (sat_cons (step1598 p h) (sat_cons (step1605 p h) (sat_cons (step553 p h) (sat_cons (step1600 p h) (sat_cons (step2268 p h) (sat_cons (step246 p h) (sat_nil p))))))))))
def c2517 : List Lit := [(1570, false), (1587, true), (17, true), (19, true)]
theorem step2517 (p : Nat → Bool) (h : Constraints p) : clause p c2517 = true :=
  Snake9.LocalRup.prove_clause [c2425, c1271, c1281, c1284, c1313, c1273, c2196, c2213] c2517 (by decide) p (sat_cons (step2425 p h) (sat_cons (step1271 p h) (sat_cons (step1281 p h) (sat_cons (step1284 p h) (sat_cons (step1313 p h) (sat_cons (step1273 p h) (sat_cons (step2196 p h) (sat_cons (step2213 p h) (sat_nil p)))))))))
def c2518 : List Lit := [(56, false), (74, false), (1713, true), (3, false)]
theorem step2518 (p : Nat → Bool) (h : Constraints p) : clause p c2518 = true :=
  Snake9.LocalRup.prove_clause [c347, c348, c1536, c1547, c1538, c1554, c1566, c1570, c1557, c1555, c1539, c1541, c1548, c1550, c2055, c1532] c2518 (by decide) p (sat_cons (step347 p h) (sat_cons (step348 p h) (sat_cons (step1536 p h) (sat_cons (step1547 p h) (sat_cons (step1538 p h) (sat_cons (step1554 p h) (sat_cons (step1566 p h) (sat_cons (step1570 p h) (sat_cons (step1557 p h) (sat_cons (step1555 p h) (sat_cons (step1539 p h) (sat_cons (step1541 p h) (sat_cons (step1548 p h) (sat_cons (step1550 p h) (sat_cons (step2055 p h) (sat_cons (step1532 p h) (sat_nil p)))))))))))))))))
def c2519 : List Lit := [(1619, true), (35, false)]
theorem step2519 (p : Nat → Bool) (h : Constraints p) : clause p c2519 = true :=
  Snake9.LocalRup.prove_clause [c1363, c1364, c1361, c1357, c1358, c192, c138, c2243] c2519 (by decide) p (sat_cons (step1363 p h) (sat_cons (step1364 p h) (sat_cons (step1361 p h) (sat_cons (step1357 p h) (sat_cons (step1358 p h) (sat_cons (step192 p h) (sat_cons (step138 p h) (sat_cons (step2243 p h) (sat_nil p)))))))))
def c2520 : List Lit := [(1585, true), (20, true), (94, false)]
theorem step2520 (p : Nat → Bool) (h : Constraints p) : clause p c2520 = true :=
  Snake9.LocalRup.prove_clause [c1274, c1277, c2423, c1304, c1278, c1280, c1296, c2172, c1276, c1272, c2492, c59, c2213] c2520 (by decide) p (sat_cons (step1274 p h) (sat_cons (step1277 p h) (sat_cons (step2423 p h) (sat_cons (step1304 p h) (sat_cons (step1278 p h) (sat_cons (step1280 p h) (sat_cons (step1296 p h) (sat_cons (step2172 p h) (sat_cons (step1276 p h) (sat_cons (step1272 p h) (sat_cons (step2492 p h) (sat_cons (step59 p h) (sat_cons (step2213 p h) (sat_nil p))))))))))))))
def c2521 : List Lit := [(78, false), (77, false), (68, false), (7, false)]
theorem step2521 (p : Nat → Bool) (h : Constraints p) : clause p c2521 = true :=
  Snake9.LocalRup.prove_clause [c376, c2305, c2306, c1950] c2521 (by decide) p (sat_cons (step376 p h) (sat_cons (step2305 p h) (sat_cons (step2306 p h) (sat_cons (step1950 p h) (sat_nil p)))))
def c2522 : List Lit := [(77, false), (68, false), (1703, false), (7, false), (1713, true)]
theorem step2522 (p : Nat → Bool) (h : Constraints p) : clause p c2522 = true :=
  Snake9.LocalRup.prove_clause [c2521, c1550, c1555, c1566, c1538, c1540, c1535, c1532, c2132, c372] c2522 (by decide) p (sat_cons (step2521 p h) (sat_cons (step1550 p h) (sat_cons (step1555 p h) (sat_cons (step1566 p h) (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step1535 p h) (sat_cons (step1532 p h) (sat_cons (step2132 p h) (sat_cons (step372 p h) (sat_nil p)))))))))))
def c2523 : List Lit := [(1800, true), (114, true), (113, false)]
theorem step2523 (p : Nat → Bool) (h : Constraints p) : clause p c2523 = true :=
  Snake9.LocalRup.prove_clause [c1736, c1744, c1773, c1769, c2193, c1758, c1751] c2523 (by decide) p (sat_cons (step1736 p h) (sat_cons (step1744 p h) (sat_cons (step1773 p h) (sat_cons (step1769 p h) (sat_cons (step2193 p h) (sat_cons (step1758 p h) (sat_cons (step1751 p h) (sat_nil p))))))))
def c2524 : List Lit := [(1777, true), (106, false), (30, false), (107, true), (102, true)]
theorem step2524 (p : Nat → Bool) (h : Constraints p) : clause p c2524 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1707, c1688, c1691, c1719, c1723, c1710, c1692, c1701, c1690, c741] c2524 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1707 p h) (sat_cons (step1688 p h) (sat_cons (step1691 p h) (sat_cons (step1719 p h) (sat_cons (step1723 p h) (sat_cons (step1710 p h) (sat_cons (step1692 p h) (sat_cons (step1701 p h) (sat_cons (step1690 p h) (sat_cons (step741 p h) (sat_nil p))))))))))))
def c2525 : List Lit := [(1788, true), (114, true), (113, false), (35, false)]
theorem step2525 (p : Nat → Bool) (h : Constraints p) : clause p c2525 = true :=
  Snake9.LocalRup.prove_clause [c1736, c1747, c1745, c1738, c1740, c835] c2525 (by decide) p (sat_cons (step1736 p h) (sat_cons (step1747 p h) (sat_cons (step1745 p h) (sat_cons (step1738 p h) (sat_cons (step1740 p h) (sat_cons (step835 p h) (sat_nil p)))))))
def c2526 : List Lit := [(1801, true), (1788, false), (108, false), (1783, false), (113, false), (35, false)]
theorem step2526 (p : Nat → Bool) (h : Constraints p) : clause p c2526 = true :=
  Snake9.LocalRup.prove_clause [c1774, c1756, c1758, c1753, c1751, c2112, c837] c2526 (by decide) p (sat_cons (step1774 p h) (sat_cons (step1756 p h) (sat_cons (step1758 p h) (sat_cons (step1753 p h) (sat_cons (step1751 p h) (sat_cons (step2112 p h) (sat_cons (step837 p h) (sat_nil p))))))))
def c2527 : List Lit := [(17, false), (21, true), (143, true), (20, true)]
theorem step2527 (p : Nat → Bool) (h : Constraints p) : clause p c2527 = true :=
  Snake9.LocalRup.prove_clause [c2216, c2218, c1922, c48] c2527 (by decide) p (sat_cons (step2216 p h) (sat_cons (step2218 p h) (sat_cons (step1922 p h) (sat_cons (step48 p h) (sat_nil p)))))
def c2528 : List Lit := [(110, false), (1803, true), (1785, false), (105, true), (116, true), (114, true), (113, false), (35, false)]
theorem step2528 (p : Nat → Bool) (h : Constraints p) : clause p c2528 = true :=
  Snake9.LocalRup.prove_clause [c832, c834, c1738, c2093, c1748, c1780] c2528 (by decide) p (sat_cons (step832 p h) (sat_cons (step834 p h) (sat_cons (step1738 p h) (sat_cons (step2093 p h) (sat_cons (step1748 p h) (sat_cons (step1780 p h) (sat_nil p)))))))
def c2529 : List Lit := [(1641, true), (210, true), (82, true), (81, false), (79, true), (65, false), (72, false)]
theorem step2529 (p : Nat → Bool) (h : Constraints p) : clause p c2529 = true :=
  Snake9.LocalRup.prove_clause [c1404, c1405, c412, c2130, c2308, c433] c2529 (by decide) p (sat_cons (step1404 p h) (sat_cons (step1405 p h) (sat_cons (step412 p h) (sat_cons (step2130 p h) (sat_cons (step2308 p h) (sat_cons (step433 p h) (sat_nil p)))))))
def c2530 : List Lit := [(1620, true), (33, false), (39, true), (35, false), (122, false)]
theorem step2530 (p : Nat → Bool) (h : Constraints p) : clause p c2530 = true :=
  Snake9.LocalRup.prove_clause [c1358, c1367, c1365, c1359, c1361, c193, c136, c2243] c2530 (by decide) p (sat_cons (step1358 p h) (sat_cons (step1367 p h) (sat_cons (step1365 p h) (sat_cons (step1359 p h) (sat_cons (step1361 p h) (sat_cons (step193 p h) (sat_cons (step136 p h) (sat_cons (step2243 p h) (sat_nil p)))))))))
def c2531 : List Lit := [(81, false), (80, true), (1719, true)]
theorem step2531 (p : Nat → Bool) (h : Constraints p) : clause p c2531 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1582, c2308, c431] c2531 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1582 p h) (sat_cons (step2308 p h) (sat_cons (step431 p h) (sat_nil p)))))
def c2532 : List Lit := [(72, false), (1701, true), (82, false), (71, true), (8, false), (1645, true), (62, true), (74, false), (3, false)]
theorem step2532 (p : Nat → Bool) (h : Constraints p) : clause p c2532 = true :=
  Snake9.LocalRup.prove_clause [c348, c349, c1402, c1537, c1411, c1406, c402, c2300, c344, c1532, c1542] c2532 (by decide) p (sat_cons (step348 p h) (sat_cons (step349 p h) (sat_cons (step1402 p h) (sat_cons (step1537 p h) (sat_cons (step1411 p h) (sat_cons (step1406 p h) (sat_cons (step402 p h) (sat_cons (step2300 p h) (sat_cons (step344 p h) (sat_cons (step1532 p h) (sat_cons (step1542 p h) (sat_nil p))))))))))))
def c2533 : List Lit := [(1813, true), (1764, false), (1767, false), (1788, false), (1783, false), (110, true), (113, false), (35, false)]
theorem step2533 (p : Nat → Bool) (h : Constraints p) : clause p c2533 = true :=
  Snake9.LocalRup.prove_clause [c1702, c1708, c1724, c1773, c1813, c1819, c2526, c1725, c1704, c1709] c2533 (by decide) p (sat_cons (step1702 p h) (sat_cons (step1708 p h) (sat_cons (step1724 p h) (sat_cons (step1773 p h) (sat_cons (step1813 p h) (sat_cons (step1819 p h) (sat_cons (step2526 p h) (sat_cons (step1725 p h) (sat_cons (step1704 p h) (sat_cons (step1709 p h) (sat_nil p)))))))))))
def c2534 : List Lit := [(1571, true), (94, false), (20, false)]
theorem step2534 (p : Nat → Bool) (h : Constraints p) : clause p c2534 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1279, c1275, c1271, c1272, c70, c59, c2221] c2534 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1279 p h) (sat_cons (step1275 p h) (sat_cons (step1271 p h) (sat_cons (step1272 p h) (sat_cons (step70 p h) (sat_cons (step59 p h) (sat_cons (step2221 p h) (sat_nil p)))))))))
def c2535 : List Lit := [(1747, true), (90, true), (1719, true)]
theorem step2535 (p : Nat → Bool) (h : Constraints p) : clause p c2535 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1604, c2062, c2053, c2096, c1650, c2138, c1611] c2535 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1604 p h) (sat_cons (step2062 p h) (sat_cons (step2053 p h) (sat_cons (step2096 p h) (sat_cons (step1650 p h) (sat_cons (step2138 p h) (sat_cons (step1611 p h) (sat_nil p)))))))))
def c2536 : List Lit := [(1736, true), (90, true)]
theorem step2536 (p : Nat → Bool) (h : Constraints p) : clause p c2536 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1604, c1611, c1615, c2138, c1588] c2536 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1604 p h) (sat_cons (step1611 p h) (sat_cons (step1615 p h) (sat_cons (step2138 p h) (sat_cons (step1588 p h) (sat_nil p)))))))
def c2537 : List Lit := [(1811, true), (1767, false), (1788, false), (1783, false), (110, true), (113, false), (35, false)]
theorem step2537 (p : Nat → Bool) (h : Constraints p) : clause p c2537 = true :=
  Snake9.LocalRup.prove_clause [c1702, c1708, c1714, c1773, c1805, c1799, c1715, c2526, c1709, c1704] c2537 (by decide) p (sat_cons (step1702 p h) (sat_cons (step1708 p h) (sat_cons (step1714 p h) (sat_cons (step1773 p h) (sat_cons (step1805 p h) (sat_cons (step1799 p h) (sat_cons (step1715 p h) (sat_cons (step2526 p h) (sat_cons (step1709 p h) (sat_cons (step1704 p h) (sat_nil p)))))))))))
def c2538 : List Lit := [(44, false), (1621, true), (39, true), (35, false), (122, false)]
theorem step2538 (p : Nat → Bool) (h : Constraints p) : clause p c2538 = true :=
  Snake9.LocalRup.prove_clause [c193, c194, c1359, c1361, c1368] c2538 (by decide) p (sat_cons (step193 p h) (sat_cons (step194 p h) (sat_cons (step1359 p h) (sat_cons (step1361 p h) (sat_cons (step1368 p h) (sat_nil p))))))
def c2539 : List Lit := [(1733, true), (92, false), (18, false), (94, true), (90, true)]
theorem step2539 (p : Nat → Bool) (h : Constraints p) : clause p c2539 = true :=
  Snake9.LocalRup.prove_clause [c1600, c1597, c1606, c1608, c1601, c1598, c543] c2539 (by decide) p (sat_cons (step1600 p h) (sat_cons (step1597 p h) (sat_cons (step1606 p h) (sat_cons (step1608 p h) (sat_cons (step1601 p h) (sat_cons (step1598 p h) (sat_cons (step543 p h) (sat_nil p))))))))
def c2540 : List Lit := [(1761, true), (1759, true), (101, true), (1767, true), (88, false)]
theorem step2540 (p : Nat → Bool) (h : Constraints p) : clause p c2540 = true :=
  Snake9.LocalRup.prove_clause [c1700, c1699, c1686, c759, c1685, c1688, c1689, c725, c714, c2338, c2342, c639] c2540 (by decide) p (sat_cons (step1700 p h) (sat_cons (step1699 p h) (sat_cons (step1686 p h) (sat_cons (step759 p h) (sat_cons (step1685 p h) (sat_cons (step1688 p h) (sat_cons (step1689 p h) (sat_cons (step725 p h) (sat_cons (step714 p h) (sat_cons (step2338 p h) (sat_cons (step2342 p h) (sat_cons (step639 p h) (sat_nil p)))))))))))))
def c2541 : List Lit := [(102, false), (1790, true), (106, true), (53, true), (1767, true), (92, false), (18, false), (113, false), (1637, true), (35, false), (122, false)]
theorem step2541 (p : Nat → Bool) (h : Constraints p) : clause p c2541 = true :=
  Snake9.LocalRup.prove_clause [c1700, c1699, c551, c540, c714, c2190, c1392, c2346, c937, c1397, c1388] c2541 (by decide) p (sat_cons (step1700 p h) (sat_cons (step1699 p h) (sat_cons (step551 p h) (sat_cons (step540 p h) (sat_cons (step714 p h) (sat_cons (step2190 p h) (sat_cons (step1392 p h) (sat_cons (step2346 p h) (sat_cons (step937 p h) (sat_cons (step1397 p h) (sat_cons (step1388 p h) (sat_nil p))))))))))))
def c2542 : List Lit := [(93, false), (1741, true), (1751, true), (1730, false), (96, false), (103, false), (1724, false), (87, true), (90, true)]
theorem step2542 (p : Nat → Bool) (h : Constraints p) : clause p c2542 = true :=
  Snake9.LocalRup.prove_clause [c578, c581, c1587, c1598, c1609, c1623, c1628, c1654, c1592, c2062] c2542 (by decide) p (sat_cons (step578 p h) (sat_cons (step581 p h) (sat_cons (step1587 p h) (sat_cons (step1598 p h) (sat_cons (step1609 p h) (sat_cons (step1623 p h) (sat_cons (step1628 p h) (sat_cons (step1654 p h) (sat_cons (step1592 p h) (sat_cons (step2062 p h) (sat_nil p)))))))))))
def c2543 : List Lit := [(1795, false), (1813, true), (1789, false), (53, true), (1759, false), (1767, true), (92, false), (18, false), (113, false), (1637, true), (35, false), (122, false)]
theorem step2543 (p : Nat → Bool) (h : Constraints p) : clause p c2543 = true :=
  Snake9.LocalRup.prove_clause [c834, c1702, c1705, c1693, c1718, c1801, c1700, c1699, c1779, c1783, c1807, c1723, c1694, c1688, c1689, c2541, c762] c2543 (by decide) p (sat_cons (step834 p h) (sat_cons (step1702 p h) (sat_cons (step1705 p h) (sat_cons (step1693 p h) (sat_cons (step1718 p h) (sat_cons (step1801 p h) (sat_cons (step1700 p h) (sat_cons (step1699 p h) (sat_cons (step1779 p h) (sat_cons (step1783 p h) (sat_cons (step1807 p h) (sat_cons (step1723 p h) (sat_cons (step1694 p h) (sat_cons (step1688 p h) (sat_cons (step1689 p h) (sat_cons (step2541 p h) (sat_cons (step762 p h) (sat_nil p))))))))))))))))))
def c2544 : List Lit := [(1795, true), (1767, true)]
theorem step2544 (p : Nat → Bool) (h : Constraints p) : clause p c2544 = true :=
  Snake9.LocalRup.prove_clause [c1700, c1756, c2200, c1753, c2107] c2544 (by decide) p (sat_cons (step1700 p h) (sat_cons (step1756 p h) (sat_cons (step2200 p h) (sat_cons (step1753 p h) (sat_cons (step2107 p h) (sat_nil p))))))
def c2545 : List Lit := [(1751, true), (1722, false), (1734, false), (1712, false)]
theorem step2545 (p : Nat → Bool) (h : Constraints p) : clause p c2545 = true :=
  Snake9.LocalRup.prove_clause [c1589, c1623, c1647, c1654, c1628, c2062, c1592] c2545 (by decide) p (sat_cons (step1589 p h) (sat_cons (step1623 p h) (sat_cons (step1647 p h) (sat_cons (step1654 p h) (sat_cons (step1628 p h) (sat_cons (step2062 p h) (sat_cons (step1592 p h) (sat_nil p))))))))
def c2546 : List Lit := [(1649, false), (20, false), (1679, true), (7, false), (44, true)]
theorem step2546 (p : Nat → Bool) (h : Constraints p) : clause p c2546 = true :=
  Snake9.LocalRup.prove_clause [c2439, c2432, c1484, c1446, c2426, c2487, c2037, c1247, c1253] c2546 (by decide) p (sat_cons (step2439 p h) (sat_cons (step2432 p h) (sat_cons (step1484 p h) (sat_cons (step1446 p h) (sat_cons (step2426 p h) (sat_cons (step2487 p h) (sat_cons (step2037 p h) (sat_cons (step1247 p h) (sat_cons (step1253 p h) (sat_nil p))))))))))
def c2547 : List Lit := [(1580, true), (15, false), (101, true), (44, true)]
theorem step2547 (p : Nat → Bool) (h : Constraints p) : clause p c2547 = true :=
  Snake9.LocalRup.prove_clause [c2172, c2196, c2232] c2547 (by decide) p (sat_cons (step2172 p h) (sat_cons (step2196 p h) (sat_cons (step2232 p h) (sat_nil p))))
def c2548 : List Lit := [(1648, true), (7, false), (101, true), (1633, false), (122, false)]
theorem step2548 (p : Nat → Bool) (h : Constraints p) : clause p c2548 = true :=
  Snake9.LocalRup.prove_clause [c1393, c1419, c2110, c1407, c371, c1405] c2548 (by decide) p (sat_cons (step1393 p h) (sat_cons (step1419 p h) (sat_cons (step2110 p h) (sat_cons (step1407 p h) (sat_cons (step371 p h) (sat_cons (step1405 p h) (sat_nil p)))))))
def c2549 : List Lit := [(1721, false), (1724, true), (1750, true), (1734, false)]
theorem step2549 (p : Nat → Bool) (h : Constraints p) : clause p c2549 = true :=
  Snake9.LocalRup.prove_clause [c1588, c1591, c1618, c2062, c1653] c2549 (by decide) p (sat_cons (step1588 p h) (sat_cons (step1591 p h) (sat_cons (step1618 p h) (sat_cons (step2062 p h) (sat_cons (step1653 p h) (sat_nil p))))))
def c2550 : List Lit := [(1748, true), (65, true), (100, false), (122, false)]
theorem step2550 (p : Nat → Bool) (h : Constraints p) : clause p c2550 = true :=
  Snake9.LocalRup.prove_clause [c2164, c2166, c1651] c2550 (by decide) p (sat_cons (step2164 p h) (sat_cons (step2166 p h) (sat_cons (step1651 p h) (sat_nil p))))
def c2551 : List Lit := [(1714, true), (1719, true), (65, true), (71, true), (122, false)]
theorem step2551 (p : Nat → Bool) (h : Constraints p) : clause p c2551 = true :=
  Snake9.LocalRup.prove_clause [c1582, c1535, c1533, c1541, c1571, c2109, c2060, c401] c2551 (by decide) p (sat_cons (step1582 p h) (sat_cons (step1535 p h) (sat_cons (step1533 p h) (sat_cons (step1541 p h) (sat_cons (step1571 p h) (sat_cons (step2109 p h) (sat_cons (step2060 p h) (sat_cons (step401 p h) (sat_nil p)))))))))
def c2552 : List Lit := [(1713, true), (65, true), (71, true), (122, false)]
theorem step2552 (p : Nat → Bool) (h : Constraints p) : clause p c2552 = true :=
  Snake9.LocalRup.prove_clause [c1535, c1533, c1541, c1573, c1570, c1544, c1542, c1552, c2159, c1534, c1537, c1550, c2186] c2552 (by decide) p (sat_cons (step1535 p h) (sat_cons (step1533 p h) (sat_cons (step1541 p h) (sat_cons (step1573 p h) (sat_cons (step1570 p h) (sat_cons (step1544 p h) (sat_cons (step1542 p h) (sat_cons (step1552 p h) (sat_cons (step2159 p h) (sat_cons (step1534 p h) (sat_cons (step1537 p h) (sat_cons (step1550 p h) (sat_cons (step2186 p h) (sat_nil p))))))))))))))
def c2553 : List Lit := [(92, true), (1572, true), (1721, true), (1733, true), (90, true)]
theorem step2553 (p : Nat → Bool) (h : Constraints p) : clause p c2553 = true :=
  Snake9.LocalRup.prove_clause [c1585, c2497, c1598, c1608, c1599, c2099, c2191, c2219] c2553 (by decide) p (sat_cons (step1585 p h) (sat_cons (step2497 p h) (sat_cons (step1598 p h) (sat_cons (step1608 p h) (sat_cons (step1599 p h) (sat_cons (step2099 p h) (sat_cons (step2191 p h) (sat_cons (step2219 p h) (sat_nil p)))))))))
def c2554 : List Lit := [(95, false), (94, false), (92, false), (1572, true), (87, false)]
theorem step2554 (p : Nat → Bool) (h : Constraints p) : clause p c2554 = true :=
  Snake9.LocalRup.prove_clause [c2191, c546] c2554 (by decide) p (sat_cons (step2191 p h) (sat_cons (step546 p h) (sat_nil p)))
def c2555 : List Lit := [(94, false), (1572, true), (1721, true), (1733, true), (90, true)]
theorem step2555 (p : Nat → Bool) (h : Constraints p) : clause p c2555 = true :=
  Snake9.LocalRup.prove_clause [c2553, c1586, c1585, c2554, c1599, c1608, c1598, c2102, c573, c2327] c2555 (by decide) p (sat_cons (step2553 p h) (sat_cons (step1586 p h) (sat_cons (step1585 p h) (sat_cons (step2554 p h) (sat_cons (step1599 p h) (sat_cons (step1608 p h) (sat_cons (step1598 p h) (sat_cons (step2102 p h) (sat_cons (step573 p h) (sat_cons (step2327 p h) (sat_nil p)))))))))))
def c2556 : List Lit := [(1702, false), (1749, true), (90, true)]
theorem step2556 (p : Nat → Bool) (h : Constraints p) : clause p c2556 = true :=
  Snake9.LocalRup.prove_clause [c2536, c1667, c1578, c1579, c1659, c2051, c2168] c2556 (by decide) p (sat_cons (step2536 p h) (sat_cons (step1667 p h) (sat_cons (step1578 p h) (sat_cons (step1579 p h) (sat_cons (step1659 p h) (sat_cons (step2051 p h) (sat_cons (step2168 p h) (sat_nil p))))))))
def c2557 : List Lit := [(87, true), (1738, true), (1719, false), (90, true)]
theorem step2557 (p : Nat → Bool) (h : Constraints p) : clause p c2557 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1604, c1625, c1592, c1585, c1587, c1591, c1621, c1607, c1605, c1598, c1599, c1600, c2136, c562] c2557 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1604 p h) (sat_cons (step1625 p h) (sat_cons (step1592 p h) (sat_cons (step1585 p h) (sat_cons (step1587 p h) (sat_cons (step1591 p h) (sat_cons (step1621 p h) (sat_cons (step1607 p h) (sat_cons (step1605 p h) (sat_cons (step1598 p h) (sat_cons (step1599 p h) (sat_cons (step1600 p h) (sat_cons (step2136 p h) (sat_cons (step562 p h) (sat_nil p))))))))))))))))
def c2558 : List Lit := [(1801, true), (121, true), (1783, false), (118, true)]
theorem step2558 (p : Nat → Bool) (h : Constraints p) : clause p c2558 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1745, c1778, c1774, c1746, c1756, c1758, c1741, c1753, c1750, c2372, c952] c2558 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1745 p h) (sat_cons (step1778 p h) (sat_cons (step1774 p h) (sat_cons (step1746 p h) (sat_cons (step1756 p h) (sat_cons (step1758 p h) (sat_cons (step1741 p h) (sat_cons (step1753 p h) (sat_cons (step1750 p h) (sat_cons (step2372 p h) (sat_cons (step952 p h) (sat_nil p)))))))))))))
def c2559 : List Lit := [(1764, true), (101, true), (88, true), (95, false), (98, true), (96, true)]
theorem step2559 (p : Nat → Bool) (h : Constraints p) : clause p c2559 = true :=
  Snake9.LocalRup.prove_clause [c1686, c1696, c1694, c1687, c1688, c2334, c719] c2559 (by decide) p (sat_cons (step1686 p h) (sat_cons (step1696 p h) (sat_cons (step1694 p h) (sat_cons (step1687 p h) (sat_cons (step1688 p h) (sat_cons (step2334 p h) (sat_cons (step719 p h) (sat_nil p))))))))
def c2560 : List Lit := [(1633, false), (1585, false), (1625, false), (1681, true), (101, true), (122, false)]
theorem step2560 (p : Nat → Bool) (h : Constraints p) : clause p c2560 = true :=
  Snake9.LocalRup.prove_clause [c2045, c1493, c1452, c1393, c2548, c1418, c1248, c1451, c1251, c1500, c2037, c1325] c2560 (by decide) p (sat_cons (step2045 p h) (sat_cons (step1493 p h) (sat_cons (step1452 p h) (sat_cons (step1393 p h) (sat_cons (step2548 p h) (sat_cons (step1418 p h) (sat_cons (step1248 p h) (sat_cons (step1451 p h) (sat_cons (step1251 p h) (sat_cons (step1500 p h) (sat_cons (step2037 p h) (sat_cons (step1325 p h) (sat_nil p)))))))))))))
def c2561 : List Lit := [(1571, false), (44, false), (1585, true), (1633, false), (1625, false), (1681, true), (122, false)]
theorem step2561 (p : Nat → Bool) (h : Constraints p) : clause p c2561 = true :=
  Snake9.LocalRup.prove_clause [c1393, c1418, c1451, c1500, c2422, c1304, c1329, c2172, c2039, c188, c191, c190, c179, c1347, c1361, c1357, c1248, c1349, c1365, c1251, c1254, c2037, c1247, c1324, c1493, c1452, c1457, c1423, c1375, c1378, c1396, c1368, c1350, c1388, c1359, c1348, c158, c153, c2244] c2561 (by decide) p (sat_cons (step1393 p h) (sat_cons (step1418 p h) (sat_cons (step1451 p h) (sat_cons (step1500 p h) (sat_cons (step2422 p h) (sat_cons (step1304 p h) (sat_cons (step1329 p h) (sat_cons (step2172 p h) (sat_cons (step2039 p h) (sat_cons (step188 p h) (sat_cons (step191 p h) (sat_cons (step190 p h) (sat_cons (step179 p h) (sat_cons (step1347 p h) (sat_cons (step1361 p h) (sat_cons (step1357 p h) (sat_cons (step1248 p h) (sat_cons (step1349 p h) (sat_cons (step1365 p h) (sat_cons (step1251 p h) (sat_cons (step1254 p h) (sat_cons (step2037 p h) (sat_cons (step1247 p h) (sat_cons (step1324 p h) (sat_cons (step1493 p h) (sat_cons (step1452 p h) (sat_cons (step1457 p h) (sat_cons (step1423 p h) (sat_cons (step1375 p h) (sat_cons (step1378 p h) (sat_cons (step1396 p h) (sat_cons (step1368 p h) (sat_cons (step1350 p h) (sat_cons (step1388 p h) (sat_cons (step1359 p h) (sat_cons (step1348 p h) (sat_cons (step158 p h) (sat_cons (step153 p h) (sat_cons (step2244 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c2562 : List Lit := [(17, false), (21, true), (95, false), (87, false)]
theorem step2562 (p : Nat → Bool) (h : Constraints p) : clause p c2562 = true :=
  Snake9.LocalRup.prove_clause [c481, c2216] c2562 (by decide) p (sat_cons (step481 p h) (sat_cons (step2216 p h) (sat_nil p)))
def c2563 : List Lit := [(27, false), (44, false), (1625, true), (122, false)]
theorem step2563 (p : Nat → Bool) (h : Constraints p) : clause p c2563 = true :=
  Snake9.LocalRup.prove_clause [c188, c191, c190, c1347, c1361, c1357, c1349, c1365, c1374] c2563 (by decide) p (sat_cons (step188 p h) (sat_cons (step191 p h) (sat_cons (step190 p h) (sat_cons (step1347 p h) (sat_cons (step1361 p h) (sat_cons (step1357 p h) (sat_cons (step1349 p h) (sat_cons (step1365 p h) (sat_cons (step1374 p h) (sat_nil p))))))))))
def c2564 : List Lit := [(7, false), (44, false), (1625, true), (122, false)]
theorem step2564 (p : Nat → Bool) (h : Constraints p) : clause p c2564 = true :=
  Snake9.LocalRup.prove_clause [c182, c184, c185, c1347, c1357, c1361, c1349, c1365, c1374] c2564 (by decide) p (sat_cons (step182 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step1347 p h) (sat_cons (step1357 p h) (sat_cons (step1361 p h) (sat_cons (step1349 p h) (sat_cons (step1365 p h) (sat_cons (step1374 p h) (sat_nil p))))))))))
def c2565 : List Lit := [(1617, false), (33, false), (3, false), (46, false), (35, true), (1625, true), (20, false)]
theorem step2565 (p : Nat → Bool) (h : Constraints p) : clause p c2565 = true :=
  Snake9.LocalRup.prove_clause [c1347, c1349, c1374, c1363, c1365, c1377, c1358, c1350, c157, c152, c1348, c2244] c2565 (by decide) p (sat_cons (step1347 p h) (sat_cons (step1349 p h) (sat_cons (step1374 p h) (sat_cons (step1363 p h) (sat_cons (step1365 p h) (sat_cons (step1377 p h) (sat_cons (step1358 p h) (sat_cons (step1350 p h) (sat_cons (step157 p h) (sat_cons (step152 p h) (sat_cons (step1348 p h) (sat_cons (step2244 p h) (sat_nil p)))))))))))))
end B112E052
