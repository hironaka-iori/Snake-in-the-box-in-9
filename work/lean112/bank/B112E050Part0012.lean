import B112E050Part0011
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2584 : List Lit := [(1707, true), (1738, true), (73, false), (80, true), (63, false), (87, true)]
theorem step2584 (p : Nat → Bool) (h : Constraints p) : clause p c2584 = true :=
  Snake9.LocalRup.prove_clause [c2274, c2390, c1424, c1432] c2584 (by decide) p (sat_cons (step2274 p h) (sat_cons (step2390 p h) (sat_cons (step1424 p h) (sat_cons (step1432 p h) (sat_nil p)))))
def c2585 : List Lit := [(1660, true), (73, false), (1738, true), (1707, true), (62, true), (1646, false), (87, true)]
theorem step2585 (p : Nat → Bool) (h : Constraints p) : clause p c2585 = true :=
  Snake9.LocalRup.prove_clause [c1370, c1369, c1250, c1266, c1253, c1255, c1251, c1247, c236, c2390, c1905, c1432, c257, c1424] c2585 (by decide) p (sat_cons (step1370 p h) (sat_cons (step1369 p h) (sat_cons (step1250 p h) (sat_cons (step1266 p h) (sat_cons (step1253 p h) (sat_cons (step1255 p h) (sat_cons (step1251 p h) (sat_cons (step1247 p h) (sat_cons (step236 p h) (sat_cons (step2390 p h) (sat_cons (step1905 p h) (sat_cons (step1432 p h) (sat_cons (step257 p h) (sat_cons (step1424 p h) (sat_nil p)))))))))))))))
def c2586 : List Lit := [(85, false), (1718, true), (123, false), (80, false)]
theorem step2586 (p : Nat → Bool) (h : Constraints p) : clause p c2586 = true :=
  Snake9.LocalRup.prove_clause [c339, c338, c1388] c2586 (by decide) p (sat_cons (step339 p h) (sat_cons (step338 p h) (sat_cons (step1388 p h) (sat_nil p))))
def c2587 : List Lit := [(62, false), (1721, true), (123, false), (80, false)]
theorem step2587 (p : Nat → Bool) (h : Constraints p) : clause p c2587 = true :=
  Snake9.LocalRup.prove_clause [c324, c327, c329, c1384, c1388, c1393] c2587 (by decide) p (sat_cons (step324 p h) (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step1384 p h) (sat_cons (step1388 p h) (sat_cons (step1393 p h) (sat_nil p)))))))
def c2588 : List Lit := [(1734, false), (72, true), (1763, true), (1745, false), (1721, false), (1718, false)]
theorem step2588 (p : Nat → Bool) (h : Constraints p) : clause p c2588 = true :=
  Snake9.LocalRup.prove_clause [c1399, c1496, c1464, c1426, c1429, c1459, c1502, c1400, c1404, c1396, c1375, c1385, c1373, c1955] c2588 (by decide) p (sat_cons (step1399 p h) (sat_cons (step1496 p h) (sat_cons (step1464 p h) (sat_cons (step1426 p h) (sat_cons (step1429 p h) (sat_cons (step1459 p h) (sat_cons (step1502 p h) (sat_cons (step1400 p h) (sat_cons (step1404 p h) (sat_cons (step1396 p h) (sat_cons (step1375 p h) (sat_cons (step1385 p h) (sat_cons (step1373 p h) (sat_cons (step1955 p h) (sat_nil p)))))))))))))))
def c2589 : List Lit := [(1736, true), (76, true), (85, false), (87, true), (80, false)]
theorem step2589 (p : Nat → Bool) (h : Constraints p) : clause p c2589 = true :=
  Snake9.LocalRup.prove_clause [c1422, c2275, c1428, c365, c1420, c2107] c2589 (by decide) p (sat_cons (step1422 p h) (sat_cons (step2275 p h) (sat_cons (step1428 p h) (sat_cons (step365 p h) (sat_cons (step1420 p h) (sat_cons (step2107 p h) (sat_nil p)))))))
def c2590 : List Lit := [(62, false), (1763, true), (1745, false), (87, true), (1721, false), (1718, false), (123, false), (80, false)]
theorem step2590 (p : Nat → Bool) (h : Constraints p) : clause p c2590 = true :=
  Snake9.LocalRup.prove_clause [c324, c330, c2588, c1424] c2590 (by decide) p (sat_cons (step324 p h) (sat_cons (step330 p h) (sat_cons (step2588 p h) (sat_cons (step1424 p h) (sat_nil p)))))
def c2591 : List Lit := [(80, false), (62, false), (123, false), (1721, false), (1763, true), (87, true), (1745, false)]
theorem step2591 (p : Nat → Bool) (h : Constraints p) : clause p c2591 = true :=
  Snake9.LocalRup.prove_clause [c327, c329, c2590, c1388] c2591 (by decide) p (sat_cons (step327 p h) (sat_cons (step329 p h) (sat_cons (step2590 p h) (sat_cons (step1388 p h) (sat_nil p)))))
def c2592 : List Lit := [(1746, false), (1721, false), (1763, true), (87, true)]
theorem step2592 (p : Nat → Bool) (h : Constraints p) : clause p c2592 = true :=
  Snake9.LocalRup.prove_clause [c1399, c1496, c1422, c1425, c1455, c1460, c1502, c1426, c2275, c1404, c1424, c1377, c1369, c1370, c257] c2592 (by decide) p (sat_cons (step1399 p h) (sat_cons (step1496 p h) (sat_cons (step1422 p h) (sat_cons (step1425 p h) (sat_cons (step1455 p h) (sat_cons (step1460 p h) (sat_cons (step1502 p h) (sat_cons (step1426 p h) (sat_cons (step2275 p h) (sat_cons (step1404 p h) (sat_cons (step1424 p h) (sat_cons (step1377 p h) (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step257 p h) (sat_nil p))))))))))))))))
def c2593 : List Lit := [(67, false), (63, false), (65, false), (66, false), (1737, true), (87, true)]
theorem step2593 (p : Nat → Bool) (h : Constraints p) : clause p c2593 = true :=
  Snake9.LocalRup.prove_clause [c257, c1777, c1424, c1429, c1419, c1420, c350, c2083] c2593 (by decide) p (sat_cons (step257 p h) (sat_cons (step1777 p h) (sat_cons (step1424 p h) (sat_cons (step1429 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step350 p h) (sat_cons (step2083 p h) (sat_nil p)))))))))
def c2594 : List Lit := [(51, false), (49, true), (55, true), (60, false)]
theorem step2594 (p : Nat → Bool) (h : Constraints p) : clause p c2594 = true :=
  Snake9.LocalRup.prove_clause [c2060, c2062, c1765] c2594 (by decide) p (sat_cons (step2060 p h) (sat_cons (step2062 p h) (sat_cons (step1765 p h) (sat_nil p))))
def c2595 : List Lit := [(1830, true), (123, true), (1816, false), (1777, false), (108, true)]
theorem step2595 (p : Nat → Bool) (h : Constraints p) : clause p c2595 = true :=
  Snake9.LocalRup.prove_clause [c1536, c1538, c1561, c1648, c1654, c2234, c1562, c2442, c1539, c1537] c2595 (by decide) p (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1561 p h) (sat_cons (step1648 p h) (sat_cons (step1654 p h) (sat_cons (step2234 p h) (sat_cons (step1562 p h) (sat_cons (step2442 p h) (sat_cons (step1539 p h) (sat_cons (step1537 p h) (sat_nil p)))))))))))
def c2596 : List Lit := [(1816, false), (1830, true), (102, false), (108, true), (1772, false), (27, false)]
theorem step2596 (p : Nat → Bool) (h : Constraints p) : clause p c2596 = true :=
  Snake9.LocalRup.prove_clause [c1892, c1530, c1536, c1538, c1654, c2595, c1566, c2340, c1531] c2596 (by decide) p (sat_cons (step1892 p h) (sat_cons (step1530 p h) (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1654 p h) (sat_cons (step2595 p h) (sat_cons (step1566 p h) (sat_cons (step2340 p h) (sat_cons (step1531 p h) (sat_nil p))))))))))
def c2597 : List Lit := [(1830, true), (102, false), (27, false), (108, true), (1772, false)]
theorem step2597 (p : Nat → Bool) (h : Constraints p) : clause p c2597 = true :=
  Snake9.LocalRup.prove_clause [c2596, c2240, c2233, c1598, c2582, c1584, c1537, c2340, c1539, c1531, c1567] c2597 (by decide) p (sat_cons (step2596 p h) (sat_cons (step2240 p h) (sat_cons (step2233 p h) (sat_cons (step1598 p h) (sat_cons (step2582 p h) (sat_cons (step1584 p h) (sat_cons (step1537 p h) (sat_cons (step2340 p h) (sat_cons (step1539 p h) (sat_cons (step1531 p h) (sat_cons (step1567 p h) (sat_nil p))))))))))))
def c2598 : List Lit := [(87, false), (1596, true), (103, false), (115, false)]
theorem step2598 (p : Nat → Bool) (h : Constraints p) : clause p c2598 = true :=
  Snake9.LocalRup.prove_clause [c2371, c1898, c1125, c1126, c463, c55, c2031] c2598 (by decide) p (sat_cons (step2371 p h) (sat_cons (step1898 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step463 p h) (sat_cons (step55 p h) (sat_cons (step2031 p h) (sat_nil p))))))))
def c2599 : List Lit := [(1731, true), (204, true), (72, true), (80, true), (1725, true)]
theorem step2599 (p : Nat → Bool) (h : Constraints p) : clause p c2599 = true :=
  Snake9.LocalRup.prove_clause [c1384, c1391, c1407, c1376, c2359, c1385, c1419, c1420, c1955, c353, c1373, c1374, c2108, c1375, c297, c1403, c1995, c1392, c1386] c2599 (by decide) p (sat_cons (step1384 p h) (sat_cons (step1391 p h) (sat_cons (step1407 p h) (sat_cons (step1376 p h) (sat_cons (step2359 p h) (sat_cons (step1385 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step1955 p h) (sat_cons (step353 p h) (sat_cons (step1373 p h) (sat_cons (step1374 p h) (sat_cons (step2108 p h) (sat_cons (step1375 p h) (sat_cons (step297 p h) (sat_cons (step1403 p h) (sat_cons (step1995 p h) (sat_cons (step1392 p h) (sat_cons (step1386 p h) (sat_nil p))))))))))))))))))))
def c2600 : List Lit := [(16, false), (25, false), (1637, true), (109, true), (30, true), (21, false), (108, true), (27, false), (44, true), (35, true)]
theorem step2600 (p : Nat → Bool) (h : Constraints p) : clause p c2600 = true :=
  Snake9.LocalRup.prove_clause [c1230, c1190, c2013, c70, c1188, c2040, c1198, c1199, c90, c1227, c1191, c2184, c1208, c93, c1201, c2048, c118] c2600 (by decide) p (sat_cons (step1230 p h) (sat_cons (step1190 p h) (sat_cons (step2013 p h) (sat_cons (step70 p h) (sat_cons (step1188 p h) (sat_cons (step2040 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step90 p h) (sat_cons (step1227 p h) (sat_cons (step1191 p h) (sat_cons (step2184 p h) (sat_cons (step1208 p h) (sat_cons (step93 p h) (sat_cons (step1201 p h) (sat_cons (step2048 p h) (sat_cons (step118 p h) (sat_nil p))))))))))))))))))
def c2601 : List Lit := [(1646, true), (1741, true), (65, false)]
theorem step2601 (p : Nat → Bool) (h : Constraints p) : clause p c2601 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1240, c1235, c1991, c1232, c1909] c2601 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1235 p h) (sat_cons (step1991 p h) (sat_cons (step1232 p h) (sat_cons (step1909 p h) (sat_nil p)))))))
def c2602 : List Lit := [(1636, true), (1623, false), (30, true)]
theorem step2602 (p : Nat → Bool) (h : Constraints p) : clause p c2602 = true :=
  Snake9.LocalRup.prove_clause [c1889, c1223, c1188, c1206, c1208, c1942, c1204, c1201, c101] c2602 (by decide) p (sat_cons (step1889 p h) (sat_cons (step1223 p h) (sat_cons (step1188 p h) (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step1942 p h) (sat_cons (step1204 p h) (sat_cons (step1201 p h) (sat_cons (step101 p h) (sat_nil p))))))))))
def c2603 : List Lit := [(1630, true), (39, false), (33, false)]
theorem step2603 (p : Nat → Bool) (h : Constraints p) : clause p c2603 = true :=
  Snake9.LocalRup.prove_clause [c1206, c1942, c1204, c101] c2603 (by decide) p (sat_cons (step1206 p h) (sat_cons (step1942 p h) (sat_cons (step1204 p h) (sat_cons (step101 p h) (sat_nil p)))))
def c2604 : List Lit := [(1744, true), (1791, true), (108, true), (1774, false), (91, true)]
theorem step2604 (p : Nat → Bool) (h : Constraints p) : clause p c2604 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1442, c2261, c2262, c1537, c1528, c1539, c1562] c2604 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1442 p h) (sat_cons (step2261 p h) (sat_cons (step2262 p h) (sat_cons (step1537 p h) (sat_cons (step1528 p h) (sat_cons (step1539 p h) (sat_cons (step1562 p h) (sat_nil p)))))))))
def c2605 : List Lit := [(1829, true), (1776, false), (108, true), (1800, false)]
theorem step2605 (p : Nat → Bool) (h : Constraints p) : clause p c2605 = true :=
  Snake9.LocalRup.prove_clause [c1536, c1538, c1556, c1611, c1647, c1641, c1557, c1612, c1539, c2582, c1537] c2605 (by decide) p (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1556 p h) (sat_cons (step1611 p h) (sat_cons (step1647 p h) (sat_cons (step1641 p h) (sat_cons (step1557 p h) (sat_cons (step1612 p h) (sat_cons (step1539 p h) (sat_cons (step2582 p h) (sat_cons (step1537 p h) (sat_nil p))))))))))))
def c2606 : List Lit := [(1810, true), (122, true)]
theorem step2606 (p : Nat → Bool) (h : Constraints p) : clause p c2606 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1598, c1590, c1592, c1585, c1587, c2166, c833] c2606 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1598 p h) (sat_cons (step1590 p h) (sat_cons (step1592 p h) (sat_cons (step1585 p h) (sat_cons (step1587 p h) (sat_cons (step2166 p h) (sat_cons (step833 p h) (sat_nil p)))))))))
def c2607 : List Lit := [(30, true), (1636, true), (1620, false)]
theorem step2607 (p : Nat → Bool) (h : Constraints p) : clause p c2607 = true :=
  Snake9.LocalRup.prove_clause [c1187, c2602, c1195] c2607 (by decide) p (sat_cons (step1187 p h) (sat_cons (step2602 p h) (sat_cons (step1195 p h) (sat_nil p))))
def c2608 : List Lit := [(32, true), (36, false), (39, false)]
theorem step2608 (p : Nat → Bool) (h : Constraints p) : clause p c2608 = true :=
  Snake9.LocalRup.prove_clause [c2048, c2049, c1760] c2608 (by decide) p (sat_cons (step2048 p h) (sat_cons (step2049 p h) (sat_cons (step1760 p h) (sat_nil p))))
def c2609 : List Lit := [(80, false), (73, false), (87, true), (7, false), (1744, false), (1762, true), (1715, false), (123, false)]
theorem step2609 (p : Nat → Bool) (h : Constraints p) : clause p c2609 = true :=
  Snake9.LocalRup.prove_clause [c319, c320, c317, c1424, c1388, c1426, c1393, c1458, c1399, c1501, c1495, c1404, c1463, c1375, c1429, c1373, c1955] c2609 (by decide) p (sat_cons (step319 p h) (sat_cons (step320 p h) (sat_cons (step317 p h) (sat_cons (step1424 p h) (sat_cons (step1388 p h) (sat_cons (step1426 p h) (sat_cons (step1393 p h) (sat_cons (step1458 p h) (sat_cons (step1399 p h) (sat_cons (step1501 p h) (sat_cons (step1495 p h) (sat_cons (step1404 p h) (sat_cons (step1463 p h) (sat_cons (step1375 p h) (sat_cons (step1429 p h) (sat_cons (step1373 p h) (sat_cons (step1955 p h) (sat_nil p))))))))))))))))))
def c2610 : List Lit := [(100, true), (62, true), (90, true), (123, true), (91, true), (102, false), (107, true), (108, true), (455, true), (88, true)]
theorem step2610 (p : Nat → Bool) (h : Constraints p) : clause p c2610 = true :=
  Snake9.LocalRup.prove_clause [c1057, c1051, c1050, c1056, c1055, c1054, c547, c598, c2135] c2610 (by decide) p (sat_cons (step1057 p h) (sat_cons (step1051 p h) (sat_cons (step1050 p h) (sat_cons (step1056 p h) (sat_cons (step1055 p h) (sat_cons (step1054 p h) (sat_cons (step547 p h) (sat_cons (step598 p h) (sat_cons (step2135 p h) (sat_nil p))))))))))
def c2611 : List Lit := [(61, false), (51, true), (102, false), (80, false), (189, true)]
theorem step2611 (p : Nat → Bool) (h : Constraints p) : clause p c2611 = true :=
  Snake9.LocalRup.prove_clause [c226, c224] c2611 (by decide) p (sat_cons (step226 p h) (sat_cons (step224 p h) (sat_nil p)))
def c2612 : List Lit := [(35, false), (34, true), (27, false), (7, false)]
theorem step2612 (p : Nat → Bool) (h : Constraints p) : clause p c2612 = true :=
  Snake9.LocalRup.prove_clause [c135, c2046] c2612 (by decide) p (sat_cons (step135 p h) (sat_cons (step2046 p h) (sat_nil p)))
def c2613 : List Lit := [(1790, true), (1773, false), (1781, false), (97, true), (93, false), (19, false)]
theorem step2613 (p : Nat → Bool) (h : Constraints p) : clause p c2613 = true :=
  Snake9.LocalRup.prove_clause [c1518, c1527, c1538, c1557, c1561, c1541, c1530, c1533, c1520, c461] c2613 (by decide) p (sat_cons (step1518 p h) (sat_cons (step1527 p h) (sat_cons (step1538 p h) (sat_cons (step1557 p h) (sat_cons (step1561 p h) (sat_cons (step1541 p h) (sat_cons (step1530 p h) (sat_cons (step1533 p h) (sat_cons (step1520 p h) (sat_cons (step461 p h) (sat_nil p)))))))))))
def c2614 : List Lit := [(1725, true), (73, true), (80, false), (7, false)]
theorem step2614 (p : Nat → Bool) (h : Constraints p) : clause p c2614 = true :=
  Snake9.LocalRup.prove_clause [c1383, c1399, c2359, c1393, c1385, c2357] c2614 (by decide) p (sat_cons (step1383 p h) (sat_cons (step1399 p h) (sat_cons (step2359 p h) (sat_cons (step1393 p h) (sat_cons (step1385 p h) (sat_cons (step2357 p h) (sat_nil p)))))))
def c2615 : List Lit := [(1761, true), (1725, false), (87, true), (1744, false), (7, false)]
theorem step2615 (p : Nat → Bool) (h : Constraints p) : clause p c2615 = true :=
  Snake9.LocalRup.prove_clause [c1494, c2363, c1458] c2615 (by decide) p (sat_cons (step1494 p h) (sat_cons (step2363 p h) (sat_cons (step1458 p h) (sat_nil p))))
def c2616 : List Lit := [(44, true), (30, true), (27, false), (159, true), (26, true)]
theorem step2616 (p : Nat → Bool) (h : Constraints p) : clause p c2616 = true :=
  Snake9.LocalRup.prove_clause [c2038, c2040, c90, c1755] c2616 (by decide) p (sat_cons (step2038 p h) (sat_cons (step2040 p h) (sat_cons (step90 p h) (sat_cons (step1755 p h) (sat_nil p)))))
def c2617 : List Lit := [(1777, false), (107, true), (1830, true), (108, false), (123, true)]
theorem step2617 (p : Nat → Bool) (h : Constraints p) : clause p c2617 = true :=
  Snake9.LocalRup.prove_clause [c1560, c2531, c1642, c1532, c1533, c2235, c2278, c618, c2141] c2617 (by decide) p (sat_cons (step1560 p h) (sat_cons (step2531 p h) (sat_cons (step1642 p h) (sat_cons (step1532 p h) (sat_cons (step1533 p h) (sat_cons (step2235 p h) (sat_cons (step2278 p h) (sat_cons (step618 p h) (sat_cons (step2141 p h) (sat_nil p))))))))))
def c2618 : List Lit := [(1725, true), (1655, true), (80, false), (75, false), (7, false), (3, false)]
theorem step2618 (p : Nat → Bool) (h : Constraints p) : clause p c2618 = true :=
  Snake9.LocalRup.prove_clause [c1399, c2386, c2552, c1247, c1250, c1255] c2618 (by decide) p (sat_cons (step1399 p h) (sat_cons (step2386 p h) (sat_cons (step2552 p h) (sat_cons (step1247 p h) (sat_cons (step1250 p h) (sat_cons (step1255 p h) (sat_nil p)))))))
def c2619 : List Lit := [(1788, true), (1781, false), (93, false), (19, false)]
theorem step2619 (p : Nat → Bool) (h : Constraints p) : clause p c2619 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1547, c1551, c1541, c1526, c1533, c1519, c461] c2619 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1547 p h) (sat_cons (step1551 p h) (sat_cons (step1541 p h) (sat_cons (step1526 p h) (sat_cons (step1533 p h) (sat_cons (step1519 p h) (sat_cons (step461 p h) (sat_nil p)))))))))
def c2620 : List Lit := [(1789, true), (1645, true), (1781, false), (22, true), (19, false), (18, false)]
theorem step2620 (p : Nat → Bool) (h : Constraints p) : clause p c2620 = true :=
  Snake9.LocalRup.prove_clause [c2031, c2028, c2383, c1519, c1526, c1538, c1556, c1552, c1527, c1541, c1522, c1533, c394, c452, c1237] c2620 (by decide) p (sat_cons (step2031 p h) (sat_cons (step2028 p h) (sat_cons (step2383 p h) (sat_cons (step1519 p h) (sat_cons (step1526 p h) (sat_cons (step1538 p h) (sat_cons (step1556 p h) (sat_cons (step1552 p h) (sat_cons (step1527 p h) (sat_cons (step1541 p h) (sat_cons (step1522 p h) (sat_cons (step1533 p h) (sat_cons (step394 p h) (sat_cons (step452 p h) (sat_cons (step1237 p h) (sat_nil p))))))))))))))))
def c2621 : List Lit := [(35, false), (1801, true), (123, false), (44, true), (7, false)]
theorem step2621 (p : Nat → Bool) (h : Constraints p) : clause p c2621 = true :=
  Snake9.LocalRup.prove_clause [c2044, c2294, c736, c1582, c1573] c2621 (by decide) p (sat_cons (step2044 p h) (sat_cons (step2294 p h) (sat_cons (step736 p h) (sat_cons (step1582 p h) (sat_cons (step1573 p h) (sat_nil p))))))
def c2622 : List Lit := [(1789, true), (1773, false), (97, true), (93, false), (19, false)]
theorem step2622 (p : Nat → Bool) (h : Constraints p) : clause p c2622 = true :=
  Snake9.LocalRup.prove_clause [c1518, c1527, c1560, c1556, c1530, c1540, c1520, c1533, c461] c2622 (by decide) p (sat_cons (step1518 p h) (sat_cons (step1527 p h) (sat_cons (step1560 p h) (sat_cons (step1556 p h) (sat_cons (step1530 p h) (sat_cons (step1540 p h) (sat_cons (step1520 p h) (sat_cons (step1533 p h) (sat_cons (step461 p h) (sat_nil p))))))))))
def c2623 : List Lit := [(1779, true), (105, false), (108, false)]
theorem step2623 (p : Nat → Bool) (h : Constraints p) : clause p c2623 = true :=
  Snake9.LocalRup.prove_clause [c1532, c1533, c618] c2623 (by decide) p (sat_cons (step1532 p h) (sat_cons (step1533 p h) (sat_cons (step618 p h) (sat_nil p))))
def c2624 : List Lit := [(1775, true), (89, false), (18, false)]
theorem step2624 (p : Nat → Bool) (h : Constraints p) : clause p c2624 = true :=
  Snake9.LocalRup.prove_clause [c1524, c1526, c1522, c1519, c403] c2624 (by decide) p (sat_cons (step1524 p h) (sat_cons (step1526 p h) (sat_cons (step1522 p h) (sat_cons (step1519 p h) (sat_cons (step403 p h) (sat_nil p))))))
def c2625 : List Lit := [(35, false), (1632, true), (39, true), (44, false), (7, false)]
theorem step2625 (p : Nat → Bool) (h : Constraints p) : clause p c2625 = true :=
  Snake9.LocalRup.prove_clause [c139, c140, c1202, c1204, c1212] c2625 (by decide) p (sat_cons (step139 p h) (sat_cons (step140 p h) (sat_cons (step1202 p h) (sat_cons (step1204 p h) (sat_cons (step1212 p h) (sat_nil p))))))
def c2626 : List Lit := [(1631, true), (39, true), (44, false), (7, false)]
theorem step2626 (p : Nat → Bool) (h : Constraints p) : clause p c2626 = true :=
  Snake9.LocalRup.prove_clause [c1201, c1211, c1209, c1202, c1204, c142] c2626 (by decide) p (sat_cons (step1201 p h) (sat_cons (step1211 p h) (sat_cons (step1209 p h) (sat_cons (step1202 p h) (sat_cons (step1204 p h) (sat_cons (step142 p h) (sat_nil p)))))))
def c2627 : List Lit := [(1619, false), (1638, true), (39, true), (44, false), (7, false)]
theorem step2627 (p : Nat → Bool) (h : Constraints p) : clause p c2627 = true :=
  Snake9.LocalRup.prove_clause [c2626, c1228, c1197, c1198, c1225, c1190, c2625] c2627 (by decide) p (sat_cons (step2626 p h) (sat_cons (step1228 p h) (sat_cons (step1197 p h) (sat_cons (step1198 p h) (sat_cons (step1225 p h) (sat_cons (step1190 p h) (sat_cons (step2625 p h) (sat_nil p))))))))
def c2628 : List Lit := [(1637, true), (39, true), (44, false), (1618, false), (7, false)]
theorem step2628 (p : Nat → Bool) (h : Constraints p) : clause p c2628 = true :=
  Snake9.LocalRup.prove_clause [c2626, c1194, c1221, c1224, c2625, c1195, c1190] c2628 (by decide) p (sat_cons (step2626 p h) (sat_cons (step1194 p h) (sat_cons (step1221 p h) (sat_cons (step1224 p h) (sat_cons (step2625 p h) (sat_cons (step1195 p h) (sat_cons (step1190 p h) (sat_nil p))))))))
def c2629 : List Lit := [(1779, false), (108, true), (1828, true), (1785, true), (1775, false)]
theorem step2629 (p : Nat → Bool) (h : Constraints p) : clause p c2629 = true :=
  Snake9.LocalRup.prove_clause [c1536, c1542, c1541, c1537, c1552, c2582, c1640, c2233] c2629 (by decide) p (sat_cons (step1536 p h) (sat_cons (step1542 p h) (sat_cons (step1541 p h) (sat_cons (step1537 p h) (sat_cons (step1552 p h) (sat_cons (step2582 p h) (sat_cons (step1640 p h) (sat_cons (step2233 p h) (sat_nil p)))))))))
def c2630 : List Lit := [(1810, true), (81, true)]
theorem step2630 (p : Nat → Bool) (h : Constraints p) : clause p c2630 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1598, c2606, c1592, c2373, c1938, c1585, c792, c2172] c2630 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1598 p h) (sat_cons (step2606 p h) (sat_cons (step1592 p h) (sat_cons (step2373 p h) (sat_cons (step1938 p h) (sat_cons (step1585 p h) (sat_cons (step792 p h) (sat_cons (step2172 p h) (sat_nil p))))))))))
def c2631 : List Lit := [(315, true), (87, true), (28, true), (33, true), (26, true), (15, false)]
theorem step2631 (p : Nat → Bool) (h : Constraints p) : clause p c2631 = true :=
  Snake9.LocalRup.prove_clause [c954, c956, c951, c919, c933, c917, c931, c915, c929, c914, c64, c31, c2034] c2631 (by decide) p (sat_cons (step954 p h) (sat_cons (step956 p h) (sat_cons (step951 p h) (sat_cons (step919 p h) (sat_cons (step933 p h) (sat_cons (step917 p h) (sat_cons (step931 p h) (sat_cons (step915 p h) (sat_cons (step929 p h) (sat_cons (step914 p h) (sat_cons (step64 p h) (sat_cons (step31 p h) (sat_cons (step2034 p h) (sat_nil p))))))))))))))
def c2632 : List Lit := [(1725, true), (1736, true), (68, false), (80, false), (7, false)]
theorem step2632 (p : Nat → Bool) (h : Constraints p) : clause p c2632 = true :=
  Snake9.LocalRup.prove_clause [c1399, c2614, c1895, c1955, c1423, c1428] c2632 (by decide) p (sat_cons (step1399 p h) (sat_cons (step2614 p h) (sat_cons (step1895 p h) (sat_cons (step1955 p h) (sat_cons (step1423 p h) (sat_cons (step1428 p h) (sat_nil p)))))))
def c2633 : List Lit := [(103, false), (1660, true), (1740, false), (1751, true), (93, false), (95, true), (19, false)]
theorem step2633 (p : Nat → Bool) (h : Constraints p) : clause p c2633 = true :=
  Snake9.LocalRup.prove_clause [c452, c456, c1235, c1438, c1238, c1446, c1266, c1455, c1253, c1879] c2633 (by decide) p (sat_cons (step452 p h) (sat_cons (step456 p h) (sat_cons (step1235 p h) (sat_cons (step1438 p h) (sat_cons (step1238 p h) (sat_cons (step1446 p h) (sat_cons (step1266 p h) (sat_cons (step1455 p h) (sat_cons (step1253 p h) (sat_cons (step1879 p h) (sat_nil p)))))))))))
def c2634 : List Lit := [(1637, false), (1725, false), (1830, false), (1745, false), (1607, false), (1658, false)]
theorem step2634 (p : Nat → Bool) (h : Constraints p) : clause p c2634 = true :=
  Snake9.LocalRup.prove_clause [c1449, c1493, c1697, c2250, c1342, c1304, c1305, c1341, c1261, c2249, c1253, c1705, c1879, c1494, c1454] c2634 (by decide) p (sat_cons (step1449 p h) (sat_cons (step1493 p h) (sat_cons (step1697 p h) (sat_cons (step2250 p h) (sat_cons (step1342 p h) (sat_cons (step1304 p h) (sat_cons (step1305 p h) (sat_cons (step1341 p h) (sat_cons (step1261 p h) (sat_cons (step2249 p h) (sat_cons (step1253 p h) (sat_cons (step1705 p h) (sat_cons (step1879 p h) (sat_cons (step1494 p h) (sat_cons (step1454 p h) (sat_nil p))))))))))))))))
def c2635 : List Lit := [(1717, true), (80, false), (7, false)]
theorem step2635 (p : Nat → Bool) (h : Constraints p) : clause p c2635 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1387, c315] c2635 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step315 p h) (sat_nil p))))
def c2636 : List Lit := [(1720, true), (80, false), (7, false)]
theorem step2636 (p : Nat → Bool) (h : Constraints p) : clause p c2636 = true :=
  Snake9.LocalRup.prove_clause [c2635, c1390, c1392, c2357, c1384] c2636 (by decide) p (sat_cons (step2635 p h) (sat_cons (step1390 p h) (sat_cons (step1392 p h) (sat_cons (step2357 p h) (sat_cons (step1384 p h) (sat_nil p))))))
def c2637 : List Lit := [(35, true), (162, true), (169, true), (1637, true), (39, true), (44, true), (33, true)]
theorem step2637 (p : Nat → Bool) (h : Constraints p) : clause p c2637 = true :=
  Snake9.LocalRup.prove_clause [c1186, c1190, c105, c1195, c2054, c1224, c1933] c2637 (by decide) p (sat_cons (step1186 p h) (sat_cons (step1190 p h) (sat_cons (step105 p h) (sat_cons (step1195 p h) (sat_cons (step2054 p h) (sat_cons (step1224 p h) (sat_cons (step1933 p h) (sat_nil p))))))))
def c2638 : List Lit := [(1636, false), (1830, false), (1745, false), (1608, false), (1725, false), (1658, false)]
theorem step2638 (p : Nat → Bool) (h : Constraints p) : clause p c2638 = true :=
  Snake9.LocalRup.prove_clause [c1449, c1493, c1697, c2250, c1350, c1297, c1298, c1349, c1261, c2249, c1253, c1705, c1879, c1494, c1454] c2638 (by decide) p (sat_cons (step1449 p h) (sat_cons (step1493 p h) (sat_cons (step1697 p h) (sat_cons (step2250 p h) (sat_cons (step1350 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step1349 p h) (sat_cons (step1261 p h) (sat_cons (step2249 p h) (sat_cons (step1253 p h) (sat_cons (step1705 p h) (sat_cons (step1879 p h) (sat_cons (step1494 p h) (sat_cons (step1454 p h) (sat_nil p))))))))))))))))
def c2639 : List Lit := [(1818, true), (35, false), (44, true), (81, true), (7, false)]
theorem step2639 (p : Nat → Bool) (h : Constraints p) : clause p c2639 = true :=
  Snake9.LocalRup.prove_clause [c2561, c2630, c1617, c2621, c1613, c1956] c2639 (by decide) p (sat_cons (step2561 p h) (sat_cons (step2630 p h) (sat_cons (step1617 p h) (sat_cons (step2621 p h) (sat_cons (step1613 p h) (sat_cons (step1956 p h) (sat_nil p)))))))
def c2640 : List Lit := [(1779, true), (94, true), (107, true), (108, false)]
theorem step2640 (p : Nat → Bool) (h : Constraints p) : clause p c2640 = true :=
  Snake9.LocalRup.prove_clause [c1532, c2623, c2144] c2640 (by decide) p (sat_cons (step1532 p h) (sat_cons (step2623 p h) (sat_cons (step2144 p h) (sat_nil p))))
def c2641 : List Lit := [(1817, true), (113, true), (100, false), (108, false), (1810, false)]
theorem step2641 (p : Nat → Bool) (h : Constraints p) : clause p c2641 = true :=
  Snake9.LocalRup.prove_clause [c1612, c2010, c2443] c2641 (by decide) p (sat_cons (step1612 p h) (sat_cons (step2010 p h) (sat_cons (step2443 p h) (sat_nil p))))
def c2642 : List Lit := [(1789, true), (1781, false), (1773, false), (1775, false), (93, false), (19, false)]
theorem step2642 (p : Nat → Bool) (h : Constraints p) : clause p c2642 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1552, c1556, c1541, c1527, c1533, c1519, c461] c2642 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1552 p h) (sat_cons (step1556 p h) (sat_cons (step1541 p h) (sat_cons (step1527 p h) (sat_cons (step1533 p h) (sat_cons (step1519 p h) (sat_cons (step461 p h) (sat_nil p)))))))))
def c2643 : List Lit := [(1779, true), (108, false), (97, false), (87, false)]
theorem step2643 (p : Nat → Bool) (h : Constraints p) : clause p c2643 = true :=
  Snake9.LocalRup.prove_clause [c1532, c2623, c669, c490, c2144] c2643 (by decide) p (sat_cons (step1532 p h) (sat_cons (step2623 p h) (sat_cons (step669 p h) (sat_cons (step490 p h) (sat_cons (step2144 p h) (sat_nil p))))))
def c2644 : List Lit := [(104, false), (1812, true), (1773, true), (97, false), (87, false)]
theorem step2644 (p : Nat → Bool) (h : Constraints p) : clause p c2644 = true :=
  Snake9.LocalRup.prove_clause [c1521, c431, c490, c666, c2142, c2134, c2278, c2263] c2644 (by decide) p (sat_cons (step1521 p h) (sat_cons (step431 p h) (sat_cons (step490 p h) (sat_cons (step666 p h) (sat_cons (step2142 p h) (sat_cons (step2134 p h) (sat_cons (step2278 p h) (sat_cons (step2263 p h) (sat_nil p)))))))))
def c2645 : List Lit := [(108, false), (1773, true), (97, false), (87, false)]
theorem step2645 (p : Nat → Bool) (h : Constraints p) : clause p c2645 = true :=
  Snake9.LocalRup.prove_clause [c1522, c1521, c2407, c594] c2645 (by decide) p (sat_cons (step1522 p h) (sat_cons (step1521 p h) (sat_cons (step2407 p h) (sat_cons (step594 p h) (sat_nil p)))))
def c2646 : List Lit := [(1637, true), (42, false), (1619, false), (35, true), (39, false), (175, true), (21, false)]
theorem step2646 (p : Nat → Bool) (h : Constraints p) : clause p c2646 = true :=
  Snake9.LocalRup.prove_clause [c1190, c1198, c1230, c1227, c1199, c1206, c1191, c1203, c1891, c2257, c163] c2646 (by decide) p (sat_cons (step1190 p h) (sat_cons (step1198 p h) (sat_cons (step1230 p h) (sat_cons (step1227 p h) (sat_cons (step1199 p h) (sat_cons (step1206 p h) (sat_cons (step1191 p h) (sat_cons (step1203 p h) (sat_cons (step1891 p h) (sat_cons (step2257 p h) (sat_cons (step163 p h) (sat_nil p))))))))))))
def c2647 : List Lit := [(1637, false), (1658, false), (1671, true), (1606, false), (1745, false), (1725, false), (87, true), (1830, false)]
theorem step2647 (p : Nat → Bool) (h : Constraints p) : clause p c2647 = true :=
  Snake9.LocalRup.prove_clause [c1304, c1305, c1331, c1261, c2248, c1253, c1712, c2387, c1495, c1459] c2647 (by decide) p (sat_cons (step1304 p h) (sat_cons (step1305 p h) (sat_cons (step1331 p h) (sat_cons (step1261 p h) (sat_cons (step2248 p h) (sat_cons (step1253 p h) (sat_cons (step1712 p h) (sat_cons (step2387 p h) (sat_cons (step1495 p h) (sat_cons (step1459 p h) (sat_nil p)))))))))))
end B112E050
