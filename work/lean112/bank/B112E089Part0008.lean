import B112E089Part0007
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2524 : List Lit := [(1733, true), (107, false), (90, false), (469, true), (115, true)]
theorem step2524 (p : Nat → Bool) (h : Constraints p) : clause p c2524 = true :=
  Snake9.LocalRup.prove_clause [c1264, c1256, c1255, c1262, c1260, c1257, c1797, c1798, c2402, c2523, c874, c872, c904] c2524 (by decide) p (sat_cons (step1264 p h) (sat_cons (step1256 p h) (sat_cons (step1255 p h) (sat_cons (step1262 p h) (sat_cons (step1260 p h) (sat_cons (step1257 p h) (sat_cons (step1797 p h) (sat_cons (step1798 p h) (sat_cons (step2402 p h) (sat_cons (step2523 p h) (sat_cons (step874 p h) (sat_cons (step872 p h) (sat_cons (step904 p h) (sat_nil p))))))))))))))
def c2525 : List Lit := [(1697, true), (73, true), (1680, false), (193, true)]
theorem step2525 (p : Nat → Bool) (h : Constraints p) : clause p c2525 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1620, c1628, c2408, c1702, c1708, c2511, c1629, c1633, c1647, c1623, c2486, c1611, c707, c1614] c2525 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1620 p h) (sat_cons (step1628 p h) (sat_cons (step2408 p h) (sat_cons (step1702 p h) (sat_cons (step1708 p h) (sat_cons (step2511 p h) (sat_cons (step1629 p h) (sat_cons (step1633 p h) (sat_cons (step1647 p h) (sat_cons (step1623 p h) (sat_cons (step2486 p h) (sat_cons (step1611 p h) (sat_cons (step707 p h) (sat_cons (step1614 p h) (sat_nil p))))))))))))))))
def c2526 : List Lit := [(1617, true), (1599, false), (1569, false), (1592, false), (103, false)]
theorem step2526 (p : Nat → Bool) (h : Constraints p) : clause p c2526 = true :=
  Snake9.LocalRup.prove_clause [c1482, c1495, c1450, c1528, c1535, c1500, c1496, c1451, c2505, c1485, c2157, c1476] c2526 (by decide) p (sat_cons (step1482 p h) (sat_cons (step1495 p h) (sat_cons (step1450 p h) (sat_cons (step1528 p h) (sat_cons (step1535 p h) (sat_cons (step1500 p h) (sat_cons (step1496 p h) (sat_cons (step1451 p h) (sat_cons (step2505 p h) (sat_cons (step1485 p h) (sat_cons (step2157 p h) (sat_cons (step1476 p h) (sat_nil p)))))))))))))
def c2527 : List Lit := [(1657, true), (60, true), (67, false), (75, false), (197, true)]
theorem step2527 (p : Nat → Bool) (h : Constraints p) : clause p c2527 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1618, c754, c657, c677] c2527 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1618 p h) (sat_cons (step754 p h) (sat_cons (step657 p h) (sat_cons (step677 p h) (sat_nil p))))))
def c2528 : List Lit := [(74, true), (1660, true), (69, false), (75, false), (193, true)]
theorem step2528 (p : Nat → Bool) (h : Constraints p) : clause p c2528 = true :=
  Snake9.LocalRup.prove_clause [c2486, c640, c656] c2528 (by decide) p (sat_cons (step2486 p h) (sat_cons (step640 p h) (sat_cons (step656 p h) (sat_nil p))))
def c2529 : List Lit := [(25, false), (1527, true), (60, true), (67, false), (146, true)]
theorem step2529 (p : Nat → Bool) (h : Constraints p) : clause p c2529 = true :=
  Snake9.LocalRup.prove_clause [c1343, c1342, c103, c152, c114] c2529 (by decide) p (sat_cons (step1343 p h) (sat_cons (step1342 p h) (sat_cons (step103 p h) (sat_cons (step152 p h) (sat_cons (step114 p h) (sat_nil p))))))
def c2530 : List Lit := [(1615, true), (1569, false), (1592, false), (103, false)]
theorem step2530 (p : Nat → Bool) (h : Constraints p) : clause p c2530 = true :=
  Snake9.LocalRup.prove_clause [c1450, c1493, c1526, c1533, c1498, c1494, c1451, c2505, c1483, c2157, c1476] c2530 (by decide) p (sat_cons (step1450 p h) (sat_cons (step1493 p h) (sat_cons (step1526 p h) (sat_cons (step1533 p h) (sat_cons (step1498 p h) (sat_cons (step1494 p h) (sat_cons (step1451 p h) (sat_cons (step2505 p h) (sat_cons (step1483 p h) (sat_cons (step2157 p h) (sat_cons (step1476 p h) (sat_nil p))))))))))))
def c2531 : List Lit := [(54, true), (1651, true), (1601, true), (67, false), (111, false), (185, true)]
theorem step2531 (p : Nat → Bool) (h : Constraints p) : clause p c2531 = true :=
  Snake9.LocalRup.prove_clause [c1476, c2503, c2492, c1484, c1608, c1478, c619] c2531 (by decide) p (sat_cons (step1476 p h) (sat_cons (step2503 p h) (sat_cons (step2492 p h) (sat_cons (step1484 p h) (sat_cons (step1608 p h) (sat_cons (step1478 p h) (sat_cons (step619 p h) (sat_nil p))))))))
def c2532 : List Lit := [(1600, true), (1651, true), (60, true), (67, false), (185, true)]
theorem step2532 (p : Nat → Bool) (h : Constraints p) : clause p c2532 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1483, c1478, c1479, c1475, c416, c474, c472, c428, c619, c1608] c2532 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1483 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step1475 p h) (sat_cons (step416 p h) (sat_cons (step474 p h) (sat_cons (step472 p h) (sat_cons (step428 p h) (sat_cons (step619 p h) (sat_cons (step1608 p h) (sat_nil p))))))))))))
def c2533 : List Lit := [(1593, true), (46, true), (49, false), (103, false)]
theorem step2533 (p : Nat → Bool) (h : Constraints p) : clause p c2533 = true :=
  Snake9.LocalRup.prove_clause [c1462, c1472, c1470, c1463, c1465, c339] c2533 (by decide) p (sat_cons (step1462 p h) (sat_cons (step1472 p h) (sat_cons (step1470 p h) (sat_cons (step1463 p h) (sat_cons (step1465 p h) (sat_cons (step339 p h) (sat_nil p)))))))
def c2534 : List Lit := [(1660, true), (73, true), (1569, true), (1657, false), (75, false), (158, true), (193, true), (121, false)]
theorem step2534 (p : Nat → Bool) (h : Constraints p) : clause p c2534 = true :=
  Snake9.LocalRup.prove_clause [c1621, c1623, c2486, c1619, c1614, c690, c732, c1413, c2073, c1422, c201, c1417] c2534 (by decide) p (sat_cons (step1621 p h) (sat_cons (step1623 p h) (sat_cons (step2486 p h) (sat_cons (step1619 p h) (sat_cons (step1614 p h) (sat_cons (step690 p h) (sat_cons (step732 p h) (sat_cons (step1413 p h) (sat_cons (step2073 p h) (sat_cons (step1422 p h) (sat_cons (step201 p h) (sat_cons (step1417 p h) (sat_nil p)))))))))))))
def c2535 : List Lit := [(1598, false), (1589, false), (50, true), (1617, true), (1568, false)]
theorem step2535 (p : Nat → Bool) (h : Constraints p) : clause p c2535 = true :=
  Snake9.LocalRup.prove_clause [c1445, c1521, c1465, c1473, c1505, c1481, c1484, c1509, c1504, c1476, c1474, c1528, c1466, c1446, c2157] c2535 (by decide) p (sat_cons (step1445 p h) (sat_cons (step1521 p h) (sat_cons (step1465 p h) (sat_cons (step1473 p h) (sat_cons (step1505 p h) (sat_cons (step1481 p h) (sat_cons (step1484 p h) (sat_cons (step1509 p h) (sat_cons (step1504 p h) (sat_cons (step1476 p h) (sat_cons (step1474 p h) (sat_cons (step1528 p h) (sat_cons (step1466 p h) (sat_cons (step1446 p h) (sat_cons (step2157 p h) (sat_nil p))))))))))))))))
def c2536 : List Lit := [(1600, false), (1589, false), (50, true), (1617, true), (1568, false), (169, true)]
theorem step2536 (p : Nat → Bool) (h : Constraints p) : clause p c2536 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1473, c1445, c1521, c1509, c1504, c1474, c1528, c1466, c1446, c1433, c1435, c2157, c1430, c2494, c2229, c302] c2536 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1473 p h) (sat_cons (step1445 p h) (sat_cons (step1521 p h) (sat_cons (step1509 p h) (sat_cons (step1504 p h) (sat_cons (step1474 p h) (sat_cons (step1528 p h) (sat_cons (step1466 p h) (sat_cons (step1446 p h) (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step2157 p h) (sat_cons (step1430 p h) (sat_cons (step2494 p h) (sat_cons (step2229 p h) (sat_cons (step302 p h) (sat_nil p))))))))))))))))))
def c2537 : List Lit := [(1576, true), (51, false), (50, true), (169, true)]
theorem step2537 (p : Nat → Bool) (h : Constraints p) : clause p c2537 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1435, c2157, c1430, c2494, c2229, c302] c2537 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step2157 p h) (sat_cons (step1430 p h) (sat_cons (step2494 p h) (sat_cons (step2229 p h) (sat_cons (step302 p h) (sat_nil p))))))))
def c2538 : List Lit := [(1598, true), (60, false), (111, false)]
theorem step2538 (p : Nat → Bool) (h : Constraints p) : clause p c2538 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1479, c459] c2538 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step459 p h) (sat_nil p))))
def c2539 : List Lit := [(1618, true), (1589, false), (50, true), (1598, false), (1569, false)]
theorem step2539 (p : Nat → Bool) (h : Constraints p) : clause p c2539 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1473, c1481, c1504, c1450, c1529, c1505, c1484, c1509, c1476, c1536, c1474, c1451, c1466, c2157] c2539 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1473 p h) (sat_cons (step1481 p h) (sat_cons (step1504 p h) (sat_cons (step1450 p h) (sat_cons (step1529 p h) (sat_cons (step1505 p h) (sat_cons (step1484 p h) (sat_cons (step1509 p h) (sat_cons (step1476 p h) (sat_cons (step1536 p h) (sat_cons (step1474 p h) (sat_cons (step1451 p h) (sat_cons (step1466 p h) (sat_cons (step2157 p h) (sat_nil p))))))))))))))))
def c2540 : List Lit := [(1617, true), (50, true), (1606, false), (1600, false), (1569, false), (1588, false), (169, true)]
theorem step2540 (p : Nat → Bool) (h : Constraints p) : clause p c2540 = true :=
  Snake9.LocalRup.prove_clause [c1450, c1528, c1535, c1504, c1451, c1471, c2537, c1466] c2540 (by decide) p (sat_cons (step1450 p h) (sat_cons (step1528 p h) (sat_cons (step1535 p h) (sat_cons (step1504 p h) (sat_cons (step1451 p h) (sat_cons (step1471 p h) (sat_cons (step2537 p h) (sat_cons (step1466 p h) (sat_nil p)))))))))
def c2541 : List Lit := [(1665, true), (73, true), (67, true), (75, false), (193, true)]
theorem step2541 (p : Nat → Bool) (h : Constraints p) : clause p c2541 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1617, c1623, c1630, c1634, c1624, c1626, c1611, c1619, c1616, c706, c655, c640] c2541 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1617 p h) (sat_cons (step1623 p h) (sat_cons (step1630 p h) (sat_cons (step1634 p h) (sat_cons (step1624 p h) (sat_cons (step1626 p h) (sat_cons (step1611 p h) (sat_cons (step1619 p h) (sat_cons (step1616 p h) (sat_cons (step706 p h) (sat_cons (step655 p h) (sat_cons (step640 p h) (sat_nil p))))))))))))))
def c2542 : List Lit := [(39, false), (1598, false), (1617, true), (1568, false), (46, true), (49, false), (103, false)]
theorem step2542 (p : Nat → Bool) (h : Constraints p) : clause p c2542 = true :=
  Snake9.LocalRup.prove_clause [c336, c334, c2535, c1463] c2542 (by decide) p (sat_cons (step336 p h) (sat_cons (step334 p h) (sat_cons (step2535 p h) (sat_cons (step1463 p h) (sat_nil p)))))
def c2543 : List Lit := [(1576, true), (61, false), (67, false), (169, true)]
theorem step2543 (p : Nat → Bool) (h : Constraints p) : clause p c2543 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1435, c1430, c2494, c610, c301] c2543 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1430 p h) (sat_cons (step2494 p h) (sat_cons (step610 p h) (sat_cons (step301 p h) (sat_nil p)))))))
def c2544 : List Lit := [(89, true), (1685, true), (79, true), (91, true), (415, true)]
theorem step2544 (p : Nat → Bool) (h : Constraints p) : clause p c2544 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1206, c1209, c1208, c2273, c1666, c778, c1674, c2272, c1663, c783] c2544 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1206 p h) (sat_cons (step1209 p h) (sat_cons (step1208 p h) (sat_cons (step2273 p h) (sat_cons (step1666 p h) (sat_cons (step778 p h) (sat_cons (step1674 p h) (sat_cons (step2272 p h) (sat_cons (step1663 p h) (sat_cons (step783 p h) (sat_nil p))))))))))))
def c2545 : List Lit := [(1576, true), (81, false), (96, false), (220, true)]
theorem step2545 (p : Nat → Bool) (h : Constraints p) : clause p c2545 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1435, c1430, c1427, c2494, c819, c829] c2545 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1430 p h) (sat_cons (step1427 p h) (sat_cons (step2494 p h) (sat_cons (step819 p h) (sat_cons (step829 p h) (sat_nil p))))))))
def c2546 : List Lit := [(1538, true), (25, true), (34, false), (23, false), (32, false), (60, false), (299, true)]
theorem step2546 (p : Nat → Bool) (h : Constraints p) : clause p c2546 = true :=
  Snake9.LocalRup.prove_clause [c1353, c1078, c1075, c1077, c1076, c1364, c1362, c1355, c1356, c1357, c119, c173, c174, c2206, c2190, c2460, c113] c2546 (by decide) p (sat_cons (step1353 p h) (sat_cons (step1078 p h) (sat_cons (step1075 p h) (sat_cons (step1077 p h) (sat_cons (step1076 p h) (sat_cons (step1364 p h) (sat_cons (step1362 p h) (sat_cons (step1355 p h) (sat_cons (step1356 p h) (sat_cons (step1357 p h) (sat_cons (step119 p h) (sat_cons (step173 p h) (sat_cons (step174 p h) (sat_cons (step2206 p h) (sat_cons (step2190 p h) (sat_cons (step2460 p h) (sat_cons (step113 p h) (sat_nil p))))))))))))))))))
def c2547 : List Lit := [(78, false), (67, true), (60, false), (75, true), (49, false)]
theorem step2547 (p : Nat → Bool) (h : Constraints p) : clause p c2547 = true :=
  Snake9.LocalRup.prove_clause [c671, c2266] c2547 (by decide) p (sat_cons (step671 p h) (sat_cons (step2266 p h) (sat_nil p)))
def c2548 : List Lit := [(74, true), (76, false), (78, true), (44, false), (200, true), (123, true)]
theorem step2548 (p : Nat → Bool) (h : Constraints p) : clause p c2548 = true :=
  Snake9.LocalRup.prove_clause [c746, c748, c2261, c557] c2548 (by decide) p (sat_cons (step746 p h) (sat_cons (step748 p h) (sat_cons (step2261 p h) (sat_cons (step557 p h) (sat_nil p)))))
def c2549 : List Lit := [(1570, false), (1617, true), (67, false), (1593, false), (169, true)]
theorem step2549 (p : Nat → Bool) (h : Constraints p) : clause p c2549 = true :=
  Snake9.LocalRup.prove_clause [c1498, c1542, c1455, c1456, c1535, c2543, c1499, c1478, c1481] c2549 (by decide) p (sat_cons (step1498 p h) (sat_cons (step1542 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step1535 p h) (sat_cons (step2543 p h) (sat_cons (step1499 p h) (sat_cons (step1478 p h) (sat_cons (step1481 p h) (sat_nil p))))))))))
def c2550 : List Lit := [(73, false), (1599, true), (67, false), (60, false)]
theorem step2550 (p : Nat → Bool) (h : Constraints p) : clause p c2550 = true :=
  Snake9.LocalRup.prove_clause [c463, c460, c1480] c2550 (by decide) p (sat_cons (step463 p h) (sat_cons (step460 p h) (sat_cons (step1480 p h) (sat_nil p))))
def c2551 : List Lit := [(39, false), (1595, true), (51, true), (46, true), (49, false), (103, false)]
theorem step2551 (p : Nat → Bool) (h : Constraints p) : clause p c2551 = true :=
  Snake9.LocalRup.prove_clause [c336, c334, c1466, c1463, c1474] c2551 (by decide) p (sat_cons (step336 p h) (sat_cons (step334 p h) (sat_cons (step1466 p h) (sat_cons (step1463 p h) (sat_cons (step1474 p h) (sat_nil p))))))
def c2552 : List Lit := [(5, true), (1506, true), (2, true), (9, false), (24, false), (133, true)]
theorem step2552 (p : Nat → Bool) (h : Constraints p) : clause p c2552 = true :=
  Snake9.LocalRup.prove_clause [c1306, c2174, c31, c56] c2552 (by decide) p (sat_cons (step1306 p h) (sat_cons (step2174 p h) (sat_cons (step31 p h) (sat_cons (step56 p h) (sat_nil p)))))
def c2553 : List Lit := [(73, false), (38, false), (49, false), (103, false)]
theorem step2553 (p : Nat → Bool) (h : Constraints p) : clause p c2553 = true :=
  Snake9.LocalRup.prove_clause [c337, c340, c2216] c2553 (by decide) p (sat_cons (step337 p h) (sat_cons (step340 p h) (sat_cons (step2216 p h) (sat_nil p))))
def c2554 : List Lit := [(1758, true), (1725, false)]
theorem step2554 (p : Nat → Bool) (h : Constraints p) : clause p c2554 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1845] c2554 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1845 p h) (sat_nil p)))
def c2555 : List Lit := [(1726, false), (1759, true)]
theorem step2555 (p : Nat → Bool) (h : Constraints p) : clause p c2555 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1851] c2555 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1851 p h) (sat_nil p)))
def c2556 : List Lit := [(1727, false), (1760, true)]
theorem step2556 (p : Nat → Bool) (h : Constraints p) : clause p c2556 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1857] c2556 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1857 p h) (sat_nil p)))
def c2557 : List Lit := [(1728, false), (1761, true)]
theorem step2557 (p : Nat → Bool) (h : Constraints p) : clause p c2557 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1863] c2557 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1863 p h) (sat_nil p)))
def c2558 : List Lit := [(1729, false), (1762, true)]
theorem step2558 (p : Nat → Bool) (h : Constraints p) : clause p c2558 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1868] c2558 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1868 p h) (sat_nil p)))
def c2559 : List Lit := [(1730, false), (1763, true)]
theorem step2559 (p : Nat → Bool) (h : Constraints p) : clause p c2559 = true :=
  Snake9.LocalRup.prove_clause [c2431, c1872] c2559 (by decide) p (sat_cons (step2431 p h) (sat_cons (step1872 p h) (sat_nil p)))
def c2560 : List Lit := [(1781, true), (1701, false)]
theorem step2560 (p : Nat → Bool) (h : Constraints p) : clause p c2560 = true :=
  Snake9.LocalRup.prove_clause [c2432, c1910] c2560 (by decide) p (sat_cons (step2432 p h) (sat_cons (step1910 p h) (sat_nil p)))
def c2561 : List Lit := [(1702, false), (1782, true)]
theorem step2561 (p : Nat → Bool) (h : Constraints p) : clause p c2561 = true :=
  Snake9.LocalRup.prove_clause [c2432, c1918] c2561 (by decide) p (sat_cons (step2432 p h) (sat_cons (step1918 p h) (sat_nil p)))
def c2562 : List Lit := [(1703, false), (1783, true)]
theorem step2562 (p : Nat → Bool) (h : Constraints p) : clause p c2562 = true :=
  Snake9.LocalRup.prove_clause [c2432, c1925] c2562 (by decide) p (sat_cons (step2432 p h) (sat_cons (step1925 p h) (sat_nil p)))
def c2563 : List Lit := [(1704, false), (1784, true)]
theorem step2563 (p : Nat → Bool) (h : Constraints p) : clause p c2563 = true :=
  Snake9.LocalRup.prove_clause [c2432, c1931] c2563 (by decide) p (sat_cons (step2432 p h) (sat_cons (step1931 p h) (sat_nil p)))
def c2564 : List Lit := [(1576, true), (1760, true), (455, true), (241, true), (103, true), (111, false)]
theorem step2564 (p : Nat → Bool) (h : Constraints p) : clause p c2564 = true :=
  Snake9.LocalRup.prove_clause [c2431, c2419] c2564 (by decide) p (sat_cons (step2431 p h) (sat_cons (step2419 p h) (sat_nil p)))
def c2565 : List Lit := [(98, true), (1715, true), (96, true), (218, true)]
theorem step2565 (p : Nat → Bool) (h : Constraints p) : clause p c2565 = true :=
  Snake9.LocalRup.prove_clause [c2281, c1754, c816, c1762, c1752] c2565 (by decide) p (sat_cons (step2281 p h) (sat_cons (step1754 p h) (sat_cons (step816 p h) (sat_cons (step1762 p h) (sat_cons (step1752 p h) (sat_nil p))))))
def c2566 : List Lit := [(68, false), (27, false), (61, false), (1651, true)]
theorem step2566 (p : Nat → Bool) (h : Constraints p) : clause p c2566 = true :=
  Snake9.LocalRup.prove_clause [c599, c598, c1608] c2566 (by decide) p (sat_cons (step599 p h) (sat_cons (step598 p h) (sat_cons (step1608 p h) (sat_nil p))))
def c2567 : List Lit := [(60, false), (1598, true), (1660, true)]
theorem step2567 (p : Nat → Bool) (h : Constraints p) : clause p c2567 = true :=
  Snake9.LocalRup.prove_clause [c1479, c1478, c458, c457, c1617, c1615, c1623] c2567 (by decide) p (sat_cons (step1479 p h) (sat_cons (step1478 p h) (sat_cons (step458 p h) (sat_cons (step457 p h) (sat_cons (step1617 p h) (sat_cons (step1615 p h) (sat_cons (step1623 p h) (sat_nil p))))))))
def c2568 : List Lit := [(1617, true), (1607, false), (1568, false), (1589, false), (50, true), (72, false), (67, false), (1660, true)]
theorem step2568 (p : Nat → Bool) (h : Constraints p) : clause p c2568 = true :=
  Snake9.LocalRup.prove_clause [c2535, c1528, c1478, c1479, c2567, c1446, c423, c1433, c2543, c1430, c1109, c610, c1112, c472, c1116, c1144, c1121, c1145, c2337, c1146, c1150] c2568 (by decide) p (sat_cons (step2535 p h) (sat_cons (step1528 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step2567 p h) (sat_cons (step1446 p h) (sat_cons (step423 p h) (sat_cons (step1433 p h) (sat_cons (step2543 p h) (sat_cons (step1430 p h) (sat_cons (step1109 p h) (sat_cons (step610 p h) (sat_cons (step1112 p h) (sat_cons (step472 p h) (sat_cons (step1116 p h) (sat_cons (step1144 p h) (sat_cons (step1121 p h) (sat_cons (step1145 p h) (sat_cons (step2337 p h) (sat_cons (step1146 p h) (sat_cons (step1150 p h) (sat_nil p))))))))))))))))))))))
def c2569 : List Lit := [(1598, true), (68, true), (185, true), (72, false), (1660, true)]
theorem step2569 (p : Nat → Bool) (h : Constraints p) : clause p c2569 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1479, c2567, c423, c472] c2569 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step2567 p h) (sat_cons (step423 p h) (sat_cons (step472 p h) (sat_nil p))))))
def c2570 : List Lit := [(1576, true), (66, false), (61, false), (38, true), (67, false)]
theorem step2570 (p : Nat → Bool) (h : Constraints p) : clause p c2570 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1435, c2543, c1431, c2098, c2328, c556, c295] c2570 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step2543 p h) (sat_cons (step1431 p h) (sat_cons (step2098 p h) (sat_cons (step2328 p h) (sat_cons (step556 p h) (sat_cons (step295 p h) (sat_nil p)))))))))
def c2571 : List Lit := [(1726, true), (97, false), (44, false), (218, true)]
theorem step2571 (p : Nat → Bool) (h : Constraints p) : clause p c2571 = true :=
  Snake9.LocalRup.prove_clause [c1779, c1787, c2515, c2095, c1758, c831, c1750, c1751, c1768, c2456, c1773, c1765] c2571 (by decide) p (sat_cons (step1779 p h) (sat_cons (step1787 p h) (sat_cons (step2515 p h) (sat_cons (step2095 p h) (sat_cons (step1758 p h) (sat_cons (step831 p h) (sat_cons (step1750 p h) (sat_cons (step1751 p h) (sat_cons (step1768 p h) (sat_cons (step2456 p h) (sat_cons (step1773 p h) (sat_cons (step1765 p h) (sat_nil p)))))))))))))
def c2572 : List Lit := [(1750, true), (68, true), (1745, false), (239, true), (67, false)]
theorem step2572 (p : Nat → Bool) (h : Constraints p) : clause p c2572 = true :=
  Snake9.LocalRup.prove_clause [c2152, c1828, c1798, c1803, c2488, c1801] c2572 (by decide) p (sat_cons (step2152 p h) (sat_cons (step1828 p h) (sat_cons (step1798 p h) (sat_cons (step1803 p h) (sat_cons (step2488 p h) (sat_cons (step1801 p h) (sat_nil p)))))))
def c2573 : List Lit := [(93, true), (44, true), (98, false), (222, true)]
theorem step2573 (p : Nat → Bool) (h : Constraints p) : clause p c2573 = true :=
  Snake9.LocalRup.prove_clause [c2500, c835, c836, c867, c2286] c2573 (by decide) p (sat_cons (step2500 p h) (sat_cons (step835 p h) (sat_cons (step836 p h) (sat_cons (step867 p h) (sat_cons (step2286 p h) (sat_nil p))))))
def c2574 : List Lit := [(102, true), (1726, true), (455, true), (46, true), (103, false), (49, false)]
theorem step2574 (p : Nat → Bool) (h : Constraints p) : clause p c2574 = true :=
  Snake9.LocalRup.prove_clause [c1252, c1236, c1227, c1787, c2095, c1779, c1234, c1231, c1230, c1250, c1248, c1242, c1240, c1765, c2287, c1772, c1773, c1783, c1768, c1756, c2093, c1753, c859, c839] c2574 (by decide) p (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1787 p h) (sat_cons (step2095 p h) (sat_cons (step1779 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1242 p h) (sat_cons (step1240 p h) (sat_cons (step1765 p h) (sat_cons (step2287 p h) (sat_cons (step1772 p h) (sat_cons (step1773 p h) (sat_cons (step1783 p h) (sat_cons (step1768 p h) (sat_cons (step1756 p h) (sat_cons (step2093 p h) (sat_cons (step1753 p h) (sat_cons (step859 p h) (sat_cons (step839 p h) (sat_nil p)))))))))))))))))))))))))
def c2575 : List Lit := [(1726, true), (94, true), (439, true)]
theorem step2575 (p : Nat → Bool) (h : Constraints p) : clause p c2575 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1758, c2282, c1234, c1232, c1229, c1236, c1227, c1787, c1783, c2095, c1770, c2500, c835, c1768, c867] c2575 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1758 p h) (sat_cons (step2282 p h) (sat_cons (step1234 p h) (sat_cons (step1232 p h) (sat_cons (step1229 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1787 p h) (sat_cons (step1783 p h) (sat_cons (step2095 p h) (sat_cons (step1770 p h) (sat_cons (step2500 p h) (sat_cons (step835 p h) (sat_cons (step1768 p h) (sat_cons (step867 p h) (sat_nil p)))))))))))))))))
def c2576 : List Lit := [(1689, true), (1680, false), (1671, false)]
theorem step2576 (p : Nat → Bool) (h : Constraints p) : clause p c2576 = true :=
  Snake9.LocalRup.prove_clause [c1667, c1658, c1686, c1690, c1670, c1659, c2097, c1651] c2576 (by decide) p (sat_cons (step1667 p h) (sat_cons (step1658 p h) (sat_cons (step1686 p h) (sat_cons (step1690 p h) (sat_cons (step1670 p h) (sat_cons (step1659 p h) (sat_cons (step2097 p h) (sat_cons (step1651 p h) (sat_nil p)))))))))
def c2577 : List Lit := [(99, false), (1717, true), (91, false), (107, false), (223, true)]
theorem step2577 (p : Nat → Bool) (h : Constraints p) : clause p c2577 = true :=
  Snake9.LocalRup.prove_clause [c2455, c789] c2577 (by decide) p (sat_cons (step2455 p h) (sat_cons (step789 p h) (sat_nil p)))
def c2578 : List Lit := [(99, false), (91, false), (107, false), (223, true), (103, false)]
theorem step2578 (p : Nat → Bool) (h : Constraints p) : clause p c2578 = true :=
  Snake9.LocalRup.prove_clause [c846, c840, c789] c2578 (by decide) p (sat_cons (step846 p h) (sat_cons (step840 p h) (sat_cons (step789 p h) (sat_nil p))))
def c2579 : List Lit := [(98, false), (123, false), (104, false), (93, true), (222, true)]
theorem step2579 (p : Nat → Bool) (h : Constraints p) : clause p c2579 = true :=
  Snake9.LocalRup.prove_clause [c835, c867] c2579 (by decide) p (sat_cons (step835 p h) (sat_cons (step867 p h) (sat_nil p)))
def c2580 : List Lit := [(1751, true), (107, false), (123, false), (68, true), (1745, false), (239, true), (241, true), (67, false)]
theorem step2580 (p : Nat → Bool) (h : Constraints p) : clause p c2580 = true :=
  Snake9.LocalRup.prove_clause [c1832, c2499, c1804, c2116, c1802, c1798, c2491] c2580 (by decide) p (sat_cons (step1832 p h) (sat_cons (step2499 p h) (sat_cons (step1804 p h) (sat_cons (step2116 p h) (sat_cons (step1802 p h) (sat_cons (step1798 p h) (sat_cons (step2491 p h) (sat_nil p))))))))
def c2581 : List Lit := [(64, false), (66, false), (113, false), (107, true), (68, true), (489, true), (72, false)]
theorem step2581 (p : Nat → Bool) (h : Constraints p) : clause p c2581 = true :=
  Snake9.LocalRup.prove_clause [c1296, c1222, c1197, c1174, c1166, c1165, c1294, c1289, c1286, c1262, c1260, c1257, c530, c539, c906, c421, c2294] c2581 (by decide) p (sat_cons (step1296 p h) (sat_cons (step1222 p h) (sat_cons (step1197 p h) (sat_cons (step1174 p h) (sat_cons (step1166 p h) (sat_cons (step1165 p h) (sat_cons (step1294 p h) (sat_cons (step1289 p h) (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1260 p h) (sat_cons (step1257 p h) (sat_cons (step530 p h) (sat_cons (step539 p h) (sat_cons (step906 p h) (sat_cons (step421 p h) (sat_cons (step2294 p h) (sat_nil p))))))))))))))))))
def c2582 : List Lit := [(101, false), (99, false), (107, true), (223, true), (46, true), (103, false)]
theorem step2582 (p : Nat → Bool) (h : Constraints p) : clause p c2582 = true :=
  Snake9.LocalRup.prove_clause [c846, c848, c2279, c2287, c841] c2582 (by decide) p (sat_cons (step846 p h) (sat_cons (step848 p h) (sat_cons (step2279 p h) (sat_cons (step2287 p h) (sat_cons (step841 p h) (sat_nil p))))))
def c2583 : List Lit := [(99, false), (107, true), (92, false), (94, false), (223, true), (46, true), (103, false)]
theorem step2583 (p : Nat → Bool) (h : Constraints p) : clause p c2583 = true :=
  Snake9.LocalRup.prove_clause [c2582, c840, c839, c2279, c2287, c807] c2583 (by decide) p (sat_cons (step2582 p h) (sat_cons (step840 p h) (sat_cons (step839 p h) (sat_cons (step2279 p h) (sat_cons (step2287 p h) (sat_cons (step807 p h) (sat_nil p)))))))
def c2584 : List Lit := [(1751, true), (107, false), (68, true), (485, true), (72, false), (67, false), (120, false)]
theorem step2584 (p : Nat → Bool) (h : Constraints p) : clause p c2584 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1281, c1272, c1266, c2088, c1270, c1268, c2153, c1286, c1262, c1259, c1258, c1832, c2580, c1829, c2144, c1814, c1820, c1812, c920, c2522, c939, c965, c2308, c2116, c2491, c1798] c2584 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step2088 p h) (sat_cons (step1270 p h) (sat_cons (step1268 p h) (sat_cons (step2153 p h) (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1259 p h) (sat_cons (step1258 p h) (sat_cons (step1832 p h) (sat_cons (step2580 p h) (sat_cons (step1829 p h) (sat_cons (step2144 p h) (sat_cons (step1814 p h) (sat_cons (step1820 p h) (sat_cons (step1812 p h) (sat_cons (step920 p h) (sat_cons (step2522 p h) (sat_cons (step939 p h) (sat_cons (step965 p h) (sat_cons (step2308 p h) (sat_cons (step2116 p h) (sat_cons (step2491 p h) (sat_cons (step1798 p h) (sat_nil p))))))))))))))))))))))))))))
def c2585 : List Lit := [(1576, true), (1650, true), (188, true), (68, true)]
theorem step2585 (p : Nat → Bool) (h : Constraints p) : clause p c2585 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1435, c1430, c1428, c2494, c2434] c2585 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1430 p h) (sat_cons (step1428 p h) (sat_cons (step2494 p h) (sat_cons (step2434 p h) (sat_nil p)))))))
def c2586 : List Lit := [(64, false), (61, false), (72, false), (1576, true), (68, true)]
theorem step2586 (p : Nat → Bool) (h : Constraints p) : clause p c2586 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1430, c1435, c2494, c301, c1109, c1112, c1116, c1121, c1157, c1160, c2361, c1296, c1222, c1197, c1174, c1166, c1165, c425, c541] c2586 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1430 p h) (sat_cons (step1435 p h) (sat_cons (step2494 p h) (sat_cons (step301 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1116 p h) (sat_cons (step1121 p h) (sat_cons (step1157 p h) (sat_cons (step1160 p h) (sat_cons (step2361 p h) (sat_cons (step1296 p h) (sat_cons (step1222 p h) (sat_cons (step1197 p h) (sat_cons (step1174 p h) (sat_cons (step1166 p h) (sat_cons (step1165 p h) (sat_cons (step425 p h) (sat_cons (step541 p h) (sat_nil p)))))))))))))))))))))
def c2587 : List Lit := [(1510, false), (1538, false), (275, true), (1553, true)]
theorem step2587 (p : Nat → Bool) (h : Constraints p) : clause p c2587 = true :=
  Snake9.LocalRup.prove_clause [c1063, c1035, c1034, c1033, c2128, c1368, c1401, c1330, c1061, c1058, c1043, c1040, c1320, c1321, c1329, c2136, c1394, c1340, c1373, c1347] c2587 (by decide) p (sat_cons (step1063 p h) (sat_cons (step1035 p h) (sat_cons (step1034 p h) (sat_cons (step1033 p h) (sat_cons (step2128 p h) (sat_cons (step1368 p h) (sat_cons (step1401 p h) (sat_cons (step1330 p h) (sat_cons (step1061 p h) (sat_cons (step1058 p h) (sat_cons (step1043 p h) (sat_cons (step1040 p h) (sat_cons (step1320 p h) (sat_cons (step1321 p h) (sat_cons (step1329 p h) (sat_cons (step2136 p h) (sat_cons (step1394 p h) (sat_cons (step1340 p h) (sat_cons (step1373 p h) (sat_cons (step1347 p h) (sat_nil p)))))))))))))))))))))
end B112E089
