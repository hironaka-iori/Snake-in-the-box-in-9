import B112E105Part0008
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2505 : List Lit := [(1715, true), (94, true), (225, true)]
theorem step2505 (p : Nat → Bool) (h : Constraints p) : clause p c2505 = true :=
  Snake9.LocalRup.prove_clause [c1647, c1649, c1644, c1645, c1641, c572, c545] c2505 (by decide) p (sat_cons (step1647 p h) (sat_cons (step1649 p h) (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step1641 p h) (sat_cons (step572 p h) (sat_cons (step545 p h) (sat_nil p))))))))
def c2506 : List Lit := [(1739, true), (123, false), (121, true), (110, false), (55, true)]
theorem step2506 (p : Nat → Bool) (h : Constraints p) : clause p c2506 = true :=
  Snake9.LocalRup.prove_clause [c1697, c1699, c1695, c1692, c707, c750, c691] c2506 (by decide) p (sat_cons (step1697 p h) (sat_cons (step1699 p h) (sat_cons (step1695 p h) (sat_cons (step1692 p h) (sat_cons (step707 p h) (sat_cons (step750 p h) (sat_cons (step691 p h) (sat_nil p))))))))
def c2507 : List Lit := [(123, false), (1752, true), (121, true), (234, false), (55, true)]
theorem step2507 (p : Nat → Bool) (h : Constraints p) : clause p c2507 = true :=
  Snake9.LocalRup.prove_clause [c1728, c1698, c1221, c1222, c1232, c2239, c1241, c1239, c1236, c690, c2506, c1724, c1711, c1713, c1709, c1705, c2301, c1695, c1696, c1700, c856, c1692, c926, c708] c2507 (by decide) p (sat_cons (step1728 p h) (sat_cons (step1698 p h) (sat_cons (step1221 p h) (sat_cons (step1222 p h) (sat_cons (step1232 p h) (sat_cons (step2239 p h) (sat_cons (step1241 p h) (sat_cons (step1239 p h) (sat_cons (step1236 p h) (sat_cons (step690 p h) (sat_cons (step2506 p h) (sat_cons (step1724 p h) (sat_cons (step1711 p h) (sat_cons (step1713 p h) (sat_cons (step1709 p h) (sat_cons (step1705 p h) (sat_cons (step2301 p h) (sat_cons (step1695 p h) (sat_cons (step1696 p h) (sat_cons (step1700 p h) (sat_cons (step856 p h) (sat_cons (step1692 p h) (sat_cons (step926 p h) (sat_cons (step708 p h) (sat_nil p)))))))))))))))))))))))))
def c2508 : List Lit := [(1752, true), (121, true), (234, false), (55, true)]
theorem step2508 (p : Nat → Bool) (h : Constraints p) : clause p c2508 = true :=
  Snake9.LocalRup.prove_clause [c1221, c1222, c1232, c2239, c1241, c1239, c1236, c690, c1720, c1712, c2507, c1708, c1710, c1711, c1714, c1724, c1705, c1697, c1694, c1695, c856, c710, c926] c2508 (by decide) p (sat_cons (step1221 p h) (sat_cons (step1222 p h) (sat_cons (step1232 p h) (sat_cons (step2239 p h) (sat_cons (step1241 p h) (sat_cons (step1239 p h) (sat_cons (step1236 p h) (sat_cons (step690 p h) (sat_cons (step1720 p h) (sat_cons (step1712 p h) (sat_cons (step2507 p h) (sat_cons (step1708 p h) (sat_cons (step1710 p h) (sat_cons (step1711 p h) (sat_cons (step1714 p h) (sat_cons (step1724 p h) (sat_cons (step1705 p h) (sat_cons (step1697 p h) (sat_cons (step1694 p h) (sat_cons (step1695 p h) (sat_cons (step856 p h) (sat_cons (step710 p h) (sat_cons (step926 p h) (sat_nil p))))))))))))))))))))))))
def c2509 : List Lit := [(110, false), (123, false), (121, true), (107, false), (234, true), (55, true)]
theorem step2509 (p : Nat → Bool) (h : Constraints p) : clause p c2509 = true :=
  Snake9.LocalRup.prove_clause [c748, c698] c2509 (by decide) p (sat_cons (step748 p h) (sat_cons (step698 p h) (sat_nil p)))
def c2510 : List Lit := [(54, false), (122, true), (110, true), (1755, true), (109, false), (104, true), (107, false), (240, true), (105, false)]
theorem step2510 (p : Nat → Bool) (h : Constraints p) : clause p c2510 = true :=
  Snake9.LocalRup.prove_clause [c1709, c1711, c1739, c686, c685, c1695, c1693, c1703, c1704, c1735, c1696, c1714, c2273, c1705] c2510 (by decide) p (sat_cons (step1709 p h) (sat_cons (step1711 p h) (sat_cons (step1739 p h) (sat_cons (step686 p h) (sat_cons (step685 p h) (sat_cons (step1695 p h) (sat_cons (step1693 p h) (sat_cons (step1703 p h) (sat_cons (step1704 p h) (sat_cons (step1735 p h) (sat_cons (step1696 p h) (sat_cons (step1714 p h) (sat_cons (step2273 p h) (sat_cons (step1705 p h) (sat_nil p)))))))))))))))
def c2511 : List Lit := [(301, true), (28, false), (20, true), (18, true), (26, true)]
theorem step2511 (p : Nat → Bool) (h : Constraints p) : clause p c2511 = true :=
  Snake9.LocalRup.prove_clause [c1048, c1049, c1047, c1042, c1044, c1041, c118, c116, c2085] c2511 (by decide) p (sat_cons (step1048 p h) (sat_cons (step1049 p h) (sat_cons (step1047 p h) (sat_cons (step1042 p h) (sat_cons (step1044 p h) (sat_cons (step1041 p h) (sat_cons (step118 p h) (sat_cons (step116 p h) (sat_cons (step2085 p h) (sat_nil p))))))))))
def c2512 : List Lit := [(1676, true), (72, false), (73, true), (82, true)]
theorem step2512 (p : Nat → Bool) (h : Constraints p) : clause p c2512 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1563, c1559, c1555, c460, c463] c2512 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1563 p h) (sat_cons (step1559 p h) (sat_cons (step1555 p h) (sat_cons (step460 p h) (sat_cons (step463 p h) (sat_nil p)))))))
def c2513 : List Lit := [(1724, true), (102, true), (104, false), (68, false)]
theorem step2513 (p : Nat → Bool) (h : Constraints p) : clause p c2513 = true :=
  Snake9.LocalRup.prove_clause [c1656, c1666, c1664, c1657, c1658, c628] c2513 (by decide) p (sat_cons (step1656 p h) (sat_cons (step1666 p h) (sat_cons (step1664 p h) (sat_cons (step1657 p h) (sat_cons (step1658 p h) (sat_cons (step628 p h) (sat_nil p)))))))
def c2514 : List Lit := [(66, false), (1754, true), (1743, false), (101, false), (121, false)]
theorem step2514 (p : Nat → Bool) (h : Constraints p) : clause p c2514 = true :=
  Snake9.LocalRup.prove_clause [c883, c880, c882, c1691, c1710, c1699, c1715, c1726] c2514 (by decide) p (sat_cons (step883 p h) (sat_cons (step880 p h) (sat_cons (step882 p h) (sat_cons (step1691 p h) (sat_cons (step1710 p h) (sat_cons (step1699 p h) (sat_cons (step1715 p h) (sat_cons (step1726 p h) (sat_nil p)))))))))
def c2515 : List Lit := [(68, false), (1723, true), (74, false)]
theorem step2515 (p : Nat → Bool) (h : Constraints p) : clause p c2515 = true :=
  Snake9.LocalRup.prove_clause [c1663, c1656, c1661, c1659, c1655, c592, c1658, c405, c2270] c2515 (by decide) p (sat_cons (step1663 p h) (sat_cons (step1656 p h) (sat_cons (step1661 p h) (sat_cons (step1659 p h) (sat_cons (step1655 p h) (sat_cons (step592 p h) (sat_cons (step1658 p h) (sat_cons (step405 p h) (sat_cons (step2270 p h) (sat_nil p))))))))))
def c2516 : List Lit := [(234, true), (121, true), (55, true), (1752, true)]
theorem step2516 (p : Nat → Bool) (h : Constraints p) : clause p c2516 = true :=
  Snake9.LocalRup.prove_clause [c2504, c917, c2501, c2499, c1724, c1708, c1711] c2516 (by decide) p (sat_cons (step2504 p h) (sat_cons (step917 p h) (sat_cons (step2501 p h) (sat_cons (step2499 p h) (sat_cons (step1724 p h) (sat_cons (step1708 p h) (sat_cons (step1711 p h) (sat_nil p))))))))
def c2517 : List Lit := [(121, true), (1752, true), (55, true)]
theorem step2517 (p : Nat → Bool) (h : Constraints p) : clause p c2517 = true :=
  Snake9.LocalRup.prove_clause [c2508, c2516] c2517 (by decide) p (sat_cons (step2508 p h) (sat_cons (step2516 p h) (sat_nil p)))
def c2518 : List Lit := [(121, false), (1752, true)]
theorem step2518 (p : Nat → Bool) (h : Constraints p) : clause p c2518 = true :=
  Snake9.LocalRup.prove_clause [c2389, c2503, c917, c2502] c2518 (by decide) p (sat_cons (step2389 p h) (sat_cons (step2503 p h) (sat_cons (step917 p h) (sat_cons (step2502 p h) (sat_nil p)))))
def c2519 : List Lit := [(1752, true), (55, true)]
theorem step2519 (p : Nat → Bool) (h : Constraints p) : clause p c2519 = true :=
  Snake9.LocalRup.prove_clause [c2517, c2518] c2519 (by decide) p (sat_cons (step2517 p h) (sat_cons (step2518 p h) (sat_nil p)))
def c2520 : List Lit := [(64, false), (60, false), (40, false), (63, true), (188, true)]
theorem step2520 (p : Nat → Bool) (h : Constraints p) : clause p c2520 = true :=
  Snake9.LocalRup.prove_clause [c375, c333] c2520 (by decide) p (sat_cons (step375 p h) (sat_cons (step333 p h) (sat_nil p)))
def c2521 : List Lit := [(115, true), (110, false), (1752, true), (247, true)]
theorem step2521 (p : Nat → Bool) (h : Constraints p) : clause p c2521 = true :=
  Snake9.LocalRup.prove_clause [c1728, c1698, c1694, c1696, c1697, c1724, c1711, c2055, c1708, c750] c2521 (by decide) p (sat_cons (step1728 p h) (sat_cons (step1698 p h) (sat_cons (step1694 p h) (sat_cons (step1696 p h) (sat_cons (step1697 p h) (sat_cons (step1724 p h) (sat_cons (step1711 p h) (sat_cons (step2055 p h) (sat_cons (step1708 p h) (sat_cons (step750 p h) (sat_nil p)))))))))))
def c2522 : List Lit := [(1684, true), (110, false), (74, false), (215, true)]
theorem step2522 (p : Nat → Bool) (h : Constraints p) : clause p c2522 = true :=
  Snake9.LocalRup.prove_clause [c1575, c2373, c1573, c732] c2522 (by decide) p (sat_cons (step1575 p h) (sat_cons (step2373 p h) (sat_cons (step1573 p h) (sat_cons (step732 p h) (sat_nil p)))))
def c2523 : List Lit := [(217, true), (225, true), (1684, true), (1716, true)]
theorem step2523 (p : Nat → Bool) (h : Constraints p) : clause p c2523 = true :=
  Snake9.LocalRup.prove_clause [c2012, c1642, c2483, c1650] c2523 (by decide) p (sat_cons (step2012 p h) (sat_cons (step1642 p h) (sat_cons (step2483 p h) (sat_cons (step1650 p h) (sat_nil p)))))
def c2524 : List Lit := [(1597, true), (54, false), (172, true), (104, true), (102, false), (49, true)]
theorem step2524 (p : Nat → Bool) (h : Constraints p) : clause p c2524 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1413, c1411, c1404, c1406, c193, c255, c205] c2524 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1413 p h) (sat_cons (step1411 p h) (sat_cons (step1404 p h) (sat_cons (step1406 p h) (sat_cons (step193 p h) (sat_cons (step255 p h) (sat_cons (step205 p h) (sat_nil p)))))))))
def c2525 : List Lit := [(110, true), (1752, true), (121, true)]
theorem step2525 (p : Nat → Bool) (h : Constraints p) : clause p c2525 = true :=
  Snake9.LocalRup.prove_clause [c1728, c1702, c1691, c2043, c1693, c1699, c1700, c917, c1724, c1694, c1695, c709, c1711, c1713, c1708, c1705, c939, c856, c918] c2525 (by decide) p (sat_cons (step1728 p h) (sat_cons (step1702 p h) (sat_cons (step1691 p h) (sat_cons (step2043 p h) (sat_cons (step1693 p h) (sat_cons (step1699 p h) (sat_cons (step1700 p h) (sat_cons (step917 p h) (sat_cons (step1724 p h) (sat_cons (step1694 p h) (sat_cons (step1695 p h) (sat_cons (step709 p h) (sat_cons (step1711 p h) (sat_cons (step1713 p h) (sat_cons (step1708 p h) (sat_cons (step1705 p h) (sat_cons (step939 p h) (sat_cons (step856 p h) (sat_cons (step918 p h) (sat_nil p))))))))))))))))))))
def c2526 : List Lit := [(1751, true), (110, false), (121, true)]
theorem step2526 (p : Nat → Bool) (h : Constraints p) : clause p c2526 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1723, c1711, c1697, c1708, c1709, c1695, c2301] c2526 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1723 p h) (sat_cons (step1711 p h) (sat_cons (step1697 p h) (sat_cons (step1708 p h) (sat_cons (step1709 p h) (sat_cons (step1695 p h) (sat_cons (step2301 p h) (sat_nil p)))))))))
def c2527 : List Lit := [(1743, false), (1752, true), (121, true)]
theorem step2527 (p : Nat → Bool) (h : Constraints p) : clause p c2527 = true :=
  Snake9.LocalRup.prove_clause [c2525, c1720, c1713, c1714, c1724, c1708, c1709, c1697, c2301, c1695] c2527 (by decide) p (sat_cons (step2525 p h) (sat_cons (step1720 p h) (sat_cons (step1713 p h) (sat_cons (step1714 p h) (sat_cons (step1724 p h) (sat_cons (step1708 p h) (sat_cons (step1709 p h) (sat_cons (step1697 p h) (sat_cons (step2301 p h) (sat_cons (step1695 p h) (sat_nil p)))))))))))
def c2528 : List Lit := [(1684, true), (1715, true)]
theorem step2528 (p : Nat → Bool) (h : Constraints p) : clause p c2528 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1577, c1572, c1569, c2404] c2528 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1577 p h) (sat_cons (step1572 p h) (sat_cons (step1569 p h) (sat_cons (step2404 p h) (sat_nil p))))))
def c2529 : List Lit := [(83, false), (1746, true), (101, false), (121, false)]
theorem step2529 (p : Nat → Bool) (h : Constraints p) : clause p c2529 = true :=
  Snake9.LocalRup.prove_clause [c893, c892, c1710] c2529 (by decide) p (sat_cons (step893 p h) (sat_cons (step892 p h) (sat_cons (step1710 p h) (sat_nil p))))
def c2530 : List Lit := [(66, false), (1754, true), (101, false), (121, false)]
theorem step2530 (p : Nat → Bool) (h : Constraints p) : clause p c2530 = true :=
  Snake9.LocalRup.prove_clause [c881, c2514, c1705] c2530 (by decide) p (sat_cons (step881 p h) (sat_cons (step2514 p h) (sat_cons (step1705 p h) (sat_nil p))))
def c2531 : List Lit := [(1747, true), (121, false)]
theorem step2531 (p : Nat → Bool) (h : Constraints p) : clause p c2531 = true :=
  Snake9.LocalRup.prove_clause [c1711, c2502, c1709] c2531 (by decide) p (sat_cons (step1711 p h) (sat_cons (step2502 p h) (sat_cons (step1709 p h) (sat_nil p))))
def c2532 : List Lit := [(1611, true), (172, true), (52, true), (56, false), (49, true), (1600, false)]
theorem step2532 (p : Nat → Bool) (h : Constraints p) : clause p c2532 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1406, c1411, c1424, c1445, c1441, c1412, c1414, c1425, c1407, c1404, c1419, c257, c2035, c236] c2532 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1406 p h) (sat_cons (step1411 p h) (sat_cons (step1424 p h) (sat_cons (step1445 p h) (sat_cons (step1441 p h) (sat_cons (step1412 p h) (sat_cons (step1414 p h) (sat_cons (step1425 p h) (sat_cons (step1407 p h) (sat_cons (step1404 p h) (sat_cons (step1419 p h) (sat_cons (step257 p h) (sat_cons (step2035 p h) (sat_cons (step236 p h) (sat_nil p))))))))))))))))
def c2533 : List Lit := [(331, true), (31, false), (1582, true), (1589, true), (155, true), (37, true), (35, true), (34, true)]
theorem step2533 (p : Nat → Bool) (h : Constraints p) : clause p c2533 = true :=
  Snake9.LocalRup.prove_clause [c1385, c1077, c1075, c2400, c1074, c2500, c2388, c2401] c2533 (by decide) p (sat_cons (step1385 p h) (sat_cons (step1077 p h) (sat_cons (step1075 p h) (sat_cons (step2400 p h) (sat_cons (step1074 p h) (sat_cons (step2500 p h) (sat_cons (step2388 p h) (sat_cons (step2401 p h) (sat_nil p)))))))))
def c2534 : List Lit := [(80, false), (81, true), (77, false), (121, false)]
theorem step2534 (p : Nat → Bool) (h : Constraints p) : clause p c2534 = true :=
  Snake9.LocalRup.prove_clause [c2135, c472] c2534 (by decide) p (sat_cons (step2135 p h) (sat_cons (step472 p h) (sat_nil p)))
def c2535 : List Lit := [(427, true), (72, false), (77, false), (121, false), (73, true), (82, true)]
theorem step2535 (p : Nat → Bool) (h : Constraints p) : clause p c2535 = true :=
  Snake9.LocalRup.prove_clause [c1185, c1187, c1182, c1150, c1166, c1148, c1157, c1139, c1156, c1138, c466, c416, c2534] c2535 (by decide) p (sat_cons (step1185 p h) (sat_cons (step1187 p h) (sat_cons (step1182 p h) (sat_cons (step1150 p h) (sat_cons (step1166 p h) (sat_cons (step1148 p h) (sat_cons (step1157 p h) (sat_cons (step1139 p h) (sat_cons (step1156 p h) (sat_cons (step1138 p h) (sat_cons (step466 p h) (sat_cons (step416 p h) (sat_cons (step2534 p h) (sat_nil p))))))))))))))
def c2536 : List Lit := [(1611, true), (172, true), (176, true), (1654, true), (56, false), (55, true), (49, true), (1600, false)]
theorem step2536 (p : Nat → Bool) (h : Constraints p) : clause p c2536 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1445, c2532, c2047, c251, c256, c258, c1404, c1405, c1414] c2536 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1445 p h) (sat_cons (step2532 p h) (sat_cons (step2047 p h) (sat_cons (step251 p h) (sat_cons (step256 p h) (sat_cons (step258 p h) (sat_cons (step1404 p h) (sat_cons (step1405 p h) (sat_cons (step1414 p h) (sat_nil p)))))))))))
def c2537 : List Lit := [(117, false), (1677, true), (77, false), (25, false)]
theorem step2537 (p : Nat → Bool) (h : Constraints p) : clause p c2537 = true :=
  Snake9.LocalRup.prove_clause [c443, c442, c1559, c1556, c1564] c2537 (by decide) p (sat_cons (step443 p h) (sat_cons (step442 p h) (sat_cons (step1559 p h) (sat_cons (step1556 p h) (sat_cons (step1564 p h) (sat_nil p))))))
def c2538 : List Lit := [(1715, true), (117, false), (121, true)]
theorem step2538 (p : Nat → Bool) (h : Constraints p) : clause p c2538 = true :=
  Snake9.LocalRup.prove_clause [c1647, c1649, c1644, c1645, c1641, c1642, c545, c526, c566] c2538 (by decide) p (sat_cons (step1647 p h) (sat_cons (step1649 p h) (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step1641 p h) (sat_cons (step1642 p h) (sat_cons (step545 p h) (sat_cons (step526 p h) (sat_cons (step566 p h) (sat_nil p))))))))))
def c2539 : List Lit := [(1685, true), (93, true), (215, true), (112, true)]
theorem step2539 (p : Nat → Bool) (h : Constraints p) : clause p c2539 = true :=
  Snake9.LocalRup.prove_clause [c1572, c1576, c1578, c1574, c1570, c517, c516, c1906] c2539 (by decide) p (sat_cons (step1572 p h) (sat_cons (step1576 p h) (sat_cons (step1578 p h) (sat_cons (step1574 p h) (sat_cons (step1570 p h) (sat_cons (step517 p h) (sat_cons (step516 p h) (sat_cons (step1906 p h) (sat_nil p)))))))))
def c2540 : List Lit := [(1763, true), (1753, false), (66, false), (1723, false), (121, false)]
theorem step2540 (p : Nat → Bool) (h : Constraints p) : clause p c2540 = true :=
  Snake9.LocalRup.prove_clause [c1669, c1747, c1752, c2530, c1674, c1644, c1647] c2540 (by decide) p (sat_cons (step1669 p h) (sat_cons (step1747 p h) (sat_cons (step1752 p h) (sat_cons (step2530 p h) (sat_cons (step1674 p h) (sat_cons (step1644 p h) (sat_cons (step1647 p h) (sat_nil p))))))))
def c2541 : List Lit := [(1745, true), (101, false), (121, false)]
theorem step2541 (p : Nat → Bool) (h : Constraints p) : clause p c2541 = true :=
  Snake9.LocalRup.prove_clause [c1708, c1709, c905] c2541 (by decide) p (sat_cons (step1708 p h) (sat_cons (step1709 p h) (sat_cons (step905 p h) (sat_nil p))))
def c2542 : List Lit := [(1762, true), (225, true), (1723, false), (121, false)]
theorem step2542 (p : Nat → Bool) (h : Constraints p) : clause p c2542 = true :=
  Snake9.LocalRup.prove_clause [c1669, c2518, c1751, c1746, c1674, c1721, c1647, c2505, c1644, c1910, c2541, c1705, c1714, c1715, c1725, c1699, c1691, c901, c902, c1710] c2542 (by decide) p (sat_cons (step1669 p h) (sat_cons (step2518 p h) (sat_cons (step1751 p h) (sat_cons (step1746 p h) (sat_cons (step1674 p h) (sat_cons (step1721 p h) (sat_cons (step1647 p h) (sat_cons (step2505 p h) (sat_cons (step1644 p h) (sat_cons (step1910 p h) (sat_cons (step2541 p h) (sat_cons (step1705 p h) (sat_cons (step1714 p h) (sat_cons (step1715 p h) (sat_cons (step1725 p h) (sat_cons (step1699 p h) (sat_cons (step1691 p h) (sat_cons (step901 p h) (sat_cons (step902 p h) (sat_cons (step1710 p h) (sat_nil p)))))))))))))))))))))
def c2543 : List Lit := [(1739, true), (1723, true)]
theorem step2543 (p : Nat → Bool) (h : Constraints p) : clause p c2543 = true :=
  Snake9.LocalRup.prove_clause [c1663, c1661, c1658, c2399, c1656, c1655, c1697, c1699, c1695, c1692, c2296] c2543 (by decide) p (sat_cons (step1663 p h) (sat_cons (step1661 p h) (sat_cons (step1658 p h) (sat_cons (step2399 p h) (sat_cons (step1656 p h) (sat_cons (step1655 p h) (sat_cons (step1697 p h) (sat_cons (step1699 p h) (sat_cons (step1695 p h) (sat_cons (step1692 p h) (sat_cons (step2296 p h) (sat_nil p))))))))))))
def c2544 : List Lit := [(1596, true), (172, true), (47, true), (51, true)]
theorem step2544 (p : Nat → Bool) (h : Constraints p) : clause p c2544 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1410, c1405, c1403, c2018, c207] c2544 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1405 p h) (sat_cons (step1403 p h) (sat_cons (step2018 p h) (sat_cons (step207 p h) (sat_nil p)))))))
def c2545 : List Lit := [(1623, false), (1641, true)]
theorem step2545 (p : Nat → Bool) (h : Constraints p) : clause p c2545 = true :=
  Snake9.LocalRup.prove_clause [c2477, c1492] c2545 (by decide) p (sat_cons (step2477 p h) (sat_cons (step1492 p h) (sat_nil p)))
def c2546 : List Lit := [(1640, true), (1622, false)]
theorem step2546 (p : Nat → Bool) (h : Constraints p) : clause p c2546 = true :=
  Snake9.LocalRup.prove_clause [c2477, c1491] c2546 (by decide) p (sat_cons (step2477 p h) (sat_cons (step1491 p h) (sat_nil p)))
def c2547 : List Lit := [(1636, true), (1618, false)]
theorem step2547 (p : Nat → Bool) (h : Constraints p) : clause p c2547 = true :=
  Snake9.LocalRup.prove_clause [c2477, c1487] c2547 (by decide) p (sat_cons (step2477 p h) (sat_cons (step1487 p h) (sat_nil p)))
def c2548 : List Lit := [(1637, true), (1619, false)]
theorem step2548 (p : Nat → Bool) (h : Constraints p) : clause p c2548 = true :=
  Snake9.LocalRup.prove_clause [c2477, c1488] c2548 (by decide) p (sat_cons (step2477 p h) (sat_cons (step1488 p h) (sat_nil p)))
def c2549 : List Lit := [(1638, true), (1620, false)]
theorem step2549 (p : Nat → Bool) (h : Constraints p) : clause p c2549 = true :=
  Snake9.LocalRup.prove_clause [c2477, c1489] c2549 (by decide) p (sat_cons (step2477 p h) (sat_cons (step1489 p h) (sat_nil p)))
def c2550 : List Lit := [(1621, false), (1639, true)]
theorem step2550 (p : Nat → Bool) (h : Constraints p) : clause p c2550 = true :=
  Snake9.LocalRup.prove_clause [c2477, c1490] c2550 (by decide) p (sat_cons (step2477 p h) (sat_cons (step1490 p h) (sat_nil p)))
def c2551 : List Lit := [(1654, true), (52, false), (121, true), (55, true)]
theorem step2551 (p : Nat → Bool) (h : Constraints p) : clause p c2551 = true :=
  Snake9.LocalRup.prove_clause [c1521, c2047, c1519, c381] c2551 (by decide) p (sat_cons (step1521 p h) (sat_cons (step2047 p h) (sat_cons (step1519 p h) (sat_cons (step381 p h) (sat_nil p)))))
def c2552 : List Lit := [(66, true), (104, true), (102, false), (1667, true), (76, true)]
theorem step2552 (p : Nat → Bool) (h : Constraints p) : clause p c2552 = true :=
  Snake9.LocalRup.prove_clause [c1529, c1532, c1549, c1522, c1519, c1520, c1521, c1546, c1533, c1535, c1531, c1526, c1527, c403, c388, c393] c2552 (by decide) p (sat_cons (step1529 p h) (sat_cons (step1532 p h) (sat_cons (step1549 p h) (sat_cons (step1522 p h) (sat_cons (step1519 p h) (sat_cons (step1520 p h) (sat_cons (step1521 p h) (sat_cons (step1546 p h) (sat_cons (step1533 p h) (sat_cons (step1535 p h) (sat_cons (step1531 p h) (sat_cons (step1526 p h) (sat_cons (step1527 p h) (sat_cons (step403 p h) (sat_cons (step388 p h) (sat_cons (step393 p h) (sat_nil p)))))))))))))))))
def c2553 : List Lit := [(64, true), (190, true), (121, true), (1655, true), (55, false)]
theorem step2553 (p : Nat → Bool) (h : Constraints p) : clause p c2553 = true :=
  Snake9.LocalRup.prove_clause [c1524, c1519, c385, c1886, c2116] c2553 (by decide) p (sat_cons (step1524 p h) (sat_cons (step1519 p h) (sat_cons (step385 p h) (sat_cons (step1886 p h) (sat_cons (step2116 p h) (sat_nil p))))))
def c2554 : List Lit := [(1684, true), (117, true), (225, false), (121, true)]
theorem step2554 (p : Nat → Bool) (h : Constraints p) : clause p c2554 = true :=
  Snake9.LocalRup.prove_clause [c1201, c1202, c1214, c1216, c1252, c2241, c1185, c1180, c1176, c1173, c1172, c565, c2012, c2469, c2151, c566] c2554 (by decide) p (sat_cons (step1201 p h) (sat_cons (step1202 p h) (sat_cons (step1214 p h) (sat_cons (step1216 p h) (sat_cons (step1252 p h) (sat_cons (step2241 p h) (sat_cons (step1185 p h) (sat_cons (step1180 p h) (sat_cons (step1176 p h) (sat_cons (step1173 p h) (sat_cons (step1172 p h) (sat_cons (step565 p h) (sat_cons (step2012 p h) (sat_cons (step2469 p h) (sat_cons (step2151 p h) (sat_cons (step566 p h) (sat_nil p)))))))))))))))))
def c2555 : List Lit := [(257, true), (4, false), (6, true), (15, true), (34, true)]
theorem step2555 (p : Nat → Bool) (h : Constraints p) : clause p c2555 = true :=
  Snake9.LocalRup.prove_clause [c1010, c1011, c1008, c1007, c18, c10, c2066] c2555 (by decide) p (sat_cons (step1010 p h) (sat_cons (step1011 p h) (sat_cons (step1008 p h) (sat_cons (step1007 p h) (sat_cons (step18 p h) (sat_cons (step10 p h) (sat_cons (step2066 p h) (sat_nil p))))))))
def c2556 : List Lit := [(6, true), (1514, true), (257, true), (15, true), (34, true)]
theorem step2556 (p : Nat → Bool) (h : Constraints p) : clause p c2556 = true :=
  Snake9.LocalRup.prove_clause [c2555, c1267] c2556 (by decide) p (sat_cons (step2555 p h) (sat_cons (step1267 p h) (sat_nil p)))
def c2557 : List Lit := [(6, false), (24, false), (23, false), (12, false)]
theorem step2557 (p : Nat → Bool) (h : Constraints p) : clause p c2557 = true :=
  Snake9.LocalRup.prove_clause [c88, c91, c2070] c2557 (by decide) p (sat_cons (step88 p h) (sat_cons (step91 p h) (sat_cons (step2070 p h) (sat_nil p))))
def c2558 : List Lit := [(1597, true), (1723, true), (49, true)]
theorem step2558 (p : Nat → Bool) (h : Constraints p) : clause p c2558 = true :=
  Snake9.LocalRup.prove_clause [c2402, c1204, c1209, c1212, c1216, c1252, c1255, c2242, c1121, c1116, c1113, c1094, c1087, c1084, c1663, c1661, c1658, c2399, c1656, c1402, c1411, c2524, c1405] c2558 (by decide) p (sat_cons (step2402 p h) (sat_cons (step1204 p h) (sat_cons (step1209 p h) (sat_cons (step1212 p h) (sat_cons (step1216 p h) (sat_cons (step1252 p h) (sat_cons (step1255 p h) (sat_cons (step2242 p h) (sat_cons (step1121 p h) (sat_cons (step1116 p h) (sat_cons (step1113 p h) (sat_cons (step1094 p h) (sat_cons (step1087 p h) (sat_cons (step1084 p h) (sat_cons (step1663 p h) (sat_cons (step1661 p h) (sat_cons (step1658 p h) (sat_cons (step2399 p h) (sat_cons (step1656 p h) (sat_cons (step1402 p h) (sat_cons (step1411 p h) (sat_cons (step2524 p h) (sat_cons (step1405 p h) (sat_nil p))))))))))))))))))))))))
def c2559 : List Lit := [(1620, true), (58, false), (22, false), (331, true), (1586, false), (1596, false)]
theorem step2559 (p : Nat → Bool) (h : Constraints p) : clause p c2559 = true :=
  Snake9.LocalRup.prove_clause [c1461, c2328] c2559 (by decide) p (sat_cons (step1461 p h) (sat_cons (step2328 p h) (sat_nil p)))
def c2560 : List Lit := [(1676, true), (1667, true), (74, false), (76, true), (73, true)]
theorem step2560 (p : Nat → Bool) (h : Constraints p) : clause p c2560 = true :=
  Snake9.LocalRup.prove_clause [c1529, c1542, c1538, c2138, c1561, c1563, c2512, c1558, c1555, c1526, c1528, c466, c1535, c1156, c1546, c1157, c1521, c1166, c1518, c1182, c403, c2229, c1152, c1133, c1130, c1129, c2409, c400, c621, c2120] c2560 (by decide) p (sat_cons (step1529 p h) (sat_cons (step1542 p h) (sat_cons (step1538 p h) (sat_cons (step2138 p h) (sat_cons (step1561 p h) (sat_cons (step1563 p h) (sat_cons (step2512 p h) (sat_cons (step1558 p h) (sat_cons (step1555 p h) (sat_cons (step1526 p h) (sat_cons (step1528 p h) (sat_cons (step466 p h) (sat_cons (step1535 p h) (sat_cons (step1156 p h) (sat_cons (step1546 p h) (sat_cons (step1157 p h) (sat_cons (step1521 p h) (sat_cons (step1166 p h) (sat_cons (step1518 p h) (sat_cons (step1182 p h) (sat_cons (step403 p h) (sat_cons (step2229 p h) (sat_cons (step1152 p h) (sat_cons (step1133 p h) (sat_cons (step1130 p h) (sat_cons (step1129 p h) (sat_cons (step2409 p h) (sat_cons (step400 p h) (sat_cons (step621 p h) (sat_cons (step2120 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2561 : List Lit := [(63, true), (64, false), (188, true), (59, false)]
theorem step2561 (p : Nat → Bool) (h : Constraints p) : clause p c2561 = true :=
  Snake9.LocalRup.prove_clause [c375, c373, c1891] c2561 (by decide) p (sat_cons (step375 p h) (sat_cons (step373 p h) (sat_cons (step1891 p h) (sat_nil p))))
def c2562 : List Lit := [(1600, false), (1610, true), (64, false), (188, true), (59, false), (1592, false)]
theorem step2562 (p : Nat → Bool) (h : Constraints p) : clause p c2562 = true :=
  Snake9.LocalRup.prove_clause [c1410, c1436, c1424, c1425, c1440, c1420, c1411, c2040, c1405] c2562 (by decide) p (sat_cons (step1410 p h) (sat_cons (step1436 p h) (sat_cons (step1424 p h) (sat_cons (step1425 p h) (sat_cons (step1440 p h) (sat_cons (step1420 p h) (sat_cons (step1411 p h) (sat_cons (step2040 p h) (sat_cons (step1405 p h) (sat_nil p))))))))))
def c2563 : List Lit := [(1676, true), (1667, true), (76, true), (73, true)]
theorem step2563 (p : Nat → Bool) (h : Constraints p) : clause p c2563 = true :=
  Snake9.LocalRup.prove_clause [c1542, c2138, c2512, c2560, c1526, c1531, c1536] c2563 (by decide) p (sat_cons (step1542 p h) (sat_cons (step2138 p h) (sat_cons (step2512 p h) (sat_cons (step2560 p h) (sat_cons (step1526 p h) (sat_cons (step1531 p h) (sat_cons (step1536 p h) (sat_nil p))))))))
def c2564 : List Lit := [(56, false), (63, false), (55, false), (17, false)]
theorem step2564 (p : Nat → Bool) (h : Constraints p) : clause p c2564 = true :=
  Snake9.LocalRup.prove_clause [c282, c279, c2115] c2564 (by decide) p (sat_cons (step282 p h) (sat_cons (step279 p h) (sat_cons (step2115 p h) (sat_nil p))))
def c2565 : List Lit := [(225, true), (89, false), (93, false), (1716, true), (117, false), (121, true)]
theorem step2565 (p : Nat → Bool) (h : Constraints p) : clause p c2565 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1648, c2495, c1650, c1641, c1642, c2374, c2496, c1646] c2565 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1648 p h) (sat_cons (step2495 p h) (sat_cons (step1650 p h) (sat_cons (step1641 p h) (sat_cons (step1642 p h) (sat_cons (step2374 p h) (sat_cons (step2496 p h) (sat_cons (step1646 p h) (sat_nil p))))))))))
def c2566 : List Lit := [(1610, true), (59, true), (55, false), (17, false), (1592, false)]
theorem step2566 (p : Nat → Bool) (h : Constraints p) : clause p c2566 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1424, c1410, c1436, c1440, c1427, c1411, c1418, c1406, c279] c2566 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1424 p h) (sat_cons (step1410 p h) (sat_cons (step1436 p h) (sat_cons (step1440 p h) (sat_cons (step1427 p h) (sat_cons (step1411 p h) (sat_cons (step1418 p h) (sat_cons (step1406 p h) (sat_cons (step279 p h) (sat_nil p)))))))))))
def c2567 : List Lit := [(1611, true), (55, false), (172, true), (1597, false), (59, true), (17, false), (49, true)]
theorem step2567 (p : Nat → Bool) (h : Constraints p) : clause p c2567 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1441, c1427, c1418, c279, c2532] c2567 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1441 p h) (sat_cons (step1427 p h) (sat_cons (step1418 p h) (sat_cons (step279 p h) (sat_cons (step2532 p h) (sat_nil p)))))))
def c2568 : List Lit := [(1609, true), (55, false), (17, false), (1592, false)]
theorem step2568 (p : Nat → Bool) (h : Constraints p) : clause p c2568 = true :=
  Snake9.LocalRup.prove_clause [c1410, c1439, c1435, c1411, c1424, c1406, c1417, c279] c2568 (by decide) p (sat_cons (step1410 p h) (sat_cons (step1439 p h) (sat_cons (step1435 p h) (sat_cons (step1411 p h) (sat_cons (step1424 p h) (sat_cons (step1406 p h) (sat_cons (step1417 p h) (sat_cons (step279 p h) (sat_nil p)))))))))
end B112E105
