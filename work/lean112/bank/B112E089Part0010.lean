import B112E089Part0009
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2652 : List Lit := [(1760, true), (1745, false), (1750, false), (112, false), (91, true), (62, false), (1725, false), (487, true)]
theorem step2652 (p : Nat → Bool) (h : Constraints p) : clause p c2652 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1252, c1234, c1231, c1230, c2645, c1852, c894, c2639] c2652 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step2645 p h) (sat_cons (step1852 p h) (sat_cons (step894 p h) (sat_cons (step2639 p h) (sat_nil p))))))))))
def c2653 : List Lit := [(115, false), (68, false), (27, false), (69, true), (1667, true), (1657, false)]
theorem step2653 (p : Nat → Bool) (h : Constraints p) : clause p c2653 = true :=
  Snake9.LocalRup.prove_clause [c607, c606, c604, c1616, c1608, c1626, c1610, c1640] c2653 (by decide) p (sat_cons (step607 p h) (sat_cons (step606 p h) (sat_cons (step604 p h) (sat_cons (step1616 p h) (sat_cons (step1608 p h) (sat_cons (step1626 p h) (sat_cons (step1610 p h) (sat_cons (step1640 p h) (sat_nil p)))))))))
def c2654 : List Lit := [(1761, true), (1746, false), (113, true), (91, true), (1725, false), (487, true)]
theorem step2654 (p : Nat → Bool) (h : Constraints p) : clause p c2654 = true :=
  Snake9.LocalRup.prove_clause [c1797, c1805, c1829, c1291, c1252, c1234, c1231, c1230, c1289, c1284, c1281, c1272, c1266, c1848, c1853, c1833, c2639, c2090] c2654 (by decide) p (sat_cons (step1797 p h) (sat_cons (step1805 p h) (sat_cons (step1829 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1848 p h) (sat_cons (step1853 p h) (sat_cons (step1833 p h) (sat_cons (step2639 p h) (sat_cons (step2090 p h) (sat_nil p)))))))))))))))))))
def c2655 : List Lit := [(120, false), (1760, true), (112, false), (91, true), (62, false), (223, true)]
theorem step2655 (p : Nat → Bool) (h : Constraints p) : clause p c2655 = true :=
  Snake9.LocalRup.prove_clause [c895, c896, c2639, c1797, c1852, c2152] c2655 (by decide) p (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step2639 p h) (sat_cons (step1797 p h) (sat_cons (step1852 p h) (sat_cons (step2152 p h) (sat_nil p)))))))
def c2656 : List Lit := [(1593, true), (51, true), (49, true), (174, true)]
theorem step2656 (p : Nat → Bool) (h : Constraints p) : clause p c2656 = true :=
  Snake9.LocalRup.prove_clause [c1464, c1468, c1470, c1466, c1461, c1462, c352, c318] c2656 (by decide) p (sat_cons (step1464 p h) (sat_cons (step1468 p h) (sat_cons (step1470 p h) (sat_cons (step1466 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step352 p h) (sat_cons (step318 p h) (sat_nil p)))))))))
def c2657 : List Lit := [(1544, true), (24, true), (1530, false), (1525, false), (153, true)]
theorem step2657 (p : Nat → Bool) (h : Constraints p) : clause p c2657 = true :=
  Snake9.LocalRup.prove_clause [c1354, c1361, c2129, c1378, c1381, c1355, c1362, c1349, c2412, c1356] c2657 (by decide) p (sat_cons (step1354 p h) (sat_cons (step1361 p h) (sat_cons (step2129 p h) (sat_cons (step1378 p h) (sat_cons (step1381 p h) (sat_cons (step1355 p h) (sat_cons (step1362 p h) (sat_cons (step1349 p h) (sat_cons (step2412 p h) (sat_cons (step1356 p h) (sat_nil p)))))))))))
def c2658 : List Lit := [(1616, true), (1569, false), (68, false), (27, false), (1572, false), (1592, false)]
theorem step2658 (p : Nat → Bool) (h : Constraints p) : clause p c2658 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1451, c1493, c1541, c1534, c1452, c1494, c1436, c1481, c1430, c1478, c593] c2658 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1451 p h) (sat_cons (step1493 p h) (sat_cons (step1541 p h) (sat_cons (step1534 p h) (sat_cons (step1452 p h) (sat_cons (step1494 p h) (sat_cons (step1436 p h) (sat_cons (step1481 p h) (sat_cons (step1430 p h) (sat_cons (step1478 p h) (sat_cons (step593 p h) (sat_nil p)))))))))))))
def c2659 : List Lit := [(69, false), (75, false), (74, true), (57, false), (193, true)]
theorem step2659 (p : Nat → Bool) (h : Constraints p) : clause p c2659 = true :=
  Snake9.LocalRup.prove_clause [c640, c650] c2659 (by decide) p (sat_cons (step640 p h) (sat_cons (step650 p h) (sat_nil p)))
def c2660 : List Lit := [(1750, true), (122, true), (1745, false), (243, true)]
theorem step2660 (p : Nat → Bool) (h : Constraints p) : clause p c2660 = true :=
  Snake9.LocalRup.prove_clause [c1815, c1825, c1828, c1818, c1820, c1803, c1816, c1812, c2139] c2660 (by decide) p (sat_cons (step1815 p h) (sat_cons (step1825 p h) (sat_cons (step1828 p h) (sat_cons (step1818 p h) (sat_cons (step1820 p h) (sat_cons (step1803 p h) (sat_cons (step1816 p h) (sat_cons (step1812 p h) (sat_cons (step2139 p h) (sat_nil p))))))))))
def c2661 : List Lit := [(1666, true), (73, true), (69, true), (63, true), (1660, false), (62, true), (1657, false), (57, false), (188, true)]
theorem step2661 (p : Nat → Bool) (h : Constraints p) : clause p c2661 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1611, c1639, c1635, c1612, c1626, c1624, c1606, c1607, c1616, c1619, c624, c424, c539] c2661 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1611 p h) (sat_cons (step1639 p h) (sat_cons (step1635 p h) (sat_cons (step1612 p h) (sat_cons (step1626 p h) (sat_cons (step1624 p h) (sat_cons (step1606 p h) (sat_cons (step1607 p h) (sat_cons (step1616 p h) (sat_cons (step1619 p h) (sat_cons (step624 p h) (sat_cons (step424 p h) (sat_cons (step539 p h) (sat_nil p)))))))))))))))
def c2662 : List Lit := [(73, false), (75, false), (60, true), (57, false), (49, true), (197, true)]
theorem step2662 (p : Nat → Bool) (h : Constraints p) : clause p c2662 = true :=
  Snake9.LocalRup.prove_clause [c680, c653] c2662 (by decide) p (sat_cons (step680 p h) (sat_cons (step653 p h) (sat_nil p)))
def c2663 : List Lit := [(32, false), (75, false), (74, false), (23, true), (156, true)]
theorem step2663 (p : Nat → Bool) (h : Constraints p) : clause p c2663 = true :=
  Snake9.LocalRup.prove_clause [c190, c1965] c2663 (by decide) p (sat_cons (step190 p h) (sat_cons (step1965 p h) (sat_nil p)))
def c2664 : List Lit := [(1614, true), (63, false), (113, false), (42, true), (1592, false)]
theorem step2664 (p : Nat → Bool) (h : Constraints p) : clause p c2664 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1435, c1441, c1493, c1518, c1525, c1494, c1442, c1483, c1438, c1475, c1429, c514] c2664 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1435 p h) (sat_cons (step1441 p h) (sat_cons (step1493 p h) (sat_cons (step1518 p h) (sat_cons (step1525 p h) (sat_cons (step1494 p h) (sat_cons (step1442 p h) (sat_cons (step1483 p h) (sat_cons (step1438 p h) (sat_cons (step1475 p h) (sat_cons (step1429 p h) (sat_cons (step514 p h) (sat_nil p))))))))))))))
def c2665 : List Lit := [(25, true), (1539, true), (34, false), (24, true), (21, false), (26, true), (18, true), (299, true)]
theorem step2665 (p : Nat → Bool) (h : Constraints p) : clause p c2665 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1075, c1077, c1076, c2189, c1355, c173, c1365, c2206, c1357, c2460] c2665 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1075 p h) (sat_cons (step1077 p h) (sat_cons (step1076 p h) (sat_cons (step2189 p h) (sat_cons (step1355 p h) (sat_cons (step173 p h) (sat_cons (step1365 p h) (sat_cons (step2206 p h) (sat_cons (step1357 p h) (sat_cons (step2460 p h) (sat_nil p))))))))))))
def c2666 : List Lit := [(27, false), (1651, true), (67, false), (26, true), (151, true)]
theorem step2666 (p : Nat → Bool) (h : Constraints p) : clause p c2666 = true :=
  Snake9.LocalRup.prove_clause [c162, c603, c605, c1608] c2666 (by decide) p (sat_cons (step162 p h) (sat_cons (step603 p h) (sat_cons (step605 p h) (sat_cons (step1608 p h) (sat_nil p)))))
def c2667 : List Lit := [(1709, true), (91, false), (81, false), (220, true)]
theorem step2667 (p : Nat → Bool) (h : Constraints p) : clause p c2667 = true :=
  Snake9.LocalRup.prove_clause [c1750, c2634, c821] c2667 (by decide) p (sat_cons (step1750 p h) (sat_cons (step2634 p h) (sat_cons (step821 p h) (sat_nil p))))
def c2668 : List Lit := [(1709, true), (91, false), (42, false), (220, true)]
theorem step2668 (p : Nat → Bool) (h : Constraints p) : clause p c2668 = true :=
  Snake9.LocalRup.prove_clause [c1750, c2634, c820] c2668 (by decide) p (sat_cons (step1750 p h) (sat_cons (step2634 p h) (sat_cons (step820 p h) (sat_nil p))))
def c2669 : List Lit := [(1652, false), (1699, true), (69, true), (1660, false), (74, true), (1680, false), (62, false), (1657, false), (200, true)]
theorem step2669 (p : Nat → Bool) (h : Constraints p) : clause p c2669 = true :=
  Snake9.LocalRup.prove_clause [c2408, c1722, c1634, c1635, c1716, c1626, c2511, c1616, c1647, c2484, c561] c2669 (by decide) p (sat_cons (step2408 p h) (sat_cons (step1722 p h) (sat_cons (step1634 p h) (sat_cons (step1635 p h) (sat_cons (step1716 p h) (sat_cons (step1626 p h) (sat_cons (step2511 p h) (sat_cons (step1616 p h) (sat_cons (step1647 p h) (sat_cons (step2484 p h) (sat_cons (step561 p h) (sat_nil p))))))))))))
def c2670 : List Lit := [(112, false), (1760, true), (91, true), (1745, false), (62, false), (1725, false), (487, true)]
theorem step2670 (p : Nat → Bool) (h : Constraints p) : clause p c2670 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1252, c1234, c1231, c1230, c1289, c1284, c1281, c1272, c1266, c2655, c2652, c2649] c2670 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step2655 p h) (sat_cons (step2652 p h) (sat_cons (step2649 p h) (sat_nil p))))))))))))))
def c2671 : List Lit := [(1750, true), (74, true), (62, false), (475, true)]
theorem step2671 (p : Nat → Bool) (h : Constraints p) : clause p c2671 = true :=
  Snake9.LocalRup.prove_clause [c1272, c1266, c1270, c1267, c2152, c2649, c1797, c947, c896] c2671 (by decide) p (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1270 p h) (sat_cons (step1267 p h) (sat_cons (step2152 p h) (sat_cons (step2649 p h) (sat_cons (step1797 p h) (sat_cons (step947 p h) (sat_cons (step896 p h) (sat_nil p))))))))))
def c2672 : List Lit := [(1665, true), (1655, false), (1660, false), (73, true), (75, false), (62, false), (395, true)]
theorem step2672 (p : Nat → Bool) (h : Constraints p) : clause p c2672 = true :=
  Snake9.LocalRup.prove_clause [c1195, c1192, c1180, c1177, c1197, c1630, c2541, c1634, c1624, c1609, c1619, c1606, c1607, c559, c624, c2070] c2672 (by decide) p (sat_cons (step1195 p h) (sat_cons (step1192 p h) (sat_cons (step1180 p h) (sat_cons (step1177 p h) (sat_cons (step1197 p h) (sat_cons (step1630 p h) (sat_cons (step2541 p h) (sat_cons (step1634 p h) (sat_cons (step1624 p h) (sat_cons (step1609 p h) (sat_cons (step1619 p h) (sat_cons (step1606 p h) (sat_cons (step1607 p h) (sat_cons (step559 p h) (sat_cons (step624 p h) (sat_cons (step2070 p h) (sat_nil p)))))))))))))))))
def c2673 : List Lit := [(1760, true), (73, true), (69, true), (1651, true), (1662, true), (1750, false), (91, true), (62, false), (1725, false), (487, true)]
theorem step2673 (p : Nat → Bool) (h : Constraints p) : clause p c2673 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1252, c1234, c1231, c1230, c1289, c1286, c1262, c1260, c1257, c2641, c1852, c2643, c905, c894, c2639] c2673 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1289 p h) (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1260 p h) (sat_cons (step1257 p h) (sat_cons (step2641 p h) (sat_cons (step1852 p h) (sat_cons (step2643 p h) (sat_cons (step905 p h) (sat_cons (step894 p h) (sat_cons (step2639 p h) (sat_nil p)))))))))))))))))
def c2674 : List Lit := [(1665, true), (73, true), (69, true), (1660, false), (62, false), (1657, false), (57, false), (188, true)]
theorem step2674 (p : Nat → Bool) (h : Constraints p) : clause p c2674 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1630, c1634, c1626, c1624, c1609, c1616, c1619, c1606, c1607, c2646, c424, c624, c539] c2674 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1630 p h) (sat_cons (step1634 p h) (sat_cons (step1626 p h) (sat_cons (step1624 p h) (sat_cons (step1609 p h) (sat_cons (step1616 p h) (sat_cons (step1619 p h) (sat_cons (step1606 p h) (sat_cons (step1607 p h) (sat_cons (step2646 p h) (sat_cons (step424 p h) (sat_cons (step624 p h) (sat_cons (step539 p h) (sat_nil p)))))))))))))))
def c2675 : List Lit := [(1750, true), (1760, true), (1701, true), (1660, false), (74, false), (91, true), (75, true), (62, false), (487, true)]
theorem step2675 (p : Nat → Bool) (h : Constraints p) : clause p c2675 = true :=
  Snake9.LocalRup.prove_clause [c1664, c1291, c1252, c1234, c1231, c1230, c1289, c1286, c1262, c1260, c1257, c1284, c1281, c1272, c1266, c2152, c2649, c1797, c2655, c711, c905, c1649, c2643, c2576, c1610, c1724, c1639] c2675 (by decide) p (sat_cons (step1664 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1289 p h) (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1260 p h) (sat_cons (step1257 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step2152 p h) (sat_cons (step2649 p h) (sat_cons (step1797 p h) (sat_cons (step2655 p h) (sat_cons (step711 p h) (sat_cons (step905 p h) (sat_cons (step1649 p h) (sat_cons (step2643 p h) (sat_cons (step2576 p h) (sat_cons (step1610 p h) (sat_cons (step1724 p h) (sat_cons (step1639 p h) (sat_nil p))))))))))))))))))))))))))))
def c2676 : List Lit := [(1750, true), (1651, true), (74, false), (62, false), (485, true)]
theorem step2676 (p : Nat → Bool) (h : Constraints p) : clause p c2676 = true :=
  Snake9.LocalRup.prove_clause [c1286, c1262, c1260, c1257, c1284, c1281, c1272, c1266, c2152, c2649, c1797, c1996, c2643, c905] c2676 (by decide) p (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1260 p h) (sat_cons (step1257 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step2152 p h) (sat_cons (step2649 p h) (sat_cons (step1797 p h) (sat_cons (step1996 p h) (sat_cons (step2643 p h) (sat_cons (step905 p h) (sat_nil p)))))))))))))))
def c2677 : List Lit := [(1537, true), (23, false), (153, true)]
theorem step2677 (p : Nat → Bool) (h : Constraints p) : clause p c2677 = true :=
  Snake9.LocalRup.prove_clause [c1359, c1361, c1356, c1353, c174, c2194] c2677 (by decide) p (sat_cons (step1359 p h) (sat_cons (step1361 p h) (sat_cons (step1356 p h) (sat_cons (step1353 p h) (sat_cons (step174 p h) (sat_cons (step2194 p h) (sat_nil p)))))))
def c2678 : List Lit := [(1750, true), (74, true), (1745, false), (75, false), (475, true)]
theorem step2678 (p : Nat → Bool) (h : Constraints p) : clause p c2678 = true :=
  Snake9.LocalRup.prove_clause [c1272, c1266, c1270, c1268, c1267, c2649, c2660, c946, c948] c2678 (by decide) p (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1270 p h) (sat_cons (step1268 p h) (sat_cons (step1267 p h) (sat_cons (step2649 p h) (sat_cons (step2660 p h) (sat_cons (step946 p h) (sat_cons (step948 p h) (sat_nil p))))))))))
def c2679 : List Lit := [(57, false), (1660, true), (60, false), (22, false)]
theorem step2679 (p : Nat → Bool) (h : Constraints p) : clause p c2679 = true :=
  Snake9.LocalRup.prove_clause [c438, c439, c1615, c1617, c1623] c2679 (by decide) p (sat_cons (step438 p h) (sat_cons (step439 p h) (sat_cons (step1615 p h) (sat_cons (step1617 p h) (sat_cons (step1623 p h) (sat_nil p))))))
def c2680 : List Lit := [(69, true), (1660, true), (60, false), (22, false)]
theorem step2680 (p : Nat → Bool) (h : Constraints p) : clause p c2680 = true :=
  Snake9.LocalRup.prove_clause [c1625, c1614, c1616, c1623, c444, c1617] c2680 (by decide) p (sat_cons (step1625 p h) (sat_cons (step1614 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step444 p h) (sat_cons (step1617 p h) (sat_nil p)))))))
def c2681 : List Lit := [(1667, false), (1727, false), (1784, true), (74, false), (75, true), (32, false), (241, true)]
theorem step2681 (p : Nat → Bool) (h : Constraints p) : clause p c2681 = true :=
  Snake9.LocalRup.prove_clause [c2556, c1913, c1648, c2145, c1731, c1730, c2161, c1906, c1649, c1858, c695, c2649] c2681 (by decide) p (sat_cons (step2556 p h) (sat_cons (step1913 p h) (sat_cons (step1648 p h) (sat_cons (step2145 p h) (sat_cons (step1731 p h) (sat_cons (step1730 p h) (sat_cons (step2161 p h) (sat_cons (step1906 p h) (sat_cons (step1649 p h) (sat_cons (step1858 p h) (sat_cons (step695 p h) (sat_cons (step2649 p h) (sat_nil p)))))))))))))
def c2682 : List Lit := [(73, false), (60, true), (75, false), (49, true), (197, true)]
theorem step2682 (p : Nat → Bool) (h : Constraints p) : clause p c2682 = true :=
  Snake9.LocalRup.prove_clause [c680, c679, c2003] c2682 (by decide) p (sat_cons (step680 p h) (sat_cons (step679 p h) (sat_cons (step2003 p h) (sat_nil p))))
def c2683 : List Lit := [(74, true), (1660, true), (75, false), (49, true), (393, true)]
theorem step2683 (p : Nat → Bool) (h : Constraints p) : clause p c2683 = true :=
  Snake9.LocalRup.prove_clause [c1625, c1192, c1180, c1177, c1190, c1188, c1182, c2486, c2528, c1614, c1616, c1623, c754, c1618, c678, c657] c2683 (by decide) p (sat_cons (step1625 p h) (sat_cons (step1192 p h) (sat_cons (step1180 p h) (sat_cons (step1177 p h) (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1182 p h) (sat_cons (step2486 p h) (sat_cons (step2528 p h) (sat_cons (step1614 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step754 p h) (sat_cons (step1618 p h) (sat_cons (step678 p h) (sat_cons (step657 p h) (sat_nil p)))))))))))))))))
def c2684 : List Lit := [(69, true), (57, false), (1660, true), (60, false)]
theorem step2684 (p : Nat → Bool) (h : Constraints p) : clause p c2684 = true :=
  Snake9.LocalRup.prove_clause [c1625, c1614, c1616, c1623, c460, c1617] c2684 (by decide) p (sat_cons (step1625 p h) (sat_cons (step1614 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step460 p h) (sat_cons (step1617 p h) (sat_nil p)))))))
def c2685 : List Lit := [(69, true), (1660, true), (75, false), (49, true), (197, true)]
theorem step2685 (p : Nat → Bool) (h : Constraints p) : clause p c2685 = true :=
  Snake9.LocalRup.prove_clause [c1625, c1614, c1616, c1623, c1617, c1618, c754, c657, c678] c2685 (by decide) p (sat_cons (step1625 p h) (sat_cons (step1614 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step1617 p h) (sat_cons (step1618 p h) (sat_cons (step754 p h) (sat_cons (step657 p h) (sat_cons (step678 p h) (sat_nil p))))))))))
def c2686 : List Lit := [(1750, true), (75, false), (483, true)]
theorem step2686 (p : Nat → Bool) (h : Constraints p) : clause p c2686 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1277, c1274, c2627, c1281, c1272, c1266, c1270, c1268, c2649, c2660, c1828, c2678, c2005, c956, c958, c1803, c2010, c1800, c1801, c926, c967, c2307] c2686 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1277 p h) (sat_cons (step1274 p h) (sat_cons (step2627 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1270 p h) (sat_cons (step1268 p h) (sat_cons (step2649 p h) (sat_cons (step2660 p h) (sat_cons (step1828 p h) (sat_cons (step2678 p h) (sat_cons (step2005 p h) (sat_cons (step956 p h) (sat_cons (step958 p h) (sat_cons (step1803 p h) (sat_cons (step2010 p h) (sat_cons (step1800 p h) (sat_cons (step1801 p h) (sat_cons (step926 p h) (sat_cons (step967 p h) (sat_cons (step2307 p h) (sat_nil p))))))))))))))))))))))))
def c2687 : List Lit := [(1759, true), (74, true), (91, true), (1725, false), (487, true)]
theorem step2687 (p : Nat → Bool) (h : Constraints p) : clause p c2687 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1252, c1234, c1231, c1230, c1289, c1284, c1281, c1272, c1266, c1270, c1267, c2555, c1846, c2639, c1831, c2649, c2090, c947, c897] c2687 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1270 p h) (sat_cons (step1267 p h) (sat_cons (step2555 p h) (sat_cons (step1846 p h) (sat_cons (step2639 p h) (sat_cons (step1831 p h) (sat_cons (step2649 p h) (sat_cons (step2090 p h) (sat_cons (step947 p h) (sat_cons (step897 p h) (sat_nil p)))))))))))))))))))))
def c2688 : List Lit := [(1750, true), (1666, true), (32, false), (74, false), (62, true), (63, false), (24, false), (241, true)]
theorem step2688 (p : Nat → Bool) (h : Constraints p) : clause p c2688 = true :=
  Snake9.LocalRup.prove_clause [c2152, c2649, c1797, c692, c2415, c1614, c1613, c1622, c1643] c2688 (by decide) p (sat_cons (step2152 p h) (sat_cons (step2649 p h) (sat_cons (step1797 p h) (sat_cons (step692 p h) (sat_cons (step2415 p h) (sat_cons (step1614 p h) (sat_cons (step1613 p h) (sat_cons (step1622 p h) (sat_cons (step1643 p h) (sat_nil p))))))))))
def c2689 : List Lit := [(69, true), (78, false), (73, false), (1700, true), (1656, true), (1680, false), (75, true), (1653, false)]
theorem step2689 (p : Nat → Bool) (h : Constraints p) : clause p c2689 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1616, c1622, c755, c1638, c1649, c1717, c2576] c2689 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1616 p h) (sat_cons (step1622 p h) (sat_cons (step755 p h) (sat_cons (step1638 p h) (sat_cons (step1649 p h) (sat_cons (step1717 p h) (sat_cons (step2576 p h) (sat_nil p)))))))))
def c2690 : List Lit := [(1759, true), (1660, true), (49, true), (487, true)]
theorem step2690 (p : Nat → Bool) (h : Constraints p) : clause p c2690 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1250, c1248, c1242, c1241, c2629, c1289, c1286, c1262, c1259, c1258, c1284, c1281, c1270, c1268, c2452, c1846, c1817, c1819, c2397, c2153, c1831, c2152, c1814, c1812, c937, c1618, c1804, c1798, c928, c1623, c1802, c1615, c915, c907] c2690 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1242 p h) (sat_cons (step1241 p h) (sat_cons (step2629 p h) (sat_cons (step1289 p h) (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1259 p h) (sat_cons (step1258 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1270 p h) (sat_cons (step1268 p h) (sat_cons (step2452 p h) (sat_cons (step1846 p h) (sat_cons (step1817 p h) (sat_cons (step1819 p h) (sat_cons (step2397 p h) (sat_cons (step2153 p h) (sat_cons (step1831 p h) (sat_cons (step2152 p h) (sat_cons (step1814 p h) (sat_cons (step1812 p h) (sat_cons (step937 p h) (sat_cons (step1618 p h) (sat_cons (step1804 p h) (sat_cons (step1798 p h) (sat_cons (step928 p h) (sat_cons (step1623 p h) (sat_cons (step1802 p h) (sat_cons (step1615 p h) (sat_cons (step915 p h) (sat_cons (step907 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c2691 : List Lit := [(22, false), (74, true), (60, false), (1660, true), (193, true)]
theorem step2691 (p : Nat → Bool) (h : Constraints p) : clause p c2691 = true :=
  Snake9.LocalRup.prove_clause [c2486, c2680, c444, c640, c654, c1615, c1618, c1623] c2691 (by decide) p (sat_cons (step2486 p h) (sat_cons (step2680 p h) (sat_cons (step444 p h) (sat_cons (step640 p h) (sat_cons (step654 p h) (sat_cons (step1615 p h) (sat_cons (step1618 p h) (sat_cons (step1623 p h) (sat_nil p)))))))))
def c2692 : List Lit := [(67, false), (1617, true), (1564, false), (1576, false), (73, false), (60, false), (1592, false)]
theorem step2692 (p : Nat → Bool) (h : Constraints p) : clause p c2692 = true :=
  Snake9.LocalRup.prove_clause [c2550, c454, c1482, c1416, c1495, c1422, c1535, c1451] c2692 (by decide) p (sat_cons (step2550 p h) (sat_cons (step454 p h) (sat_cons (step1482 p h) (sat_cons (step1416 p h) (sat_cons (step1495 p h) (sat_cons (step1422 p h) (sat_cons (step1535 p h) (sat_cons (step1451 p h) (sat_nil p)))))))))
def c2693 : List Lit := [(67, true), (74, true), (1660, true), (193, true)]
theorem step2693 (p : Nat → Bool) (h : Constraints p) : clause p c2693 = true :=
  Snake9.LocalRup.prove_clause [c2486, c1625, c1615, c1616, c1623, c640, c654, c1618] c2693 (by decide) p (sat_cons (step2486 p h) (sat_cons (step1625 p h) (sat_cons (step1615 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step640 p h) (sat_cons (step654 p h) (sat_cons (step1618 p h) (sat_nil p)))))))))
def c2694 : List Lit := [(81, true), (1692, true), (1670, false), (91, true), (415, true), (79, true)]
theorem step2694 (p : Nat → Bool) (h : Constraints p) : clause p c2694 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1206, c1209, c1208, c1207, c2276, c1652, c782, c1657, c2271, c1693, c779, c2544, c2274, c788] c2694 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1206 p h) (sat_cons (step1209 p h) (sat_cons (step1208 p h) (sat_cons (step1207 p h) (sat_cons (step2276 p h) (sat_cons (step1652 p h) (sat_cons (step782 p h) (sat_cons (step1657 p h) (sat_cons (step2271 p h) (sat_cons (step1693 p h) (sat_cons (step779 p h) (sat_cons (step2544 p h) (sat_cons (step2274 p h) (sat_cons (step788 p h) (sat_nil p))))))))))))))))
def c2695 : List Lit := [(1760, true), (62, false), (1745, false), (63, true), (91, true), (1725, false), (487, true)]
theorem step2695 (p : Nat → Bool) (h : Constraints p) : clause p c2695 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1286, c1262, c1260, c1257, c2645, c2670, c905] c2695 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1260 p h) (sat_cons (step1257 p h) (sat_cons (step2645 p h) (sat_cons (step2670 p h) (sat_cons (step905 p h) (sat_nil p)))))))))
def c2696 : List Lit := [(22, false), (74, true), (1660, true), (20, true), (26, true), (275, false)]
theorem step2696 (p : Nat → Bool) (h : Constraints p) : clause p c2696 = true :=
  Snake9.LocalRup.prove_clause [c1090, c1162, c2361, c1296, c1222, c1195, c1192, c1180, c1177, c2324, c1086, c1069, c1068, c1067, c115, c2691] c2696 (by decide) p (sat_cons (step1090 p h) (sat_cons (step1162 p h) (sat_cons (step2361 p h) (sat_cons (step1296 p h) (sat_cons (step1222 p h) (sat_cons (step1195 p h) (sat_cons (step1192 p h) (sat_cons (step1180 p h) (sat_cons (step1177 p h) (sat_cons (step2324 p h) (sat_cons (step1086 p h) (sat_cons (step1069 p h) (sat_cons (step1068 p h) (sat_cons (step1067 p h) (sat_cons (step115 p h) (sat_cons (step2691 p h) (sat_nil p)))))))))))))))))
def c2697 : List Lit := [(76, false), (65, true), (67, false), (73, false), (74, true), (200, true)]
theorem step2697 (p : Nat → Bool) (h : Constraints p) : clause p c2697 = true :=
  Snake9.LocalRup.prove_clause [c748, c755] c2697 (by decide) p (sat_cons (step748 p h) (sat_cons (step755 p h) (sat_nil p)))
def c2698 : List Lit := [(67, true), (73, true), (1661, true), (75, false), (74, true), (193, true)]
theorem step2698 (p : Nat → Bool) (h : Constraints p) : clause p c2698 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1626, c1615, c1616, c1624, c640, c1619, c655] c2698 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1626 p h) (sat_cons (step1615 p h) (sat_cons (step1616 p h) (sat_cons (step1624 p h) (sat_cons (step640 p h) (sat_cons (step1619 p h) (sat_cons (step655 p h) (sat_nil p)))))))))
def c2699 : List Lit := [(1760, true), (63, true), (75, false), (62, true), (91, true), (1725, false), (487, true)]
theorem step2699 (p : Nat → Bool) (h : Constraints p) : clause p c2699 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1284, c2686, c1279, c1277, c1274, c2627, c1291, c1252, c1234, c1231, c1230, c1286, c1262, c1260, c1257, c1852, c2645, c2639, c905, c2389, c897] c2699 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step2686 p h) (sat_cons (step1279 p h) (sat_cons (step1277 p h) (sat_cons (step1274 p h) (sat_cons (step2627 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1260 p h) (sat_cons (step1257 p h) (sat_cons (step1852 p h) (sat_cons (step2645 p h) (sat_cons (step2639 p h) (sat_cons (step905 p h) (sat_cons (step2389 p h) (sat_cons (step897 p h) (sat_nil p)))))))))))))))))))))))
def c2700 : List Lit := [(25, true), (1539, true), (22, true), (24, true), (18, true), (153, true)]
theorem step2700 (p : Nat → Bool) (h : Constraints p) : clause p c2700 = true :=
  Snake9.LocalRup.prove_clause [c1355, c2190, c1365, c174, c1356] c2700 (by decide) p (sat_cons (step1355 p h) (sat_cons (step2190 p h) (sat_cons (step1365 p h) (sat_cons (step174 p h) (sat_cons (step1356 p h) (sat_nil p))))))
def c2701 : List Lit := [(111, false), (60, false), (22, false), (1599, true)]
theorem step2701 (p : Nat → Bool) (h : Constraints p) : clause p c2701 = true :=
  Snake9.LocalRup.prove_clause [c440, c443, c1480] c2701 (by decide) p (sat_cons (step440 p h) (sat_cons (step443 p h) (sat_cons (step1480 p h) (sat_nil p))))
def c2702 : List Lit := [(67, false), (1670, true), (62, false), (74, true), (200, true)]
theorem step2702 (p : Nat → Bool) (h : Constraints p) : clause p c2702 = true :=
  Snake9.LocalRup.prove_clause [c1647, c2484, c561] c2702 (by decide) p (sat_cons (step1647 p h) (sat_cons (step2484 p h) (sat_cons (step561 p h) (sat_nil p))))
def c2703 : List Lit := [(39, false), (1599, true), (60, false), (22, false)]
theorem step2703 (p : Nat → Bool) (h : Constraints p) : clause p c2703 = true :=
  Snake9.LocalRup.prove_clause [c433, c432, c1480] c2703 (by decide) p (sat_cons (step433 p h) (sat_cons (step432 p h) (sat_cons (step1480 p h) (sat_nil p))))
def c2704 : List Lit := [(1598, true), (60, false), (22, false)]
theorem step2704 (p : Nat → Bool) (h : Constraints p) : clause p c2704 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1479, c437] c2704 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step437 p h) (sat_nil p))))
def c2705 : List Lit := [(1759, true), (60, false), (22, false), (1602, true), (91, true), (1725, false), (487, true)]
theorem step2705 (p : Nat → Bool) (h : Constraints p) : clause p c2705 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1252, c1234, c1231, c1230, c1289, c1286, c1262, c1260, c1257, c1284, c1281, c1272, c1266, c2555, c1846, c2639, c1831, c2152, c2649, c2090, c1798, c897, c904, c2701, c877, c1485, c1475] c2705 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1289 p h) (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1260 p h) (sat_cons (step1257 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step2555 p h) (sat_cons (step1846 p h) (sat_cons (step2639 p h) (sat_cons (step1831 p h) (sat_cons (step2152 p h) (sat_cons (step2649 p h) (sat_cons (step2090 p h) (sat_cons (step1798 p h) (sat_cons (step897 p h) (sat_cons (step904 p h) (sat_cons (step2701 p h) (sat_cons (step877 p h) (sat_cons (step1485 p h) (sat_cons (step1475 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2706 : List Lit := [(73, false), (1601, true), (1576, false), (1617, true), (70, false), (1564, false), (75, false), (1660, true), (49, true), (1592, false), (197, true)]
theorem step2706 (p : Nat → Bool) (h : Constraints p) : clause p c2706 = true :=
  Snake9.LocalRup.prove_clause [c2685, c2682, c2692, c2567, c1615, c1484, c1623, c1475, c1618, c646] c2706 (by decide) p (sat_cons (step2685 p h) (sat_cons (step2682 p h) (sat_cons (step2692 p h) (sat_cons (step2567 p h) (sat_cons (step1615 p h) (sat_cons (step1484 p h) (sat_cons (step1623 p h) (sat_cons (step1475 p h) (sat_cons (step1618 p h) (sat_cons (step646 p h) (sat_nil p)))))))))))
def c2707 : List Lit := [(39, false), (60, false), (22, false), (1660, true)]
theorem step2707 (p : Nat → Bool) (h : Constraints p) : clause p c2707 = true :=
  Snake9.LocalRup.prove_clause [c435, c434, c1617, c1615, c1623] c2707 (by decide) p (sat_cons (step435 p h) (sat_cons (step434 p h) (sat_cons (step1617 p h) (sat_cons (step1615 p h) (sat_cons (step1623 p h) (sat_nil p))))))
def c2708 : List Lit := [(1709, true), (91, false), (218, true)]
theorem step2708 (p : Nat → Bool) (h : Constraints p) : clause p c2708 = true :=
  Snake9.LocalRup.prove_clause [c1750, c1751, c806, c817] c2708 (by decide) p (sat_cons (step1750 p h) (sat_cons (step1751 p h) (sat_cons (step806 p h) (sat_cons (step817 p h) (sat_nil p)))))
def c2709 : List Lit := [(81, true), (1689, true), (209, true), (211, true), (79, true)]
theorem step2709 (p : Nat → Bool) (h : Constraints p) : clause p c2709 = true :=
  Snake9.LocalRup.prove_clause [c2276, c1652, c782, c1654, c2271, c1686, c779, c1672, c1663] c2709 (by decide) p (sat_cons (step2276 p h) (sat_cons (step1652 p h) (sat_cons (step782 p h) (sat_cons (step1654 p h) (sat_cons (step2271 p h) (sat_cons (step1686 p h) (sat_cons (step779 p h) (sat_cons (step1672 p h) (sat_cons (step1663 p h) (sat_nil p))))))))))
def c2710 : List Lit := [(73, false), (1617, true), (1576, false), (60, false), (22, false), (75, false), (1592, false), (158, true)]
theorem step2710 (p : Nat → Bool) (h : Constraints p) : clause p c2710 = true :=
  Snake9.LocalRup.prove_clause [c442, c435, c439, c2101, c1480, c1451, c1482, c1535, c1495] c2710 (by decide) p (sat_cons (step442 p h) (sat_cons (step435 p h) (sat_cons (step439 p h) (sat_cons (step2101 p h) (sat_cons (step1480 p h) (sat_cons (step1451 p h) (sat_cons (step1482 p h) (sat_cons (step1535 p h) (sat_cons (step1495 p h) (sat_nil p))))))))))
def c2711 : List Lit := [(23, false), (21, false), (62, true), (24, true), (18, true)]
theorem step2711 (p : Nat → Bool) (h : Constraints p) : clause p c2711 = true :=
  Snake9.LocalRup.prove_clause [c2192, c2194] c2711 (by decide) p (sat_cons (step2192 p h) (sat_cons (step2194 p h) (sat_nil p)))
def c2712 : List Lit := [(81, true), (1691, true), (1670, false), (209, true), (211, true), (213, true), (79, true)]
theorem step2712 (p : Nat → Bool) (h : Constraints p) : clause p c2712 = true :=
  Snake9.LocalRup.prove_clause [c2276, c1652, c782, c1657, c2271, c1692, c779, c2274, c1663, c788, c1673, c1665] c2712 (by decide) p (sat_cons (step2276 p h) (sat_cons (step1652 p h) (sat_cons (step782 p h) (sat_cons (step1657 p h) (sat_cons (step2271 p h) (sat_cons (step1692 p h) (sat_cons (step779 p h) (sat_cons (step2274 p h) (sat_cons (step1663 p h) (sat_cons (step788 p h) (sat_cons (step1673 p h) (sat_cons (step1665 p h) (sat_nil p)))))))))))))
def c2713 : List Lit := [(1593, false), (60, true), (1615, true), (1576, false), (91, false), (49, true), (163, true)]
theorem step2713 (p : Nat → Bool) (h : Constraints p) : clause p c2713 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1519, c1498, c1499, c1526, c1481, c1446, c1479, c1419, c2647, c1416] c2713 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1519 p h) (sat_cons (step1498 p h) (sat_cons (step1499 p h) (sat_cons (step1526 p h) (sat_cons (step1481 p h) (sat_cons (step1446 p h) (sat_cons (step1479 p h) (sat_cons (step1419 p h) (sat_cons (step2647 p h) (sat_cons (step1416 p h) (sat_nil p))))))))))))
def c2714 : List Lit := [(32, true), (1577, false), (60, false), (22, false), (1618, true), (75, true), (1592, false), (158, true)]
theorem step2714 (p : Nat → Bool) (h : Constraints p) : clause p c2714 = true :=
  Snake9.LocalRup.prove_clause [c2704, c1481, c1494, c1549, c1457, c2074, c2393, c1452, c2703, c1543, c1482, c1495] c2714 (by decide) p (sat_cons (step2704 p h) (sat_cons (step1481 p h) (sat_cons (step1494 p h) (sat_cons (step1549 p h) (sat_cons (step1457 p h) (sat_cons (step2074 p h) (sat_cons (step2393 p h) (sat_cons (step1452 p h) (sat_cons (step2703 p h) (sat_cons (step1543 p h) (sat_cons (step1482 p h) (sat_cons (step1495 p h) (sat_nil p)))))))))))))
def c2715 : List Lit := [(89, true), (1691, true), (1671, false), (209, true), (211, true), (79, true)]
theorem step2715 (p : Nat → Bool) (h : Constraints p) : clause p c2715 = true :=
  Snake9.LocalRup.prove_clause [c2273, c1665, c778, c2424] c2715 (by decide) p (sat_cons (step2273 p h) (sat_cons (step1665 p h) (sat_cons (step778 p h) (sat_cons (step2424 p h) (sat_nil p)))))
end B112E089
