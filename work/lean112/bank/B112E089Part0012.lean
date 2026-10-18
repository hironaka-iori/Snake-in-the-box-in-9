import B112E089Part0011
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2780 : List Lit := [(1615, true), (1568, false), (1605, false), (1588, false), (50, true), (169, true)]
theorem step2780 (p : Nat → Bool) (h : Constraints p) : clause p c2780 = true :=
  Snake9.LocalRup.prove_clause [c1445, c1526, c1519, c1446, c1503, c2537, c1471, c1466] c2780 (by decide) p (sat_cons (step1445 p h) (sat_cons (step1526 p h) (sat_cons (step1519 p h) (sat_cons (step1446 p h) (sat_cons (step1503 p h) (sat_cons (step2537 p h) (sat_cons (step1471 p h) (sat_cons (step1466 p h) (sat_nil p)))))))))
def c2781 : List Lit := [(1727, true), (103, true), (455, true)]
theorem step2781 (p : Nat → Bool) (h : Constraints p) : clause p c2781 = true :=
  Snake9.LocalRup.prove_clause [c1764, c1772, c2293, c1250, c1248, c1242, c1240, c1252, c1236, c1227, c1780, c2731, c1788, c1758, c2095, c1750, c1751, c2093, c2456, c1768, c1766, c1776] c2781 (by decide) p (sat_cons (step1764 p h) (sat_cons (step1772 p h) (sat_cons (step2293 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1242 p h) (sat_cons (step1240 p h) (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1780 p h) (sat_cons (step2731 p h) (sat_cons (step1788 p h) (sat_cons (step1758 p h) (sat_cons (step2095 p h) (sat_cons (step1750 p h) (sat_cons (step1751 p h) (sat_cons (step2093 p h) (sat_cons (step2456 p h) (sat_cons (step1768 p h) (sat_cons (step1766 p h) (sat_cons (step1776 p h) (sat_nil p)))))))))))))))))))))))
def c2782 : List Lit := [(103, false), (1615, true), (1568, false), (49, false), (14, false), (169, true)]
theorem step2782 (p : Nat → Bool) (h : Constraints p) : clause p c2782 = true :=
  Snake9.LocalRup.prove_clause [c328, c330, c2104, c1461, c1498, c2780] c2782 (by decide) p (sat_cons (step328 p h) (sat_cons (step330 p h) (sat_cons (step2104 p h) (sat_cons (step1461 p h) (sat_cons (step1498 p h) (sat_cons (step2780 p h) (sat_nil p)))))))
def c2783 : List Lit := [(1727, false), (68, false), (27, false), (1660, false), (1783, true), (1750, false), (62, true), (63, false), (24, false), (241, true)]
theorem step2783 (p : Nat → Bool) (h : Constraints p) : clause p c2783 = true :=
  Snake9.LocalRup.prove_clause [c2636, c1612, c1639, c2375, c1891, c1859, c1858, c1898, c2376, c1644, c1613, c2415, c1797, c2116, c606, c604, c1608] c2783 (by decide) p (sat_cons (step2636 p h) (sat_cons (step1612 p h) (sat_cons (step1639 p h) (sat_cons (step2375 p h) (sat_cons (step1891 p h) (sat_cons (step1859 p h) (sat_cons (step1858 p h) (sat_cons (step1898 p h) (sat_cons (step2376 p h) (sat_cons (step1644 p h) (sat_cons (step1613 p h) (sat_cons (step2415 p h) (sat_cons (step1797 p h) (sat_cons (step2116 p h) (sat_cons (step606 p h) (sat_cons (step604 p h) (sat_cons (step1608 p h) (sat_nil p))))))))))))))))))
def c2784 : List Lit := [(113, false), (1568, false), (1593, false), (1616, true), (63, false), (24, false)]
theorem step2784 (p : Nat → Bool) (h : Constraints p) : clause p c2784 = true :=
  Snake9.LocalRup.prove_clause [c504, c500, c1475, c1428, c1483, c1435, c1499, c1446, c1527] c2784 (by decide) p (sat_cons (step504 p h) (sat_cons (step500 p h) (sat_cons (step1475 p h) (sat_cons (step1428 p h) (sat_cons (step1483 p h) (sat_cons (step1435 p h) (sat_cons (step1499 p h) (sat_cons (step1446 p h) (sat_cons (step1527 p h) (sat_nil p))))))))))
def c2785 : List Lit := [(113, false), (1568, false), (1615, true), (63, false), (24, false), (1592, false)]
theorem step2785 (p : Nat → Bool) (h : Constraints p) : clause p c2785 = true :=
  Snake9.LocalRup.prove_clause [c504, c500, c1475, c1428, c1483, c1435, c1494, c1446, c1526] c2785 (by decide) p (sat_cons (step504 p h) (sat_cons (step500 p h) (sat_cons (step1475 p h) (sat_cons (step1428 p h) (sat_cons (step1483 p h) (sat_cons (step1435 p h) (sat_cons (step1494 p h) (sat_cons (step1446 p h) (sat_cons (step1526 p h) (sat_nil p))))))))))
def c2786 : List Lit := [(1750, true), (1700, true), (74, false), (75, true), (32, false), (62, true), (63, false), (24, false), (241, true)]
theorem step2786 (p : Nat → Bool) (h : Constraints p) : clause p c2786 = true :=
  Snake9.LocalRup.prove_clause [c2649, c2688, c695, c1723, c1649, c2161] c2786 (by decide) p (sat_cons (step2649 p h) (sat_cons (step2688 p h) (sat_cons (step695 p h) (sat_cons (step1723 p h) (sat_cons (step1649 p h) (sat_cons (step2161 p h) (sat_nil p)))))))
def c2787 : List Lit := [(1600, false), (1617, true), (1588, false), (1569, false), (1593, false), (50, true), (169, true)]
theorem step2787 (p : Nat → Bool) (h : Constraints p) : clause p c2787 = true :=
  Snake9.LocalRup.prove_clause [c2540, c1499] c2787 (by decide) p (sat_cons (step2540 p h) (sat_cons (step1499 p h) (sat_nil p)))
def c2788 : List Lit := [(1783, true), (1727, false), (1760, false), (1660, false), (1687, false), (62, true), (63, false), (24, false)]
theorem step2788 (p : Nat → Bool) (h : Constraints p) : clause p c2788 = true :=
  Snake9.LocalRup.prove_clause [c2636, c1612, c1639, c1722, c1898, c1905, c1858, c1730, c2152, c1644, c1797, c1613, c2415] c2788 (by decide) p (sat_cons (step2636 p h) (sat_cons (step1612 p h) (sat_cons (step1639 p h) (sat_cons (step1722 p h) (sat_cons (step1898 p h) (sat_cons (step1905 p h) (sat_cons (step1858 p h) (sat_cons (step1730 p h) (sat_cons (step2152 p h) (sat_cons (step1644 p h) (sat_cons (step1797 p h) (sat_cons (step1613 p h) (sat_cons (step2415 p h) (sat_nil p))))))))))))))
def c2789 : List Lit := [(1593, false), (1568, false), (1615, true), (63, false), (24, false)]
theorem step2789 (p : Nat → Bool) (h : Constraints p) : clause p c2789 = true :=
  Snake9.LocalRup.prove_clause [c1445, c1519, c1498, c1499, c1526, c1483, c1446, c1475, c1435, c496, c1428] c2789 (by decide) p (sat_cons (step1445 p h) (sat_cons (step1519 p h) (sat_cons (step1498 p h) (sat_cons (step1499 p h) (sat_cons (step1526 p h) (sat_cons (step1483 p h) (sat_cons (step1446 p h) (sat_cons (step1475 p h) (sat_cons (step1435 p h) (sat_cons (step496 p h) (sat_cons (step1428 p h) (sat_nil p))))))))))))
def c2790 : List Lit := [(1614, true), (51, false), (1568, false), (1592, false)]
theorem step2790 (p : Nat → Bool) (h : Constraints p) : clause p c2790 = true :=
  Snake9.LocalRup.prove_clause [c1445, c1493, c1525, c1518, c1446, c1494, c2157, c1483, c1476] c2790 (by decide) p (sat_cons (step1445 p h) (sat_cons (step1493 p h) (sat_cons (step1525 p h) (sat_cons (step1518 p h) (sat_cons (step1446 p h) (sat_cons (step1494 p h) (sat_cons (step2157 p h) (sat_cons (step1483 p h) (sat_cons (step1476 p h) (sat_nil p))))))))))
def c2791 : List Lit := [(1544, true), (67, false), (26, false), (18, true), (1533, false), (1525, false)]
theorem step2791 (p : Nat → Bool) (h : Constraints p) : clause p c2791 = true :=
  Snake9.LocalRup.prove_clause [c1343, c1348, c1361, c1381, c1378, c1349, c1362, c1344, c1357, c153] c2791 (by decide) p (sat_cons (step1343 p h) (sat_cons (step1348 p h) (sat_cons (step1361 p h) (sat_cons (step1381 p h) (sat_cons (step1378 p h) (sat_cons (step1349 p h) (sat_cons (step1362 p h) (sat_cons (step1344 p h) (sat_cons (step1357 p h) (sat_cons (step153 p h) (sat_nil p)))))))))))
def c2792 : List Lit := [(1616, true), (50, true), (47, true), (1605, false), (75, false), (1569, false), (175, true)]
theorem step2792 (p : Nat → Bool) (h : Constraints p) : clause p c2792 = true :=
  Snake9.LocalRup.prove_clause [c2114, c1534, c1431, c1451, c1433] c2792 (by decide) p (sat_cons (step2114 p h) (sat_cons (step1534 p h) (sat_cons (step1431 p h) (sat_cons (step1451 p h) (sat_cons (step1433 p h) (sat_nil p))))))
def c2793 : List Lit := [(1666, false), (1781, true), (1750, false), (439, true)]
theorem step2793 (p : Nat → Bool) (h : Constraints p) : clause p c2793 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1227, c2375, c1889, c1852, c2575, c2724, c2745, c1664, c1846, c2408, c1896, c1722] c2793 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step2375 p h) (sat_cons (step1889 p h) (sat_cons (step1852 p h) (sat_cons (step2575 p h) (sat_cons (step2724 p h) (sat_cons (step2745 p h) (sat_cons (step1664 p h) (sat_cons (step1846 p h) (sat_cons (step2408 p h) (sat_cons (step1896 p h) (sat_cons (step1722 p h) (sat_nil p))))))))))))))
def c2794 : List Lit := [(1782, true), (1665, false), (69, false), (1727, false), (1760, false), (75, true), (74, false), (241, true)]
theorem step2794 (p : Nat → Bool) (h : Constraints p) : clause p c2794 = true :=
  Snake9.LocalRup.prove_clause [c1648, c2145, c1715, c1897, c1890, c1716, c1858, c2161, c2649, c1649, c714] c2794 (by decide) p (sat_cons (step1648 p h) (sat_cons (step2145 p h) (sat_cons (step1715 p h) (sat_cons (step1897 p h) (sat_cons (step1890 p h) (sat_cons (step1716 p h) (sat_cons (step1858 p h) (sat_cons (step2161 p h) (sat_cons (step2649 p h) (sat_cons (step1649 p h) (sat_cons (step714 p h) (sat_nil p))))))))))))
def c2795 : List Lit := [(32, false), (120, false), (1653, false), (1699, true), (75, true), (74, false)]
theorem step2795 (p : Nat → Bool) (h : Constraints p) : clause p c2795 = true :=
  Snake9.LocalRup.prove_clause [c692, c695, c1614, c1649, c1622, c2161, c1638, c1716] c2795 (by decide) p (sat_cons (step692 p h) (sat_cons (step695 p h) (sat_cons (step1614 p h) (sat_cons (step1649 p h) (sat_cons (step1622 p h) (sat_cons (step2161 p h) (sat_cons (step1638 p h) (sat_cons (step1716 p h) (sat_nil p)))))))))
def c2796 : List Lit := [(67, true), (1653, false), (1782, true), (1727, false), (1760, false), (75, true), (1656, true), (74, false), (241, true)]
theorem step2796 (p : Nat → Bool) (h : Constraints p) : clause p c2796 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1616, c1622, c2794, c1638] c2796 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1616 p h) (sat_cons (step1622 p h) (sat_cons (step2794 p h) (sat_cons (step1638 p h) (sat_nil p))))))
def c2797 : List Lit := [(120, false), (1699, true), (1653, false), (51, false), (75, true), (74, false)]
theorem step2797 (p : Nat → Bool) (h : Constraints p) : clause p c2797 = true :=
  Snake9.LocalRup.prove_clause [c702, c705, c1614, c1649, c1622, c2161, c1638, c1716] c2797 (by decide) p (sat_cons (step702 p h) (sat_cons (step705 p h) (sat_cons (step1614 p h) (sat_cons (step1649 p h) (sat_cons (step1622 p h) (sat_cons (step2161 p h) (sat_cons (step1638 p h) (sat_cons (step1716 p h) (sat_nil p)))))))))
def c2798 : List Lit := [(39, false), (1593, true), (49, false), (14, false)]
theorem step2798 (p : Nat → Bool) (h : Constraints p) : clause p c2798 = true :=
  Snake9.LocalRup.prove_clause [c323, c322, c1465, c1461, c1470] c2798 (by decide) p (sat_cons (step323 p h) (sat_cons (step322 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step1470 p h) (sat_nil p))))))
def c2799 : List Lit := [(32, false), (1698, true), (74, false), (75, true), (1652, false), (62, false)]
theorem step2799 (p : Nat → Bool) (h : Constraints p) : clause p c2799 = true :=
  Snake9.LocalRup.prove_clause [c688, c686, c1649, c1614, c2161, c1622, c1709, c1633] c2799 (by decide) p (sat_cons (step688 p h) (sat_cons (step686 p h) (sat_cons (step1649 p h) (sat_cons (step1614 p h) (sat_cons (step2161 p h) (sat_cons (step1622 p h) (sat_cons (step1709 p h) (sat_cons (step1633 p h) (sat_nil p)))))))))
def c2800 : List Lit := [(1760, true), (62, false), (75, false), (63, true), (487, true)]
theorem step2800 (p : Nat → Bool) (h : Constraints p) : clause p c2800 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1284, c2686, c1279, c1277, c1274, c2627, c1291, c1252, c1236, c1227, c1852, c2575, c2724, c2745, c2695] c2800 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step2686 p h) (sat_cons (step1279 p h) (sat_cons (step1277 p h) (sat_cons (step1274 p h) (sat_cons (step2627 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1852 p h) (sat_cons (step2575 p h) (sat_cons (step2724 p h) (sat_cons (step2745 p h) (sat_cons (step2695 p h) (sat_nil p)))))))))))))))))
def c2801 : List Lit := [(1696, true), (74, false), (1652, false), (75, false)]
theorem step2801 (p : Nat → Bool) (h : Constraints p) : clause p c2801 = true :=
  Snake9.LocalRup.prove_clause [c1632, c2373, c1701, c1633, c2145, c1622, c1647, c1614, c712] c2801 (by decide) p (sat_cons (step1632 p h) (sat_cons (step2373 p h) (sat_cons (step1701 p h) (sat_cons (step1633 p h) (sat_cons (step2145 p h) (sat_cons (step1622 p h) (sat_cons (step1647 p h) (sat_cons (step1614 p h) (sat_cons (step712 p h) (sat_nil p))))))))))
def c2802 : List Lit := [(69, true), (1666, true), (1599, true), (73, true), (64, false), (66, false), (62, true), (1660, false), (63, true), (188, true)]
theorem step2802 (p : Nat → Bool) (h : Constraints p) : clause p c2802 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1611, c1635, c1626, c1614, c2661, c1624, c1480, c1616, c1619, c621, c425, c539] c2802 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1611 p h) (sat_cons (step1635 p h) (sat_cons (step1626 p h) (sat_cons (step1614 p h) (sat_cons (step2661 p h) (sat_cons (step1624 p h) (sat_cons (step1480 p h) (sat_cons (step1616 p h) (sat_cons (step1619 p h) (sat_cons (step621 p h) (sat_cons (step425 p h) (sat_cons (step539 p h) (sat_nil p))))))))))))))
def c2803 : List Lit := [(1576, true), (1650, true), (188, true)]
theorem step2803 (p : Nat → Bool) (h : Constraints p) : clause p c2803 = true :=
  Snake9.LocalRup.prove_clause [c1433, c2585, c1430, c2147] c2803 (by decide) p (sat_cons (step1433 p h) (sat_cons (step2585 p h) (sat_cons (step1430 p h) (sat_cons (step2147 p h) (sat_nil p)))))
def c2804 : List Lit := [(1666, false), (1782, true), (1750, false), (74, true), (1670, false), (487, true)]
theorem step2804 (p : Nat → Bool) (h : Constraints p) : clause p c2804 = true :=
  Snake9.LocalRup.prove_clause [c2145, c1291, c1252, c1236, c1227, c1722, c1897, c1852, c2575, c2724, c2745, c1664, c2687, c2511, c1904, c1723] c2804 (by decide) p (sat_cons (step2145 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1722 p h) (sat_cons (step1897 p h) (sat_cons (step1852 p h) (sat_cons (step2575 p h) (sat_cons (step2724 p h) (sat_cons (step2745 p h) (sat_cons (step1664 p h) (sat_cons (step2687 p h) (sat_cons (step2511 p h) (sat_cons (step1904 p h) (sat_cons (step1723 p h) (sat_nil p)))))))))))))))))
def c2805 : List Lit := [(1539, true), (67, false), (34, false), (24, true), (18, true), (25, true), (299, true)]
theorem step2805 (p : Nat → Bool) (h : Constraints p) : clause p c2805 = true :=
  Snake9.LocalRup.prove_clause [c1355, c1077, c1076, c2700, c1365, c1357, c2779, c153] c2805 (by decide) p (sat_cons (step1355 p h) (sat_cons (step1077 p h) (sat_cons (step1076 p h) (sat_cons (step2700 p h) (sat_cons (step1365 p h) (sat_cons (step1357 p h) (sat_cons (step2779 p h) (sat_cons (step153 p h) (sat_nil p)))))))))
def c2806 : List Lit := [(1760, true), (74, true), (62, false), (63, true), (487, true)]
theorem step2806 (p : Nat → Bool) (h : Constraints p) : clause p c2806 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1284, c1281, c2671, c1291, c1252, c1234, c1231, c1230, c1270, c1267, c1236, c1227, c1852, c2575, c2724, c2745, c2695, c1819, c1811, c2655, c947] c2806 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step2671 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1270 p h) (sat_cons (step1267 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1852 p h) (sat_cons (step2575 p h) (sat_cons (step2724 p h) (sat_cons (step2745 p h) (sat_cons (step2695 p h) (sat_cons (step1819 p h) (sat_cons (step1811 p h) (sat_cons (step2655 p h) (sat_cons (step947 p h) (sat_nil p)))))))))))))))))))))))
def c2807 : List Lit := [(39, false), (1606, true), (74, true), (62, false), (49, false), (14, false), (42, false), (175, true)]
theorem step2807 (p : Nat → Bool) (h : Constraints p) : clause p c2807 = true :=
  Snake9.LocalRup.prove_clause [c1503, c323, c322, c2798, c1465, c1461, c1499, c1473, c1471, c1483, c1463, c1466, c1476, c362, c232, c357] c2807 (by decide) p (sat_cons (step1503 p h) (sat_cons (step323 p h) (sat_cons (step322 p h) (sat_cons (step2798 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step1499 p h) (sat_cons (step1473 p h) (sat_cons (step1471 p h) (sat_cons (step1483 p h) (sat_cons (step1463 p h) (sat_cons (step1466 p h) (sat_cons (step1476 p h) (sat_cons (step362 p h) (sat_cons (step232 p h) (sat_cons (step357 p h) (sat_nil p)))))))))))))))))
def c2808 : List Lit := [(1750, true), (74, false), (62, false), (63, true), (485, true)]
theorem step2808 (p : Nat → Bool) (h : Constraints p) : clause p c2808 = true :=
  Snake9.LocalRup.prove_clause [c1286, c1262, c1260, c1257, c1284, c1281, c1272, c1266, c2152, c2649, c1797, c1996, c905] c2808 (by decide) p (sat_cons (step1286 p h) (sat_cons (step1262 p h) (sat_cons (step1260 p h) (sat_cons (step1257 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step2152 p h) (sat_cons (step2649 p h) (sat_cons (step1797 p h) (sat_cons (step1996 p h) (sat_cons (step905 p h) (sat_nil p))))))))))))))
def c2809 : List Lit := [(23, false), (74, false), (62, false), (24, true), (18, true), (25, true)]
theorem step2809 (p : Nat → Bool) (h : Constraints p) : clause p c2809 = true :=
  Snake9.LocalRup.prove_clause [c1962, c2193] c2809 (by decide) p (sat_cons (step1962 p h) (sat_cons (step2193 p h) (sat_nil p)))
def c2810 : List Lit := [(69, true), (64, false), (66, false), (1661, true), (73, true), (62, false), (379, true)]
theorem step2810 (p : Nat → Bool) (h : Constraints p) : clause p c2810 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1626, c1614, c1616, c1624, c559, c624, c1619, c2070] c2810 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1626 p h) (sat_cons (step1614 p h) (sat_cons (step1616 p h) (sat_cons (step1624 p h) (sat_cons (step559 p h) (sat_cons (step624 p h) (sat_cons (step1619 p h) (sat_cons (step2070 p h) (sat_nil p))))))))))
def c2811 : List Lit := [(1545, true), (1534, false), (1526, false), (153, true)]
theorem step2811 (p : Nat → Bool) (h : Constraints p) : clause p c2811 = true :=
  Snake9.LocalRup.prove_clause [c1364, c1350, c1379, c1382, c1365, c1351, c1356, c2413] c2811 (by decide) p (sat_cons (step1364 p h) (sat_cons (step1350 p h) (sat_cons (step1379 p h) (sat_cons (step1382 p h) (sat_cons (step1365 p h) (sat_cons (step1351 p h) (sat_cons (step1356 p h) (sat_cons (step2413 p h) (sat_nil p)))))))))
def c2812 : List Lit := [(1598, false), (1615, true), (1568, false), (49, true), (174, true)]
theorem step2812 (p : Nat → Bool) (h : Constraints p) : clause p c2812 = true :=
  Snake9.LocalRup.prove_clause [c2753, c1445, c1519, c1495, c1481, c1484, c1494, c1499, c1476, c1526, c2656, c1446, c2157] c2812 (by decide) p (sat_cons (step2753 p h) (sat_cons (step1445 p h) (sat_cons (step1519 p h) (sat_cons (step1495 p h) (sat_cons (step1481 p h) (sat_cons (step1484 p h) (sat_cons (step1494 p h) (sat_cons (step1499 p h) (sat_cons (step1476 p h) (sat_cons (step1526 p h) (sat_cons (step2656 p h) (sat_cons (step1446 p h) (sat_cons (step2157 p h) (sat_nil p))))))))))))))
def c2813 : List Lit := [(22, false), (1599, true), (1660, true), (20, true), (21, true), (146, true)]
theorem step2813 (p : Nat → Bool) (h : Constraints p) : clause p c2813 = true :=
  Snake9.LocalRup.prove_clause [c116, c2679, c2470] c2813 (by decide) p (sat_cons (step116 p h) (sat_cons (step2679 p h) (sat_cons (step2470 p h) (sat_nil p))))
def c2814 : List Lit := [(1614, true), (1598, false), (49, true), (174, true)]
theorem step2814 (p : Nat → Bool) (h : Constraints p) : clause p c2814 = true :=
  Snake9.LocalRup.prove_clause [c2753, c1481, c1494, c1513, c1518, c1495, c1499, c1441, c1484, c2656, c1476, c2157] c2814 (by decide) p (sat_cons (step2753 p h) (sat_cons (step1481 p h) (sat_cons (step1494 p h) (sat_cons (step1513 p h) (sat_cons (step1518 p h) (sat_cons (step1495 p h) (sat_cons (step1499 p h) (sat_cons (step1441 p h) (sat_cons (step1484 p h) (sat_cons (step2656 p h) (sat_cons (step1476 p h) (sat_cons (step2157 p h) (sat_nil p)))))))))))))
def c2815 : List Lit := [(1614, true), (49, true), (42, false), (365, true)]
theorem step2815 (p : Nat → Bool) (h : Constraints p) : clause p c2815 = true :=
  Snake9.LocalRup.prove_clause [c1155, c1152, c1134, c1132, c1130, c2753, c1157, c1121, c1118, c1106, c1103, c2814, c2149, c1416, c1419, c1445, c2790, c1518, c2656, c1498] c2815 (by decide) p (sat_cons (step1155 p h) (sat_cons (step1152 p h) (sat_cons (step1134 p h) (sat_cons (step1132 p h) (sat_cons (step1130 p h) (sat_cons (step2753 p h) (sat_cons (step1157 p h) (sat_cons (step1121 p h) (sat_cons (step1118 p h) (sat_cons (step1106 p h) (sat_cons (step1103 p h) (sat_cons (step2814 p h) (sat_cons (step2149 p h) (sat_cons (step1416 p h) (sat_cons (step1419 p h) (sat_cons (step1445 p h) (sat_cons (step2790 p h) (sat_cons (step1518 p h) (sat_cons (step2656 p h) (sat_cons (step1498 p h) (sat_nil p)))))))))))))))))))))
def c2816 : List Lit := [(39, false), (1689, true), (67, false), (73, false), (75, true), (49, true), (42, false), (305, false)]
theorem step2816 (p : Nat → Bool) (h : Constraints p) : clause p c2816 = true :=
  Snake9.LocalRup.prove_clause [c1162, c2361, c1296, c1222, c1195, c1190, c1188, c1182, c2338, c1157, c1121, c1118, c1106, c1103, c454, c679, c221, c755, c209, c1649, c1664, c2576] c2816 (by decide) p (sat_cons (step1162 p h) (sat_cons (step2361 p h) (sat_cons (step1296 p h) (sat_cons (step1222 p h) (sat_cons (step1195 p h) (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1182 p h) (sat_cons (step2338 p h) (sat_cons (step1157 p h) (sat_cons (step1121 p h) (sat_cons (step1118 p h) (sat_cons (step1106 p h) (sat_cons (step1103 p h) (sat_cons (step454 p h) (sat_cons (step679 p h) (sat_cons (step221 p h) (sat_cons (step755 p h) (sat_cons (step209 p h) (sat_cons (step1649 p h) (sat_cons (step1664 p h) (sat_cons (step2576 p h) (sat_nil p)))))))))))))))))))))))
def c2817 : List Lit := [(1759, true), (1750, false), (439, true)]
theorem step2817 (p : Nat → Bool) (h : Constraints p) : clause p c2817 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1227, c2555, c1846, c2575, c2745] c2817 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step2555 p h) (sat_cons (step1846 p h) (sat_cons (step2575 p h) (sat_cons (step2745 p h) (sat_nil p)))))))
def c2818 : List Lit := [(1592, true), (74, true), (75, false), (49, false), (42, false), (347, true)]
theorem step2818 (p : Nat → Bool) (h : Constraints p) : clause p c2818 = true :=
  Snake9.LocalRup.prove_clause [c1136, c1128, c1126, c1134, c1132, c1129, c1467, c1469, c2155, c1464, c1465, c1461, c365, c1979, c356, c317, c230, c2217] c2818 (by decide) p (sat_cons (step1136 p h) (sat_cons (step1128 p h) (sat_cons (step1126 p h) (sat_cons (step1134 p h) (sat_cons (step1132 p h) (sat_cons (step1129 p h) (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_cons (step2155 p h) (sat_cons (step1464 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step365 p h) (sat_cons (step1979 p h) (sat_cons (step356 p h) (sat_cons (step317 p h) (sat_cons (step230 p h) (sat_cons (step2217 p h) (sat_nil p)))))))))))))))))))
def c2819 : List Lit := [(24, false), (1650, true), (148, true), (6, true), (19, true)]
theorem step2819 (p : Nat → Bool) (h : Constraints p) : clause p c2819 = true :=
  Snake9.LocalRup.prove_clause [c135, c2636] c2819 (by decide) p (sat_cons (step135 p h) (sat_cons (step2636 p h) (sat_nil p)))
def c2820 : List Lit := [(63, false), (1601, true), (64, false), (66, false), (42, false), (188, true)]
theorem step2820 (p : Nat → Bool) (h : Constraints p) : clause p c2820 = true :=
  Snake9.LocalRup.prove_clause [c1486, c524, c1997, c1475, c1477, c1484, c283, c1478, c1479, c541, c422] c2820 (by decide) p (sat_cons (step1486 p h) (sat_cons (step524 p h) (sat_cons (step1997 p h) (sat_cons (step1475 p h) (sat_cons (step1477 p h) (sat_cons (step1484 p h) (sat_cons (step283 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step541 p h) (sat_cons (step422 p h) (sat_nil p))))))))))))
def c2821 : List Lit := [(1760, true), (63, true), (62, true), (75, false), (487, true)]
theorem step2821 (p : Nat → Bool) (h : Constraints p) : clause p c2821 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1284, c2686, c1291, c1252, c1236, c1227, c1852, c2575, c2724, c2745, c2699] c2821 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step2686 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1852 p h) (sat_cons (step2575 p h) (sat_cons (step2724 p h) (sat_cons (step2745 p h) (sat_cons (step2699 p h) (sat_nil p)))))))))))))
def c2822 : List Lit := [(74, true), (1599, true), (67, false), (1660, true), (75, false), (393, true)]
theorem step2822 (p : Nat → Bool) (h : Constraints p) : clause p c2822 = true :=
  Snake9.LocalRup.prove_clause [c1192, c1180, c1177, c1190, c1188, c1182, c2486, c2528, c2550, c1614, c2527, c1623] c2822 (by decide) p (sat_cons (step1192 p h) (sat_cons (step1180 p h) (sat_cons (step1177 p h) (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1182 p h) (sat_cons (step2486 p h) (sat_cons (step2528 p h) (sat_cons (step2550 p h) (sat_cons (step1614 p h) (sat_cons (step2527 p h) (sat_cons (step1623 p h) (sat_nil p)))))))))))))
def c2823 : List Lit := [(51, true), (103, false), (1614, true), (49, false)]
theorem step2823 (p : Nat → Bool) (h : Constraints p) : clause p c2823 = true :=
  Snake9.LocalRup.prove_clause [c1513, c1503, c2775, c2505, c1416, c1498, c1419, c1518, c1445] c2823 (by decide) p (sat_cons (step1513 p h) (sat_cons (step1503 p h) (sat_cons (step2775 p h) (sat_cons (step2505 p h) (sat_cons (step1416 p h) (sat_cons (step1498 p h) (sat_cons (step1419 p h) (sat_cons (step1518 p h) (sat_cons (step1445 p h) (sat_nil p))))))))))
def c2824 : List Lit := [(1750, true), (1651, true), (62, false), (485, true)]
theorem step2824 (p : Nat → Bool) (h : Constraints p) : clause p c2824 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1281, c2671, c2676] c2824 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step2671 p h) (sat_cons (step2676 p h) (sat_nil p)))))
def c2825 : List Lit := [(1600, true), (1650, true), (1660, true), (185, true)]
theorem step2825 (p : Nat → Bool) (h : Constraints p) : clause p c2825 = true :=
  Snake9.LocalRup.prove_clause [c1607, c1606, c1481, c1483, c1478, c2567, c1475, c419, c618, c472] c2825 (by decide) p (sat_cons (step1607 p h) (sat_cons (step1606 p h) (sat_cons (step1481 p h) (sat_cons (step1483 p h) (sat_cons (step1478 p h) (sat_cons (step2567 p h) (sat_cons (step1475 p h) (sat_cons (step419 p h) (sat_cons (step618 p h) (sat_cons (step472 p h) (sat_nil p)))))))))))
def c2826 : List Lit := [(1657, false), (1698, true), (1652, false), (74, false), (62, false), (1660, true), (75, true)]
theorem step2826 (p : Nat → Bool) (h : Constraints p) : clause p c2826 = true :=
  Snake9.LocalRup.prove_clause [c1620, c1623, c1633, c1614, c1709, c707, c2161, c1649] c2826 (by decide) p (sat_cons (step1620 p h) (sat_cons (step1623 p h) (sat_cons (step1633 p h) (sat_cons (step1614 p h) (sat_cons (step1709 p h) (sat_cons (step707 p h) (sat_cons (step2161 p h) (sat_cons (step1649 p h) (sat_nil p)))))))))
def c2827 : List Lit := [(1600, false), (1605, true), (1615, true), (32, true), (75, true), (158, true)]
theorem step2827 (p : Nat → Bool) (h : Constraints p) : clause p c2827 = true :=
  Snake9.LocalRup.prove_clause [c1489, c1494, c1533, c2155, c1455, c2393] c2827 (by decide) p (sat_cons (step1489 p h) (sat_cons (step1494 p h) (sat_cons (step1533 p h) (sat_cons (step2155 p h) (sat_cons (step1455 p h) (sat_cons (step2393 p h) (sat_nil p)))))))
def c2828 : List Lit := [(1539, true), (24, true), (25, true), (18, true), (26, false), (10, false), (153, true)]
theorem step2828 (p : Nat → Bool) (h : Constraints p) : clause p c2828 = true :=
  Snake9.LocalRup.prove_clause [c2737, c2700] c2828 (by decide) p (sat_cons (step2737 p h) (sat_cons (step2700 p h) (sat_nil p)))
def c2829 : List Lit := [(75, false), (74, false), (62, false), (1660, true), (49, true), (197, true)]
theorem step2829 (p : Nat → Bool) (h : Constraints p) : clause p c2829 = true :=
  Snake9.LocalRup.prove_clause [c2685, c706] c2829 (by decide) p (sat_cons (step2685 p h) (sat_cons (step706 p h) (sat_nil p)))
def c2830 : List Lit := [(67, true), (74, false), (62, false), (1660, true), (49, true), (197, true)]
theorem step2830 (p : Nat → Bool) (h : Constraints p) : clause p c2830 = true :=
  Snake9.LocalRup.prove_clause [c2829, c1625, c1615, c1616, c1623, c707, c1617, c1618, c2264, c654, c678] c2830 (by decide) p (sat_cons (step2829 p h) (sat_cons (step1625 p h) (sat_cons (step1615 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step707 p h) (sat_cons (step1617 p h) (sat_cons (step1618 p h) (sat_cons (step2264 p h) (sat_cons (step654 p h) (sat_cons (step678 p h) (sat_nil p))))))))))))
def c2831 : List Lit := [(22, true), (1545, true), (25, true), (18, true), (1525, false), (153, true)]
theorem step2831 (p : Nat → Bool) (h : Constraints p) : clause p c2831 = true :=
  Snake9.LocalRup.prove_clause [c1353, c1344, c2190, c1349, c174, c1382, c1356, c1362] c2831 (by decide) p (sat_cons (step1353 p h) (sat_cons (step1344 p h) (sat_cons (step2190 p h) (sat_cons (step1349 p h) (sat_cons (step174 p h) (sat_cons (step1382 p h) (sat_cons (step1356 p h) (sat_cons (step1362 p h) (sat_nil p)))))))))
def c2832 : List Lit := [(113, false), (1615, true), (63, false), (24, false), (1592, false), (42, true)]
theorem step2832 (p : Nat → Bool) (h : Constraints p) : clause p c2832 = true :=
  Snake9.LocalRup.prove_clause [c504, c500, c1475, c1429, c1483, c1438, c1494, c1442, c1526] c2832 (by decide) p (sat_cons (step504 p h) (sat_cons (step500 p h) (sat_cons (step1475 p h) (sat_cons (step1429 p h) (sat_cons (step1483 p h) (sat_cons (step1438 p h) (sat_cons (step1494 p h) (sat_cons (step1442 p h) (sat_cons (step1526 p h) (sat_nil p))))))))))
def c2833 : List Lit := [(73, false), (22, false), (1617, true), (75, false), (49, true), (1592, false), (1576, false), (305, false)]
theorem step2833 (p : Nat → Bool) (h : Constraints p) : clause p c2833 = true :=
  Snake9.LocalRup.prove_clause [c1162, c2361, c1296, c1222, c1195, c1190, c1188, c1182, c2338, c1157, c1123, c1099, c1098, c1097, c2682, c2710] c2833 (by decide) p (sat_cons (step1162 p h) (sat_cons (step2361 p h) (sat_cons (step1296 p h) (sat_cons (step1222 p h) (sat_cons (step1195 p h) (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1182 p h) (sat_cons (step2338 p h) (sat_cons (step1157 p h) (sat_cons (step1123 p h) (sat_cons (step1099 p h) (sat_cons (step1098 p h) (sat_cons (step1097 p h) (sat_cons (step2682 p h) (sat_cons (step2710 p h) (sat_nil p)))))))))))))))))
def c2834 : List Lit := [(73, true), (1782, true), (67, true), (74, true), (75, true), (62, false), (489, true)]
theorem step2834 (p : Nat → Bool) (h : Constraints p) : clause p c2834 = true :=
  Snake9.LocalRup.prove_clause [c1294, c1648, c1289, c1284, c1281, c2671, c2804, c1296, c1222, c1195, c1192, c1180, c1177, c2740, c2730, c1897, c1635, c2806, c1609, c2646] c2834 (by decide) p (sat_cons (step1294 p h) (sat_cons (step1648 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step2671 p h) (sat_cons (step2804 p h) (sat_cons (step1296 p h) (sat_cons (step1222 p h) (sat_cons (step1195 p h) (sat_cons (step1192 p h) (sat_cons (step1180 p h) (sat_cons (step1177 p h) (sat_cons (step2740 p h) (sat_cons (step2730 p h) (sat_cons (step1897 p h) (sat_cons (step1635 p h) (sat_cons (step2806 p h) (sat_cons (step1609 p h) (sat_cons (step2646 p h) (sat_nil p)))))))))))))))))))))
def c2835 : List Lit := [(75, false), (1660, true), (62, false), (49, true), (393, true)]
theorem step2835 (p : Nat → Bool) (h : Constraints p) : clause p c2835 = true :=
  Snake9.LocalRup.prove_clause [c1190, c1188, c1182, c2683, c2829] c2835 (by decide) p (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1182 p h) (sat_cons (step2683 p h) (sat_cons (step2829 p h) (sat_nil p))))))
def c2836 : List Lit := [(32, false), (74, true), (62, false), (18, false), (156, true)]
theorem step2836 (p : Nat → Bool) (h : Constraints p) : clause p c2836 = true :=
  Snake9.LocalRup.prove_clause [c122, c189] c2836 (by decide) p (sat_cons (step122 p h) (sat_cons (step189 p h) (sat_nil p)))
def c2837 : List Lit := [(1615, true), (75, false), (49, true), (42, false), (158, true), (163, true), (174, true)]
theorem step2837 (p : Nat → Bool) (h : Constraints p) : clause p c2837 = true :=
  Snake9.LocalRup.prove_clause [c2099, c2753, c1493, c2812, c1533, c2149, c2101, c1450, c1451, c1526, c1498, c1494, c2656, c1483, c2157, c1476] c2837 (by decide) p (sat_cons (step2099 p h) (sat_cons (step2753 p h) (sat_cons (step1493 p h) (sat_cons (step2812 p h) (sat_cons (step1533 p h) (sat_cons (step2149 p h) (sat_cons (step2101 p h) (sat_cons (step1450 p h) (sat_cons (step1451 p h) (sat_cons (step1526 p h) (sat_cons (step1498 p h) (sat_cons (step1494 p h) (sat_cons (step2656 p h) (sat_cons (step1483 p h) (sat_cons (step2157 p h) (sat_cons (step1476 p h) (sat_nil p)))))))))))))))))
def c2838 : List Lit := [(23, false), (32, true), (26, false), (18, true), (62, true)]
theorem step2838 (p : Nat → Bool) (h : Constraints p) : clause p c2838 = true :=
  Snake9.LocalRup.prove_clause [c2197, c2191] c2838 (by decide) p (sat_cons (step2197 p h) (sat_cons (step2191 p h) (sat_nil p)))
def c2839 : List Lit := [(1653, false), (1701, true), (74, false), (32, false), (67, true), (1680, false), (1660, false), (1783, true), (75, true), (487, true)]
theorem step2839 (p : Nat → Bool) (h : Constraints p) : clause p c2839 = true :=
  Snake9.LocalRup.prove_clause [c1648, c2511, c1731, c1639, c1640, c1723, c1724, c1905, c2576, c1649, c691, c695, c1616, c2750, c1626, c1618] c2839 (by decide) p (sat_cons (step1648 p h) (sat_cons (step2511 p h) (sat_cons (step1731 p h) (sat_cons (step1639 p h) (sat_cons (step1640 p h) (sat_cons (step1723 p h) (sat_cons (step1724 p h) (sat_cons (step1905 p h) (sat_cons (step2576 p h) (sat_cons (step1649 p h) (sat_cons (step691 p h) (sat_cons (step695 p h) (sat_cons (step1616 p h) (sat_cons (step2750 p h) (sat_cons (step1626 p h) (sat_cons (step1618 p h) (sat_nil p)))))))))))))))))
def c2840 : List Lit := [(1759, true), (1713, false), (49, true), (487, true)]
theorem step2840 (p : Nat → Bool) (h : Constraints p) : clause p c2840 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1250, c1248, c1242, c1241, c2629, c2555, c2452, c1783, c2489, c1772, c1765] c2840 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1242 p h) (sat_cons (step1241 p h) (sat_cons (step2629 p h) (sat_cons (step2555 p h) (sat_cons (step2452 p h) (sat_cons (step1783 p h) (sat_cons (step2489 p h) (sat_cons (step1772 p h) (sat_cons (step1765 p h) (sat_nil p)))))))))))))
def c2841 : List Lit := [(1760, true), (1709, false), (1750, false), (49, true), (487, true)]
theorem step2841 (p : Nat → Bool) (h : Constraints p) : clause p c2841 = true :=
  Snake9.LocalRup.prove_clause [c1758, c1291, c1250, c1248, c1242, c1241, c2725, c1852, c862, c1787, c1783, c1759, c1772, c1753, c2404] c2841 (by decide) p (sat_cons (step1758 p h) (sat_cons (step1291 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1242 p h) (sat_cons (step1241 p h) (sat_cons (step2725 p h) (sat_cons (step1852 p h) (sat_cons (step862 p h) (sat_cons (step1787 p h) (sat_cons (step1783 p h) (sat_cons (step1759 p h) (sat_cons (step1772 p h) (sat_cons (step1753 p h) (sat_cons (step2404 p h) (sat_nil p))))))))))))))))
def c2842 : List Lit := [(103, false), (1615, true), (14, false), (49, false), (169, true)]
theorem step2842 (p : Nat → Bool) (h : Constraints p) : clause p c2842 = true :=
  Snake9.LocalRup.prove_clause [c325, c2782, c1416, c1419] c2842 (by decide) p (sat_cons (step325 p h) (sat_cons (step2782 p h) (sat_cons (step1416 p h) (sat_cons (step1419 p h) (sat_nil p)))))
def c2843 : List Lit := [(1545, true), (27, true), (1534, false), (18, false), (24, true), (1525, false), (153, true)]
theorem step2843 (p : Nat → Bool) (h : Constraints p) : clause p c2843 = true :=
  Snake9.LocalRup.prove_clause [c1357, c1347, c1375, c1366, c1358, c2746] c2843 (by decide) p (sat_cons (step1357 p h) (sat_cons (step1347 p h) (sat_cons (step1375 p h) (sat_cons (step1366 p h) (sat_cons (step1358 p h) (sat_cons (step2746 p h) (sat_nil p)))))))
end B112E089
