import B112E057Part0012
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2857 : List Lit := [(1095, true), (1111, false), (1029, false), (73, true), (90, false), (1055, false), (69, true)]
theorem step2857 (p : Nat → Bool) (h : Constraints p) : clause p c2857 = true :=
  Snake9.LocalRup.prove_clause [c2803, c2831, c2082, c1545] c2857 (by decide) p (sat_cons (step2803 p h) (sat_cons (step2831 p h) (sat_cons (step2082 p h) (sat_cons (step1545 p h) (sat_nil p)))))
def c2858 : List Lit := [(1056, true), (101, false), (97, true), (1083, true), (1087, false), (69, true), (7, false), (76, false)]
theorem step2858 (p : Nat → Bool) (h : Constraints p) : clause p c2858 = true :=
  Snake9.TreeRup.prove_clause [c1675, c2110, c1599, c2335, c1676, c1600, c1602, c1593, c1594, c1965, c547, c543, c540, c1727, c1554, c1729, c2804, c2835, c2840, c1588, c1617, c2839, c2844, c2807, c2426, c1810, c2845, c2342, c2334, c2331, c2341, c823, c1191, c1192, c1201, c2399, c1216, c2401, c1197, c1251, c2406, c1212, c1194, c1254, c2407, c1246, c1206, c827, c2408, c1188, c1228, c1203, c1133, c1135, c1158, c1226, c1130, c1074, c1143, c1222, c1098, c1043, c1139, c1086, c1032, c1138, c1080, c1031, c2284, c1077, c1030, c216, c213, c207, c2271, c217, c1317, c2856, c2857, c1708, c1768, c2850, c1724, c2355, c907, c2628, c2593, c1388, c1389, c2849, c280, c861, c2245, c255, c1980] c2858 (by decide) p (sat_cons (step1675 p h) (sat_cons (step2110 p h) (sat_cons (step1599 p h) (sat_cons (step2335 p h) (sat_cons (step1676 p h) (sat_cons (step1600 p h) (sat_cons (step1602 p h) (sat_cons (step1593 p h) (sat_cons (step1594 p h) (sat_cons (step1965 p h) (sat_cons (step547 p h) (sat_cons (step543 p h) (sat_cons (step540 p h) (sat_cons (step1727 p h) (sat_cons (step1554 p h) (sat_cons (step1729 p h) (sat_cons (step2804 p h) (sat_cons (step2835 p h) (sat_cons (step2840 p h) (sat_cons (step1588 p h) (sat_cons (step1617 p h) (sat_cons (step2839 p h) (sat_cons (step2844 p h) (sat_cons (step2807 p h) (sat_cons (step2426 p h) (sat_cons (step1810 p h) (sat_cons (step2845 p h) (sat_cons (step2342 p h) (sat_cons (step2334 p h) (sat_cons (step2331 p h) (sat_cons (step2341 p h) (sat_cons (step823 p h) (sat_cons (step1191 p h) (sat_cons (step1192 p h) (sat_cons (step1201 p h) (sat_cons (step2399 p h) (sat_cons (step1216 p h) (sat_cons (step2401 p h) (sat_cons (step1197 p h) (sat_cons (step1251 p h) (sat_cons (step2406 p h) (sat_cons (step1212 p h) (sat_cons (step1194 p h) (sat_cons (step1254 p h) (sat_cons (step2407 p h) (sat_cons (step1246 p h) (sat_cons (step1206 p h) (sat_cons (step827 p h) (sat_cons (step2408 p h) (sat_cons (step1188 p h) (sat_cons (step1228 p h) (sat_cons (step1203 p h) (sat_cons (step1133 p h) (sat_cons (step1135 p h) (sat_cons (step1158 p h) (sat_cons (step1226 p h) (sat_cons (step1130 p h) (sat_cons (step1074 p h) (sat_cons (step1143 p h) (sat_cons (step1222 p h) (sat_cons (step1098 p h) (sat_cons (step1043 p h) (sat_cons (step1139 p h) (sat_cons (step1086 p h) (sat_cons (step1032 p h) (sat_cons (step1138 p h) (sat_cons (step1080 p h) (sat_cons (step1031 p h) (sat_cons (step2284 p h) (sat_cons (step1077 p h) (sat_cons (step1030 p h) (sat_cons (step216 p h) (sat_cons (step213 p h) (sat_cons (step207 p h) (sat_cons (step2271 p h) (sat_cons (step217 p h) (sat_cons (step1317 p h) (sat_cons (step2856 p h) (sat_cons (step2857 p h) (sat_cons (step1708 p h) (sat_cons (step1768 p h) (sat_cons (step2850 p h) (sat_cons (step1724 p h) (sat_cons (step2355 p h) (sat_cons (step907 p h) (sat_cons (step2628 p h) (sat_cons (step2593 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step2849 p h) (sat_cons (step280 p h) (sat_cons (step861 p h) (sat_cons (step2245 p h) (sat_cons (step255 p h) (sat_cons (step1980 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2859 : List Lit := [(1045, true), (90, false), (89, false)]
theorem step2859 (p : Nat → Bool) (h : Constraints p) : clause p c2859 = true :=
  Snake9.LocalRup.prove_clause [c1582, c1583, c703, c754, c2316] c2859 (by decide) p (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step703 p h) (sat_cons (step754 p h) (sat_cons (step2316 p h) (sat_nil p))))))
def c2860 : List Lit := [(1134, true), (1100, false), (90, false), (114, true), (1087, false)]
theorem step2860 (p : Nat → Bool) (h : Constraints p) : clause p c2860 = true :=
  Snake9.LocalRup.prove_clause [c1727, c1729, c1749, c1771, c1767, c1709, c2855] c2860 (by decide) p (sat_cons (step1727 p h) (sat_cons (step1729 p h) (sat_cons (step1749 p h) (sat_cons (step1771 p h) (sat_cons (step1767 p h) (sat_cons (step1709 p h) (sat_cons (step2855 p h) (sat_nil p))))))))
def c2861 : List Lit := [(1075, false), (1124, false), (1076, true), (1045, false), (90, false), (1160, true), (1029, false), (73, true), (1056, false), (1055, false), (1087, false), (69, true)]
theorem step2861 (p : Nat → Bool) (h : Constraints p) : clause p c2861 = true :=
  Snake9.LocalRup.prove_clause [c1544, c2081, c1551, c1559, c1571, c1653, c1623, c1591, c1810, c2841, c1772, c1709, c2814, c760, c757, c751, c1584, c1552, c1586, c1562, c1618, c1572, c1660] c2861 (by decide) p (sat_cons (step1544 p h) (sat_cons (step2081 p h) (sat_cons (step1551 p h) (sat_cons (step1559 p h) (sat_cons (step1571 p h) (sat_cons (step1653 p h) (sat_cons (step1623 p h) (sat_cons (step1591 p h) (sat_cons (step1810 p h) (sat_cons (step2841 p h) (sat_cons (step1772 p h) (sat_cons (step1709 p h) (sat_cons (step2814 p h) (sat_cons (step760 p h) (sat_cons (step757 p h) (sat_cons (step751 p h) (sat_cons (step1584 p h) (sat_cons (step1552 p h) (sat_cons (step1586 p h) (sat_cons (step1562 p h) (sat_cons (step1618 p h) (sat_cons (step1572 p h) (sat_cons (step1660 p h) (sat_nil p))))))))))))))))))))))))
def c2862 : List Lit := [(1043, true), (72, false), (79, false), (89, false), (95, false)]
theorem step2862 (p : Nat → Bool) (h : Constraints p) : clause p c2862 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1580, c630, c674, c483, c2310] c2862 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step630 p h) (sat_cons (step674 p h) (sat_cons (step483 p h) (sat_cons (step2310 p h) (sat_nil p)))))))
def c2863 : List Lit := [(1040, true), (1048, true), (73, true), (77, true), (89, false), (95, false), (69, true)]
theorem step2863 (p : Nat → Bool) (h : Constraints p) : clause p c2863 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1551, c1559, c1544, c2081, c1572, c1576, c1562, c1560, c2082, c1552, c1555, c1545, c2862, c1588, c1582, c1583, c703, c744, c2316] c2863 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1551 p h) (sat_cons (step1559 p h) (sat_cons (step1544 p h) (sat_cons (step2081 p h) (sat_cons (step1572 p h) (sat_cons (step1576 p h) (sat_cons (step1562 p h) (sat_cons (step1560 p h) (sat_cons (step2082 p h) (sat_cons (step1552 p h) (sat_cons (step1555 p h) (sat_cons (step1545 p h) (sat_cons (step2862 p h) (sat_cons (step1588 p h) (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step703 p h) (sat_cons (step744 p h) (sat_cons (step2316 p h) (sat_nil p)))))))))))))))))))))
def c2864 : List Lit := [(72, false), (81, true), (82, false), (83, false), (95, false)]
theorem step2864 (p : Nat → Bool) (h : Constraints p) : clause p c2864 = true :=
  Snake9.LocalRup.prove_clause [c674, c483, c2310] c2864 (by decide) p (sat_cons (step674 p h) (sat_cons (step483 p h) (sat_cons (step2310 p h) (sat_nil p))))
def c2865 : List Lit := [(105, true), (83, false), (72, false), (1096, true)]
theorem step2865 (p : Nat → Bool) (h : Constraints p) : clause p c2865 = true :=
  Snake9.LocalRup.prove_clause [c1700, c1689, c1691, c1698, c679, c1693, c2344, c2345, c2020] c2865 (by decide) p (sat_cons (step1700 p h) (sat_cons (step1689 p h) (sat_cons (step1691 p h) (sat_cons (step1698 p h) (sat_cons (step679 p h) (sat_cons (step1693 p h) (sat_cons (step2344 p h) (sat_cons (step2345 p h) (sat_cons (step2020 p h) (sat_nil p))))))))))
def c2866 : List Lit := [(87, false), (88, true), (79, false), (89, false)]
theorem step2866 (p : Nat → Bool) (h : Constraints p) : clause p c2866 = true :=
  Snake9.LocalRup.prove_clause [c702, c2316] c2866 (by decide) p (sat_cons (step702 p h) (sat_cons (step2316 p h) (sat_nil p)))
def c2867 : List Lit := [(88, true), (83, true), (1092, true), (72, false), (79, false), (1049, true), (89, false), (101, false), (95, false)]
theorem step2867 (p : Nat → Bool) (h : Constraints p) : clause p c2867 = true :=
  Snake9.LocalRup.prove_clause [c2862, c1589, c2866, c1582, c1584, c1591, c2813, c1581, c1691, c629, c483, c676, c2310] c2867 (by decide) p (sat_cons (step2862 p h) (sat_cons (step1589 p h) (sat_cons (step2866 p h) (sat_cons (step1582 p h) (sat_cons (step1584 p h) (sat_cons (step1591 p h) (sat_cons (step2813 p h) (sat_cons (step1581 p h) (sat_cons (step1691 p h) (sat_cons (step629 p h) (sat_cons (step483 p h) (sat_cons (step676 p h) (sat_cons (step2310 p h) (sat_nil p))))))))))))))
def c2868 : List Lit := [(1043, true), (126, true), (119, true), (121, false), (125, false)]
theorem step2868 (p : Nat → Bool) (h : Constraints p) : clause p c2868 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1580, c927, c686, c2367] c2868 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step927 p h) (sat_cons (step686 p h) (sat_cons (step2367 p h) (sat_nil p))))))
def c2869 : List Lit := [(123, true), (81, true), (82, false), (83, false), (1125, true), (1109, false), (95, false)]
theorem step2869 (p : Nat → Bool) (h : Constraints p) : clause p c2869 = true :=
  Snake9.LocalRup.prove_clause [c1729, c1751, c1744, c1737, c1739, c1742, c686, c1754, c2310, c1732, c489, c1724] c2869 (by decide) p (sat_cons (step1729 p h) (sat_cons (step1751 p h) (sat_cons (step1744 p h) (sat_cons (step1737 p h) (sat_cons (step1739 p h) (sat_cons (step1742 p h) (sat_cons (step686 p h) (sat_cons (step1754 p h) (sat_cons (step2310 p h) (sat_cons (step1732 p h) (sat_cons (step489 p h) (sat_cons (step1724 p h) (sat_nil p)))))))))))))
def c2870 : List Lit := [(1095, true), (105, false), (84, true)]
theorem step2870 (p : Nat → Bool) (h : Constraints p) : clause p c2870 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1697, c1693, c1690, c869, c2344] c2870 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1697 p h) (sat_cons (step1693 p h) (sat_cons (step1690 p h) (sat_cons (step869 p h) (sat_cons (step2344 p h) (sat_nil p)))))))
def c2871 : List Lit := [(1124, true), (114, true), (1115, true), (1043, true)]
theorem step2871 (p : Nat → Bool) (h : Constraints p) : clause p c2871 = true :=
  Snake9.LocalRup.prove_clause [c1727, c1729, c1738, c1737, c1753, c1750, c1730, c1741, c1728, c1740, c922, c962, c2868] c2871 (by decide) p (sat_cons (step1727 p h) (sat_cons (step1729 p h) (sat_cons (step1738 p h) (sat_cons (step1737 p h) (sat_cons (step1753 p h) (sat_cons (step1750 p h) (sat_cons (step1730 p h) (sat_cons (step1741 p h) (sat_cons (step1728 p h) (sat_cons (step1740 p h) (sat_cons (step922 p h) (sat_cons (step962 p h) (sat_cons (step2868 p h) (sat_nil p))))))))))))))
def c2872 : List Lit := [(92, false), (220, true), (101, false), (1083, true)]
theorem step2872 (p : Nat → Bool) (h : Constraints p) : clause p c2872 = true :=
  Snake9.LocalRup.prove_clause [c1675, c2336, c1676, c795, c796, c804] c2872 (by decide) p (sat_cons (step1675 p h) (sat_cons (step2336 p h) (sat_cons (step1676 p h) (sat_cons (step795 p h) (sat_cons (step796 p h) (sat_cons (step804 p h) (sat_nil p)))))))
def c2873 : List Lit := [(107, true), (108, false), (105, true), (103, true), (97, true), (99, false)]
theorem step2873 (p : Nat → Bool) (h : Constraints p) : clause p c2873 = true :=
  Snake9.LocalRup.prove_clause [c827, c871, c1194, c1207, c1197, c1210, c1199, c1211, c2401] c2873 (by decide) p (sat_cons (step827 p h) (sat_cons (step871 p h) (sat_cons (step1194 p h) (sat_cons (step1207 p h) (sat_cons (step1197 p h) (sat_cons (step1210 p h) (sat_cons (step1199 p h) (sat_cons (step1211 p h) (sat_cons (step2401 p h) (sat_nil p))))))))))
def c2874 : List Lit := [(1045, true), (90, false), (85, true)]
theorem step2874 (p : Nat → Bool) (h : Constraints p) : clause p c2874 = true :=
  Snake9.LocalRup.prove_clause [c1582, c2316, c754, c1583] c2874 (by decide) p (sat_cons (step1582 p h) (sat_cons (step2316 p h) (sat_cons (step754 p h) (sat_cons (step1583 p h) (sat_nil p)))))
def c2875 : List Lit := [(1096, true), (84, true), (105, true), (1091, false), (90, false)]
theorem step2875 (p : Nat → Bool) (h : Constraints p) : clause p c2875 = true :=
  Snake9.LocalRup.prove_clause [c1700, c1698, c1691, c1693, c2344, c867] c2875 (by decide) p (sat_cons (step1700 p h) (sat_cons (step1698 p h) (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step2344 p h) (sat_cons (step867 p h) (sat_nil p)))))))
def c2876 : List Lit := [(1089, true), (101, true), (96, true), (92, true), (77, false), (70, true)]
theorem step2876 (p : Nat → Bool) (h : Constraints p) : clause p c2876 = true :=
  Snake9.LocalRup.prove_clause [c1678, c1675, c1687, c1685, c1677, c1680, c2331, c821] c2876 (by decide) p (sat_cons (step1678 p h) (sat_cons (step1675 p h) (sat_cons (step1687 p h) (sat_cons (step1685 p h) (sat_cons (step1677 p h) (sat_cons (step1680 p h) (sat_cons (step2331 p h) (sat_cons (step821 p h) (sat_nil p)))))))))
def c2877 : List Lit := [(1111, true), (40, true), (77, false), (70, true)]
theorem step2877 (p : Nat → Bool) (h : Constraints p) : clause p c2877 = true :=
  Snake9.LocalRup.prove_clause [c1729, c1731, c1727, c1724, c2159] c2877 (by decide) p (sat_cons (step1729 p h) (sat_cons (step1731 p h) (sat_cons (step1727 p h) (sat_cons (step1724 p h) (sat_cons (step2159 p h) (sat_nil p))))))
def c2878 : List Lit := [(111, true), (109, false), (118, false)]
theorem step2878 (p : Nat → Bool) (h : Constraints p) : clause p c2878 = true :=
  Snake9.LocalRup.prove_clause [c2350, c2352, c2021] c2878 (by decide) p (sat_cons (step2350 p h) (sat_cons (step2352 p h) (sat_cons (step2021 p h) (sat_nil p))))
def c2879 : List Lit := [(921, false), (1005, true), (941, false), (45, false), (959, false), (113, false), (1006, true)]
theorem step2879 (p : Nat → Bool) (h : Constraints p) : clause p c2879 = true :=
  Snake9.LocalRup.prove_clause [c2069, c1534, c1491, c1418, c1414, c2799, c1451, c1533, c2066, c2416, c1466] c2879 (by decide) p (sat_cons (step2069 p h) (sat_cons (step1534 p h) (sat_cons (step1491 p h) (sat_cons (step1418 p h) (sat_cons (step1414 p h) (sat_cons (step2799 p h) (sat_cons (step1451 p h) (sat_cons (step1533 p h) (sat_cons (step2066 p h) (sat_cons (step2416 p h) (sat_cons (step1466 p h) (sat_nil p))))))))))))
def c2880 : List Lit := [(109, true), (84, true), (105, true), (1094, true), (90, false), (1097, true)]
theorem step2880 (p : Nat → Bool) (h : Constraints p) : clause p c2880 = true :=
  Snake9.LocalRup.prove_clause [c1692, c1694, c1701, c1691, c2344, c867] c2880 (by decide) p (sat_cons (step1692 p h) (sat_cons (step1694 p h) (sat_cons (step1701 p h) (sat_cons (step1691 p h) (sat_cons (step2344 p h) (sat_cons (step867 p h) (sat_nil p)))))))
def c2881 : List Lit := [(1060, true), (70, true), (1045, false), (90, false)]
theorem step2881 (p : Nat → Bool) (h : Constraints p) : clause p c2881 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1616, c1612, c1588, c1601, c2840, c1594] c2881 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1616 p h) (sat_cons (step1612 p h) (sat_cons (step1588 p h) (sat_cons (step1601 p h) (sat_cons (step2840 p h) (sat_cons (step1594 p h) (sat_nil p))))))))
def c2882 : List Lit := [(1038, true), (1027, false), (89, false)]
theorem step2882 (p : Nat → Bool) (h : Constraints p) : clause p c2882 = true :=
  Snake9.LocalRup.prove_clause [c1558, c2085, c1570, c1559, c2081, c1553, c1554, c1543, c1544, c470, c553, c624, c2286] c2882 (by decide) p (sat_cons (step1558 p h) (sat_cons (step2085 p h) (sat_cons (step1570 p h) (sat_cons (step1559 p h) (sat_cons (step2081 p h) (sat_cons (step1553 p h) (sat_cons (step1554 p h) (sat_cons (step1543 p h) (sat_cons (step1544 p h) (sat_cons (step470 p h) (sat_cons (step553 p h) (sat_cons (step624 p h) (sat_cons (step2286 p h) (sat_nil p))))))))))))))
def c2883 : List Lit := [(1027, false), (1051, true), (1055, false), (89, false), (1073, true)]
theorem step2883 (p : Nat → Bool) (h : Constraints p) : clause p c2883 = true :=
  Snake9.LocalRup.prove_clause [c2804, c1585, c1612, c1650, c1593, c1558, c1575, c2082, c2882, c1643, c1617, c1588, c1580, c2840, c2143, c1554, c1559, c1571, c2081, c1543, c1544, c471] c2883 (by decide) p (sat_cons (step2804 p h) (sat_cons (step1585 p h) (sat_cons (step1612 p h) (sat_cons (step1650 p h) (sat_cons (step1593 p h) (sat_cons (step1558 p h) (sat_cons (step1575 p h) (sat_cons (step2082 p h) (sat_cons (step2882 p h) (sat_cons (step1643 p h) (sat_cons (step1617 p h) (sat_cons (step1588 p h) (sat_cons (step1580 p h) (sat_cons (step2840 p h) (sat_cons (step2143 p h) (sat_cons (step1554 p h) (sat_cons (step1559 p h) (sat_cons (step1571 p h) (sat_cons (step2081 p h) (sat_cons (step1543 p h) (sat_cons (step1544 p h) (sat_cons (step471 p h) (sat_nil p)))))))))))))))))))))))
def c2884 : List Lit := [(1021, true), (70, false), (82, false)]
theorem step2884 (p : Nat → Bool) (h : Constraints p) : clause p c2884 = true :=
  Snake9.LocalRup.prove_clause [c1543, c1544, c471] c2884 (by decide) p (sat_cons (step1543 p h) (sat_cons (step1544 p h) (sat_cons (step471 p h) (sat_nil p))))
def c2885 : List Lit := [(1048, true), (1022, true), (73, false), (75, false), (1039, true), (1045, false), (90, false), (89, false)]
theorem step2885 (p : Nat → Bool) (h : Constraints p) : clause p c2885 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1588, c2809, c1579, c1580, c2840, c2143, c2884, c2081, c1571, c1557, c1555, c696, c2810, c1584, c517, c2293, c2297, c550, c597, c1545] c2885 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1588 p h) (sat_cons (step2809 p h) (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step2840 p h) (sat_cons (step2143 p h) (sat_cons (step2884 p h) (sat_cons (step2081 p h) (sat_cons (step1571 p h) (sat_cons (step1557 p h) (sat_cons (step1555 p h) (sat_cons (step696 p h) (sat_cons (step2810 p h) (sat_cons (step1584 p h) (sat_cons (step517 p h) (sat_cons (step2293 p h) (sat_cons (step2297 p h) (sat_cons (step550 p h) (sat_cons (step597 p h) (sat_cons (step1545 p h) (sat_nil p))))))))))))))))))))))
def c2886 : List Lit := [(1031, false), (1051, true), (1055, false), (89, false), (1073, true)]
theorem step2886 (p : Nat → Bool) (h : Constraints p) : clause p c2886 = true :=
  Snake9.LocalRup.prove_clause [c2883, c1551, c1550, c2804, c1585, c1612, c1650, c1593, c2084, c1575, c1636, c2082, c1622, c2885, c1617, c1643, c2085, c1570, c1557, c2081, c1543, c1544, c597, c550, c2114, c1589, c2809, c2297, c517, c516, c1584, c1555, c2866] c2886 (by decide) p (sat_cons (step2883 p h) (sat_cons (step1551 p h) (sat_cons (step1550 p h) (sat_cons (step2804 p h) (sat_cons (step1585 p h) (sat_cons (step1612 p h) (sat_cons (step1650 p h) (sat_cons (step1593 p h) (sat_cons (step2084 p h) (sat_cons (step1575 p h) (sat_cons (step1636 p h) (sat_cons (step2082 p h) (sat_cons (step1622 p h) (sat_cons (step2885 p h) (sat_cons (step1617 p h) (sat_cons (step1643 p h) (sat_cons (step2085 p h) (sat_cons (step1570 p h) (sat_cons (step1557 p h) (sat_cons (step2081 p h) (sat_cons (step1543 p h) (sat_cons (step1544 p h) (sat_cons (step597 p h) (sat_cons (step550 p h) (sat_cons (step2114 p h) (sat_cons (step1589 p h) (sat_cons (step2809 p h) (sat_cons (step2297 p h) (sat_cons (step517 p h) (sat_cons (step516 p h) (sat_cons (step1584 p h) (sat_cons (step1555 p h) (sat_cons (step2866 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c2887 : List Lit := [(1051, true), (1055, false), (1073, true), (89, false)]
theorem step2887 (p : Nat → Bool) (h : Constraints p) : clause p c2887 = true :=
  Snake9.LocalRup.prove_clause [c2883, c1550, c1551, c2886, c1556, c1553, c1554, c696, c559, c516, c2293] c2887 (by decide) p (sat_cons (step2883 p h) (sat_cons (step1550 p h) (sat_cons (step1551 p h) (sat_cons (step2886 p h) (sat_cons (step1556 p h) (sat_cons (step1553 p h) (sat_cons (step1554 p h) (sat_cons (step696 p h) (sat_cons (step559 p h) (sat_cons (step516 p h) (sat_cons (step2293 p h) (sat_nil p))))))))))))
def c2888 : List Lit := [(1021, true), (79, false), (76, true), (77, false), (89, false)]
theorem step2888 (p : Nat → Bool) (h : Constraints p) : clause p c2888 = true :=
  Snake9.LocalRup.prove_clause [c1543, c1544, c624, c470, c2286] c2888 (by decide) p (sat_cons (step1543 p h) (sat_cons (step1544 p h) (sat_cons (step624 p h) (sat_cons (step470 p h) (sat_cons (step2286 p h) (sat_nil p))))))
def c2889 : List Lit := [(1045, true), (75, false), (79, false), (89, false)]
theorem step2889 (p : Nat → Bool) (h : Constraints p) : clause p c2889 = true :=
  Snake9.LocalRup.prove_clause [c1582, c1583, c2866, c744] c2889 (by decide) p (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step2866 p h) (sat_cons (step744 p h) (sat_nil p)))))
def c2890 : List Lit := [(1045, false), (1027, false), (76, true), (1055, false), (77, false), (89, false), (1073, true)]
theorem step2890 (p : Nat → Bool) (h : Constraints p) : clause p c2890 = true :=
  Snake9.LocalRup.prove_clause [c2882, c1643, c1617, c1558, c1585, c1588, c1612, c1579, c1580, c1650, c631, c1575, c2082, c2143, c2286, c2310, c1545, c674] c2890 (by decide) p (sat_cons (step2882 p h) (sat_cons (step1643 p h) (sat_cons (step1617 p h) (sat_cons (step1558 p h) (sat_cons (step1585 p h) (sat_cons (step1588 p h) (sat_cons (step1612 p h) (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step1650 p h) (sat_cons (step631 p h) (sat_cons (step1575 p h) (sat_cons (step2082 p h) (sat_cons (step2143 p h) (sat_cons (step2286 p h) (sat_cons (step2310 p h) (sat_cons (step1545 p h) (sat_cons (step674 p h) (sat_nil p)))))))))))))))))))
def c2891 : List Lit := [(1043, true), (1040, true), (77, false), (1045, true), (1027, false), (89, false)]
theorem step2891 (p : Nat → Bool) (h : Constraints p) : clause p c2891 = true :=
  Snake9.LocalRup.prove_clause [c1582, c1583, c703, c2318, c1579, c1580, c631, c619, c1553, c1559, c1576, c2082, c2143, c2310, c674, c647, c1545, c2287] c2891 (by decide) p (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step703 p h) (sat_cons (step2318 p h) (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step631 p h) (sat_cons (step619 p h) (sat_cons (step1553 p h) (sat_cons (step1559 p h) (sat_cons (step1576 p h) (sat_cons (step2082 p h) (sat_cons (step2143 p h) (sat_cons (step2310 p h) (sat_cons (step674 p h) (sat_cons (step647 p h) (sat_cons (step1545 p h) (sat_cons (step2287 p h) (sat_nil p)))))))))))))))))))
def c2892 : List Lit := [(1073, true), (77, false), (1045, true), (75, true), (89, false)]
theorem step2892 (p : Nat → Bool) (h : Constraints p) : clause p c2892 = true :=
  Snake9.LocalRup.prove_clause [c2804, c1601, c1582, c1583, c703, c1550, c2882, c2422, c1643, c1617, c1590, c2891, c1587, c1612, c1650, c2136, c553, c559, c1544, c1552, c2081, c1561, c1571] c2892 (by decide) p (sat_cons (step2804 p h) (sat_cons (step1601 p h) (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step703 p h) (sat_cons (step1550 p h) (sat_cons (step2882 p h) (sat_cons (step2422 p h) (sat_cons (step1643 p h) (sat_cons (step1617 p h) (sat_cons (step1590 p h) (sat_cons (step2891 p h) (sat_cons (step1587 p h) (sat_cons (step1612 p h) (sat_cons (step1650 p h) (sat_cons (step2136 p h) (sat_cons (step553 p h) (sat_cons (step559 p h) (sat_cons (step1544 p h) (sat_cons (step1552 p h) (sat_cons (step2081 p h) (sat_cons (step1561 p h) (sat_cons (step1571 p h) (sat_nil p))))))))))))))))))))))))
def c2893 : List Lit := [(1088, true), (1053, true), (70, true), (77, false)]
theorem step2893 (p : Nat → Bool) (h : Constraints p) : clause p c2893 = true :=
  Snake9.LocalRup.prove_clause [c2110, c1675, c1597, c1596, c1686, c1684, c1677, c1679, c793, c821, c2331] c2893 (by decide) p (sat_cons (step2110 p h) (sat_cons (step1675 p h) (sat_cons (step1597 p h) (sat_cons (step1596 p h) (sat_cons (step1686 p h) (sat_cons (step1684 p h) (sat_cons (step1677 p h) (sat_cons (step1679 p h) (sat_cons (step793 p h) (sat_cons (step821 p h) (sat_cons (step2331 p h) (sat_nil p))))))))))))
def c2894 : List Lit := [(101, false), (1053, true), (79, false)]
theorem step2894 (p : Nat → Bool) (h : Constraints p) : clause p c2894 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1596, c794, c833, c2342] c2894 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1596 p h) (sat_cons (step794 p h) (sat_cons (step833 p h) (sat_cons (step2342 p h) (sat_nil p))))))
def c2895 : List Lit := [(1089, false), (1136, true), (84, false), (72, false), (105, true), (123, true), (1095, false)]
theorem step2895 (p : Nat → Bool) (h : Constraints p) : clause p c2895 = true :=
  Snake9.LocalRup.prove_clause [c1737, c1742, c1746, c1780, c1717, c1718, c1777, c1700, c1747, c1691, c1744, c683, c1739] c2895 (by decide) p (sat_cons (step1737 p h) (sat_cons (step1742 p h) (sat_cons (step1746 p h) (sat_cons (step1780 p h) (sat_cons (step1717 p h) (sat_cons (step1718 p h) (sat_cons (step1777 p h) (sat_cons (step1700 p h) (sat_cons (step1747 p h) (sat_cons (step1691 p h) (sat_cons (step1744 p h) (sat_cons (step683 p h) (sat_cons (step1739 p h) (sat_nil p))))))))))))))
def c2896 : List Lit := [(1089, true), (101, true), (96, true), (91, false), (94, false), (70, true), (77, false)]
theorem step2896 (p : Nat → Bool) (h : Constraints p) : clause p c2896 = true :=
  Snake9.LocalRup.prove_clause [c1678, c1687, c2876, c1677, c793] c2896 (by decide) p (sat_cons (step1678 p h) (sat_cons (step1687 p h) (sat_cons (step2876 p h) (sat_cons (step1677 p h) (sat_cons (step793 p h) (sat_nil p))))))
def c2897 : List Lit := [(884, true), (877, false)]
theorem step2897 (p : Nat → Bool) (h : Constraints p) : clause p c2897 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1293, c1297, c1287, c1270, c1272, c1278, c1268, c1264, c1265, c2144, c7] c2897 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1293 p h) (sat_cons (step1297 p h) (sat_cons (step1287 p h) (sat_cons (step1270 p h) (sat_cons (step1272 p h) (sat_cons (step1278 p h) (sat_cons (step1268 p h) (sat_cons (step1264 p h) (sat_cons (step1265 p h) (sat_cons (step2144 p h) (sat_cons (step7 p h) (sat_nil p)))))))))))))
def c2898 : List Lit := [(917, true), (908, false)]
theorem step2898 (p : Nat → Bool) (h : Constraints p) : clause p c2898 = true :=
  Snake9.LocalRup.prove_clause [c2771, c1361] c2898 (by decide) p (sat_cons (step2771 p h) (sat_cons (step1361 p h) (sat_nil p)))
def c2899 : List Lit := [(918, true), (909, false)]
theorem step2899 (p : Nat → Bool) (h : Constraints p) : clause p c2899 = true :=
  Snake9.LocalRup.prove_clause [c2771, c1362] c2899 (by decide) p (sat_cons (step2771 p h) (sat_cons (step1362 p h) (sat_nil p)))
def c2900 : List Lit := [(910, false), (919, true)]
theorem step2900 (p : Nat → Bool) (h : Constraints p) : clause p c2900 = true :=
  Snake9.LocalRup.prove_clause [c2771, c1363] c2900 (by decide) p (sat_cons (step2771 p h) (sat_cons (step1363 p h) (sat_nil p)))
def c2901 : List Lit := [(911, false), (920, true)]
theorem step2901 (p : Nat → Bool) (h : Constraints p) : clause p c2901 = true :=
  Snake9.LocalRup.prove_clause [c2771, c1364] c2901 (by decide) p (sat_cons (step2771 p h) (sat_cons (step1364 p h) (sat_nil p)))
def c2902 : List Lit := [(912, false), (921, true)]
theorem step2902 (p : Nat → Bool) (h : Constraints p) : clause p c2902 = true :=
  Snake9.LocalRup.prove_clause [c2771, c1365] c2902 (by decide) p (sat_cons (step2771 p h) (sat_cons (step1365 p h) (sat_nil p)))
def c2903 : List Lit := [(986, false), (1004, true)]
theorem step2903 (p : Nat → Bool) (h : Constraints p) : clause p c2903 = true :=
  Snake9.LocalRup.prove_clause [c2775, c1510] c2903 (by decide) p (sat_cons (step2775 p h) (sat_cons (step1510 p h) (sat_nil p)))
def c2904 : List Lit := [(987, false), (1005, true)]
theorem step2904 (p : Nat → Bool) (h : Constraints p) : clause p c2904 = true :=
  Snake9.LocalRup.prove_clause [c2775, c1511] c2904 (by decide) p (sat_cons (step2775 p h) (sat_cons (step1511 p h) (sat_nil p)))
def c2905 : List Lit := [(1132, true), (1123, false)]
theorem step2905 (p : Nat → Bool) (h : Constraints p) : clause p c2905 = true :=
  Snake9.LocalRup.prove_clause [c2800, c1761] c2905 (by decide) p (sat_cons (step2800 p h) (sat_cons (step1761 p h) (sat_nil p)))
def c2906 : List Lit := [(1133, true), (1124, false)]
theorem step2906 (p : Nat → Bool) (h : Constraints p) : clause p c2906 = true :=
  Snake9.LocalRup.prove_clause [c2800, c1762] c2906 (by decide) p (sat_cons (step2800 p h) (sat_cons (step1762 p h) (sat_nil p)))
def c2907 : List Lit := [(1134, true), (1125, false)]
theorem step2907 (p : Nat → Bool) (h : Constraints p) : clause p c2907 = true :=
  Snake9.LocalRup.prove_clause [c2800, c1763] c2907 (by decide) p (sat_cons (step2800 p h) (sat_cons (step1763 p h) (sat_nil p)))
def c2908 : List Lit := [(1135, true), (1126, false)]
theorem step2908 (p : Nat → Bool) (h : Constraints p) : clause p c2908 = true :=
  Snake9.LocalRup.prove_clause [c2800, c1764] c2908 (by decide) p (sat_cons (step2800 p h) (sat_cons (step1764 p h) (sat_nil p)))
def c2909 : List Lit := [(1155, true), (1074, false)]
theorem step2909 (p : Nat → Bool) (h : Constraints p) : clause p c2909 = true :=
  Snake9.LocalRup.prove_clause [c2801, c1800] c2909 (by decide) p (sat_cons (step2801 p h) (sat_cons (step1800 p h) (sat_nil p)))
def c2910 : List Lit := [(1156, true), (1075, false)]
theorem step2910 (p : Nat → Bool) (h : Constraints p) : clause p c2910 = true :=
  Snake9.LocalRup.prove_clause [c2801, c1806] c2910 (by decide) p (sat_cons (step2801 p h) (sat_cons (step1806 p h) (sat_nil p)))
def c2911 : List Lit := [(1076, false), (1157, true)]
theorem step2911 (p : Nat → Bool) (h : Constraints p) : clause p c2911 = true :=
  Snake9.LocalRup.prove_clause [c2801, c1813] c2911 (by decide) p (sat_cons (step2801 p h) (sat_cons (step1813 p h) (sat_nil p)))
def c2912 : List Lit := [(1077, false), (1158, true)]
theorem step2912 (p : Nat → Bool) (h : Constraints p) : clause p c2912 = true :=
  Snake9.LocalRup.prove_clause [c2801, c1818] c2912 (by decide) p (sat_cons (step2801 p h) (sat_cons (step1818 p h) (sat_nil p)))
def c2913 : List Lit := [(1078, false), (1159, true)]
theorem step2913 (p : Nat → Bool) (h : Constraints p) : clause p c2913 = true :=
  Snake9.LocalRup.prove_clause [c2801, c1822] c2913 (by decide) p (sat_cons (step2801 p h) (sat_cons (step1822 p h) (sat_nil p)))
def c2914 : List Lit := [(1079, false), (1160, true)]
theorem step2914 (p : Nat → Bool) (h : Constraints p) : clause p c2914 = true :=
  Snake9.LocalRup.prove_clause [c2801, c1825] c2914 (by decide) p (sat_cons (step2801 p h) (sat_cons (step1825 p h) (sat_nil p)))
def c2915 : List Lit := [(1053, true), (1089, true), (70, true), (79, false), (77, false)]
theorem step2915 (p : Nat → Bool) (h : Constraints p) : clause p c2915 = true :=
  Snake9.LocalRup.prove_clause [c1596, c1597, c2110, c2894, c2896] c2915 (by decide) p (sat_cons (step1596 p h) (sat_cons (step1597 p h) (sat_cons (step2110 p h) (sat_cons (step2894 p h) (sat_cons (step2896 p h) (sat_nil p))))))
def c2916 : List Lit := [(986, true), (950, false), (45, false), (936, false), (941, false), (113, false), (59, true)]
theorem step2916 (p : Nat → Bool) (h : Constraints p) : clause p c2916 = true :=
  Snake9.LocalRup.prove_clause [c1452, c2066, c2284, c1138, c1139, c1143, c1158, c1188, c1256, c2408, c1133, c1128, c1123, c1121, c1112, c1111, c1119, c1117, c1115, c1113, c1110, c416, c2447, c1466, c1502, c1498, c1427, c2662, c1414, c2799] c2916 (by decide) p (sat_cons (step1452 p h) (sat_cons (step2066 p h) (sat_cons (step2284 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1143 p h) (sat_cons (step1158 p h) (sat_cons (step1188 p h) (sat_cons (step1256 p h) (sat_cons (step2408 p h) (sat_cons (step1133 p h) (sat_cons (step1128 p h) (sat_cons (step1123 p h) (sat_cons (step1121 p h) (sat_cons (step1112 p h) (sat_cons (step1111 p h) (sat_cons (step1119 p h) (sat_cons (step1117 p h) (sat_cons (step1115 p h) (sat_cons (step1113 p h) (sat_cons (step1110 p h) (sat_cons (step416 p h) (sat_cons (step2447 p h) (sat_cons (step1466 p h) (sat_cons (step1502 p h) (sat_cons (step1498 p h) (sat_cons (step1427 p h) (sat_cons (step2662 p h) (sat_cons (step1414 p h) (sat_cons (step2799 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2917 : List Lit := [(871, true), (2, true)]
theorem step2917 (p : Nat → Bool) (h : Constraints p) : clause p c2917 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1272, c1268, c1265, c2144] c2917 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1272 p h) (sat_cons (step1268 p h) (sat_cons (step1265 p h) (sat_cons (step2144 p h) (sat_nil p))))))
def c2918 : List Lit := [(10, false), (877, true), (2, true), (13, true)]
theorem step2918 (p : Nat → Bool) (h : Constraints p) : clause p c2918 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1281, c2211, c90] c2918 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1281 p h) (sat_cons (step2211 p h) (sat_cons (step90 p h) (sat_nil p)))))
def c2919 : List Lit := [(7, false), (19, false), (18, false), (115, true), (114, false), (251, true), (77, false)]
theorem step2919 (p : Nat → Bool) (h : Constraints p) : clause p c2919 = true :=
  Snake9.LocalRup.prove_clause [c545, c165, c2134] c2919 (by decide) p (sat_cons (step545 p h) (sat_cons (step165 p h) (sat_cons (step2134 p h) (sat_nil p))))
def c2920 : List Lit := [(112, false), (931, false), (7, false), (6, false), (987, true), (59, true), (40, false), (4, false)]
theorem step2920 (p : Nat → Bool) (h : Constraints p) : clause p c2920 = true :=
  Snake9.LocalRup.prove_clause [c2284, c1138, c1139, c1143, c1158, c1188, c1256, c2408, c1133, c1130, c1098, c1085, c1083, c1082, c1096, c1093, c1092, c1091, c1452, c2066, c299, c2160, c301, c296, c1406, c1398, c1438, c283, c1445, c2098, c1466, c2256, c1506, c1402, c1432, c1411, c1414, c1431, c1404, c1503, c41, c2253, c2662, c2154] c2920 (by decide) p (sat_cons (step2284 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1143 p h) (sat_cons (step1158 p h) (sat_cons (step1188 p h) (sat_cons (step1256 p h) (sat_cons (step2408 p h) (sat_cons (step1133 p h) (sat_cons (step1130 p h) (sat_cons (step1098 p h) (sat_cons (step1085 p h) (sat_cons (step1083 p h) (sat_cons (step1082 p h) (sat_cons (step1096 p h) (sat_cons (step1093 p h) (sat_cons (step1092 p h) (sat_cons (step1091 p h) (sat_cons (step1452 p h) (sat_cons (step2066 p h) (sat_cons (step299 p h) (sat_cons (step2160 p h) (sat_cons (step301 p h) (sat_cons (step296 p h) (sat_cons (step1406 p h) (sat_cons (step1398 p h) (sat_cons (step1438 p h) (sat_cons (step283 p h) (sat_cons (step1445 p h) (sat_cons (step2098 p h) (sat_cons (step1466 p h) (sat_cons (step2256 p h) (sat_cons (step1506 p h) (sat_cons (step1402 p h) (sat_cons (step1432 p h) (sat_cons (step1411 p h) (sat_cons (step1414 p h) (sat_cons (step1431 p h) (sat_cons (step1404 p h) (sat_cons (step1503 p h) (sat_cons (step41 p h) (sat_cons (step2253 p h) (sat_cons (step2662 p h) (sat_cons (step2154 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
end B112E057
