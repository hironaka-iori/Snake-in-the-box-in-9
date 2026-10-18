import B112E050Part0014
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2776 : List Lit := [(1811, false), (97, false), (1830, true), (1776, false), (108, true), (123, true), (93, true)]
theorem step2776 (p : Nat → Bool) (h : Constraints p) : clause p c2776 = true :=
  Snake9.LocalRup.prove_clause [c1536, c1538, c1556, c1642, c2235, c2515, c1532, c2234, c1613, c1648, c2738, c1557, c1537, c1539] c2776 (by decide) p (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1556 p h) (sat_cons (step1642 p h) (sat_cons (step2235 p h) (sat_cons (step2515 p h) (sat_cons (step1532 p h) (sat_cons (step2234 p h) (sat_cons (step1613 p h) (sat_cons (step1648 p h) (sat_cons (step2738 p h) (sat_cons (step1557 p h) (sat_cons (step1537 p h) (sat_cons (step1539 p h) (sat_nil p)))))))))))))))
def c2777 : List Lit := [(1830, true), (1776, false), (108, true), (102, false), (27, false), (46, false), (123, true), (96, true), (93, true)]
theorem step2777 (p : Nat → Bool) (h : Constraints p) : clause p c2777 = true :=
  Snake9.LocalRup.prove_clause [c1584, c2515, c2597, c1532, c1520, c2776, c2466, c1599, c670, c1590, c1587] c2777 (by decide) p (sat_cons (step1584 p h) (sat_cons (step2515 p h) (sat_cons (step2597 p h) (sat_cons (step1532 p h) (sat_cons (step1520 p h) (sat_cons (step2776 p h) (sat_cons (step2466 p h) (sat_cons (step1599 p h) (sat_cons (step670 p h) (sat_cons (step1590 p h) (sat_cons (step1587 p h) (sat_nil p))))))))))))
def c2778 : List Lit := [(1744, false), (1762, true), (1736, false), (1707, false), (87, true), (1725, false), (80, false), (7, false)]
theorem step2778 (p : Nat → Bool) (h : Constraints p) : clause p c2778 = true :=
  Snake9.LocalRup.prove_clause [c1458, c2773] c2778 (by decide) p (sat_cons (step1458 p h) (sat_cons (step2773 p h) (sat_nil p)))
def c2779 : List Lit := [(1731, true), (81, false), (8, false)]
theorem step2779 (p : Nat → Bool) (h : Constraints p) : clause p c2779 = true :=
  Snake9.LocalRup.prove_clause [c1419, c1420, c346] c2779 (by decide) p (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step346 p h) (sat_nil p))))
def c2780 : List Lit := [(91, false), (53, false), (1776, true), (96, true)]
theorem step2780 (p : Nat → Bool) (h : Constraints p) : clause p c2780 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1527, c1522, c2697, c411] c2780 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1527 p h) (sat_cons (step1522 p h) (sat_cons (step2697 p h) (sat_cons (step411 p h) (sat_nil p))))))
def c2781 : List Lit := [(91, false), (107, true), (100, false), (101, false), (97, false)]
theorem step2781 (p : Nat → Bool) (h : Constraints p) : clause p c2781 = true :=
  Snake9.LocalRup.prove_clause [c435, c588, c2134] c2781 (by decide) p (sat_cons (step435 p h) (sat_cons (step588 p h) (sat_cons (step2134 p h) (sat_nil p))))
def c2782 : List Lit := [(1636, true), (1623, false), (1618, false), (38, false), (7, false), (3, false)]
theorem step2782 (p : Nat → Bool) (h : Constraints p) : clause p c2782 = true :=
  Snake9.LocalRup.prove_clause [c2381, c1223, c117, c1208, c1201] c2782 (by decide) p (sat_cons (step2381 p h) (sat_cons (step1223 p h) (sat_cons (step117 p h) (sat_cons (step1208 p h) (sat_cons (step1201 p h) (sat_nil p))))))
def c2783 : List Lit := [(1739, true), (1776, true), (96, true)]
theorem step2783 (p : Nat → Bool) (h : Constraints p) : clause p c2783 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1527, c1522, c1433, c1434, c2697, c417] c2783 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1527 p h) (sat_cons (step1522 p h) (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step2697 p h) (sat_cons (step417 p h) (sat_nil p))))))))
def c2784 : List Lit := [(1777, false), (1831, true), (108, true), (1800, false), (123, true)]
theorem step2784 (p : Nat → Bool) (h : Constraints p) : clause p c2784 = true :=
  Snake9.LocalRup.prove_clause [c1584, c1598, c1612, c1655, c1536, c1538, c1561, c1562, c1649, c1539, c1613, c1537, c2442] c2784 (by decide) p (sat_cons (step1584 p h) (sat_cons (step1598 p h) (sat_cons (step1612 p h) (sat_cons (step1655 p h) (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1561 p h) (sat_cons (step1562 p h) (sat_cons (step1649 p h) (sat_cons (step1539 p h) (sat_cons (step1613 p h) (sat_cons (step1537 p h) (sat_cons (step2442 p h) (sat_nil p))))))))))))))
def c2785 : List Lit := [(1739, false), (1745, true), (1855, true), (108, true), (1773, false), (1800, false), (1776, false), (123, true), (96, true), (95, true), (93, true), (87, true), (1725, false), (7, false)]
theorem step2785 (p : Nat → Bool) (h : Constraints p) : clause p c2785 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1442, c1443, c2615, c1438, c1706, c2576, c2784, c1532, c1530, c2775, c1520] c2785 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1442 p h) (sat_cons (step1443 p h) (sat_cons (step2615 p h) (sat_cons (step1438 p h) (sat_cons (step1706 p h) (sat_cons (step2576 p h) (sat_cons (step2784 p h) (sat_cons (step1532 p h) (sat_cons (step1530 p h) (sat_cons (step2775 p h) (sat_cons (step1520 p h) (sat_nil p)))))))))))))
def c2786 : List Lit := [(1828, true), (1776, false)]
theorem step2786 (p : Nat → Bool) (h : Constraints p) : clause p c2786 = true :=
  Snake9.LocalRup.prove_clause [c2238, c2669, c1557, c1611, c2233, c1539, c1595, c2582, c1590, c2373, c1535, c1537, c1588, c1541, c2374, c2173, c1533, c640] c2786 (by decide) p (sat_cons (step2238 p h) (sat_cons (step2669 p h) (sat_cons (step1557 p h) (sat_cons (step1611 p h) (sat_cons (step2233 p h) (sat_cons (step1539 p h) (sat_cons (step1595 p h) (sat_cons (step2582 p h) (sat_cons (step1590 p h) (sat_cons (step2373 p h) (sat_cons (step1535 p h) (sat_cons (step1537 p h) (sat_cons (step1588 p h) (sat_cons (step1541 p h) (sat_cons (step2374 p h) (sat_cons (step2173 p h) (sat_cons (step1533 p h) (sat_cons (step640 p h) (sat_nil p)))))))))))))))))))
def c2787 : List Lit := [(1646, true), (95, false), (93, true)]
theorem step2787 (p : Nat → Bool) (h : Constraints p) : clause p c2787 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1240, c1235, c1236, c1232, c191, c167, c2070] c2787 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step1232 p h) (sat_cons (step191 p h) (sat_cons (step167 p h) (sat_cons (step2070 p h) (sat_nil p)))))))))
def c2788 : List Lit := [(1776, true), (1740, true), (30, false), (96, true)]
theorem step2788 (p : Nat → Bool) (h : Constraints p) : clause p c2788 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1529, c1527, c2733, c1520, c1521, c1522, c1435, c646, c2781] c2788 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1529 p h) (sat_cons (step1527 p h) (sat_cons (step2733 p h) (sat_cons (step1520 p h) (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step1435 p h) (sat_cons (step646 p h) (sat_cons (step2781 p h) (sat_nil p)))))))))))
def c2789 : List Lit := [(1776, true), (1744, true), (95, false), (96, true), (93, true)]
theorem step2789 (p : Nat → Bool) (h : Constraints p) : clause p c2789 = true :=
  Snake9.LocalRup.prove_clause [c1529, c2783, c1520, c1442, c1437, c2122, c491] c2789 (by decide) p (sat_cons (step1529 p h) (sat_cons (step2783 p h) (sat_cons (step1520 p h) (sat_cons (step1442 p h) (sat_cons (step1437 p h) (sat_cons (step2122 p h) (sat_cons (step491 p h) (sat_nil p))))))))
def c2790 : List Lit := [(1781, false), (1785, true), (1772, false), (1791, true), (105, true), (104, true), (93, true)]
theorem step2790 (p : Nat → Bool) (h : Constraints p) : clause p c2790 = true :=
  Snake9.LocalRup.prove_clause [c1532, c1544, c1541, c1534, c1562, c2140, c2138, c1530, c1806, c1522] c2790 (by decide) p (sat_cons (step1532 p h) (sat_cons (step1544 p h) (sat_cons (step1541 p h) (sat_cons (step1534 p h) (sat_cons (step1562 p h) (sat_cons (step2140 p h) (sat_cons (step2138 p h) (sat_cons (step1530 p h) (sat_cons (step1806 p h) (sat_cons (step1522 p h) (sat_nil p)))))))))))
def c2791 : List Lit := [(1789, true), (1773, false), (1776, false), (95, false), (96, true)]
theorem step2791 (p : Nat → Bool) (h : Constraints p) : clause p c2791 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1556, c1530, c1538, c1540, c1520, c1536, c1532, c2623, c669, c494, c2144] c2791 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1556 p h) (sat_cons (step1530 p h) (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step1520 p h) (sat_cons (step1536 p h) (sat_cons (step1532 p h) (sat_cons (step2623 p h) (sat_cons (step669 p h) (sat_cons (step494 p h) (sat_cons (step2144 p h) (sat_nil p)))))))))))))
def c2792 : List Lit := [(91, true), (1790, true), (1745, true), (1776, false), (95, true), (96, true), (93, true)]
theorem step2792 (p : Nat → Bool) (h : Constraints p) : clause p c2792 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1445, c1433, c1435, c1443, c2774, c1438] c2792 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1445 p h) (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1443 p h) (sat_cons (step2774 p h) (sat_cons (step1438 p h) (sat_nil p))))))))
def c2793 : List Lit := [(1580, true), (21, false), (93, true)]
theorem step2793 (p : Nat → Bool) (h : Constraints p) : clause p c2793 = true :=
  Snake9.LocalRup.prove_clause [c1125, c1126, c2031, c55] c2793 (by decide) p (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step2031 p h) (sat_cons (step55 p h) (sat_nil p)))))
def c2794 : List Lit := [(92, false), (97, false), (95, false), (93, true)]
theorem step2794 (p : Nat → Bool) (h : Constraints p) : clause p c2794 = true :=
  Snake9.LocalRup.prove_clause [c2122, c491] c2794 (by decide) p (sat_cons (step2122 p h) (sat_cons (step491 p h) (sat_nil p)))
def c2795 : List Lit := [(1590, true), (1773, true), (16, false), (15, false), (44, true)]
theorem step2795 (p : Nat → Bool) (h : Constraints p) : clause p c2795 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1143, c1139, c1135, c2695, c1749] c2795 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1139 p h) (sat_cons (step1135 p h) (sat_cons (step2695 p h) (sat_cons (step1749 p h) (sat_nil p)))))))
def c2796 : List Lit := [(91, false), (113, false), (1776, true), (96, true)]
theorem step2796 (p : Nat → Bool) (h : Constraints p) : clause p c2796 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1527, c1522, c2697, c424] c2796 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1527 p h) (sat_cons (step1522 p h) (sat_cons (step2697 p h) (sat_cons (step424 p h) (sat_nil p))))))
def c2797 : List Lit := [(88, false), (91, false), (18, false), (21, false)]
theorem step2797 (p : Nat → Bool) (h : Constraints p) : clause p c2797 = true :=
  Snake9.LocalRup.prove_clause [c396, c36, c2029] c2797 (by decide) p (sat_cons (step396 p h) (sat_cons (step36 p h) (sat_cons (step2029 p h) (sat_nil p))))
def c2798 : List Lit := [(1830, true), (1818, false), (1800, false), (1776, false), (1811, false), (123, true), (1771, false), (93, true)]
theorem step2798 (p : Nat → Bool) (h : Constraints p) : clause p c2798 = true :=
  Snake9.LocalRup.prove_clause [c2678, c1642, c2696, c1556] c2798 (by decide) p (sat_cons (step2678 p h) (sat_cons (step1642 p h) (sat_cons (step2696 p h) (sat_cons (step1556 p h) (sat_nil p)))))
def c2799 : List Lit := [(1591, true), (1774, true), (28, true), (62, false), (16, false), (44, true)]
theorem step2799 (p : Nat → Bool) (h : Constraints p) : clause p c2799 = true :=
  Snake9.LocalRup.prove_clause [c1142, c2319, c1140, c2769] c2799 (by decide) p (sat_cons (step1142 p h) (sat_cons (step2319 p h) (sat_cons (step1140 p h) (sat_cons (step2769 p h) (sat_nil p)))))
def c2800 : List Lit := [(1789, true), (95, false), (1776, false), (96, true), (93, true)]
theorem step2800 (p : Nat → Bool) (h : Constraints p) : clause p c2800 = true :=
  Snake9.LocalRup.prove_clause [c1556, c2791, c2696, c1522] c2800 (by decide) p (sat_cons (step1556 p h) (sat_cons (step2791 p h) (sat_cons (step2696 p h) (sat_cons (step1522 p h) (sat_nil p)))))
def c2801 : List Lit := [(1597, true), (21, true), (1773, true), (1579, false), (15, false), (44, true), (93, true)]
theorem step2801 (p : Nat → Bool) (h : Constraints p) : clause p c2801 = true :=
  Snake9.LocalRup.prove_clause [c1132, c2330, c1156, c1138, c1139, c1146, c2042, c2695, c1137, c66] c2801 (by decide) p (sat_cons (step1132 p h) (sat_cons (step2330 p h) (sat_cons (step1156 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1146 p h) (sat_cons (step2042 p h) (sat_cons (step2695 p h) (sat_cons (step1137 p h) (sat_cons (step66 p h) (sat_nil p)))))))))))
def c2802 : List Lit := [(1744, true), (1790, true), (1776, false), (95, true), (96, true), (93, true)]
theorem step2802 (p : Nat → Bool) (h : Constraints p) : clause p c2802 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1440, c1442, c1438, c1434, c2774] c2802 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1440 p h) (sat_cons (step1442 p h) (sat_cons (step1438 p h) (sat_cons (step1434 p h) (sat_cons (step2774 p h) (sat_nil p)))))))
def c2803 : List Lit := [(1597, true), (1773, true), (1579, false), (15, false), (44, true), (93, true)]
theorem step2803 (p : Nat → Bool) (h : Constraints p) : clause p c2803 = true :=
  Snake9.LocalRup.prove_clause [c2330, c2801, c1138, c1139, c2793, c2042, c2695, c1133, c66, c1160, c1135, c1143] c2803 (by decide) p (sat_cons (step2330 p h) (sat_cons (step2801 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step2793 p h) (sat_cons (step2042 p h) (sat_cons (step2695 p h) (sat_cons (step1133 p h) (sat_cons (step66 p h) (sat_cons (step1160 p h) (sat_cons (step1135 p h) (sat_cons (step1143 p h) (sat_nil p)))))))))))))
def c2804 : List Lit := [(1707, true), (97, false), (1656, true), (30, false), (62, true), (81, true)]
theorem step2804 (p : Nat → Bool) (h : Constraints p) : clause p c2804 = true :=
  Snake9.LocalRup.prove_clause [c1369, c1370, c2727, c641, c1251, c1256, c1247, c211, c237, c2091] c2804 (by decide) p (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step2727 p h) (sat_cons (step641 p h) (sat_cons (step1251 p h) (sat_cons (step1256 p h) (sat_cons (step1247 p h) (sat_cons (step211 p h) (sat_cons (step237 p h) (sat_cons (step2091 p h) (sat_nil p)))))))))))
def c2805 : List Lit := [(1773, true), (91, false), (97, false), (1774, true), (96, false)]
theorem step2805 (p : Nat → Bool) (h : Constraints p) : clause p c2805 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1522, c545, c2771, c588] c2805 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step545 p h) (sat_cons (step2771 p h) (sat_cons (step588 p h) (sat_nil p))))))
def c2806 : List Lit := [(1597, true), (1583, false), (1588, false), (88, false), (91, false), (96, false), (93, true)]
theorem step2806 (p : Nat → Bool) (h : Constraints p) : clause p c2806 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1156, c1160, c1144, c1865, c1136, c2463, c2797, c1127] c2806 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1156 p h) (sat_cons (step1160 p h) (sat_cons (step1144 p h) (sat_cons (step1865 p h) (sat_cons (step1136 p h) (sat_cons (step2463 p h) (sat_cons (step2797 p h) (sat_cons (step1127 p h) (sat_nil p))))))))))
def c2807 : List Lit := [(1773, true), (30, false), (88, false), (97, false)]
theorem step2807 (p : Nat → Bool) (h : Constraints p) : clause p c2807 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1522, c646, c543, c434, c2135] c2807 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step646 p h) (sat_cons (step543 p h) (sat_cons (step434 p h) (sat_cons (step2135 p h) (sat_nil p)))))))
def c2808 : List Lit := [(1783, true), (108, false), (96, false), (93, true)]
theorem step2808 (p : Nat → Bool) (h : Constraints p) : clause p c2808 = true :=
  Snake9.LocalRup.prove_clause [c1540, c1987, c1533, c634] c2808 (by decide) p (sat_cons (step1540 p h) (sat_cons (step1987 p h) (sat_cons (step1533 p h) (sat_cons (step634 p h) (sat_nil p)))))
def c2809 : List Lit := [(104, true), (1784, true), (106, true), (95, false), (93, true)]
theorem step2809 (p : Nat → Bool) (h : Constraints p) : clause p c2809 = true :=
  Snake9.LocalRup.prove_clause [c1543, c1532, c1534, c1541, c2138, c1536, c616] c2809 (by decide) p (sat_cons (step1543 p h) (sat_cons (step1532 p h) (sat_cons (step1534 p h) (sat_cons (step1541 p h) (sat_cons (step2138 p h) (sat_cons (step1536 p h) (sat_cons (step616 p h) (sat_nil p))))))))
def c2810 : List Lit := [(104, false), (1812, true), (66, false), (97, false), (123, true), (95, false)]
theorem step2810 (p : Nat → Bool) (h : Constraints p) : clause p c2810 = true :=
  Snake9.LocalRup.prove_clause [c657, c494, c2278, c2142] c2810 (by decide) p (sat_cons (step657 p h) (sat_cons (step494 p h) (sat_cons (step2278 p h) (sat_cons (step2142 p h) (sat_nil p)))))
def c2811 : List Lit := [(88, false), (102, true), (100, false), (101, false), (97, false)]
theorem step2811 (p : Nat → Bool) (h : Constraints p) : clause p c2811 = true :=
  Snake9.LocalRup.prove_clause [c543, c434, c2136] c2811 (by decide) p (sat_cons (step543 p h) (sat_cons (step434 p h) (sat_cons (step2136 p h) (sat_nil p))))
def c2812 : List Lit := [(1739, true), (1773, true)]
theorem step2812 (p : Nat → Bool) (h : Constraints p) : clause p c2812 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1434, c2759] c2812 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step2759 p h) (sat_nil p))))
def c2813 : List Lit := [(1784, true), (104, true), (100, false), (95, false), (96, false), (93, true)]
theorem step2813 (p : Nat → Bool) (h : Constraints p) : clause p c2813 = true :=
  Snake9.LocalRup.prove_clause [c1543, c2809, c1534, c631] c2813 (by decide) p (sat_cons (step1543 p h) (sat_cons (step2809 p h) (sat_cons (step1534 p h) (sat_cons (step631 p h) (sat_nil p)))))
def c2814 : List Lit := [(91, true), (66, false), (1782, true), (1773, true), (1744, true)]
theorem step2814 (p : Nat → Bool) (h : Constraints p) : clause p c2814 = true :=
  Snake9.LocalRup.prove_clause [c1522, c1521, c1444, c2261, c1435, c1537, c543, c2661, c661, c2133] c2814 (by decide) p (sat_cons (step1522 p h) (sat_cons (step1521 p h) (sat_cons (step1444 p h) (sat_cons (step2261 p h) (sat_cons (step1435 p h) (sat_cons (step1537 p h) (sat_cons (step543 p h) (sat_cons (step2661 p h) (sat_cons (step661 p h) (sat_cons (step2133 p h) (sat_nil p)))))))))))
def c2815 : List Lit := [(1739, true), (62, false), (1776, true), (96, false)]
theorem step2815 (p : Nat → Bool) (h : Constraints p) : clause p c2815 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1434, c416, c2772] c2815 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step416 p h) (sat_cons (step2772 p h) (sat_nil p)))))
def c2816 : List Lit := [(91, true), (1854, true), (1779, false), (1744, true), (1818, false), (1776, false), (1725, false), (1736, false)]
theorem step2816 (p : Nat → Bool) (h : Constraints p) : clause p c2816 = true :=
  Snake9.LocalRup.prove_clause [c1433, c2261, c1441, c1535, c1457, c1541, c1493, c1557, c1698, c1649] c2816 (by decide) p (sat_cons (step1433 p h) (sat_cons (step2261 p h) (sat_cons (step1441 p h) (sat_cons (step1535 p h) (sat_cons (step1457 p h) (sat_cons (step1541 p h) (sat_cons (step1493 p h) (sat_cons (step1557 p h) (sat_cons (step1698 p h) (sat_cons (step1649 p h) (sat_nil p)))))))))))
def c2817 : List Lit := [(1784, true), (1741, true), (96, false), (93, true)]
theorem step2817 (p : Nat → Bool) (h : Constraints p) : clause p c2817 = true :=
  Snake9.LocalRup.prove_clause [c1437, c1436, c2122, c492, c1532, c1543, c2809, c1541, c1534, c1536, c634] c2817 (by decide) p (sat_cons (step1437 p h) (sat_cons (step1436 p h) (sat_cons (step2122 p h) (sat_cons (step492 p h) (sat_cons (step1532 p h) (sat_cons (step1543 p h) (sat_cons (step2809 p h) (sat_cons (step1541 p h) (sat_cons (step1534 p h) (sat_cons (step1536 p h) (sat_cons (step634 p h) (sat_nil p))))))))))))
def c2818 : List Lit := [(1783, true), (96, false), (93, true)]
theorem step2818 (p : Nat → Bool) (h : Constraints p) : clause p c2818 = true :=
  Snake9.LocalRup.prove_clause [c1538, c2808, c1536] c2818 (by decide) p (sat_cons (step1538 p h) (sat_cons (step2808 p h) (sat_cons (step1536 p h) (sat_nil p))))
def c2819 : List Lit := [(1773, true), (1596, true), (1597, true), (96, false), (15, false), (44, true), (93, true)]
theorem step2819 (p : Nat → Bool) (h : Constraints p) : clause p c2819 = true :=
  Snake9.LocalRup.prove_clause [c1522, c2803, c1978, c1862, c1864, c2795, c1155] c2819 (by decide) p (sat_cons (step1522 p h) (sat_cons (step2803 p h) (sat_cons (step1978 p h) (sat_cons (step1862 p h) (sat_cons (step1864 p h) (sat_cons (step2795 p h) (sat_cons (step1155 p h) (sat_nil p))))))))
def c2820 : List Lit := [(1580, true), (96, false), (93, true)]
theorem step2820 (p : Nat → Bool) (h : Constraints p) : clause p c2820 = true :=
  Snake9.LocalRup.prove_clause [c1125, c1126, c2031, c56] c2820 (by decide) p (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step2031 p h) (sat_cons (step56 p h) (sat_nil p)))))
def c2821 : List Lit := [(1779, true), (98, true), (95, false), (93, true)]
theorem step2821 (p : Nat → Bool) (h : Constraints p) : clause p c2821 = true :=
  Snake9.LocalRup.prove_clause [c1532, c1533, c615, c2140] c2821 (by decide) p (sat_cons (step1532 p h) (sat_cons (step1533 p h) (sat_cons (step615 p h) (sat_cons (step2140 p h) (sat_nil p)))))
def c2822 : List Lit := [(91, false), (18, false), (1776, true), (96, true)]
theorem step2822 (p : Nat → Bool) (h : Constraints p) : clause p c2822 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1527, c1522, c2697, c401] c2822 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1527 p h) (sat_cons (step1522 p h) (sat_cons (step2697 p h) (sat_cons (step401 p h) (sat_nil p))))))
def c2823 : List Lit := [(1741, true), (97, false), (93, true)]
theorem step2823 (p : Nat → Bool) (h : Constraints p) : clause p c2823 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1437, c2794] c2823 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step2794 p h) (sat_nil p))))
def c2824 : List Lit := [(1763, true), (1707, false), (1745, false), (1725, false), (1736, false), (80, false), (87, true), (7, false)]
theorem step2824 (p : Nat → Bool) (h : Constraints p) : clause p c2824 = true :=
  Snake9.LocalRup.prove_clause [c1377, c1459, c2636, c1496, c1502, c2753, c1408, c1373, c1378] c2824 (by decide) p (sat_cons (step1377 p h) (sat_cons (step1459 p h) (sat_cons (step2636 p h) (sat_cons (step1496 p h) (sat_cons (step1502 p h) (sat_cons (step2753 p h) (sat_cons (step1408 p h) (sat_cons (step1373 p h) (sat_cons (step1378 p h) (sat_nil p))))))))))
def c2825 : List Lit := [(88, false), (1596, true), (1776, true), (96, true)]
theorem step2825 (p : Nat → Bool) (h : Constraints p) : clause p c2825 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1527, c1522, c2730, c2417, c1892, c1139] c2825 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1527 p h) (sat_cons (step1522 p h) (sat_cons (step2730 p h) (sat_cons (step2417 p h) (sat_cons (step1892 p h) (sat_cons (step1139 p h) (sat_nil p))))))))
def c2826 : List Lit := [(1588, false), (1596, true), (93, true)]
theorem step2826 (p : Nat → Bool) (h : Constraints p) : clause p c2826 = true :=
  Snake9.LocalRup.prove_clause [c1868, c1141, c1144, c1155, c1136, c1864, c2793] c2826 (by decide) p (sat_cons (step1868 p h) (sat_cons (step1141 p h) (sat_cons (step1144 p h) (sat_cons (step1155 p h) (sat_cons (step1136 p h) (sat_cons (step1864 p h) (sat_cons (step2793 p h) (sat_nil p))))))))
def c2827 : List Lit := [(108, true), (1784, true), (1800, true), (123, true), (1812, true), (97, false), (93, true)]
theorem step2827 (p : Nat → Bool) (h : Constraints p) : clause p c2827 = true :=
  Snake9.LocalRup.prove_clause [c1539, c1536, c1537, c1541, c2738, c1532] c2827 (by decide) p (sat_cons (step1539 p h) (sat_cons (step1536 p h) (sat_cons (step1537 p h) (sat_cons (step1541 p h) (sat_cons (step2738 p h) (sat_cons (step1532 p h) (sat_nil p)))))))
def c2828 : List Lit := [(21, true), (26, false), (27, false), (1596, true)]
theorem step2828 (p : Nat → Bool) (h : Constraints p) : clause p c2828 = true :=
  Snake9.LocalRup.prove_clause [c1868, c1146, c1136, c1137, c1143, c70, c1155, c1862, c1132] c2828 (by decide) p (sat_cons (step1868 p h) (sat_cons (step1146 p h) (sat_cons (step1136 p h) (sat_cons (step1137 p h) (sat_cons (step1143 p h) (sat_cons (step70 p h) (sat_cons (step1155 p h) (sat_cons (step1862 p h) (sat_cons (step1132 p h) (sat_nil p))))))))))
def c2829 : List Lit := [(90, false), (94, false), (103, false), (66, false), (30, false), (108, false), (97, false), (93, true)]
theorem step2829 (p : Nat → Bool) (h : Constraints p) : clause p c2829 = true :=
  Snake9.LocalRup.prove_clause [c648, c526, c529, c2043, c2090, c2741] c2829 (by decide) p (sat_cons (step648 p h) (sat_cons (step526 p h) (sat_cons (step529 p h) (sat_cons (step2043 p h) (sat_cons (step2090 p h) (sat_cons (step2741 p h) (sat_nil p)))))))
def c2830 : List Lit := [(100, false), (90, true), (108, false), (91, false), (53, false)]
theorem step2830 (p : Nat → Bool) (h : Constraints p) : clause p c2830 = true :=
  Snake9.LocalRup.prove_clause [c411, c589, c2121] c2830 (by decide) p (sat_cons (step411 p h) (sat_cons (step589 p h) (sat_cons (step2121 p h) (sat_nil p))))
def c2831 : List Lit := [(101, false), (66, false), (108, false), (91, false), (97, false)]
theorem step2831 (p : Nat → Bool) (h : Constraints p) : clause p c2831 = true :=
  Snake9.LocalRup.prove_clause [c591, c2268] c2831 (by decide) p (sat_cons (step591 p h) (sat_cons (step2268 p h) (sat_nil p)))
def c2832 : List Lit := [(1829, true), (1817, false), (1776, false), (1771, false), (93, true)]
theorem step2832 (p : Nat → Bool) (h : Constraints p) : clause p c2832 = true :=
  Snake9.LocalRup.prove_clause [c2754, c1641, c1560, c1556, c1528, c2696, c2731, c1523, c2414] c2832 (by decide) p (sat_cons (step2754 p h) (sat_cons (step1641 p h) (sat_cons (step1560 p h) (sat_cons (step1556 p h) (sat_cons (step1528 p h) (sat_cons (step2696 p h) (sat_cons (step2731 p h) (sat_cons (step1523 p h) (sat_cons (step2414 p h) (sat_nil p))))))))))
def c2833 : List Lit := [(1739, true), (1830, true), (114, true), (1783, false), (113, false), (123, false), (96, true), (1810, false)]
theorem step2833 (p : Nat → Bool) (h : Constraints p) : clause p c2833 = true :=
  Snake9.LocalRup.prove_clause [c2233, c1654, c1566, c1433, c1434, c418, c2716, c2737] c2833 (by decide) p (sat_cons (step2233 p h) (sat_cons (step1654 p h) (sat_cons (step1566 p h) (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step418 p h) (sat_cons (step2716 p h) (sat_cons (step2737 p h) (sat_nil p)))))))))
def c2834 : List Lit := [(1784, true), (100, false), (109, true), (93, true)]
theorem step2834 (p : Nat → Bool) (h : Constraints p) : clause p c2834 = true :=
  Snake9.LocalRup.prove_clause [c1535, c2745, c1541, c539, c1533] c2834 (by decide) p (sat_cons (step1535 p h) (sat_cons (step2745 p h) (sat_cons (step1541 p h) (sat_cons (step539 p h) (sat_cons (step1533 p h) (sat_nil p))))))
def c2835 : List Lit := [(1707, false), (1737, true), (1726, true), (80, false), (87, true), (7, false)]
theorem step2835 (p : Nat → Bool) (h : Constraints p) : clause p c2835 = true :=
  Snake9.LocalRup.prove_clause [c2636, c1408, c1377, c1378, c1404, c1373, c2700] c2835 (by decide) p (sat_cons (step2636 p h) (sat_cons (step1408 p h) (sat_cons (step1377 p h) (sat_cons (step1378 p h) (sat_cons (step1404 p h) (sat_cons (step1373 p h) (sat_cons (step2700 p h) (sat_nil p))))))))
def c2836 : List Lit := [(21, true), (27, false), (1596, true), (15, true)]
theorem step2836 (p : Nat → Bool) (h : Constraints p) : clause p c2836 = true :=
  Snake9.LocalRup.prove_clause [c1868, c1146, c1137, c2828, c2035] c2836 (by decide) p (sat_cons (step1868 p h) (sat_cons (step1146 p h) (sat_cons (step1137 p h) (sat_cons (step2828 p h) (sat_cons (step2035 p h) (sat_nil p))))))
def c2837 : List Lit := [(1596, true), (15, true), (93, true)]
theorem step2837 (p : Nat → Bool) (h : Constraints p) : clause p c2837 = true :=
  Snake9.LocalRup.prove_clause [c1159, c2826, c1139, c2836, c2793, c1864, c1133, c1155, c1862, c1143, c2026, c70, c1135] c2837 (by decide) p (sat_cons (step1159 p h) (sat_cons (step2826 p h) (sat_cons (step1139 p h) (sat_cons (step2836 p h) (sat_cons (step2793 p h) (sat_cons (step1864 p h) (sat_cons (step1133 p h) (sat_cons (step1155 p h) (sat_cons (step1862 p h) (sat_cons (step1143 p h) (sat_cons (step2026 p h) (sat_cons (step70 p h) (sat_cons (step1135 p h) (sat_nil p))))))))))))))
def c2838 : List Lit := [(108, false), (102, false), (91, false), (1774, true)]
theorem step2838 (p : Nat → Bool) (h : Constraints p) : clause p c2838 = true :=
  Snake9.LocalRup.prove_clause [c591, c589, c1523] c2838 (by decide) p (sat_cons (step591 p h) (sat_cons (step589 p h) (sat_cons (step1523 p h) (sat_nil p))))
def c2839 : List Lit := [(1829, true), (108, true), (97, false), (1788, false), (1775, false), (1811, false), (123, true), (93, true)]
theorem step2839 (p : Nat → Bool) (h : Constraints p) : clause p c2839 = true :=
  Snake9.LocalRup.prove_clause [c2234, c1641, c1635, c1552, c2235, c1613, c2827] c2839 (by decide) p (sat_cons (step2234 p h) (sat_cons (step1641 p h) (sat_cons (step1635 p h) (sat_cons (step1552 p h) (sat_cons (step2235 p h) (sat_cons (step1613 p h) (sat_cons (step2827 p h) (sat_nil p))))))))
end B112E050
