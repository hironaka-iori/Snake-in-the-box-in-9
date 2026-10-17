import B112E052Part0009
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2630 : List Lit := [(1648, true), (1641, false), (88, true), (87, false)]
theorem step2630 (p : Nat → Bool) (h : Constraints p) : clause p c2630 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1416, c1419, c1410, c1393, c1395, c1402, c1390, c1391, c1387, c259, c211, c2266, c230] c2630 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1416 p h) (sat_cons (step1419 p h) (sat_cons (step1410 p h) (sat_cons (step1393 p h) (sat_cons (step1395 p h) (sat_cons (step1402 p h) (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step1387 p h) (sat_cons (step259 p h) (sat_cons (step211 p h) (sat_cons (step2266 p h) (sat_cons (step230 p h) (sat_nil p)))))))))))))))
def c2631 : List Lit := [(1619, true), (44, false), (122, false)]
theorem step2631 (p : Nat → Bool) (h : Constraints p) : clause p c2631 = true :=
  Snake9.LocalRup.prove_clause [c1363, c1364, c1361, c1357, c195] c2631 (by decide) p (sat_cons (step1363 p h) (sat_cons (step1364 p h) (sat_cons (step1361 p h) (sat_cons (step1357 p h) (sat_cons (step195 p h) (sat_nil p))))))
def c2632 : List Lit := [(36, false), (3, false), (39, false), (46, false)]
theorem step2632 (p : Nat → Bool) (h : Constraints p) : clause p c2632 = true :=
  Snake9.LocalRup.prove_clause [c153, c158, c2244] c2632 (by decide) p (sat_cons (step153 p h) (sat_cons (step158 p h) (sat_cons (step2244 p h) (sat_nil p))))
def c2633 : List Lit := [(38, true), (63, false), (4, false), (3, false), (8, false), (52, false), (56, false)]
theorem step2633 (p : Nat → Bool) (h : Constraints p) : clause p c2633 = true :=
  Snake9.LocalRup.prove_clause [c2201, c2203, c251, c23, c2282] c2633 (by decide) p (sat_cons (step2201 p h) (sat_cons (step2203 p h) (sat_cons (step251 p h) (sat_cons (step23 p h) (sat_cons (step2282 p h) (sat_nil p))))))
def c2634 : List Lit := [(1585, true), (101, true), (44, true), (1569, false), (1571, false)]
theorem step2634 (p : Nat → Bool) (h : Constraints p) : clause p c2634 = true :=
  Snake9.LocalRup.prove_clause [c2423, c1304, c1280, c2547, c1272] c2634 (by decide) p (sat_cons (step2423 p h) (sat_cons (step1304 p h) (sat_cons (step1280 p h) (sat_cons (step2547 p h) (sat_cons (step1272 p h) (sat_nil p))))))
def c2635 : List Lit := [(114, false), (92, false), (54, false), (148, true), (21, false), (20, true)]
theorem step2635 (p : Nat → Bool) (h : Constraints p) : clause p c2635 = true :=
  Snake9.LocalRup.prove_clause [c560, c541, c75] c2635 (by decide) p (sat_cons (step560 p h) (sat_cons (step541 p h) (sat_cons (step75 p h) (sat_nil p))))
def c2636 : List Lit := [(1705, true), (79, false), (311, false)]
theorem step2636 (p : Nat → Bool) (h : Constraints p) : clause p c2636 = true :=
  Snake9.LocalRup.prove_clause [c1081, c1137, c2421, c1240, c1183, c1158, c1155, c1149, c1147, c1181, c1179, c1167, c1163, c1162, c2400, c1055, c1051, c1048, c1044, c2212, c1549, c1550, c376, c379, c353, c2310, c2309, c1957, c433] c2636 (by decide) p (sat_cons (step1081 p h) (sat_cons (step1137 p h) (sat_cons (step2421 p h) (sat_cons (step1240 p h) (sat_cons (step1183 p h) (sat_cons (step1158 p h) (sat_cons (step1155 p h) (sat_cons (step1149 p h) (sat_cons (step1147 p h) (sat_cons (step1181 p h) (sat_cons (step1179 p h) (sat_cons (step1167 p h) (sat_cons (step1163 p h) (sat_cons (step1162 p h) (sat_cons (step2400 p h) (sat_cons (step1055 p h) (sat_cons (step1051 p h) (sat_cons (step1048 p h) (sat_cons (step1044 p h) (sat_cons (step2212 p h) (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step376 p h) (sat_cons (step379 p h) (sat_cons (step353 p h) (sat_cons (step2310 p h) (sat_cons (step2309 p h) (sat_cons (step1957 p h) (sat_cons (step433 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2637 : List Lit := [(1769, false), (1776, true), (87, false)]
theorem step2637 (p : Nat → Bool) (h : Constraints p) : clause p c2637 = true :=
  Snake9.LocalRup.prove_clause [c1714, c1705, c1708, c1718, c1699, c1691, c1693, c2621, c1689, c1685, c690] c2637 (by decide) p (sat_cons (step1714 p h) (sat_cons (step1705 p h) (sat_cons (step1708 p h) (sat_cons (step1718 p h) (sat_cons (step1699 p h) (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step2621 p h) (sat_cons (step1689 p h) (sat_cons (step1685 p h) (sat_cons (step690 p h) (sat_nil p))))))))))))
def c2638 : List Lit := [(100, false), (103, false), (107, false), (89, true), (98, true)]
theorem step2638 (p : Nat → Bool) (h : Constraints p) : clause p c2638 = true :=
  Snake9.LocalRup.prove_clause [c2340, c762] c2638 (by decide) p (sat_cons (step2340 p h) (sat_cons (step762 p h) (sat_nil p)))
def c2639 : List Lit := [(1761, false), (1788, false), (122, true), (1811, true)]
theorem step2639 (p : Nat → Bool) (h : Constraints p) : clause p c2639 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1758, c1774, c1799, c1722, c1691, c1694, c1717, c1718, c1686, c1793, c1707, c1775, c1699, c1700, c2592, c759] c2639 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1758 p h) (sat_cons (step1774 p h) (sat_cons (step1799 p h) (sat_cons (step1722 p h) (sat_cons (step1691 p h) (sat_cons (step1694 p h) (sat_cons (step1717 p h) (sat_cons (step1718 p h) (sat_cons (step1686 p h) (sat_cons (step1793 p h) (sat_cons (step1707 p h) (sat_cons (step1775 p h) (sat_cons (step1699 p h) (sat_cons (step1700 p h) (sat_cons (step2592 p h) (sat_cons (step759 p h) (sat_nil p))))))))))))))))))
def c2640 : List Lit := [(1785, true), (106, true), (1796, true), (113, false), (35, false)]
theorem step2640 (p : Nat → Bool) (h : Constraints p) : clause p c2640 = true :=
  Snake9.LocalRup.prove_clause [c1761, c1739, c1740, c837, c1751, c1752, c1759, c1753, c2108, c952, c2389] c2640 (by decide) p (sat_cons (step1761 p h) (sat_cons (step1739 p h) (sat_cons (step1740 p h) (sat_cons (step837 p h) (sat_cons (step1751 p h) (sat_cons (step1752 p h) (sat_cons (step1759 p h) (sat_cons (step1753 p h) (sat_cons (step2108 p h) (sat_cons (step952 p h) (sat_cons (step2389 p h) (sat_nil p))))))))))))
def c2641 : List Lit := [(1788, false), (1801, true), (110, true), (1783, false), (1811, true), (113, false), (35, false)]
theorem step2641 (p : Nat → Bool) (h : Constraints p) : clause p c2641 = true :=
  Snake9.LocalRup.prove_clause [c2537, c1774, c2544] c2641 (by decide) p (sat_cons (step2537 p h) (sat_cons (step1774 p h) (sat_cons (step2544 p h) (sat_nil p))))
def c2642 : List Lit := [(120, false), (121, true), (1769, false), (122, true), (1811, true), (1787, false)]
theorem step2642 (p : Nat → Bool) (h : Constraints p) : clause p c2642 = true :=
  Snake9.LocalRup.prove_clause [c1705, c1713, c1793, c1771, c2372, c2374, c1988, c1752, c1761, c1762, c1770, c1753, c1799, c950, c1714, c1700, c1708] c2642 (by decide) p (sat_cons (step1705 p h) (sat_cons (step1713 p h) (sat_cons (step1793 p h) (sat_cons (step1771 p h) (sat_cons (step2372 p h) (sat_cons (step2374 p h) (sat_cons (step1988 p h) (sat_cons (step1752 p h) (sat_cons (step1761 p h) (sat_cons (step1762 p h) (sat_cons (step1770 p h) (sat_cons (step1753 p h) (sat_cons (step1799 p h) (sat_cons (step950 p h) (sat_cons (step1714 p h) (sat_cons (step1700 p h) (sat_cons (step1708 p h) (sat_nil p))))))))))))))))))
def c2643 : List Lit := [(1783, true), (1811, true), (113, false), (35, false), (69, false)]
theorem step2643 (p : Nat → Bool) (h : Constraints p) : clause p c2643 = true :=
  Snake9.LocalRup.prove_clause [c2593, c1736, c1737, c832, c835, c836, c810, c812, c1702, c1751, c2364, c2366, c1705, c1758, c1969, c870, c1713, c1211, c1793, c1212, c1219, c2418, c1226, c1222, c1221, c909, c2642, c1741, c1743, c1774, c2639, c1775, c1799, c1688, c2093, c1759, c1714, c1754, c1708, c728, c1699] c2643 (by decide) p (sat_cons (step2593 p h) (sat_cons (step1736 p h) (sat_cons (step1737 p h) (sat_cons (step832 p h) (sat_cons (step835 p h) (sat_cons (step836 p h) (sat_cons (step810 p h) (sat_cons (step812 p h) (sat_cons (step1702 p h) (sat_cons (step1751 p h) (sat_cons (step2364 p h) (sat_cons (step2366 p h) (sat_cons (step1705 p h) (sat_cons (step1758 p h) (sat_cons (step1969 p h) (sat_cons (step870 p h) (sat_cons (step1713 p h) (sat_cons (step1211 p h) (sat_cons (step1793 p h) (sat_cons (step1212 p h) (sat_cons (step1219 p h) (sat_cons (step2418 p h) (sat_cons (step1226 p h) (sat_cons (step1222 p h) (sat_cons (step1221 p h) (sat_cons (step909 p h) (sat_cons (step2642 p h) (sat_cons (step1741 p h) (sat_cons (step1743 p h) (sat_cons (step1774 p h) (sat_cons (step2639 p h) (sat_cons (step1775 p h) (sat_cons (step1799 p h) (sat_cons (step1688 p h) (sat_cons (step2093 p h) (sat_cons (step1759 p h) (sat_cons (step1714 p h) (sat_cons (step1754 p h) (sat_cons (step1708 p h) (sat_cons (step728 p h) (sat_cons (step1699 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c2644 : List Lit := [(122, true), (124, false), (106, true), (1797, true), (1802, true), (103, false), (1783, false)]
theorem step2644 (p : Nat → Bool) (h : Constraints p) : clause p c2644 = true :=
  Snake9.LocalRup.prove_clause [c2592, c1775, c1745, c1739, c950, c949, c1753, c1752, c1762] c2644 (by decide) p (sat_cons (step2592 p h) (sat_cons (step1775 p h) (sat_cons (step1745 p h) (sat_cons (step1739 p h) (sat_cons (step950 p h) (sat_cons (step949 p h) (sat_cons (step1753 p h) (sat_cons (step1752 p h) (sat_cons (step1762 p h) (sat_nil p))))))))))
def c2645 : List Lit := [(1769, false), (1776, true), (1783, false), (1811, true), (113, false), (35, false)]
theorem step2645 (p : Nat → Bool) (h : Constraints p) : clause p c2645 = true :=
  Snake9.LocalRup.prove_clause [c1714, c2593, c1705, c1708, c1713, c1718, c1699, c1700, c2544, c1793, c1691, c1779, c1771, c1688, c1689, c1746, c714, c762, c2346, c2644, c837, c1740, c1741, c1745, c950, c949, c1775, c1753, c1750, c1759] c2645 (by decide) p (sat_cons (step1714 p h) (sat_cons (step2593 p h) (sat_cons (step1705 p h) (sat_cons (step1708 p h) (sat_cons (step1713 p h) (sat_cons (step1718 p h) (sat_cons (step1699 p h) (sat_cons (step1700 p h) (sat_cons (step2544 p h) (sat_cons (step1793 p h) (sat_cons (step1691 p h) (sat_cons (step1779 p h) (sat_cons (step1771 p h) (sat_cons (step1688 p h) (sat_cons (step1689 p h) (sat_cons (step1746 p h) (sat_cons (step714 p h) (sat_cons (step762 p h) (sat_cons (step2346 p h) (sat_cons (step2644 p h) (sat_cons (step837 p h) (sat_cons (step1740 p h) (sat_cons (step1741 p h) (sat_cons (step1745 p h) (sat_cons (step950 p h) (sat_cons (step949 p h) (sat_cons (step1775 p h) (sat_cons (step1753 p h) (sat_cons (step1750 p h) (sat_cons (step1759 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2646 : List Lit := [(1796, true), (118, true), (122, true), (1768, true), (1783, false), (1811, true)]
theorem step2646 (p : Nat → Bool) (h : Constraints p) : clause p c2646 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1745, c2639, c1689, c1751, c1758, c1761, c1759, c1752, c1753, c2108, c2134, c2389, c2592, c952, c1700, c1741, c1707, c1746, c1713, c1779, c1793] c2646 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1745 p h) (sat_cons (step2639 p h) (sat_cons (step1689 p h) (sat_cons (step1751 p h) (sat_cons (step1758 p h) (sat_cons (step1761 p h) (sat_cons (step1759 p h) (sat_cons (step1752 p h) (sat_cons (step1753 p h) (sat_cons (step2108 p h) (sat_cons (step2134 p h) (sat_cons (step2389 p h) (sat_cons (step2592 p h) (sat_cons (step952 p h) (sat_cons (step1700 p h) (sat_cons (step1741 p h) (sat_cons (step1707 p h) (sat_cons (step1746 p h) (sat_cons (step1713 p h) (sat_cons (step1779 p h) (sat_cons (step1793 p h) (sat_nil p)))))))))))))))))))))))
def c2647 : List Lit := [(1776, true), (1783, false), (1811, true), (113, false), (35, false)]
theorem step2647 (p : Nat → Bool) (h : Constraints p) : clause p c2647 = true :=
  Snake9.LocalRup.prove_clause [c1788, c1714, c1710, c2645, c1702, c834, c833, c1740, c1745, c1776, c2639, c1688, c1689, c2646, c1775, c1780, c1793, c1746, c1713, c1741, c1707, c1699, c1700, c714, c762, c2095, c2346, c1753, c949, c1762, c1752] c2647 (by decide) p (sat_cons (step1788 p h) (sat_cons (step1714 p h) (sat_cons (step1710 p h) (sat_cons (step2645 p h) (sat_cons (step1702 p h) (sat_cons (step834 p h) (sat_cons (step833 p h) (sat_cons (step1740 p h) (sat_cons (step1745 p h) (sat_cons (step1776 p h) (sat_cons (step2639 p h) (sat_cons (step1688 p h) (sat_cons (step1689 p h) (sat_cons (step2646 p h) (sat_cons (step1775 p h) (sat_cons (step1780 p h) (sat_cons (step1793 p h) (sat_cons (step1746 p h) (sat_cons (step1713 p h) (sat_cons (step1741 p h) (sat_cons (step1707 p h) (sat_cons (step1699 p h) (sat_cons (step1700 p h) (sat_cons (step714 p h) (sat_cons (step762 p h) (sat_cons (step2095 p h) (sat_cons (step2346 p h) (sat_cons (step1753 p h) (sat_cons (step949 p h) (sat_cons (step1762 p h) (sat_cons (step1752 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2648 : List Lit := [(122, true), (1783, false), (1811, true), (113, false), (35, false)]
theorem step2648 (p : Nat → Bool) (h : Constraints p) : clause p c2648 = true :=
  Snake9.LocalRup.prove_clause [c2593, c2647, c1799, c1770, c1761, c1751, c1752, c1758, c1759, c1769, c1774, c1753, c1805, c1745, c2108, c1715, c1739, c1740, c2640, c952, c833, c2107, c2380, c1709, c897, c1704] c2648 (by decide) p (sat_cons (step2593 p h) (sat_cons (step2647 p h) (sat_cons (step1799 p h) (sat_cons (step1770 p h) (sat_cons (step1761 p h) (sat_cons (step1751 p h) (sat_cons (step1752 p h) (sat_cons (step1758 p h) (sat_cons (step1759 p h) (sat_cons (step1769 p h) (sat_cons (step1774 p h) (sat_cons (step1753 p h) (sat_cons (step1805 p h) (sat_cons (step1745 p h) (sat_cons (step2108 p h) (sat_cons (step1715 p h) (sat_cons (step1739 p h) (sat_cons (step1740 p h) (sat_cons (step2640 p h) (sat_cons (step952 p h) (sat_cons (step833 p h) (sat_cons (step2107 p h) (sat_cons (step2380 p h) (sat_cons (step1709 p h) (sat_cons (step897 p h) (sat_cons (step1704 p h) (sat_nil p)))))))))))))))))))))))))))
def c2649 : List Lit := [(1783, false), (1811, true), (35, false), (113, false)]
theorem step2649 (p : Nat → Bool) (h : Constraints p) : clause p c2649 = true :=
  Snake9.LocalRup.prove_clause [c2647, c1799, c2648, c837, c834, c1740, c2641, c1745] c2649 (by decide) p (sat_cons (step2647 p h) (sat_cons (step1799 p h) (sat_cons (step2648 p h) (sat_cons (step837 p h) (sat_cons (step834 p h) (sat_cons (step1740 p h) (sat_cons (step2641 p h) (sat_cons (step1745 p h) (sat_nil p)))))))))
def c2650 : List Lit := [(1811, true), (113, false), (69, false), (35, false)]
theorem step2650 (p : Nat → Bool) (h : Constraints p) : clause p c2650 = true :=
  Snake9.LocalRup.prove_clause [c2643, c2649] c2650 (by decide) p (sat_cons (step2643 p h) (sat_cons (step2649 p h) (sat_nil p)))
def c2651 : List Lit := [(46, true), (1648, true), (101, true), (79, true)]
theorem step2651 (p : Nat → Bool) (h : Constraints p) : clause p c2651 = true :=
  Snake9.LocalRup.prove_clause [c1423, c1398, c1388, c1389, c1395, c1419, c1407, c1409, c1405, c1401, c2279, c273] c2651 (by decide) p (sat_cons (step1423 p h) (sat_cons (step1398 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1395 p h) (sat_cons (step1419 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1405 p h) (sat_cons (step1401 p h) (sat_cons (step2279 p h) (sat_cons (step273 p h) (sat_nil p)))))))))))))
def c2652 : List Lit := [(1584, true), (101, true), (44, true)]
theorem step2652 (p : Nat → Bool) (h : Constraints p) : clause p c2652 = true :=
  Snake9.LocalRup.prove_clause [c1300, c2422, c2547, c1279, c1272] c2652 (by decide) p (sat_cons (step1300 p h) (sat_cons (step2422 p h) (sat_cons (step2547 p h) (sat_cons (step1279 p h) (sat_cons (step1272 p h) (sat_nil p))))))
def c2653 : List Lit := [(63, true), (1648, true), (101, true), (79, true)]
theorem step2653 (p : Nat → Bool) (h : Constraints p) : clause p c2653 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1408, c1404, c1406, c1407, c1410, c2279, c1419, c1401, c273, c1395, c1387] c2653 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1408 p h) (sat_cons (step1404 p h) (sat_cons (step1406 p h) (sat_cons (step1407 p h) (sat_cons (step1410 p h) (sat_cons (step2279 p h) (sat_cons (step1419 p h) (sat_cons (step1401 p h) (sat_cons (step273 p h) (sat_cons (step1395 p h) (sat_cons (step1387 p h) (sat_nil p)))))))))))))
def c2654 : List Lit := [(1714, true), (81, true), (72, true), (1697, false)]
theorem step2654 (p : Nat → Bool) (h : Constraints p) : clause p c2654 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1547, c1555, c1538, c1567, c1571, c1556, c1558, c1539, c1541, c1551, c1548, c2055, c1532] c2654 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1547 p h) (sat_cons (step1555 p h) (sat_cons (step1538 p h) (sat_cons (step1567 p h) (sat_cons (step1571 p h) (sat_cons (step1556 p h) (sat_cons (step1558 p h) (sat_cons (step1539 p h) (sat_cons (step1541 p h) (sat_cons (step1551 p h) (sat_cons (step1548 p h) (sat_cons (step2055 p h) (sat_cons (step1532 p h) (sat_nil p)))))))))))))))
def c2655 : List Lit := [(107, false), (94, false), (92, true), (102, false), (66, false), (106, false)]
theorem step2655 (p : Nat → Bool) (h : Constraints p) : clause p c2655 = true :=
  Snake9.LocalRup.prove_clause [c778, c2483] c2655 (by decide) p (sat_cons (step778 p h) (sat_cons (step2483 p h) (sat_nil p)))
def c2656 : List Lit := [(55, true), (92, true), (53, false), (54, false)]
theorem step2656 (p : Nat → Bool) (h : Constraints p) : clause p c2656 = true :=
  Snake9.LocalRup.prove_clause [c2268, c2270, c1936] c2656 (by decide) p (sat_cons (step2268 p h) (sat_cons (step2270 p h) (sat_cons (step1936 p h) (sat_nil p))))
def c2657 : List Lit := [(56, true), (51, false), (1644, true), (79, true), (101, true)]
theorem step2657 (p : Nat → Bool) (h : Constraints p) : clause p c2657 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1402, c1403, c1410, c1405, c2279, c273] c2657 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step1410 p h) (sat_cons (step1405 p h) (sat_cons (step2279 p h) (sat_cons (step273 p h) (sat_nil p))))))))
def c2658 : List Lit := [(62, false), (60, false), (51, false), (79, true), (101, true)]
theorem step2658 (p : Nat → Bool) (h : Constraints p) : clause p c2658 = true :=
  Snake9.LocalRup.prove_clause [c2279, c273] c2658 (by decide) p (sat_cons (step2279 p h) (sat_cons (step273 p h) (sat_nil p)))
def c2659 : List Lit := [(1585, false), (1680, true), (1625, false), (101, true), (122, false)]
theorem step2659 (p : Nat → Bool) (h : Constraints p) : clause p c2659 = true :=
  Snake9.LocalRup.prove_clause [c1450, c1499, c2045, c1492, c1325, c1451, c2037, c2573, c1251, c1248] c2659 (by decide) p (sat_cons (step1450 p h) (sat_cons (step1499 p h) (sat_cons (step2045 p h) (sat_cons (step1492 p h) (sat_cons (step1325 p h) (sat_cons (step1451 p h) (sat_cons (step2037 p h) (sat_cons (step2573 p h) (sat_cons (step1251 p h) (sat_cons (step1248 p h) (sat_nil p)))))))))))
def c2660 : List Lit := [(1721, true), (99, false), (101, true), (100, false)]
theorem step2660 (p : Nat → Bool) (h : Constraints p) : clause p c2660 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1586, c634, c516, c2341] c2660 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1586 p h) (sat_cons (step634 p h) (sat_cons (step516 p h) (sat_cons (step2341 p h) (sat_nil p))))))
def c2661 : List Lit := [(1585, true), (88, true), (44, true), (87, false), (101, true)]
theorem step2661 (p : Nat → Bool) (h : Constraints p) : clause p c2661 = true :=
  Snake9.LocalRup.prove_clause [c2619, c2423, c1304, c2634, c1282, c2547, c1274, c1273, c46, c2217] c2661 (by decide) p (sat_cons (step2619 p h) (sat_cons (step2423 p h) (sat_cons (step1304 p h) (sat_cons (step2634 p h) (sat_cons (step1282 p h) (sat_cons (step2547 p h) (sat_cons (step1274 p h) (sat_cons (step1273 p h) (sat_cons (step46 p h) (sat_cons (step2217 p h) (sat_nil p)))))))))))
def c2662 : List Lit := [(1647, true), (1633, true), (88, true), (87, false)]
theorem step2662 (p : Nat → Bool) (h : Constraints p) : clause p c2662 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1390, c1415, c1418, c1409, c1395, c1402, c1387, c259, c230, c211, c2266] c2662 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1390 p h) (sat_cons (step1415 p h) (sat_cons (step1418 p h) (sat_cons (step1409 p h) (sat_cons (step1395 p h) (sat_cons (step1402 p h) (sat_cons (step1387 p h) (sat_cons (step259 p h) (sat_cons (step230 p h) (sat_cons (step211 p h) (sat_cons (step2266 p h) (sat_nil p)))))))))))))
def c2663 : List Lit := [(101, false), (1813, true), (113, false), (35, false), (62, false), (122, false)]
theorem step2663 (p : Nat → Bool) (h : Constraints p) : clause p c2663 = true :=
  Snake9.LocalRup.prove_clause [c836, c1737, c837, c1740, c1745, c834, c682, c683, c680, c1689, c1699, c1685, c1694, c2533] c2663 (by decide) p (sat_cons (step836 p h) (sat_cons (step1737 p h) (sat_cons (step837 p h) (sat_cons (step1740 p h) (sat_cons (step1745 p h) (sat_cons (step834 p h) (sat_cons (step682 p h) (sat_cons (step683 p h) (sat_cons (step680 p h) (sat_cons (step1689 p h) (sat_cons (step1699 p h) (sat_cons (step1685 p h) (sat_cons (step1694 p h) (sat_cons (step2533 p h) (sat_nil p)))))))))))))))
def c2664 : List Lit := [(89, false), (86, false), (87, false), (1764, true)]
theorem step2664 (p : Nat → Bool) (h : Constraints p) : clause p c2664 = true :=
  Snake9.LocalRup.prove_clause [c516, c515, c1689, c1686, c1694] c2664 (by decide) p (sat_cons (step516 p h) (sat_cons (step515 p h) (sat_cons (step1689 p h) (sat_cons (step1686 p h) (sat_cons (step1694 p h) (sat_nil p))))))
def c2665 : List Lit := [(51, false), (92, true), (53, false), (54, false), (79, true), (1644, true), (101, true)]
theorem step2665 (p : Nat → Bool) (h : Constraints p) : clause p c2665 = true :=
  Snake9.LocalRup.prove_clause [c211, c2657, c2269, c259] c2665 (by decide) p (sat_cons (step211 p h) (sat_cons (step2657 p h) (sat_cons (step2269 p h) (sat_cons (step259 p h) (sat_nil p)))))
def c2666 : List Lit := [(65, false), (58, true), (64, true), (30, false), (1813, true), (1788, false), (1783, false), (110, true), (113, false), (35, false), (66, false), (62, false)]
theorem step2666 (p : Nat → Bool) (h : Constraints p) : clause p c2666 = true :=
  Snake9.LocalRup.prove_clause [c294, c2286, c1699, c733, c732, c2533, c1689, c1686, c1694] c2666 (by decide) p (sat_cons (step294 p h) (sat_cons (step2286 p h) (sat_cons (step1699 p h) (sat_cons (step733 p h) (sat_cons (step732 p h) (sat_cons (step2533 p h) (sat_cons (step1689 p h) (sat_cons (step1686 p h) (sat_cons (step1694 p h) (sat_nil p))))))))))
def c2667 : List Lit := [(95, false), (1572, true), (54, false), (88, true)]
theorem step2667 (p : Nat → Bool) (h : Constraints p) : clause p c2667 = true :=
  Snake9.LocalRup.prove_clause [c2581, c2603] c2667 (by decide) p (sat_cons (step2581 p h) (sat_cons (step2603 p h) (sat_nil p)))
def c2668 : List Lit := [(1749, true), (1737, false), (87, true), (1713, false), (65, true), (90, true), (71, true), (79, true)]
theorem step2668 (p : Nat → Bool) (h : Constraints p) : clause p c2668 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1659, c2557, c2109] c2668 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1659 p h) (sat_cons (step2557 p h) (sat_cons (step2109 p h) (sat_nil p)))))
def c2669 : List Lit := [(1571, true), (1730, true), (53, false)]
theorem step2669 (p : Nat → Bool) (h : Constraints p) : clause p c2669 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1279, c2619, c1274, c1271, c477, c2534, c1601] c2669 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1279 p h) (sat_cons (step2619 p h) (sat_cons (step1274 p h) (sat_cons (step1271 p h) (sat_cons (step477 p h) (sat_cons (step2534 p h) (sat_cons (step1601 p h) (sat_nil p)))))))))
def c2670 : List Lit := [(30, false), (1764, true), (106, false), (65, false)]
theorem step2670 (p : Nat → Bool) (h : Constraints p) : clause p c2670 = true :=
  Snake9.LocalRup.prove_clause [c733, c732, c1689, c1686, c1694] c2670 (by decide) p (sat_cons (step733 p h) (sat_cons (step732 p h) (sat_cons (step1689 p h) (sat_cons (step1686 p h) (sat_cons (step1694 p h) (sat_nil p))))))
def c2671 : List Lit := [(1571, true), (94, false)]
theorem step2671 (p : Nat → Bool) (h : Constraints p) : clause p c2671 = true :=
  Snake9.LocalRup.prove_clause [c1277, c2534, c1274] c2671 (by decide) p (sat_cons (step1277 p h) (sat_cons (step2534 p h) (sat_cons (step1274 p h) (sat_nil p))))
def c2672 : List Lit := [(1572, true), (20, true), (102, false), (94, false)]
theorem step2672 (p : Nat → Bool) (h : Constraints p) : clause p c2672 = true :=
  Snake9.LocalRup.prove_clause [c1274, c1278, c1280, c1276, c1272, c547, c59, c2220] c2672 (by decide) p (sat_cons (step1274 p h) (sat_cons (step1278 p h) (sat_cons (step1280 p h) (sat_cons (step1276 p h) (sat_cons (step1272 p h) (sat_cons (step547 p h) (sat_cons (step59 p h) (sat_cons (step2220 p h) (sat_nil p)))))))))
def c2673 : List Lit := [(18, false), (15, false), (92, true), (94, false)]
theorem step2673 (p : Nat → Bool) (h : Constraints p) : clause p c2673 = true :=
  Snake9.LocalRup.prove_clause [c59, c2220] c2673 (by decide) p (sat_cons (step59 p h) (sat_cons (step2220 p h) (sat_nil p)))
def c2674 : List Lit := [(1626, true), (46, false), (1617, false), (42, true), (3, false), (35, true)]
theorem step2674 (p : Nat → Bool) (h : Constraints p) : clause p c2674 = true :=
  Snake9.LocalRup.prove_clause [c1357, c1365, c1347, c1349, c1375, c1378, c1368, c1350, c1359, c1348, c2632] c2674 (by decide) p (sat_cons (step1357 p h) (sat_cons (step1365 p h) (sat_cons (step1347 p h) (sat_cons (step1349 p h) (sat_cons (step1375 p h) (sat_cons (step1378 p h) (sat_cons (step1368 p h) (sat_cons (step1350 p h) (sat_cons (step1359 p h) (sat_cons (step1348 p h) (sat_cons (step2632 p h) (sat_nil p))))))))))))
def c2675 : List Lit := [(72, true), (65, true), (1714, true), (1697, false)]
theorem step2675 (p : Nat → Bool) (h : Constraints p) : clause p c2675 = true :=
  Snake9.LocalRup.prove_clause [c1533, c1541, c1571, c1557, c1547, c1548, c1554, c1555, c1574, c1550, c1544, c1542, c2055, c1534] c2675 (by decide) p (sat_cons (step1533 p h) (sat_cons (step1541 p h) (sat_cons (step1571 p h) (sat_cons (step1557 p h) (sat_cons (step1547 p h) (sat_cons (step1548 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step1574 p h) (sat_cons (step1550 p h) (sat_cons (step1544 p h) (sat_cons (step1542 p h) (sat_cons (step2055 p h) (sat_cons (step1534 p h) (sat_nil p)))))))))))))))
def c2676 : List Lit := [(72, false), (56, false), (1562, true), (63, false)]
theorem step2676 (p : Nat → Bool) (h : Constraints p) : clause p c2676 = true :=
  Snake9.LocalRup.prove_clause [c2037, c1253, c1247, c1264, c2034, c2030, c402, c2501] c2676 (by decide) p (sat_cons (step2037 p h) (sat_cons (step1253 p h) (sat_cons (step1247 p h) (sat_cons (step1264 p h) (sat_cons (step2034 p h) (sat_cons (step2030 p h) (sat_cons (step402 p h) (sat_cons (step2501 p h) (sat_nil p)))))))))
def c2677 : List Lit := [(1714, true), (72, true), (56, false), (1697, false), (8, false), (63, false)]
theorem step2677 (p : Nat → Bool) (h : Constraints p) : clause p c2677 = true :=
  Snake9.LocalRup.prove_clause [c2654, c2675, c403, c284, c2282] c2677 (by decide) p (sat_cons (step2654 p h) (sat_cons (step2675 p h) (sat_cons (step403 p h) (sat_cons (step284 p h) (sat_cons (step2282 p h) (sat_nil p))))))
def c2678 : List Lit := [(1569, true), (17, false), (92, true)]
theorem step2678 (p : Nat → Bool) (h : Constraints p) : clause p c2678 = true :=
  Snake9.LocalRup.prove_clause [c1274, c1275, c70, c2219] c2678 (by decide) p (sat_cons (step1274 p h) (sat_cons (step1275 p h) (sat_cons (step70 p h) (sat_cons (step2219 p h) (sat_nil p)))))
def c2679 : List Lit := [(122, false), (1625, true), (101, true), (113, true), (79, true), (7, false)]
theorem step2679 (p : Nat → Bool) (h : Constraints p) : clause p c2679 = true :=
  Snake9.LocalRup.prove_clause [c2379, c2564] c2679 (by decide) p (sat_cons (step2379 p h) (sat_cons (step2564 p h) (sat_nil p)))
def c2680 : List Lit := [(1776, true), (93, false), (91, false), (107, true)]
theorem step2680 (p : Nat → Bool) (h : Constraints p) : clause p c2680 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1707, c1714, c1718, c1710, c1693, c1701, c1686, c581] c2680 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1707 p h) (sat_cons (step1714 p h) (sat_cons (step1718 p h) (sat_cons (step1710 p h) (sat_cons (step1693 p h) (sat_cons (step1701 p h) (sat_cons (step1686 p h) (sat_cons (step581 p h) (sat_nil p))))))))))
def c2681 : List Lit := [(1649, false), (46, false), (1585, false), (1681, true), (7, false)]
theorem step2681 (p : Nat → Bool) (h : Constraints p) : clause p c2681 = true :=
  Snake9.LocalRup.prove_clause [c2045, c1493, c2432, c1446, c1500, c1370, c2612, c2076, c1325, c1367, c1343, c1346, c1347, c2037, c151, c1253, c2244, c1247, c158, c1358, c1359, c1365, c180, c1361, c2243, c136] c2681 (by decide) p (sat_cons (step2045 p h) (sat_cons (step1493 p h) (sat_cons (step2432 p h) (sat_cons (step1446 p h) (sat_cons (step1500 p h) (sat_cons (step1370 p h) (sat_cons (step2612 p h) (sat_cons (step2076 p h) (sat_cons (step1325 p h) (sat_cons (step1367 p h) (sat_cons (step1343 p h) (sat_cons (step1346 p h) (sat_cons (step1347 p h) (sat_cons (step2037 p h) (sat_cons (step151 p h) (sat_cons (step1253 p h) (sat_cons (step2244 p h) (sat_cons (step1247 p h) (sat_cons (step158 p h) (sat_cons (step1358 p h) (sat_cons (step1359 p h) (sat_cons (step1365 p h) (sat_cons (step180 p h) (sat_cons (step1361 p h) (sat_cons (step2243 p h) (sat_cons (step136 p h) (sat_nil p)))))))))))))))))))))))))))
def c2682 : List Lit := [(1624, true), (39, true), (35, false), (7, false)]
theorem step2682 (p : Nat → Bool) (h : Constraints p) : clause p c2682 = true :=
  Snake9.LocalRup.prove_clause [c1358, c1370, c2612, c1367, c1365, c1343, c1359, c1361, c180, c136, c2252] c2682 (by decide) p (sat_cons (step1358 p h) (sat_cons (step1370 p h) (sat_cons (step2612 p h) (sat_cons (step1367 p h) (sat_cons (step1365 p h) (sat_cons (step1343 p h) (sat_cons (step1359 p h) (sat_cons (step1361 p h) (sat_cons (step180 p h) (sat_cons (step136 p h) (sat_cons (step2252 p h) (sat_nil p))))))))))))
def c2683 : List Lit := [(72, true), (1697, false), (1713, true)]
theorem step2683 (p : Nat → Bool) (h : Constraints p) : clause p c2683 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1566, c1557, c1547, c1548, c1554, c1555, c1570, c1550, c1539, c1541, c2055, c1532] c2683 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1566 p h) (sat_cons (step1557 p h) (sat_cons (step1547 p h) (sat_cons (step1548 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step1570 p h) (sat_cons (step1550 p h) (sat_cons (step1539 p h) (sat_cons (step1541 p h) (sat_cons (step2055 p h) (sat_cons (step1532 p h) (sat_nil p))))))))))))))
def c2684 : List Lit := [(1703, false), (1697, false), (1713, true), (80, true)]
theorem step2684 (p : Nat → Bool) (h : Constraints p) : clause p c2684 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1566, c2683, c1554, c1555, c1570, c1549, c1550, c1539, c1541, c2308, c2310, c1532, c2055, c2122, c353, c1147, c1149, c1155, c2409, c1158, c1153, c1183, c2413, c1152, c1240, c1179, c2421, c1167, c1137, c1163, c1083, c1162, c1055, c433, c1051, c1048, c1044, c2212, c379, c2305, c2186, c357] c2684 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1566 p h) (sat_cons (step2683 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step1570 p h) (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step1539 p h) (sat_cons (step1541 p h) (sat_cons (step2308 p h) (sat_cons (step2310 p h) (sat_cons (step1532 p h) (sat_cons (step2055 p h) (sat_cons (step2122 p h) (sat_cons (step353 p h) (sat_cons (step1147 p h) (sat_cons (step1149 p h) (sat_cons (step1155 p h) (sat_cons (step2409 p h) (sat_cons (step1158 p h) (sat_cons (step1153 p h) (sat_cons (step1183 p h) (sat_cons (step2413 p h) (sat_cons (step1152 p h) (sat_cons (step1240 p h) (sat_cons (step1179 p h) (sat_cons (step2421 p h) (sat_cons (step1167 p h) (sat_cons (step1137 p h) (sat_cons (step1163 p h) (sat_cons (step1083 p h) (sat_cons (step1162 p h) (sat_cons (step1055 p h) (sat_cons (step433 p h) (sat_cons (step1051 p h) (sat_cons (step1048 p h) (sat_cons (step1044 p h) (sat_cons (step2212 p h) (sat_cons (step379 p h) (sat_cons (step2305 p h) (sat_cons (step2186 p h) (sat_cons (step357 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c2685 : List Lit := [(106, true), (20, false), (30, false), (31, true)]
theorem step2685 (p : Nat → Bool) (h : Constraints p) : clause p c2685 = true :=
  Snake9.LocalRup.prove_clause [c2237, c2238, c1925] c2685 (by decide) p (sat_cons (step2237 p h) (sat_cons (step2238 p h) (sat_cons (step1925 p h) (sat_nil p))))
def c2686 : List Lit := [(1834, true), (1812, false), (1800, false), (1747, false), (1723, false), (92, false), (17, false), (94, true), (88, false), (1712, false), (1772, false), (1761, false), (96, true), (18, false)]
theorem step2686 (p : Nat → Bool) (h : Constraints p) : clause p c2686 = true :=
  Snake9.LocalRup.prove_clause [c1849, c1854, c1819, c1644, c1729, c1617, c1697, c2539, c1687, c485] c2686 (by decide) p (sat_cons (step1849 p h) (sat_cons (step1854 p h) (sat_cons (step1819 p h) (sat_cons (step1644 p h) (sat_cons (step1729 p h) (sat_cons (step1617 p h) (sat_cons (step1697 p h) (sat_cons (step2539 p h) (sat_cons (step1687 p h) (sat_cons (step485 p h) (sat_nil p)))))))))))
def c2687 : List Lit := [(1749, true), (1733, false), (1738, false), (1712, false), (1721, false)]
theorem step2687 (p : Nat → Bool) (h : Constraints p) : clause p c2687 = true :=
  Snake9.LocalRup.prove_clause [c1645, c1652, c1622, c2062, c1591] c2687 (by decide) p (sat_cons (step1645 p h) (sat_cons (step1652 p h) (sat_cons (step1622 p h) (sat_cons (step2062 p h) (sat_cons (step1591 p h) (sat_nil p))))))
def c2688 : List Lit := [(1620, false), (1585, false), (1679, true), (20, false)]
theorem step2688 (p : Nat → Bool) (h : Constraints p) : clause p c2688 = true :=
  Snake9.LocalRup.prove_clause [c2045, c1491, c1450, c1370, c1443, c1498, c1325, c1374, c2037, c1349, c2569, c1253, c1346, c156, c1247] c2688 (by decide) p (sat_cons (step2045 p h) (sat_cons (step1491 p h) (sat_cons (step1450 p h) (sat_cons (step1370 p h) (sat_cons (step1443 p h) (sat_cons (step1498 p h) (sat_cons (step1325 p h) (sat_cons (step1374 p h) (sat_cons (step2037 p h) (sat_cons (step1349 p h) (sat_cons (step2569 p h) (sat_cons (step1253 p h) (sat_cons (step1346 p h) (sat_cons (step156 p h) (sat_cons (step1247 p h) (sat_nil p))))))))))))))))
def c2689 : List Lit := [(1543, false), (1611, true), (1620, true), (1585, false), (1679, true)]
theorem step2689 (p : Nat → Bool) (h : Constraints p) : clause p c2689 = true :=
  Snake9.LocalRup.prove_clause [c1351, c1343, c1349, c1347, c2447, c1330, c2039, c1253, c1254, c2037, c1248, c1325, c1498, c1443, c2682, c135, c2243, c181, c180, c1361, c1357, c1365] c2689 (by decide) p (sat_cons (step1351 p h) (sat_cons (step1343 p h) (sat_cons (step1349 p h) (sat_cons (step1347 p h) (sat_cons (step2447 p h) (sat_cons (step1330 p h) (sat_cons (step2039 p h) (sat_cons (step1253 p h) (sat_cons (step1254 p h) (sat_cons (step2037 p h) (sat_cons (step1248 p h) (sat_cons (step1325 p h) (sat_cons (step1498 p h) (sat_cons (step1443 p h) (sat_cons (step2682 p h) (sat_cons (step135 p h) (sat_cons (step2243 p h) (sat_cons (step181 p h) (sat_cons (step180 p h) (sat_cons (step1361 p h) (sat_cons (step1357 p h) (sat_cons (step1365 p h) (sat_nil p)))))))))))))))))))))))
def c2690 : List Lit := [(1611, true), (1620, true), (1585, false), (1679, true)]
theorem step2690 (p : Nat → Bool) (h : Constraints p) : clause p c2690 = true :=
  Snake9.LocalRup.prove_clause [c1367, c1349, c1351, c2569, c1346, c1347, c1343, c2689, c1247, c158, c1358, c1359, c1365, c1361, c136, c192, c2243] c2690 (by decide) p (sat_cons (step1367 p h) (sat_cons (step1349 p h) (sat_cons (step1351 p h) (sat_cons (step2569 p h) (sat_cons (step1346 p h) (sat_cons (step1347 p h) (sat_cons (step1343 p h) (sat_cons (step2689 p h) (sat_cons (step1247 p h) (sat_cons (step158 p h) (sat_cons (step1358 p h) (sat_cons (step1359 p h) (sat_cons (step1365 p h) (sat_cons (step1361 p h) (sat_cons (step136 p h) (sat_cons (step192 p h) (sat_cons (step2243 p h) (sat_nil p))))))))))))))))))
def c2691 : List Lit := [(35, false), (33, false), (44, true), (1620, true)]
theorem step2691 (p : Nat → Bool) (h : Constraints p) : clause p c2691 = true :=
  Snake9.LocalRup.prove_clause [c2243, c135, c136, c1358, c1361, c1365] c2691 (by decide) p (sat_cons (step2243 p h) (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step1358 p h) (sat_cons (step1361 p h) (sat_cons (step1365 p h) (sat_nil p)))))))
def c2692 : List Lit := [(1617, false), (35, true), (33, false), (3, false), (1620, true), (1625, true)]
theorem step2692 (p : Nat → Bool) (h : Constraints p) : clause p c2692 = true :=
  Snake9.LocalRup.prove_clause [c1363, c1365, c1377, c1358, c1350, c1348, c158, c150, c2244] c2692 (by decide) p (sat_cons (step1363 p h) (sat_cons (step1365 p h) (sat_cons (step1377 p h) (sat_cons (step1358 p h) (sat_cons (step1350 p h) (sat_cons (step1348 p h) (sat_cons (step158 p h) (sat_cons (step150 p h) (sat_cons (step2244 p h) (sat_nil p))))))))))
def c2693 : List Lit := [(1697, true), (1647, true)]
theorem step2693 (p : Nat → Bool) (h : Constraints p) : clause p c2693 = true :=
  Snake9.LocalRup.prove_clause [c1415, c1409, c1402, c1418, c1535, c1536, c2073] c2693 (by decide) p (sat_cons (step1415 p h) (sat_cons (step1409 p h) (sat_cons (step1402 p h) (sat_cons (step1418 p h) (sat_cons (step1535 p h) (sat_cons (step1536 p h) (sat_cons (step2073 p h) (sat_nil p))))))))
end B112E052
