import B112E089Part0010
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2716 : List Lit := [(69, true), (60, true), (76, false), (1660, true), (49, true), (197, true)]
theorem step2716 (p : Nat → Bool) (h : Constraints p) : clause p c2716 = true :=
  Snake9.LocalRup.prove_clause [c1625, c1614, c1616, c1623, c1617, c755, c679] c2716 (by decide) p (sat_cons (step1625 p h) (sat_cons (step1614 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step1617 p h) (sat_cons (step755 p h) (sat_cons (step679 p h) (sat_nil p))))))))
def c2717 : List Lit := [(76, false), (67, false), (73, false), (74, true), (62, false), (200, true)]
theorem step2717 (p : Nat → Bool) (h : Constraints p) : clause p c2717 = true :=
  Snake9.LocalRup.prove_clause [c2697, c561] c2717 (by decide) p (sat_cons (step2697 p h) (sat_cons (step561 p h) (sat_nil p)))
def c2718 : List Lit := [(76, false), (64, false), (66, false), (74, false), (62, false), (1660, true), (379, true)]
theorem step2718 (p : Nat → Bool) (h : Constraints p) : clause p c2718 = true :=
  Snake9.LocalRup.prove_clause [c1625, c1995, c707, c1614, c1616, c1623, c624, c1618, c2070] c2718 (by decide) p (sat_cons (step1625 p h) (sat_cons (step1995 p h) (sat_cons (step707 p h) (sat_cons (step1614 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step624 p h) (sat_cons (step1618 p h) (sat_cons (step2070 p h) (sat_nil p))))))))))
def c2719 : List Lit := [(1659, true), (1650, true), (62, false), (379, true)]
theorem step2719 (p : Nat → Bool) (h : Constraints p) : clause p c2719 = true :=
  Snake9.LocalRup.prove_clause [c1607, c1606, c1620, c1622, c1618, c1615, c559, c624, c2070] c2719 (by decide) p (sat_cons (step1607 p h) (sat_cons (step1606 p h) (sat_cons (step1620 p h) (sat_cons (step1622 p h) (sat_cons (step1618 p h) (sat_cons (step1615 p h) (sat_cons (step559 p h) (sat_cons (step624 p h) (sat_cons (step2070 p h) (sat_nil p))))))))))
def c2720 : List Lit := [(1663, true), (62, false), (379, true)]
theorem step2720 (p : Nat → Bool) (h : Constraints p) : clause p c2720 = true :=
  Snake9.LocalRup.prove_clause [c1628, c1632, c2719, c1609] c2720 (by decide) p (sat_cons (step1628 p h) (sat_cons (step1632 p h) (sat_cons (step2719 p h) (sat_cons (step1609 p h) (sat_nil p)))))
def c2721 : List Lit := [(1725, false), (1688, false), (91, true), (1660, false), (1783, true), (62, true), (63, false), (24, false), (75, false), (487, true)]
theorem step2721 (p : Nat → Bool) (h : Constraints p) : clause p c2721 = true :=
  Snake9.LocalRup.prove_clause [c2636, c1612, c1639, c1723, c1905, c1289, c1284, c2686, c1279, c1277, c1274, c2627, c1846, c2645, c1912, c2415, c1731, c1613, c1644] c2721 (by decide) p (sat_cons (step2636 p h) (sat_cons (step1612 p h) (sat_cons (step1639 p h) (sat_cons (step1723 p h) (sat_cons (step1905 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step2686 p h) (sat_cons (step1279 p h) (sat_cons (step1277 p h) (sat_cons (step1274 p h) (sat_cons (step2627 p h) (sat_cons (step1846 p h) (sat_cons (step2645 p h) (sat_cons (step1912 p h) (sat_cons (step2415 p h) (sat_cons (step1731 p h) (sat_cons (step1613 p h) (sat_cons (step1644 p h) (sat_nil p))))))))))))))))))))
def c2722 : List Lit := [(1688, false), (91, true), (1660, false), (1783, true), (62, true), (63, false), (24, false), (75, false), (487, true)]
theorem step2722 (p : Nat → Bool) (h : Constraints p) : clause p c2722 = true :=
  Snake9.LocalRup.prove_clause [c2636, c1612, c1639, c1289, c1284, c2686, c1291, c1252, c1236, c1227, c1723, c1905, c1852, c2575, c2721, c1778, c1782, c1772, c1758, c1765, c1750, c2456] c2722 (by decide) p (sat_cons (step2636 p h) (sat_cons (step1612 p h) (sat_cons (step1639 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step2686 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1723 p h) (sat_cons (step1905 p h) (sat_cons (step1852 p h) (sat_cons (step2575 p h) (sat_cons (step2721 p h) (sat_cons (step1778 p h) (sat_cons (step1782 p h) (sat_cons (step1772 p h) (sat_cons (step1758 p h) (sat_cons (step1765 p h) (sat_cons (step1750 p h) (sat_cons (step2456 p h) (sat_nil p)))))))))))))))))))))))
def c2723 : List Lit := [(1725, false), (107, false), (1760, true), (72, false), (74, true), (91, true), (1745, false), (487, true)]
theorem step2723 (p : Nat → Bool) (h : Constraints p) : clause p c2723 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1284, c1281, c1272, c1266, c2088, c1270, c1268, c1267, c1847, c2645, c1829, c2483, c947, c897] c2723 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step2088 p h) (sat_cons (step1270 p h) (sat_cons (step1268 p h) (sat_cons (step1267 p h) (sat_cons (step1847 p h) (sat_cons (step2645 p h) (sat_cons (step1829 p h) (sat_cons (step2483 p h) (sat_cons (step947 p h) (sat_cons (step897 p h) (sat_nil p))))))))))))))))
def c2724 : List Lit := [(1726, true), (91, false), (439, true)]
theorem step2724 (p : Nat → Bool) (h : Constraints p) : clause p c2724 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1227, c2708, c1758, c2575, c1783, c817, c807, c1772, c1765] c2724 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step2708 p h) (sat_cons (step1758 p h) (sat_cons (step2575 p h) (sat_cons (step1783 p h) (sat_cons (step817 p h) (sat_cons (step807 p h) (sat_cons (step1772 p h) (sat_cons (step1765 p h) (sat_nil p)))))))))))
def c2725 : List Lit := [(103, true), (1760, true), (487, true)]
theorem step2725 (p : Nat → Bool) (h : Constraints p) : clause p c2725 = true :=
  Snake9.LocalRup.prove_clause [c1764, c2465] c2725 (by decide) p (sat_cons (step1764 p h) (sat_cons (step2465 p h) (sat_nil p)))
def c2726 : List Lit := [(1616, true), (1569, false), (66, false), (1572, false), (1592, false), (185, true)]
theorem step2726 (p : Nat → Bool) (h : Constraints p) : clause p c2726 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1451, c1493, c1541, c1534, c1452, c1494, c1436, c2106, c1430] c2726 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1451 p h) (sat_cons (step1493 p h) (sat_cons (step1541 p h) (sat_cons (step1534 p h) (sat_cons (step1452 p h) (sat_cons (step1494 p h) (sat_cons (step1436 p h) (sat_cons (step2106 p h) (sat_cons (step1430 p h) (sat_nil p)))))))))))
def c2727 : List Lit := [(1653, false), (1700, true), (1657, false), (1680, false), (74, false), (67, true), (1660, false), (75, false)]
theorem step2727 (p : Nat → Bool) (h : Constraints p) : clause p c2727 = true :=
  Snake9.LocalRup.prove_clause [c2408, c1730, c1639, c1640, c1723, c1626, c2511, c1616, c1647, c712] c2727 (by decide) p (sat_cons (step2408 p h) (sat_cons (step1730 p h) (sat_cons (step1639 p h) (sat_cons (step1640 p h) (sat_cons (step1723 p h) (sat_cons (step1626 p h) (sat_cons (step2511 p h) (sat_cons (step1616 p h) (sat_cons (step1647 p h) (sat_cons (step712 p h) (sat_nil p)))))))))))
def c2728 : List Lit := [(1657, true), (1617, true), (1564, false), (67, false), (1576, false), (75, false), (1592, false), (197, true)]
theorem step2728 (p : Nat → Bool) (h : Constraints p) : clause p c2728 = true :=
  Snake9.LocalRup.prove_clause [c1617, c2527, c2692] c2728 (by decide) p (sat_cons (step1617 p h) (sat_cons (step2527 p h) (sat_cons (step2692 p h) (sat_nil p))))
def c2729 : List Lit := [(113, false), (1651, true), (107, false), (62, false), (237, true)]
theorem step2729 (p : Nat → Bool) (h : Constraints p) : clause p c2729 = true :=
  Snake9.LocalRup.prove_clause [c2643, c894, c905] c2729 (by decide) p (sat_cons (step2643 p h) (sat_cons (step894 p h) (sat_cons (step905 p h) (sat_nil p))))
def c2730 : List Lit := [(1661, true), (73, true), (67, true), (74, true), (193, true)]
theorem step2730 (p : Nat → Bool) (h : Constraints p) : clause p c2730 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1615, c1624, c1626, c1619, c1616, c641, c640, c2001] c2730 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1615 p h) (sat_cons (step1624 p h) (sat_cons (step1626 p h) (sat_cons (step1619 p h) (sat_cons (step1616 p h) (sat_cons (step641 p h) (sat_cons (step640 p h) (sat_cons (step2001 p h) (sat_nil p))))))))))
def c2731 : List Lit := [(1727, true), (1713, false), (1717, false), (106, true), (455, true)]
theorem step2731 (p : Nat → Bool) (h : Constraints p) : clause p c2731 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1250, c1248, c1242, c1240, c1252, c1236, c1227, c1784, c1788, c1773, c2095, c1768, c2093] c2731 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1242 p h) (sat_cons (step1240 p h) (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1784 p h) (sat_cons (step1788 p h) (sat_cons (step1773 p h) (sat_cons (step2095 p h) (sat_cons (step1768 p h) (sat_cons (step2093 p h) (sat_nil p)))))))))))))))
def c2732 : List Lit := [(23, false), (24, true), (62, true), (26, false), (18, true)]
theorem step2732 (p : Nat → Bool) (h : Constraints p) : clause p c2732 = true :=
  Snake9.LocalRup.prove_clause [c2197, c2192] c2732 (by decide) p (sat_cons (step2197 p h) (sat_cons (step2192 p h) (sat_nil p)))
def c2733 : List Lit := [(1781, true), (1666, false), (1670, false), (487, true)]
theorem step2733 (p : Nat → Bool) (h : Constraints p) : clause p c2733 = true :=
  Snake9.LocalRup.prove_clause [c2145, c1722, c1291, c1252, c1234, c1231, c1230, c1289, c1284, c1281, c1272, c1266, c1896, c2555, c2724, c2639, c1664, c2088, c2511, c2396, c1723, c1903] c2733 (by decide) p (sat_cons (step2145 p h) (sat_cons (step1722 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1896 p h) (sat_cons (step2555 p h) (sat_cons (step2724 p h) (sat_cons (step2639 p h) (sat_cons (step1664 p h) (sat_cons (step2088 p h) (sat_cons (step2511 p h) (sat_cons (step2396 p h) (sat_cons (step1723 p h) (sat_cons (step1903 p h) (sat_nil p)))))))))))))))))))))))
def c2734 : List Lit := [(67, false), (1546, true), (25, true), (26, false), (18, true), (10, false), (1525, false), (153, true)]
theorem step2734 (p : Nat → Bool) (h : Constraints p) : clause p c2734 = true :=
  Snake9.LocalRup.prove_clause [c1353, c147, c150, c1344, c2190, c1349, c174, c1383, c1358, c1363] c2734 (by decide) p (sat_cons (step1353 p h) (sat_cons (step147 p h) (sat_cons (step150 p h) (sat_cons (step1344 p h) (sat_cons (step2190 p h) (sat_cons (step1349 p h) (sat_cons (step174 p h) (sat_cons (step1383 p h) (sat_cons (step1358 p h) (sat_cons (step1363 p h) (sat_nil p)))))))))))
def c2735 : List Lit := [(34, false), (27, true), (33, true), (158, true)]
theorem step2735 (p : Nat → Bool) (h : Constraints p) : clause p c2735 = true :=
  Snake9.LocalRup.prove_clause [c201, c199, c2471] c2735 (by decide) p (sat_cons (step201 p h) (sat_cons (step199 p h) (sat_cons (step2471 p h) (sat_nil p))))
def c2736 : List Lit := [(1653, false), (32, false), (1700, true), (1657, false), (67, true), (74, false), (1660, false), (75, true)]
theorem step2736 (p : Nat → Bool) (h : Constraints p) : clause p c2736 = true :=
  Snake9.LocalRup.prove_clause [c1648, c2145, c1730, c1639, c1640, c1723, c1626, c2161, c1616, c1649, c691] c2736 (by decide) p (sat_cons (step1648 p h) (sat_cons (step2145 p h) (sat_cons (step1730 p h) (sat_cons (step1639 p h) (sat_cons (step1640 p h) (sat_cons (step1723 p h) (sat_cons (step1626 p h) (sat_cons (step2161 p h) (sat_cons (step1616 p h) (sat_cons (step1649 p h) (sat_cons (step691 p h) (sat_nil p))))))))))))
def c2737 : List Lit := [(22, false), (1539, true), (24, true), (26, false), (10, false)]
theorem step2737 (p : Nat → Bool) (h : Constraints p) : clause p c2737 = true :=
  Snake9.LocalRup.prove_clause [c146, c145, c1357, c1355, c1365] c2737 (by decide) p (sat_cons (step146 p h) (sat_cons (step145 p h) (sat_cons (step1357 p h) (sat_cons (step1355 p h) (sat_cons (step1365 p h) (sat_nil p))))))
def c2738 : List Lit := [(24, false), (62, false), (148, true), (6, true), (19, true)]
theorem step2738 (p : Nat → Bool) (h : Constraints p) : clause p c2738 = true :=
  Snake9.LocalRup.prove_clause [c135, c136, c1961] c2738 (by decide) p (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step1961 p h) (sat_nil p))))
def c2739 : List Lit := [(1666, false), (1700, true), (1783, true), (1717, false), (106, true), (1750, false), (1670, false), (455, true)]
theorem step2739 (p : Nat → Bool) (h : Constraints p) : clause p c2739 = true :=
  Snake9.LocalRup.prove_clause [c2145, c1252, c1236, c1227, c1722, c1723, c1898, c2511, c1858, c1664, c2731, c2708, c1758] c2739 (by decide) p (sat_cons (step2145 p h) (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1722 p h) (sat_cons (step1723 p h) (sat_cons (step1898 p h) (sat_cons (step2511 p h) (sat_cons (step1858 p h) (sat_cons (step1664 p h) (sat_cons (step2731 p h) (sat_cons (step2708 p h) (sat_cons (step1758 p h) (sat_nil p))))))))))))))
def c2740 : List Lit := [(73, true), (1699, true), (74, true), (67, true), (62, false), (75, true), (393, true)]
theorem step2740 (p : Nat → Bool) (h : Constraints p) : clause p c2740 = true :=
  Snake9.LocalRup.prove_clause [c1648, c2145, c1722, c1192, c1180, c1177, c1190, c1186, c1183, c2730, c2266, c1630, c1635, c1716, c1609, c2161, c1606, c1649, c748, c560] c2740 (by decide) p (sat_cons (step1648 p h) (sat_cons (step2145 p h) (sat_cons (step1722 p h) (sat_cons (step1192 p h) (sat_cons (step1180 p h) (sat_cons (step1177 p h) (sat_cons (step1190 p h) (sat_cons (step1186 p h) (sat_cons (step1183 p h) (sat_cons (step2730 p h) (sat_cons (step2266 p h) (sat_cons (step1630 p h) (sat_cons (step1635 p h) (sat_cons (step1716 p h) (sat_cons (step1609 p h) (sat_cons (step2161 p h) (sat_cons (step1606 p h) (sat_cons (step1649 p h) (sat_cons (step748 p h) (sat_cons (step560 p h) (sat_nil p)))))))))))))))))))))
def c2741 : List Lit := [(1543, true), (24, true), (1529, false), (153, true)]
theorem step2741 (p : Nat → Bool) (h : Constraints p) : clause p c2741 = true :=
  Snake9.LocalRup.prove_clause [c1373, c2411] c2741 (by decide) p (sat_cons (step1373 p h) (sat_cons (step2411 p h) (sat_nil p)))
def c2742 : List Lit := [(1670, true), (67, false), (75, false), (62, false), (200, true)]
theorem step2742 (p : Nat → Bool) (h : Constraints p) : clause p c2742 = true :=
  Snake9.LocalRup.prove_clause [c1647, c2702, c709] c2742 (by decide) p (sat_cons (step1647 p h) (sat_cons (step2702 p h) (sat_cons (step709 p h) (sat_nil p))))
def c2743 : List Lit := [(67, true), (1660, true), (75, false), (62, false), (193, true)]
theorem step2743 (p : Nat → Bool) (h : Constraints p) : clause p c2743 = true :=
  Snake9.LocalRup.prove_clause [c1625, c2693, c1616, c706] c2743 (by decide) p (sat_cons (step1625 p h) (sat_cons (step2693 p h) (sat_cons (step1616 p h) (sat_cons (step706 p h) (sat_nil p)))))
def c2744 : List Lit := [(65, false), (76, false), (1651, true), (42, true), (1578, true), (67, false), (169, true)]
theorem step2744 (p : Nat → Bool) (h : Constraints p) : clause p c2744 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1437, c558, c562, c1431, c1432, c1608, c1439, c613, c1429, c301, c275] c2744 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1437 p h) (sat_cons (step558 p h) (sat_cons (step562 p h) (sat_cons (step1431 p h) (sat_cons (step1432 p h) (sat_cons (step1608 p h) (sat_cons (step1439 p h) (sat_cons (step613 p h) (sat_cons (step1429 p h) (sat_cons (step301 p h) (sat_cons (step275 p h) (sat_nil p)))))))))))))
def c2745 : List Lit := [(1725, true), (94, false), (218, true)]
theorem step2745 (p : Nat → Bool) (h : Constraints p) : clause p c2745 = true :=
  Snake9.LocalRup.prove_clause [c1778, c1782, c1772, c1758, c1765, c1750, c2456] c2745 (by decide) p (sat_cons (step1778 p h) (sat_cons (step1782 p h) (sat_cons (step1772 p h) (sat_cons (step1758 p h) (sat_cons (step1765 p h) (sat_cons (step1750 p h) (sat_cons (step2456 p h) (sat_nil p))))))))
def c2746 : List Lit := [(29, false), (1545, true), (1535, false), (24, true), (18, false), (1525, false), (153, true)]
theorem step2746 (p : Nat → Bool) (h : Constraints p) : clause p c2746 = true :=
  Snake9.LocalRup.prove_clause [c2413, c2131, c1348, c1355, c1379, c1365] c2746 (by decide) p (sat_cons (step2413 p h) (sat_cons (step2131 p h) (sat_cons (step1348 p h) (sat_cons (step1355 p h) (sat_cons (step1379 p h) (sat_cons (step1365 p h) (sat_nil p)))))))
def c2747 : List Lit := [(89, true), (1782, true), (1675, false), (1665, false), (415, true), (439, true), (79, true)]
theorem step2747 (p : Nat → Bool) (h : Constraints p) : clause p c2747 = true :=
  Snake9.LocalRup.prove_clause [c2561, c1719, c1688, c1210, c1206, c2273, c1665, c2544, c778, c2724, c1662, c2555, c1670, c1904, c1686, c1717] c2747 (by decide) p (sat_cons (step2561 p h) (sat_cons (step1719 p h) (sat_cons (step1688 p h) (sat_cons (step1210 p h) (sat_cons (step1206 p h) (sat_cons (step2273 p h) (sat_cons (step1665 p h) (sat_cons (step2544 p h) (sat_cons (step778 p h) (sat_cons (step2724 p h) (sat_cons (step1662 p h) (sat_cons (step2555 p h) (sat_cons (step1670 p h) (sat_cons (step1904 p h) (sat_cons (step1686 p h) (sat_cons (step1717 p h) (sat_nil p)))))))))))))))))
def c2748 : List Lit := [(75, false), (69, false), (72, false), (74, false), (1760, true), (487, true)]
theorem step2748 (p : Nat → Bool) (h : Constraints p) : clause p c2748 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1252, c1234, c1231, c1230, c1289, c1284, c1281, c1272, c1266, c1270, c1268, c1236, c1227, c2686, c713, c1852, c2483, c2575, c2724, c2639, c2745, c2088, c1847, c1829] c2748 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1270 p h) (sat_cons (step1268 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step2686 p h) (sat_cons (step713 p h) (sat_cons (step1852 p h) (sat_cons (step2483 p h) (sat_cons (step2575 p h) (sat_cons (step2724 p h) (sat_cons (step2639 p h) (sat_cons (step2745 p h) (sat_cons (step2088 p h) (sat_cons (step1847 p h) (sat_cons (step1829 p h) (sat_nil p))))))))))))))))))))))))))
def c2749 : List Lit := [(120, false), (1576, false), (1618, true), (75, true), (69, false), (74, false), (1588, false), (50, true), (39, true), (158, true)]
theorem step2749 (p : Nat → Bool) (h : Constraints p) : clause p c2749 = true :=
  Snake9.LocalRup.prove_clause [c692, c702, c2393, c1466, c1456, c1471, c1543, c1503] c2749 (by decide) p (sat_cons (step692 p h) (sat_cons (step702 p h) (sat_cons (step2393 p h) (sat_cons (step1466 p h) (sat_cons (step1456 p h) (sat_cons (step1471 p h) (sat_cons (step1543 p h) (sat_cons (step1503 p h) (sat_nil p)))))))))
def c2750 : List Lit := [(120, true), (72, false), (1760, true), (487, true)]
theorem step2750 (p : Nat → Bool) (h : Constraints p) : clause p c2750 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1252, c1234, c1231, c1230, c1289, c1284, c1281, c1272, c1266, c1270, c1268, c1236, c1227, c2649, c2483, c1852, c2575, c2724, c2639, c2745, c2088, c1847, c1829] c2750 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1230 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1266 p h) (sat_cons (step1270 p h) (sat_cons (step1268 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step2649 p h) (sat_cons (step2483 p h) (sat_cons (step1852 p h) (sat_cons (step2575 p h) (sat_cons (step2724 p h) (sat_cons (step2639 p h) (sat_cons (step2745 p h) (sat_cons (step2088 p h) (sat_cons (step1847 p h) (sat_cons (step1829 p h) (sat_nil p)))))))))))))))))))))))))
def c2751 : List Lit := [(1618, true), (120, false), (75, true), (67, false), (69, false), (74, false), (1588, false), (50, true), (39, true), (333, true)]
theorem step2751 (p : Nat → Bool) (h : Constraints p) : clause p c2751 = true :=
  Snake9.LocalRup.prove_clause [c702, c1466, c1471, c1123, c1099, c1098, c1097, c692, c2393, c1455, c1121, c1116, c1112, c1109, c2749, c2543, c1478, c1536, c1481, c1504] c2751 (by decide) p (sat_cons (step702 p h) (sat_cons (step1466 p h) (sat_cons (step1471 p h) (sat_cons (step1123 p h) (sat_cons (step1099 p h) (sat_cons (step1098 p h) (sat_cons (step1097 p h) (sat_cons (step692 p h) (sat_cons (step2393 p h) (sat_cons (step1455 p h) (sat_cons (step1121 p h) (sat_cons (step1116 p h) (sat_cons (step1112 p h) (sat_cons (step1109 p h) (sat_cons (step2749 p h) (sat_cons (step2543 p h) (sat_cons (step1478 p h) (sat_cons (step1536 p h) (sat_cons (step1481 p h) (sat_cons (step1504 p h) (sat_nil p)))))))))))))))))))))
def c2752 : List Lit := [(1569, true), (30, true), (32, true), (155, true)]
theorem step2752 (p : Nat → Bool) (h : Constraints p) : clause p c2752 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1424, c1422, c1415, c1417, c2422] c2752 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1424 p h) (sat_cons (step1422 p h) (sat_cons (step1415 p h) (sat_cons (step1417 p h) (sat_cons (step2422 p h) (sat_nil p)))))))
def c2753 : List Lit := [(1592, true), (49, true), (174, true)]
theorem step2753 (p : Nat → Bool) (h : Constraints p) : clause p c2753 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1469, c1465, c1461, c1462, c352, c318] c2753 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step352 p h) (sat_cons (step318 p h) (sat_nil p))))))))
def c2754 : List Lit := [(75, false), (1666, false), (1781, true), (49, true), (487, true)]
theorem step2754 (p : Nat → Bool) (h : Constraints p) : clause p c2754 = true :=
  Snake9.LocalRup.prove_clause [c2375, c1889, c1291, c1250, c1248, c1242, c1241, c2629, c1289, c1284, c1279, c1277, c1274, c1252, c2627, c2686, c2452, c1896, c1852, c1722, c2724, c2408, c1664] c2754 (by decide) p (sat_cons (step2375 p h) (sat_cons (step1889 p h) (sat_cons (step1291 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1242 p h) (sat_cons (step1241 p h) (sat_cons (step2629 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1279 p h) (sat_cons (step1277 p h) (sat_cons (step1274 p h) (sat_cons (step1252 p h) (sat_cons (step2627 p h) (sat_cons (step2686 p h) (sat_cons (step2452 p h) (sat_cons (step1896 p h) (sat_cons (step1852 p h) (sat_cons (step1722 p h) (sat_cons (step2724 p h) (sat_cons (step2408 p h) (sat_cons (step1664 p h) (sat_nil p))))))))))))))))))))))))
def c2755 : List Lit := [(1666, false), (1781, true), (49, true), (487, true)]
theorem step2755 (p : Nat → Bool) (h : Constraints p) : clause p c2755 = true :=
  Snake9.LocalRup.prove_clause [c2733, c2754, c1648] c2755 (by decide) p (sat_cons (step2733 p h) (sat_cons (step2754 p h) (sat_cons (step1648 p h) (sat_nil p))))
def c2756 : List Lit := [(1698, true), (75, true), (49, true), (1653, false), (197, true)]
theorem step2756 (p : Nat → Bool) (h : Constraints p) : clause p c2756 = true :=
  Snake9.LocalRup.prove_clause [c1648, c2145, c1637, c1715, c1709, c1638, c2161, c1620, c1622, c1649, c1617, c1618, c1614, c1615, c654, c755, c678] c2756 (by decide) p (sat_cons (step1648 p h) (sat_cons (step2145 p h) (sat_cons (step1637 p h) (sat_cons (step1715 p h) (sat_cons (step1709 p h) (sat_cons (step1638 p h) (sat_cons (step2161 p h) (sat_cons (step1620 p h) (sat_cons (step1622 p h) (sat_cons (step1649 p h) (sat_cons (step1617 p h) (sat_cons (step1618 p h) (sat_cons (step1614 p h) (sat_cons (step1615 p h) (sat_cons (step654 p h) (sat_cons (step755 p h) (sat_cons (step678 p h) (sat_nil p))))))))))))))))))
def c2757 : List Lit := [(1592, true), (1660, true), (75, false), (49, false), (193, true)]
theorem step2757 (p : Nat → Bool) (h : Constraints p) : clause p c2757 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1469, c1464, c1465, c1461, c338, c1617, c2486, c1623, c700, c1614] c2757 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_cons (step1464 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step338 p h) (sat_cons (step1617 p h) (sat_cons (step2486 p h) (sat_cons (step1623 p h) (sat_cons (step700 p h) (sat_cons (step1614 p h) (sat_nil p))))))))))))
def c2758 : List Lit := [(23, true), (32, false), (75, false), (156, true)]
theorem step2758 (p : Nat → Bool) (h : Constraints p) : clause p c2758 = true :=
  Snake9.LocalRup.prove_clause [c2663, c189] c2758 (by decide) p (sat_cons (step2663 p h) (sat_cons (step189 p h) (sat_nil p)))
def c2759 : List Lit := [(1616, true), (1651, true), (1569, false), (42, true), (1592, false), (365, true)]
theorem step2759 (p : Nat → Bool) (h : Constraints p) : clause p c2759 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1435, c1451, c1493, c1157, c1121, c1116, c1112, c1109, c1155, c1150, c1146, c1145, c1144, c2726, c1541, c1534, c1608, c1452, c1494, c1438, c1436, c1481, c1483, c1429, c1430, c1478, c1476, c277, c301, c608] c2759 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1435 p h) (sat_cons (step1451 p h) (sat_cons (step1493 p h) (sat_cons (step1157 p h) (sat_cons (step1121 p h) (sat_cons (step1116 p h) (sat_cons (step1112 p h) (sat_cons (step1109 p h) (sat_cons (step1155 p h) (sat_cons (step1150 p h) (sat_cons (step1146 p h) (sat_cons (step1145 p h) (sat_cons (step1144 p h) (sat_cons (step2726 p h) (sat_cons (step1541 p h) (sat_cons (step1534 p h) (sat_cons (step1608 p h) (sat_cons (step1452 p h) (sat_cons (step1494 p h) (sat_cons (step1438 p h) (sat_cons (step1436 p h) (sat_cons (step1481 p h) (sat_cons (step1483 p h) (sat_cons (step1429 p h) (sat_cons (step1430 p h) (sat_cons (step1478 p h) (sat_cons (step1476 p h) (sat_cons (step277 p h) (sat_cons (step301 p h) (sat_cons (step608 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2760 : List Lit := [(1780, true), (1665, false), (1759, false), (1750, false), (439, true)]
theorem step2760 (p : Nat → Bool) (h : Constraints p) : clause p c2760 = true :=
  Snake9.LocalRup.prove_clause [c2374, c1882, c1888, c1852, c1715, c2724, c2408, c1664] c2760 (by decide) p (sat_cons (step2374 p h) (sat_cons (step1882 p h) (sat_cons (step1888 p h) (sat_cons (step1852 p h) (sat_cons (step1715 p h) (sat_cons (step2724 p h) (sat_cons (step2408 p h) (sat_cons (step1664 p h) (sat_nil p)))))))))
def c2761 : List Lit := [(32, false), (62, false), (75, false), (18, false), (156, true)]
theorem step2761 (p : Nat → Bool) (h : Constraints p) : clause p c2761 = true :=
  Snake9.LocalRup.prove_clause [c122, c2758] c2761 (by decide) p (sat_cons (step122 p h) (sat_cons (step2758 p h) (sat_nil p)))
def c2762 : List Lit := [(91, false), (1727, true), (49, true), (455, true)]
theorem step2762 (p : Nat → Bool) (h : Constraints p) : clause p c2762 = true :=
  Snake9.LocalRup.prove_clause [c1252, c1236, c1227, c2708, c2513] c2762 (by decide) p (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step2708 p h) (sat_cons (step2513 p h) (sat_nil p))))))
def c2763 : List Lit := [(1698, true), (74, false), (1680, false), (32, false), (1652, false), (75, true)]
theorem step2763 (p : Nat → Bool) (h : Constraints p) : clause p c2763 = true :=
  Snake9.LocalRup.prove_clause [c1648, c2511, c1632, c1703, c1709, c2576, c1633, c1649, c1622, c691, c1614] c2763 (by decide) p (sat_cons (step1648 p h) (sat_cons (step2511 p h) (sat_cons (step1632 p h) (sat_cons (step1703 p h) (sat_cons (step1709 p h) (sat_cons (step2576 p h) (sat_cons (step1633 p h) (sat_cons (step1649 p h) (sat_cons (step1622 p h) (sat_cons (step691 p h) (sat_cons (step1614 p h) (sat_nil p))))))))))))
def c2764 : List Lit := [(67, true), (74, false), (32, false), (1660, true), (75, true), (49, true), (197, true)]
theorem step2764 (p : Nat → Bool) (h : Constraints p) : clause p c2764 = true :=
  Snake9.LocalRup.prove_clause [c1625, c1615, c1616, c1623, c2451] c2764 (by decide) p (sat_cons (step1625 p h) (sat_cons (step1615 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step2451 p h) (sat_nil p))))))
def c2765 : List Lit := [(1614, true), (1576, false), (75, false), (158, true)]
theorem step2765 (p : Nat → Bool) (h : Constraints p) : clause p c2765 = true :=
  Snake9.LocalRup.prove_clause [c2099, c1446, c1532, c1525, c1451, c1493, c2101, c2155] c2765 (by decide) p (sat_cons (step2099 p h) (sat_cons (step1446 p h) (sat_cons (step1532 p h) (sat_cons (step1525 p h) (sat_cons (step1451 p h) (sat_cons (step1493 p h) (sat_cons (step2101 p h) (sat_cons (step2155 p h) (sat_nil p)))))))))
def c2766 : List Lit := [(1592, true), (1583, true), (42, true), (75, false), (49, false), (365, true)]
theorem step2766 (p : Nat → Bool) (h : Constraints p) : clause p c2766 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1157, c1123, c1099, c1098, c1097, c1155, c1152, c1136, c1128, c1126, c1134, c1132, c1130, c1129, c1467, c1469, c2155, c1464, c1465, c1461, c1462, c2101, c1979, c1452, c317, c351, c1438, c1436, c2217, c1429, c1430, c2124, c380] c2766 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1157 p h) (sat_cons (step1123 p h) (sat_cons (step1099 p h) (sat_cons (step1098 p h) (sat_cons (step1097 p h) (sat_cons (step1155 p h) (sat_cons (step1152 p h) (sat_cons (step1136 p h) (sat_cons (step1128 p h) (sat_cons (step1126 p h) (sat_cons (step1134 p h) (sat_cons (step1132 p h) (sat_cons (step1130 p h) (sat_cons (step1129 p h) (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_cons (step2155 p h) (sat_cons (step1464 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step2101 p h) (sat_cons (step1979 p h) (sat_cons (step1452 p h) (sat_cons (step317 p h) (sat_cons (step351 p h) (sat_cons (step1438 p h) (sat_cons (step1436 p h) (sat_cons (step2217 p h) (sat_cons (step1429 p h) (sat_cons (step1430 p h) (sat_cons (step2124 p h) (sat_cons (step380 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c2767 : List Lit := [(1653, false), (1697, true), (1660, true), (75, false), (193, true)]
theorem step2767 (p : Nat → Bool) (h : Constraints p) : clause p c2767 = true :=
  Snake9.LocalRup.prove_clause [c2374, c1637, c1638, c1708, c1622, c2145, c1614, c1647, c2528, c712] c2767 (by decide) p (sat_cons (step2374 p h) (sat_cons (step1637 p h) (sat_cons (step1638 p h) (sat_cons (step1708 p h) (sat_cons (step1622 p h) (sat_cons (step2145 p h) (sat_cons (step1614 p h) (sat_cons (step1647 p h) (sat_cons (step2528 p h) (sat_cons (step712 p h) (sat_nil p)))))))))))
def c2768 : List Lit := [(74, true), (39, false), (1660, true), (75, false), (49, false), (393, true)]
theorem step2768 (p : Nat → Bool) (h : Constraints p) : clause p c2768 = true :=
  Snake9.LocalRup.prove_clause [c1192, c1180, c1177, c1190, c1188, c1182, c2486, c2693, c2528, c1970, c1614, c2527, c1623] c2768 (by decide) p (sat_cons (step1192 p h) (sat_cons (step1180 p h) (sat_cons (step1177 p h) (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1182 p h) (sat_cons (step2486 p h) (sat_cons (step2693 p h) (sat_cons (step2528 p h) (sat_cons (step1970 p h) (sat_cons (step1614 p h) (sat_cons (step2527 p h) (sat_cons (step1623 p h) (sat_nil p))))))))))))))
def c2769 : List Lit := [(1680, false), (74, false), (1697, true), (1652, false), (75, false)]
theorem step2769 (p : Nat → Bool) (h : Constraints p) : clause p c2769 = true :=
  Snake9.LocalRup.prove_clause [c1632, c1702, c2408, c2511, c1708, c1647, c1633, c712, c1622, c1614] c2769 (by decide) p (sat_cons (step1632 p h) (sat_cons (step1702 p h) (sat_cons (step2408 p h) (sat_cons (step2511 p h) (sat_cons (step1708 p h) (sat_cons (step1647 p h) (sat_cons (step1633 p h) (sat_cons (step712 p h) (sat_cons (step1622 p h) (sat_cons (step1614 p h) (sat_nil p)))))))))))
def c2770 : List Lit := [(1780, true), (1665, false), (1670, false), (439, true)]
theorem step2770 (p : Nat → Bool) (h : Constraints p) : clause p c2770 = true :=
  Snake9.LocalRup.prove_clause [c2145, c1715, c1236, c1227, c1888, c2555, c2575, c2724, c2745, c1664, c2554, c2511, c1895, c1716] c2770 (by decide) p (sat_cons (step2145 p h) (sat_cons (step1715 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1888 p h) (sat_cons (step2555 p h) (sat_cons (step2575 p h) (sat_cons (step2724 p h) (sat_cons (step2745 p h) (sat_cons (step1664 p h) (sat_cons (step2554 p h) (sat_cons (step2511 p h) (sat_cons (step1895 p h) (sat_cons (step1716 p h) (sat_nil p)))))))))))))))
def c2771 : List Lit := [(1653, false), (1698, true), (74, false), (32, false), (75, true)]
theorem step2771 (p : Nat → Bool) (h : Constraints p) : clause p c2771 = true :=
  Snake9.LocalRup.prove_clause [c1648, c2145, c1715, c1637, c1638, c1709, c1622, c2161, c1614, c1649, c691] c2771 (by decide) p (sat_cons (step1648 p h) (sat_cons (step2145 p h) (sat_cons (step1715 p h) (sat_cons (step1637 p h) (sat_cons (step1638 p h) (sat_cons (step1709 p h) (sat_cons (step1622 p h) (sat_cons (step2161 p h) (sat_cons (step1614 p h) (sat_cons (step1649 p h) (sat_cons (step691 p h) (sat_nil p))))))))))))
def c2772 : List Lit := [(1697, true), (74, false), (32, false), (1652, false), (75, true)]
theorem step2772 (p : Nat → Bool) (h : Constraints p) : clause p c2772 = true :=
  Snake9.LocalRup.prove_clause [c1632, c1648, c2145, c1702, c1708, c2161, c1633, c1649, c1622, c691, c1614] c2772 (by decide) p (sat_cons (step1632 p h) (sat_cons (step1648 p h) (sat_cons (step2145 p h) (sat_cons (step1702 p h) (sat_cons (step1708 p h) (sat_cons (step2161 p h) (sat_cons (step1633 p h) (sat_cons (step1649 p h) (sat_cons (step1622 p h) (sat_cons (step691 p h) (sat_cons (step1614 p h) (sat_nil p))))))))))))
def c2773 : List Lit := [(103, false), (1594, true), (39, false), (74, false), (32, false), (1660, true), (49, false)]
theorem step2773 (p : Nat → Bool) (h : Constraints p) : clause p c2773 = true :=
  Snake9.LocalRup.prove_clause [c337, c336, c334, c1617, c1461, c1623, c1471, c1614, c1466, c682] c2773 (by decide) p (sat_cons (step337 p h) (sat_cons (step336 p h) (sat_cons (step334 p h) (sat_cons (step1617 p h) (sat_cons (step1461 p h) (sat_cons (step1623 p h) (sat_cons (step1471 p h) (sat_cons (step1614 p h) (sat_cons (step1466 p h) (sat_cons (step682 p h) (sat_nil p)))))))))))
def c2774 : List Lit := [(27, false), (1568, true), (1660, true), (26, false), (10, false), (158, true)]
theorem step2774 (p : Nat → Bool) (h : Constraints p) : clause p c2774 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1414, c1419, c1417, c150, c202, c1615, c200, c1623, c167, c1618] c2774 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1414 p h) (sat_cons (step1419 p h) (sat_cons (step1417 p h) (sat_cons (step150 p h) (sat_cons (step202 p h) (sat_cons (step1615 p h) (sat_cons (step200 p h) (sat_cons (step1623 p h) (sat_cons (step167 p h) (sat_cons (step1618 p h) (sat_nil p))))))))))))
def c2775 : List Lit := [(103, false), (39, false), (1594, true), (51, true), (49, false)]
theorem step2775 (p : Nat → Bool) (h : Constraints p) : clause p c2775 = true :=
  Snake9.LocalRup.prove_clause [c336, c334, c1466, c1461, c1471] c2775 (by decide) p (sat_cons (step336 p h) (sat_cons (step334 p h) (sat_cons (step1466 p h) (sat_cons (step1461 p h) (sat_cons (step1471 p h) (sat_nil p))))))
def c2776 : List Lit := [(1665, false), (1717, false), (106, true), (1750, false), (1671, false), (1700, true), (1783, true), (455, true)]
theorem step2776 (p : Nat → Bool) (h : Constraints p) : clause p c2776 = true :=
  Snake9.LocalRup.prove_clause [c2161, c1252, c1236, c1227, c1717, c1716, c2576, c1898, c1664, c1858, c2708, c2731, c1758] c2776 (by decide) p (sat_cons (step2161 p h) (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step1717 p h) (sat_cons (step1716 p h) (sat_cons (step2576 p h) (sat_cons (step1898 p h) (sat_cons (step1664 p h) (sat_cons (step1858 p h) (sat_cons (step2708 p h) (sat_cons (step2731 p h) (sat_cons (step1758 p h) (sat_nil p))))))))))))))
def c2777 : List Lit := [(39, false), (1615, true), (1568, false), (49, false), (14, false), (169, true)]
theorem step2777 (p : Nat → Bool) (h : Constraints p) : clause p c2777 = true :=
  Snake9.LocalRup.prove_clause [c1445, c1519, c1503, c323, c322, c1465, c1461, c1470, c1471, c1498, c1466, c1526, c2537, c1446] c2777 (by decide) p (sat_cons (step1445 p h) (sat_cons (step1519 p h) (sat_cons (step1503 p h) (sat_cons (step323 p h) (sat_cons (step322 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step1470 p h) (sat_cons (step1471 p h) (sat_cons (step1498 p h) (sat_cons (step1466 p h) (sat_cons (step1526 p h) (sat_cons (step2537 p h) (sat_cons (step1446 p h) (sat_nil p)))))))))))))))
def c2778 : List Lit := [(103, true), (1750, false), (1700, true), (1783, true), (1670, false), (1666, false), (455, true)]
theorem step2778 (p : Nat → Bool) (h : Constraints p) : clause p c2778 = true :=
  Snake9.LocalRup.prove_clause [c2293, c1764, c2739] c2778 (by decide) p (sat_cons (step2293 p h) (sat_cons (step1764 p h) (sat_cons (step2739 p h) (sat_nil p))))
def c2779 : List Lit := [(1535, true), (34, false), (26, true), (299, true)]
theorem step2779 (p : Nat → Bool) (h : Constraints p) : clause p c2779 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1075, c1077, c1076, c1356, c1357, c173, c2460, c2206] c2779 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1075 p h) (sat_cons (step1077 p h) (sat_cons (step1076 p h) (sat_cons (step1356 p h) (sat_cons (step1357 p h) (sat_cons (step173 p h) (sat_cons (step2460 p h) (sat_cons (step2206 p h) (sat_nil p))))))))))
end B112E089
