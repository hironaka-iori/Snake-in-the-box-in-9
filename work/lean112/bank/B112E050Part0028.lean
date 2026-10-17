import B112E050Part0027
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c3608 : List Lit := [(1597, true), (1580, false), (30, false), (44, true), (102, true)]
theorem step3608 (p : Nat → Bool) (h : Constraints p) : clause p c3608 = true :=
  Snake9.LocalRup.prove_clause [c1864, c3183, c1160, c1156, c1133, c3129, c1862, c2038, c3580, c3575] c3608 (by decide) p (sat_cons (step1864 p h) (sat_cons (step3183 p h) (sat_cons (step1160 p h) (sat_cons (step1156 p h) (sat_cons (step1133 p h) (sat_cons (step3129 p h) (sat_cons (step1862 p h) (sat_cons (step2038 p h) (sat_cons (step3580 p h) (sat_cons (step3575 p h) (sat_nil p)))))))))))
def c3609 : List Lit := [(1745, true), (1739, false), (1741, false), (49, true), (56, false), (53, false), (54, false), (93, false), (1581, true)]
theorem step3609 (p : Nat → Bool) (h : Constraints p) : clause p c3609 = true :=
  Snake9.LocalRup.prove_clause [c200, c1443, c1445, c3533, c3556, c1127, c3472, c2066, c2280, c179] c3609 (by decide) p (sat_cons (step200 p h) (sat_cons (step1443 p h) (sat_cons (step1445 p h) (sat_cons (step3533 p h) (sat_cons (step3556 p h) (sat_cons (step1127 p h) (sat_cons (step3472 p h) (sat_cons (step2066 p h) (sat_cons (step2280 p h) (sat_cons (step179 p h) (sat_nil p)))))))))))
def c3610 : List Lit := [(1817, true), (1636, true), (123, false), (46, false)]
theorem step3610 (p : Nat → Bool) (h : Constraints p) : clause p c3610 = true :=
  Snake9.LocalRup.prove_clause [c1616, c2234, c3584, c2333, c736, c1759, c1573, c1919, c1582] c3610 (by decide) p (sat_cons (step1616 p h) (sat_cons (step2234 p h) (sat_cons (step3584 p h) (sat_cons (step2333 p h) (sat_cons (step736 p h) (sat_cons (step1759 p h) (sat_cons (step1573 p h) (sat_cons (step1919 p h) (sat_cons (step1582 p h) (sat_nil p))))))))))
def c3611 : List Lit := [(1831, false), (1855, true), (1745, false), (1580, false), (123, false)]
theorem step3611 (p : Nat → Bool) (h : Constraints p) : clause p c3611 = true :=
  Snake9.LocalRup.prove_clause [c3549, c1706] c3611 (by decide) p (sat_cons (step3549 p h) (sat_cons (step1706 p h) (sat_nil p)))
def c3612 : List Lit := [(1765, false), (1856, true)]
theorem step3612 (p : Nat → Bool) (h : Constraints p) : clause p c3612 = true :=
  Snake9.LocalRup.prove_clause [c3017, c1731] c3612 (by decide) p (sat_cons (step3017 p h) (sat_cons (step1731 p h) (sat_nil p)))
def c3613 : List Lit := [(1792, false), (1831, true)]
theorem step3613 (p : Nat → Bool) (h : Constraints p) : clause p c3613 = true :=
  Snake9.LocalRup.prove_clause [c3266, c1660] c3613 (by decide) p (sat_cons (step3266 p h) (sat_cons (step1660 p h) (sat_nil p)))
def c3614 : List Lit := [(1790, false), (1829, true)]
theorem step3614 (p : Nat → Bool) (h : Constraints p) : clause p c3614 = true :=
  Snake9.LocalRup.prove_clause [c3266, c1647] c3614 (by decide) p (sat_cons (step3266 p h) (sat_cons (step1647 p h) (sat_nil p)))
def c3615 : List Lit := [(1793, false), (1832, true)]
theorem step3615 (p : Nat → Bool) (h : Constraints p) : clause p c3615 = true :=
  Snake9.LocalRup.prove_clause [c3266, c1666] c3615 (by decide) p (sat_cons (step3266 p h) (sat_cons (step1666 p h) (sat_nil p)))
def c3616 : List Lit := [(1794, false), (1833, true)]
theorem step3616 (p : Nat → Bool) (h : Constraints p) : clause p c3616 = true :=
  Snake9.LocalRup.prove_clause [c3266, c1671] c3616 (by decide) p (sat_cons (step3266 p h) (sat_cons (step1671 p h) (sat_nil p)))
def c3617 : List Lit := [(1850, true), (1759, false)]
theorem step3617 (p : Nat → Bool) (h : Constraints p) : clause p c3617 = true :=
  Snake9.LocalRup.prove_clause [c3017, c1687] c3617 (by decide) p (sat_cons (step3017 p h) (sat_cons (step1687 p h) (sat_nil p)))
def c3618 : List Lit := [(1851, true), (1760, false)]
theorem step3618 (p : Nat → Bool) (h : Constraints p) : clause p c3618 = true :=
  Snake9.LocalRup.prove_clause [c3017, c1695] c3618 (by decide) p (sat_cons (step3017 p h) (sat_cons (step1695 p h) (sat_nil p)))
def c3619 : List Lit := [(1853, true), (1762, false)]
theorem step3619 (p : Nat → Bool) (h : Constraints p) : clause p c3619 = true :=
  Snake9.LocalRup.prove_clause [c3017, c1710] c3619 (by decide) p (sat_cons (step3017 p h) (sat_cons (step1710 p h) (sat_nil p)))
def c3620 : List Lit := [(1852, true), (1761, false)]
theorem step3620 (p : Nat → Bool) (h : Constraints p) : clause p c3620 = true :=
  Snake9.LocalRup.prove_clause [c3017, c1703] c3620 (by decide) p (sat_cons (step3017 p h) (sat_cons (step1703 p h) (sat_nil p)))
def c3621 : List Lit := [(1830, true), (1791, false)]
theorem step3621 (p : Nat → Bool) (h : Constraints p) : clause p c3621 = true :=
  Snake9.LocalRup.prove_clause [c3266, c1654] c3621 (by decide) p (sat_cons (step3266 p h) (sat_cons (step1654 p h) (sat_nil p)))
def c3622 : List Lit := [(1764, false), (1855, true)]
theorem step3622 (p : Nat → Bool) (h : Constraints p) : clause p c3622 = true :=
  Snake9.LocalRup.prove_clause [c3017, c1725] c3622 (by decide) p (sat_cons (step3017 p h) (sat_cons (step1725 p h) (sat_nil p)))
def c3623 : List Lit := [(1763, false), (1854, true)]
theorem step3623 (p : Nat → Bool) (h : Constraints p) : clause p c3623 = true :=
  Snake9.LocalRup.prove_clause [c3017, c1718] c3623 (by decide) p (sat_cons (step3017 p h) (sat_cons (step1718 p h) (sat_nil p)))
def c3624 : List Lit := [(1827, true), (1775, false)]
theorem step3624 (p : Nat → Bool) (h : Constraints p) : clause p c3624 = true :=
  Snake9.LocalRup.prove_clause [c3266, c2694] c3624 (by decide) p (sat_cons (step3266 p h) (sat_cons (step2694 p h) (sat_nil p)))
def c3625 : List Lit := [(1777, false), (123, true), (1830, true), (108, true)]
theorem step3625 (p : Nat → Bool) (h : Constraints p) : clause p c3625 = true :=
  Snake9.LocalRup.prove_clause [c3266, c2595] c3625 (by decide) p (sat_cons (step3266 p h) (sat_cons (step2595 p h) (sat_nil p)))
def c3626 : List Lit := [(1829, true), (1777, false)]
theorem step3626 (p : Nat → Bool) (h : Constraints p) : clause p c3626 = true :=
  Snake9.LocalRup.prove_clause [c3266, c3088] c3626 (by decide) p (sat_cons (step3266 p h) (sat_cons (step3088 p h) (sat_nil p)))
def c3627 : List Lit := [(1707, true), (1773, false), (57, true), (56, false), (96, true), (1790, true)]
theorem step3627 (p : Nat → Bool) (h : Constraints p) : clause p c3627 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1369, c1370, c237, c2088, c1911, c3103, c1520, c1536, c1530, c1538, c1561] c3627 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step237 p h) (sat_cons (step2088 p h) (sat_cons (step1911 p h) (sat_cons (step3103 p h) (sat_cons (step1520 p h) (sat_cons (step1536 p h) (sat_cons (step1530 p h) (sat_cons (step1538 p h) (sat_cons (step1561 p h) (sat_nil p)))))))))))))
def c3628 : List Lit := [(27, false), (44, true), (30, false), (102, true), (108, false)]
theorem step3628 (p : Nat → Bool) (h : Constraints p) : clause p c3628 = true :=
  Snake9.LocalRup.prove_clause [c2037, c87] c3628 (by decide) p (sat_cons (step2037 p h) (sat_cons (step87 p h) (sat_nil p)))
def c3629 : List Lit := [(1591, false), (1712, false), (1762, false), (1751, false), (61, true), (62, false), (54, false), (93, false), (1829, false), (1817, false), (1658, false), (123, false)]
theorem step3629 (p : Nat → Bool) (h : Constraints p) : clause p c3629 = true :=
  Snake9.LocalRup.prove_clause [c2293, c1290, c1868, c2380, c2247, c1726, c1713, c1509, c1655, c1409, c2587, c2080, c587, c584, c586, c1536, c1523, c1538, c1525, c3203, c1125, c1864, c1156, c2203, c1348, c2248, c1712, c1648, c1561, c1557, c1528, c1541, c1519, c1533, c471] c3629 (by decide) p (sat_cons (step2293 p h) (sat_cons (step1290 p h) (sat_cons (step1868 p h) (sat_cons (step2380 p h) (sat_cons (step2247 p h) (sat_cons (step1726 p h) (sat_cons (step1713 p h) (sat_cons (step1509 p h) (sat_cons (step1655 p h) (sat_cons (step1409 p h) (sat_cons (step2587 p h) (sat_cons (step2080 p h) (sat_cons (step587 p h) (sat_cons (step584 p h) (sat_cons (step586 p h) (sat_cons (step1536 p h) (sat_cons (step1523 p h) (sat_cons (step1538 p h) (sat_cons (step1525 p h) (sat_cons (step3203 p h) (sat_cons (step1125 p h) (sat_cons (step1864 p h) (sat_cons (step1156 p h) (sat_cons (step2203 p h) (sat_cons (step1348 p h) (sat_cons (step2248 p h) (sat_cons (step1712 p h) (sat_cons (step1648 p h) (sat_cons (step1561 p h) (sat_cons (step1557 p h) (sat_cons (step1528 p h) (sat_cons (step1541 p h) (sat_cons (step1519 p h) (sat_cons (step1533 p h) (sat_cons (step471 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c3630 : List Lit := [(1659, true), (1829, false), (1817, false), (46, true), (1745, false), (1636, true), (1725, false), (123, false)]
theorem step3630 (p : Nat → Bool) (h : Constraints p) : clause p c3630 = true :=
  Snake9.LocalRup.prove_clause [c2293, c1233, c1240, c1264, c1290, c1889, c3411, c3426, c1261, c1269, c2750, c1265, c1243, c1241, c1252, c1254, c1234, c1235, c1236, c1250, c1246, c1247, c200, c3020, c2377, c221, c3138, c2077, c1459, c170, c1495, c1373, c1378, c3629, c3129, c567, c2080, c2587, c310, c1409, c1099, c1509, c1896, c1726, c1175, c2247, c1339] c3630 (by decide) p (sat_cons (step2293 p h) (sat_cons (step1233 p h) (sat_cons (step1240 p h) (sat_cons (step1264 p h) (sat_cons (step1290 p h) (sat_cons (step1889 p h) (sat_cons (step3411 p h) (sat_cons (step3426 p h) (sat_cons (step1261 p h) (sat_cons (step1269 p h) (sat_cons (step2750 p h) (sat_cons (step1265 p h) (sat_cons (step1243 p h) (sat_cons (step1241 p h) (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step1234 p h) (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step1250 p h) (sat_cons (step1246 p h) (sat_cons (step1247 p h) (sat_cons (step200 p h) (sat_cons (step3020 p h) (sat_cons (step2377 p h) (sat_cons (step221 p h) (sat_cons (step3138 p h) (sat_cons (step2077 p h) (sat_cons (step1459 p h) (sat_cons (step170 p h) (sat_cons (step1495 p h) (sat_cons (step1373 p h) (sat_cons (step1378 p h) (sat_cons (step3629 p h) (sat_cons (step3129 p h) (sat_cons (step567 p h) (sat_cons (step2080 p h) (sat_cons (step2587 p h) (sat_cons (step310 p h) (sat_cons (step1409 p h) (sat_cons (step1099 p h) (sat_cons (step1509 p h) (sat_cons (step1896 p h) (sat_cons (step1726 p h) (sat_cons (step1175 p h) (sat_cons (step2247 p h) (sat_cons (step1339 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c3631 : List Lit := [(1597, false), (1644, false), (46, true), (102, true), (1609, true), (1693, true), (123, false)]
theorem step3631 (p : Nat → Bool) (h : Constraints p) : clause p c3631 = true :=
  Snake9.LocalRup.prove_clause [c2293, c2203, c1177, c1350, c1896, c1292, c1099, c2976] c3631 (by decide) p (sat_cons (step2293 p h) (sat_cons (step2203 p h) (sat_cons (step1177 p h) (sat_cons (step1350 p h) (sat_cons (step1896 p h) (sat_cons (step1292 p h) (sat_cons (step1099 p h) (sat_cons (step2976 p h) (sat_nil p)))))))))
def c3632 : List Lit := [(96, false), (93, false), (1580, true), (1645, true)]
theorem step3632 (p : Nat → Bool) (h : Constraints p) : clause p c3632 = true :=
  Snake9.LocalRup.prove_clause [c1126, c1125, c1754, c2383, c2028] c3632 (by decide) p (sat_cons (step1126 p h) (sat_cons (step1125 p h) (sat_cons (step1754 p h) (sat_cons (step2383 p h) (sat_cons (step2028 p h) (sat_nil p))))))
def c3633 : List Lit := [(1607, true), (21, true), (123, false), (1595, false), (102, true)]
theorem step3633 (p : Nat → Bool) (h : Constraints p) : clause p c3633 = true :=
  Snake9.LocalRup.prove_clause [c2202, c1175, c2873, c1896, c1099] c3633 (by decide) p (sat_cons (step2202 p h) (sat_cons (step1175 p h) (sat_cons (step2873 p h) (sat_cons (step1896 p h) (sat_cons (step1099 p h) (sat_nil p))))))
def c3634 : List Lit := [(1596, true), (21, true), (44, true), (30, false), (102, true)]
theorem step3634 (p : Nat → Bool) (h : Constraints p) : clause p c3634 = true :=
  Snake9.LocalRup.prove_clause [c1868, c3129, c2038, c2828] c3634 (by decide) p (sat_cons (step1868 p h) (sat_cons (step3129 p h) (sat_cons (step2038 p h) (sat_cons (step2828 p h) (sat_nil p)))))
def c3635 : List Lit := [(1829, true), (95, false), (108, true), (1776, false), (93, true)]
theorem step3635 (p : Nat → Bool) (h : Constraints p) : clause p c3635 = true :=
  Snake9.LocalRup.prove_clause [c3626, c2875, c3073, c3492, c1532, c1533, c2338, c615, c2138] c3635 (by decide) p (sat_cons (step3626 p h) (sat_cons (step2875 p h) (sat_cons (step3073 p h) (sat_cons (step3492 p h) (sat_cons (step1532 p h) (sat_cons (step1533 p h) (sat_cons (step2338 p h) (sat_cons (step615 p h) (sat_cons (step2138 p h) (sat_nil p))))))))))
def c3636 : List Lit := [(503, false), (80, false), (1736, true), (123, false)]
theorem step3636 (p : Nat → Bool) (h : Constraints p) : clause p c3636 = true :=
  Snake9.LocalRup.prove_clause [c1089, c2199, c2200, c1047, c1007, c1028, c956, c1026, c919, c1018, c917, c1017, c916, c913, c2024, c320, c317, c1423, c297, c1428, c2919] c3636 (by decide) p (sat_cons (step1089 p h) (sat_cons (step2199 p h) (sat_cons (step2200 p h) (sat_cons (step1047 p h) (sat_cons (step1007 p h) (sat_cons (step1028 p h) (sat_cons (step956 p h) (sat_cons (step1026 p h) (sat_cons (step919 p h) (sat_cons (step1018 p h) (sat_cons (step917 p h) (sat_cons (step1017 p h) (sat_cons (step916 p h) (sat_cons (step913 p h) (sat_cons (step2024 p h) (sat_cons (step320 p h) (sat_cons (step317 p h) (sat_cons (step1423 p h) (sat_cons (step297 p h) (sat_cons (step1428 p h) (sat_cons (step2919 p h) (sat_nil p))))))))))))))))))))))
def c3637 : List Lit := [(1659, false), (1831, false), (1580, false), (91, false), (1736, true), (123, false)]
theorem step3637 (p : Nat → Bool) (h : Constraints p) : clause p c3637 = true :=
  Snake9.LocalRup.prove_clause [c2293, c1291, c3558, c3366, c2249] c3637 (by decide) p (sat_cons (step2293 p h) (sat_cons (step1291 p h) (sat_cons (step3558 p h) (sat_cons (step3366 p h) (sat_cons (step2249 p h) (sat_nil p))))))
def c3638 : List Lit := [(1779, false), (1777, false), (113, true), (108, true), (93, true), (1831, true)]
theorem step3638 (p : Nat → Bool) (h : Constraints p) : clause p c3638 = true :=
  Snake9.LocalRup.prove_clause [c3613, c1563, c1536, c1541, c1542, c1562, c1537, c1655, c2582, c2758] c3638 (by decide) p (sat_cons (step3613 p h) (sat_cons (step1563 p h) (sat_cons (step1536 p h) (sat_cons (step1541 p h) (sat_cons (step1542 p h) (sat_cons (step1562 p h) (sat_cons (step1537 p h) (sat_cons (step1655 p h) (sat_cons (step2582 p h) (sat_cons (step2758 p h) (sat_nil p)))))))))))
def c3639 : List Lit := [(1777, false), (1801, false), (108, true), (1831, true)]
theorem step3639 (p : Nat → Bool) (h : Constraints p) : clause p c3639 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1655, c1536, c1538, c1561, c1562, c1649, c1539, c1617, c1537, c2582] c3639 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1655 p h) (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1561 p h) (sat_cons (step1562 p h) (sat_cons (step1649 p h) (sat_cons (step1539 p h) (sat_cons (step1617 p h) (sat_cons (step1537 p h) (sat_cons (step2582 p h) (sat_nil p))))))))))))
def c3640 : List Lit := [(88, false), (89, false), (113, true), (104, false), (108, true), (102, true), (1831, true), (91, false), (123, false)]
theorem step3640 (p : Nat → Bool) (h : Constraints p) : clause p c3640 = true :=
  Snake9.LocalRup.prove_clause [c417, c1789, c416, c2118, c1519, c752, c749, c1573, c1572, c1582, c3639, c1528, c1523, c2861, c2134] c3640 (by decide) p (sat_cons (step417 p h) (sat_cons (step1789 p h) (sat_cons (step416 p h) (sat_cons (step2118 p h) (sat_cons (step1519 p h) (sat_cons (step752 p h) (sat_cons (step749 p h) (sat_cons (step1573 p h) (sat_cons (step1572 p h) (sat_cons (step1582 p h) (sat_cons (step3639 p h) (sat_cons (step1528 p h) (sat_cons (step1523 p h) (sat_cons (step2861 p h) (sat_cons (step2134 p h) (sat_nil p))))))))))))))))
def c3641 : List Lit := [(100, true), (90, true), (96, true), (1774, true), (1777, true), (104, false), (102, true)]
theorem step3641 (p : Nat → Bool) (h : Constraints p) : clause p c3641 = true :=
  Snake9.LocalRup.prove_clause [c1523, c2861, c2134] c3641 (by decide) p (sat_cons (step1523 p h) (sat_cons (step2861 p h) (sat_cons (step2134 p h) (sat_nil p))))
def c3642 : List Lit := [(1801, false), (1831, true), (1776, false), (1805, false), (108, true), (104, false)]
theorem step3642 (p : Nat → Bool) (h : Constraints p) : clause p c3642 = true :=
  Snake9.LocalRup.prove_clause [c1536, c1538, c1556, c1643, c1590, c1595, c1617, c1618, c1649, c2001, c1557, c1537, c1539] c3642 (by decide) p (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1556 p h) (sat_cons (step1643 p h) (sat_cons (step1590 p h) (sat_cons (step1595 p h) (sat_cons (step1617 p h) (sat_cons (step1618 p h) (sat_cons (step1649 p h) (sat_cons (step2001 p h) (sat_cons (step1557 p h) (sat_cons (step1537 p h) (sat_cons (step1539 p h) (sat_nil p))))))))))))))
def c3643 : List Lit := [(1795, true), (114, false), (91, false)]
theorem step3643 (p : Nat → Bool) (h : Constraints p) : clause p c3643 = true :=
  Snake9.LocalRup.prove_clause [c1570, c1571, c747] c3643 (by decide) p (sat_cons (step1570 p h) (sat_cons (step1571 p h) (sat_cons (step747 p h) (sat_nil p))))
def c3644 : List Lit := [(123, false), (1796, true), (114, false), (91, false)]
theorem step3644 (p : Nat → Bool) (h : Constraints p) : clause p c3644 = true :=
  Snake9.LocalRup.prove_clause [c751, c749, c1572] c3644 (by decide) p (sat_cons (step751 p h) (sat_cons (step749 p h) (sat_cons (step1572 p h) (sat_nil p))))
def c3645 : List Lit := [(1796, true), (114, false), (91, false), (1807, false), (1818, true)]
theorem step3645 (p : Nat → Bool) (h : Constraints p) : clause p c3645 = true :=
  Snake9.LocalRup.prove_clause [c3643, c3644, c1584, c1599, c1613, c1579, c1573, c750, c748, c1572] c3645 (by decide) p (sat_cons (step3643 p h) (sat_cons (step3644 p h) (sat_cons (step1584 p h) (sat_cons (step1599 p h) (sat_cons (step1613 p h) (sat_cons (step1579 p h) (sat_cons (step1573 p h) (sat_cons (step750 p h) (sat_cons (step748 p h) (sat_cons (step1572 p h) (sat_nil p)))))))))))
def c3646 : List Lit := [(114, false), (91, false), (1807, false), (1818, true), (1801, true)]
theorem step3646 (p : Nat → Bool) (h : Constraints p) : clause p c3646 = true :=
  Snake9.LocalRup.prove_clause [c3645, c1581, c1582, c1613, c1573, c1599, c752, c1584] c3646 (by decide) p (sat_cons (step3645 p h) (sat_cons (step1581 p h) (sat_cons (step1582 p h) (sat_cons (step1613 p h) (sat_cons (step1573 p h) (sat_cons (step1599 p h) (sat_cons (step752 p h) (sat_cons (step1584 p h) (sat_nil p)))))))))
def c3647 : List Lit := [(1691, true), (1669, false), (1580, false), (1644, false), (102, true), (1595, false), (123, false)]
theorem step3647 (p : Nat → Bool) (h : Constraints p) : clause p c3647 = true :=
  Snake9.LocalRup.prove_clause [c2293, c1340, c3056, c1175, c2406, c1896, c1099] c3647 (by decide) p (sat_cons (step2293 p h) (sat_cons (step1340 p h) (sat_cons (step3056 p h) (sat_cons (step1175 p h) (sat_cons (step2406 p h) (sat_cons (step1896 p h) (sat_cons (step1099 p h) (sat_nil p))))))))
def c3648 : List Lit := [(1659, true), (1751, true), (1763, true), (1744, false), (53, true), (102, true), (115, false), (123, false), (103, false)]
theorem step3648 (p : Nat → Bool) (h : Constraints p) : clause p c3648 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1238, c1269, c1265, c3115, c1239, c1241, c1252, c1254, c1237, c1232, c1250, c1247, c473, c1985, c3177, c2587, c330, c329, c327, c324, c1907, c3138, c1424, c1388, c1370, c2712] c3648 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1238 p h) (sat_cons (step1269 p h) (sat_cons (step1265 p h) (sat_cons (step3115 p h) (sat_cons (step1239 p h) (sat_cons (step1241 p h) (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step1237 p h) (sat_cons (step1232 p h) (sat_cons (step1250 p h) (sat_cons (step1247 p h) (sat_cons (step473 p h) (sat_cons (step1985 p h) (sat_cons (step3177 p h) (sat_cons (step2587 p h) (sat_cons (step330 p h) (sat_cons (step329 p h) (sat_cons (step327 p h) (sat_cons (step324 p h) (sat_cons (step1907 p h) (sat_cons (step3138 p h) (sat_cons (step1424 p h) (sat_cons (step1388 p h) (sat_cons (step1370 p h) (sat_cons (step2712 p h) (sat_nil p))))))))))))))))))))))))))))
def c3649 : List Lit := [(1807, true), (100, false), (1797, true), (103, false)]
theorem step3649 (p : Nat → Bool) (h : Constraints p) : clause p c3649 = true :=
  Snake9.LocalRup.prove_clause [c1590, c1588, c3587, c638, c3010] c3649 (by decide) p (sat_cons (step1590 p h) (sat_cons (step1588 p h) (sat_cons (step3587 p h) (sat_cons (step638 p h) (sat_cons (step3010 p h) (sat_nil p))))))
def c3650 : List Lit := [(1791, false), (1855, true), (1725, false), (1817, false), (1744, false), (1580, false), (53, true), (102, true), (115, false), (123, false), (91, false), (103, false)]
theorem step3650 (p : Nat → Bool) (h : Constraints p) : clause p c3650 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1238, c1264, c2475, c2247, c3621, c1720, c1712, c1495, c3648, c1655, c3637, c1706, c1458, c1494] c3650 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1238 p h) (sat_cons (step1264 p h) (sat_cons (step2475 p h) (sat_cons (step2247 p h) (sat_cons (step3621 p h) (sat_cons (step1720 p h) (sat_cons (step1712 p h) (sat_cons (step1495 p h) (sat_cons (step3648 p h) (sat_cons (step1655 p h) (sat_cons (step3637 p h) (sat_cons (step1706 p h) (sat_cons (step1458 p h) (sat_cons (step1494 p h) (sat_nil p))))))))))))))))
def c3651 : List Lit := [(1745, false), (1750, true), (1761, true), (87, false), (1732, true), (1830, false), (1580, false), (114, true), (123, false)]
theorem step3651 (p : Nat → Bool) (h : Constraints p) : clause p c3651 = true :=
  Snake9.LocalRup.prove_clause [c2293, c1449, c1454, c3100, c1500, c1425, c1945, c1697, c1423, c2250, c3312, c3448] c3651 (by decide) p (sat_cons (step2293 p h) (sat_cons (step1449 p h) (sat_cons (step1454 p h) (sat_cons (step3100 p h) (sat_cons (step1500 p h) (sat_cons (step1425 p h) (sat_cons (step1945 p h) (sat_cons (step1697 p h) (sat_cons (step1423 p h) (sat_cons (step2250 p h) (sat_cons (step3312 p h) (sat_cons (step3448 p h) (sat_nil p)))))))))))))
def c3652 : List Lit := [(1659, false), (44, false), (1693, true), (1596, false), (1583, false), (123, false)]
theorem step3652 (p : Nat → Bool) (h : Constraints p) : clause p c3652 = true :=
  Snake9.LocalRup.prove_clause [c2202, c1342, c2293, c1291, c1305, c1357, c3438, c1298, c1350, c2203, c1176, c1156, c1896, c1099, c2668, c138, c1187, c3129] c3652 (by decide) p (sat_cons (step2202 p h) (sat_cons (step1342 p h) (sat_cons (step2293 p h) (sat_cons (step1291 p h) (sat_cons (step1305 p h) (sat_cons (step1357 p h) (sat_cons (step3438 p h) (sat_cons (step1298 p h) (sat_cons (step1350 p h) (sat_cons (step2203 p h) (sat_cons (step1176 p h) (sat_cons (step1156 p h) (sat_cons (step1896 p h) (sat_cons (step1099 p h) (sat_cons (step2668 p h) (sat_cons (step138 p h) (sat_cons (step1187 p h) (sat_cons (step3129 p h) (sat_nil p)))))))))))))))))))
def c3653 : List Lit := [(1726, true), (1707, false), (1732, true), (62, true), (53, false), (1655, true), (80, true), (114, true)]
theorem step3653 (p : Nat → Bool) (h : Constraints p) : clause p c3653 = true :=
  Snake9.LocalRup.prove_clause [c1377, c1253, c1251, c1416, c3347, c1404, c3345, c1412, c1379, c3346, c2656, c3341, c1383, c1385, c1393, c3043, c2094, c2095, c1374, c267, c276, c1388] c3653 (by decide) p (sat_cons (step1377 p h) (sat_cons (step1253 p h) (sat_cons (step1251 p h) (sat_cons (step1416 p h) (sat_cons (step3347 p h) (sat_cons (step1404 p h) (sat_cons (step3345 p h) (sat_cons (step1412 p h) (sat_cons (step1379 p h) (sat_cons (step3346 p h) (sat_cons (step2656 p h) (sat_cons (step3341 p h) (sat_cons (step1383 p h) (sat_cons (step1385 p h) (sat_cons (step1393 p h) (sat_cons (step3043 p h) (sat_cons (step2094 p h) (sat_cons (step2095 p h) (sat_cons (step1374 p h) (sat_cons (step267 p h) (sat_cons (step276 p h) (sat_cons (step1388 p h) (sat_nil p)))))))))))))))))))))))
def c3654 : List Lit := [(1692, true), (27, true), (44, false), (1596, false), (1658, false), (1583, false), (123, false)]
theorem step3654 (p : Nat → Bool) (h : Constraints p) : clause p c3654 = true :=
  Snake9.LocalRup.prove_clause [c2202, c2293, c1290, c1356, c1341, c3438, c1304, c1297, c1349, c2203, c1176, c1156, c1896, c3129, c1099, c1187, c2668] c3654 (by decide) p (sat_cons (step2202 p h) (sat_cons (step2293 p h) (sat_cons (step1290 p h) (sat_cons (step1356 p h) (sat_cons (step1341 p h) (sat_cons (step3438 p h) (sat_cons (step1304 p h) (sat_cons (step1297 p h) (sat_cons (step1349 p h) (sat_cons (step2203 p h) (sat_cons (step1176 p h) (sat_cons (step1156 p h) (sat_cons (step1896 p h) (sat_cons (step3129 p h) (sat_cons (step1099 p h) (sat_cons (step1187 p h) (sat_cons (step2668 p h) (sat_nil p))))))))))))))))))
def c3655 : List Lit := [(1771, true), (93, false), (1745, true), (1644, true), (123, false)]
theorem step3655 (p : Nat → Bool) (h : Constraints p) : clause p c3655 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1235, c1518, c1519, c3424, c3533, c1443] c3655 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1235 p h) (sat_cons (step1518 p h) (sat_cons (step1519 p h) (sat_cons (step3424 p h) (sat_cons (step3533 p h) (sat_cons (step1443 p h) (sat_nil p))))))))
def c3656 : List Lit := [(1739, true), (96, false), (49, true), (57, true), (56, false), (53, false)]
theorem step3656 (p : Nat → Bool) (h : Constraints p) : clause p c3656 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1434, c410, c179, c2066] c3656 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step410 p h) (sat_cons (step179 p h) (sat_cons (step2066 p h) (sat_nil p))))))
def c3657 : List Lit := [(102, false), (91, false), (1774, true), (123, false)]
theorem step3657 (p : Nat → Bool) (h : Constraints p) : clause p c3657 = true :=
  Snake9.LocalRup.prove_clause [c592, c590, c1523] c3657 (by decide) p (sat_cons (step592 p h) (sat_cons (step590 p h) (sat_cons (step1523 p h) (sat_nil p))))
def c3658 : List Lit := [(1636, true), (1692, true), (1811, true), (1829, false), (1745, false), (35, true), (1817, false), (1580, false), (1774, true), (91, false), (123, false)]
theorem step3658 (p : Nat → Bool) (h : Constraints p) : clause p c3658 = true :=
  Snake9.LocalRup.prove_clause [c3657, c3605, c2293, c3603, c3584, c2203, c1233, c1349, c1240, c1291, c1265, c3630, c1252, c3330, c1250] c3658 (by decide) p (sat_cons (step3657 p h) (sat_cons (step3605 p h) (sat_cons (step2293 p h) (sat_cons (step3603 p h) (sat_cons (step3584 p h) (sat_cons (step2203 p h) (sat_cons (step1233 p h) (sat_cons (step1349 p h) (sat_cons (step1240 p h) (sat_cons (step1291 p h) (sat_cons (step1265 p h) (sat_cons (step3630 p h) (sat_cons (step1252 p h) (sat_cons (step3330 p h) (sat_cons (step1250 p h) (sat_nil p))))))))))))))))
def c3659 : List Lit := [(1658, true), (96, false)]
theorem step3659 (p : Nat → Bool) (h : Constraints p) : clause p c3659 = true :=
  Snake9.LocalRup.prove_clause [c1260, c1264, c1252, c1254, c1238, c1240, c1250, c1246, c1232, c221, c2539] c3659 (by decide) p (sat_cons (step1260 p h) (sat_cons (step1264 p h) (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1250 p h) (sat_cons (step1246 p h) (sat_cons (step1232 p h) (sat_cons (step221 p h) (sat_cons (step2539 p h) (sat_nil p))))))))))))
def c3660 : List Lit := [(1654, true), (51, false), (1764, true), (1745, false), (102, true), (123, false)]
theorem step3660 (p : Nat → Bool) (h : Constraints p) : clause p c3660 = true :=
  Snake9.LocalRup.prove_clause [c1252, c1254, c1249, c1250, c1246, c1247, c221, c2377, c2077, c2080, c2081, c3138, c170, c330, c1993, c1459, c1424, c3501] c3660 (by decide) p (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step1249 p h) (sat_cons (step1250 p h) (sat_cons (step1246 p h) (sat_cons (step1247 p h) (sat_cons (step221 p h) (sat_cons (step2377 p h) (sat_cons (step2077 p h) (sat_cons (step2080 p h) (sat_cons (step2081 p h) (sat_cons (step3138 p h) (sat_cons (step170 p h) (sat_cons (step330 p h) (sat_cons (step1993 p h) (sat_cons (step1459 p h) (sat_cons (step1424 p h) (sat_cons (step3501 p h) (sat_nil p)))))))))))))))))))
def c3661 : List Lit := [(1642, true), (1764, true), (1646, false), (1802, false), (1761, false), (1776, false), (1745, false), (35, true), (1580, false), (102, true), (123, false)]
theorem step3661 (p : Nat → Bool) (h : Constraints p) : clause p c3661 = true :=
  Snake9.LocalRup.prove_clause [c1621, c1555, c2293, c1232, c1233, c3660, c1265, c1291, c3547, c1637, c1623, c2693, c3132, c1556, c2058, c1642, c3478, c1705, c2249] c3661 (by decide) p (sat_cons (step1621 p h) (sat_cons (step1555 p h) (sat_cons (step2293 p h) (sat_cons (step1232 p h) (sat_cons (step1233 p h) (sat_cons (step3660 p h) (sat_cons (step1265 p h) (sat_cons (step1291 p h) (sat_cons (step3547 p h) (sat_cons (step1637 p h) (sat_cons (step1623 p h) (sat_cons (step2693 p h) (sat_cons (step3132 p h) (sat_cons (step1556 p h) (sat_cons (step2058 p h) (sat_cons (step1642 p h) (sat_cons (step3478 p h) (sat_cons (step1705 p h) (sat_cons (step2249 p h) (sat_nil p))))))))))))))))))))
def c3662 : List Lit := [(103, false), (1761, false), (1776, false), (93, false), (1745, false), (114, false), (1580, false), (96, false), (102, true), (91, false), (123, false)]
theorem step3662 (p : Nat → Bool) (h : Constraints p) : clause p c3662 = true :=
  Snake9.LocalRup.prove_clause [c1555, c3659, c2475, c2247, c730, c2293, c471, c483, c1235, c3308, c1238, c1621, c1635, c1726, c3661, c1241, c1269, c1291, c3056, c3547, c2248, c1637, c1649, c1623, c1557, c2693, c1539, c1556, c1642, c1643, c1705, c1712, c1622, c2249, c2582, c3558, c3387, c1537, c1459, c3136, c1495] c3662 (by decide) p (sat_cons (step1555 p h) (sat_cons (step3659 p h) (sat_cons (step2475 p h) (sat_cons (step2247 p h) (sat_cons (step730 p h) (sat_cons (step2293 p h) (sat_cons (step471 p h) (sat_cons (step483 p h) (sat_cons (step1235 p h) (sat_cons (step3308 p h) (sat_cons (step1238 p h) (sat_cons (step1621 p h) (sat_cons (step1635 p h) (sat_cons (step1726 p h) (sat_cons (step3661 p h) (sat_cons (step1241 p h) (sat_cons (step1269 p h) (sat_cons (step1291 p h) (sat_cons (step3056 p h) (sat_cons (step3547 p h) (sat_cons (step2248 p h) (sat_cons (step1637 p h) (sat_cons (step1649 p h) (sat_cons (step1623 p h) (sat_cons (step1557 p h) (sat_cons (step2693 p h) (sat_cons (step1539 p h) (sat_cons (step1556 p h) (sat_cons (step1642 p h) (sat_cons (step1643 p h) (sat_cons (step1705 p h) (sat_cons (step1712 p h) (sat_cons (step1622 p h) (sat_cons (step2249 p h) (sat_cons (step2582 p h) (sat_cons (step3558 p h) (sat_cons (step3387 p h) (sat_cons (step1537 p h) (sat_cons (step1459 p h) (sat_cons (step3136 p h) (sat_cons (step1495 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c3663 : List Lit := [(1830, true), (1789, false), (1779, false), (1776, false), (1801, false)]
theorem step3663 (p : Nat → Bool) (h : Constraints p) : clause p c3663 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1648, c1642, c1557, c1617, c1541, c2582, c1535] c3663 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1648 p h) (sat_cons (step1642 p h) (sat_cons (step1557 p h) (sat_cons (step1617 p h) (sat_cons (step1541 p h) (sat_cons (step2582 p h) (sat_cons (step1535 p h) (sat_nil p)))))))))
def c3664 : List Lit := [(1818, true), (114, false), (96, false), (100, false), (91, false), (123, false)]
theorem step3664 (p : Nat → Bool) (h : Constraints p) : clause p c3664 = true :=
  Snake9.LocalRup.prove_clause [c3074, c1621, c1617, c3308, c1595, c1590, c1588, c773, c633, c3010] c3664 (by decide) p (sat_cons (step3074 p h) (sat_cons (step1621 p h) (sat_cons (step1617 p h) (sat_cons (step3308 p h) (sat_cons (step1595 p h) (sat_cons (step1590 p h) (sat_cons (step1588 p h) (sat_cons (step773 p h) (sat_cons (step633 p h) (sat_cons (step3010 p h) (sat_nil p)))))))))))
def c3665 : List Lit := [(1761, true), (1745, false), (1731, false), (123, false)]
theorem step3665 (p : Nat → Bool) (h : Constraints p) : clause p c3665 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1454, c2860, c1486, c1494, c1459, c3274, c1428, c1423] c3665 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1454 p h) (sat_cons (step2860 p h) (sat_cons (step1486 p h) (sat_cons (step1494 p h) (sat_cons (step1459 p h) (sat_cons (step3274 p h) (sat_cons (step1428 p h) (sat_cons (step1423 p h) (sat_nil p))))))))))
def c3666 : List Lit := [(1725, true), (1661, true), (106, true), (96, false), (91, false), (123, false)]
theorem step3666 (p : Nat → Bool) (h : Constraints p) : clause p c3666 = true :=
  Snake9.LocalRup.prove_clause [c3040, c3330, c1370, c3446, c1250, c209, c1998, c1247, c1239, c1255, c1271] c3666 (by decide) p (sat_cons (step3040 p h) (sat_cons (step3330 p h) (sat_cons (step1370 p h) (sat_cons (step3446 p h) (sat_cons (step1250 p h) (sat_cons (step209 p h) (sat_cons (step1998 p h) (sat_cons (step1247 p h) (sat_cons (step1239 p h) (sat_cons (step1255 p h) (sat_cons (step1271 p h) (sat_nil p))))))))))))
def c3667 : List Lit := [(1661, true), (1707, true), (106, true), (96, false)]
theorem step3667 (p : Nat → Bool) (h : Constraints p) : clause p c3667 = true :=
  Snake9.LocalRup.prove_clause [c1370, c3446, c1998, c1239, c209, c1247, c1369, c1968, c1271, c1993, c1255, c1250] c3667 (by decide) p (sat_cons (step1370 p h) (sat_cons (step3446 p h) (sat_cons (step1998 p h) (sat_cons (step1239 p h) (sat_cons (step209 p h) (sat_cons (step1247 p h) (sat_cons (step1369 p h) (sat_cons (step1968 p h) (sat_cons (step1271 p h) (sat_cons (step1993 p h) (sat_cons (step1255 p h) (sat_cons (step1250 p h) (sat_nil p)))))))))))))
def c3668 : List Lit := [(1652, true), (1707, true), (106, true)]
theorem step3668 (p : Nat → Bool) (h : Constraints p) : clause p c3668 = true :=
  Snake9.LocalRup.prove_clause [c1370, c1369, c1249, c1250, c238, c1993, c2085] c3668 (by decide) p (sat_cons (step1370 p h) (sat_cons (step1369 p h) (sat_cons (step1249 p h) (sat_cons (step1250 p h) (sat_cons (step238 p h) (sat_cons (step1993 p h) (sat_cons (step2085 p h) (sat_nil p))))))))
def c3669 : List Lit := [(62, false), (1645, false), (56, true), (1707, true), (1725, false), (114, false), (1580, false), (96, false), (102, true), (91, false), (123, false)]
theorem step3669 (p : Nat → Bool) (h : Constraints p) : clause p c3669 = true :=
  Snake9.LocalRup.prove_clause [c1370, c1369, c2293, c3352, c1993, c799, c310, c330, c3026, c2024, c1099, c1954, c238, c913, c1896, c1492, c3447, c916, c3617, c1294, c917, c2253, c1360, c919, c3604, c2186, c1301, c949, c1353, c946, c1176, c943, c3479, c941] c3669 (by decide) p (sat_cons (step1370 p h) (sat_cons (step1369 p h) (sat_cons (step2293 p h) (sat_cons (step3352 p h) (sat_cons (step1993 p h) (sat_cons (step799 p h) (sat_cons (step310 p h) (sat_cons (step330 p h) (sat_cons (step3026 p h) (sat_cons (step2024 p h) (sat_cons (step1099 p h) (sat_cons (step1954 p h) (sat_cons (step238 p h) (sat_cons (step913 p h) (sat_cons (step1896 p h) (sat_cons (step1492 p h) (sat_cons (step3447 p h) (sat_cons (step916 p h) (sat_cons (step3617 p h) (sat_cons (step1294 p h) (sat_cons (step917 p h) (sat_cons (step2253 p h) (sat_cons (step1360 p h) (sat_cons (step919 p h) (sat_cons (step3604 p h) (sat_cons (step2186 p h) (sat_cons (step1301 p h) (sat_cons (step949 p h) (sat_cons (step1353 p h) (sat_cons (step946 p h) (sat_cons (step1176 p h) (sat_cons (step943 p h) (sat_cons (step3479 p h) (sat_cons (step941 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c3670 : List Lit := [(1596, true), (44, true), (102, true), (1580, false)]
theorem step3670 (p : Nat → Bool) (h : Constraints p) : clause p c3670 = true :=
  Snake9.LocalRup.prove_clause [c1864, c1159, c1155, c1133, c1141, c1143, c1862, c1139, c1135, c3580] c3670 (by decide) p (sat_cons (step1864 p h) (sat_cons (step1159 p h) (sat_cons (step1155 p h) (sat_cons (step1133 p h) (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1862 p h) (sat_cons (step1139 p h) (sat_cons (step1135 p h) (sat_cons (step3580 p h) (sat_nil p)))))))))))
def c3671 : List Lit := [(1748, true), (90, false), (123, false), (91, false), (96, false)]
theorem step3671 (p : Nat → Bool) (h : Constraints p) : clause p c3671 = true :=
  Snake9.LocalRup.prove_clause [c1448, c1456, c3138, c426, c3560, c1434, c1442] c3671 (by decide) p (sat_cons (step1448 p h) (sat_cons (step1456 p h) (sat_cons (step3138 p h) (sat_cons (step426 p h) (sat_cons (step3560 p h) (sat_cons (step1434 p h) (sat_cons (step1442 p h) (sat_nil p))))))))
end B112E050
