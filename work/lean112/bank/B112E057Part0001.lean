import B112E057Part0000
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2089 : List Lit := [(1064, false), (1074, true)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c2083, c1632] c2089 (by decide) p (sat_cons (step2083 p h) (sat_cons (step1632 p h) (sat_nil p)))
def c2090 : List Lit := [(1065, false), (1075, true)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c2083, c1633] c2090 (by decide) p (sat_cons (step2083 p h) (sat_cons (step1633 p h) (sat_nil p)))
def c2091 : List Lit := [(1066, false), (1076, true)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c2083, c1634] c2091 (by decide) p (sat_cons (step2083 p h) (sat_cons (step1634 p h) (sat_nil p)))
def c2092 : List Lit := [(14, true), (70, false), (1565, true)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c1848, c1844, c1841, c1842, c1843, c1846, c1850, c1839, c1837, c1838, c75, c1835, c1836, c20, c1, c6] c2092 (by decide) p (sat_cons (step1848 p h) (sat_cons (step1844 p h) (sat_cons (step1841 p h) (sat_cons (step1842 p h) (sat_cons (step1843 p h) (sat_cons (step1846 p h) (sat_cons (step1850 p h) (sat_cons (step1839 p h) (sat_cons (step1837 p h) (sat_cons (step1838 p h) (sat_cons (step75 p h) (sat_cons (step1835 p h) (sat_cons (step1836 p h) (sat_cons (step20 p h) (sat_cons (step1 p h) (sat_cons (step6 p h) (sat_nil p)))))))))))))))))
def c2093 : List Lit := [(1564, true)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c1847, c1849, c1843, c1845, c1837, c1838, c1841, c1839, c1840, c1835, c1836, c51, c1, c80, c13] c2093 (by decide) p (sat_cons (step1847 p h) (sat_cons (step1849 p h) (sat_cons (step1843 p h) (sat_cons (step1845 p h) (sat_cons (step1837 p h) (sat_cons (step1838 p h) (sat_cons (step1841 p h) (sat_cons (step1839 p h) (sat_cons (step1840 p h) (sat_cons (step1835 p h) (sat_cons (step1836 p h) (sat_cons (step51 p h) (sat_cons (step1 p h) (sat_cons (step80 p h) (sat_cons (step13 p h) (sat_nil p))))))))))))))))
def c2094 : List Lit := [(69, false), (76, true), (71, false), (83, false), (70, true)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c1000, c450, c1994] c2094 (by decide) p (sat_cons (step1000 p h) (sat_cons (step450 p h) (sat_cons (step1994 p h) (sat_nil p))))
def c2095 : List Lit := [(235, true), (105, true), (84, false), (107, true), (108, false)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c871, c872, c2011] c2095 (by decide) p (sat_cons (step871 p h) (sat_cons (step872 p h) (sat_cons (step2011 p h) (sat_nil p))))
def c2096 : List Lit := [(1622, true), (165, true)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c1876, c1878, c1874, c1872, c1873, c324, c283] c2096 (by decide) p (sat_cons (step1876 p h) (sat_cons (step1878 p h) (sat_cons (step1874 p h) (sat_cons (step1872 p h) (sat_cons (step1873 p h) (sat_cons (step324 p h) (sat_cons (step283 p h) (sat_nil p))))))))
def c2097 : List Lit := [(1614, true)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c2030, c1870, c1871, c1868, c1869, c1866, c1867, c276, c239, c266, c247, c264, c1063, c1078, c1064, c1079, c1066, c1086, c1068, c1098, c1072, c1130, c1136] c2097 (by decide) p (sat_cons (step2030 p h) (sat_cons (step1870 p h) (sat_cons (step1871 p h) (sat_cons (step1868 p h) (sat_cons (step1869 p h) (sat_cons (step1866 p h) (sat_cons (step1867 p h) (sat_cons (step276 p h) (sat_cons (step239 p h) (sat_cons (step266 p h) (sat_cons (step247 p h) (sat_cons (step264 p h) (sat_cons (step1063 p h) (sat_cons (step1078 p h) (sat_cons (step1064 p h) (sat_cons (step1079 p h) (sat_cons (step1066 p h) (sat_cons (step1086 p h) (sat_cons (step1068 p h) (sat_cons (step1098 p h) (sat_cons (step1072 p h) (sat_cons (step1130 p h) (sat_cons (step1136 p h) (sat_nil p))))))))))))))))))))))))
def c2098 : List Lit := [(44, false), (47, true), (38, true), (171, true)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c987, c335, c334, c1987, c359] c2098 (by decide) p (sat_cons (step987 p h) (sat_cons (step335 p h) (sat_cons (step334 p h) (sat_cons (step1987 p h) (sat_cons (step359 p h) (sat_nil p))))))
def c2099 : List Lit := [(1037, true), (94, false), (78, true)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c1003, c2084, c1569, c1556, c1558, c2081, c1554, c1550, c1551, c1543, c444, c516, c532] c2099 (by decide) p (sat_cons (step1003 p h) (sat_cons (step2084 p h) (sat_cons (step1569 p h) (sat_cons (step1556 p h) (sat_cons (step1558 p h) (sat_cons (step2081 p h) (sat_cons (step1554 p h) (sat_cons (step1550 p h) (sat_cons (step1551 p h) (sat_cons (step1543 p h) (sat_cons (step444 p h) (sat_cons (step516 p h) (sat_cons (step532 p h) (sat_nil p))))))))))))))
def c2100 : List Lit := [(901, true), (36, false), (23, true)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c981, c1329, c1330, c256, c252] c2100 (by decide) p (sat_cons (step981 p h) (sat_cons (step1329 p h) (sat_cons (step1330 p h) (sat_cons (step256 p h) (sat_cons (step252 p h) (sat_nil p))))))
def c2101 : List Lit := [(1038, true), (76, false), (72, true), (73, false)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c1543, c2081, c1574, c1570, c2082, c1556, c1545, c1554, c549] c2101 (by decide) p (sat_cons (step1543 p h) (sat_cons (step2081 p h) (sat_cons (step1574 p h) (sat_cons (step1570 p h) (sat_cons (step2082 p h) (sat_cons (step1556 p h) (sat_cons (step1545 p h) (sat_cons (step1554 p h) (sat_cons (step549 p h) (sat_nil p))))))))))
def c2102 : List Lit := [(69, false), (76, true), (112, false), (81, true), (82, false)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c1000, c450, c478] c2102 (by decide) p (sat_cons (step1000 p h) (sat_cons (step450 p h) (sat_cons (step478 p h) (sat_nil p))))
def c2103 : List Lit := [(26, false), (5, false), (870, true), (73, false)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c44, c47, c1269] c2103 (by decide) p (sat_cons (step44 p h) (sat_cons (step47 p h) (sat_cons (step1269 p h) (sat_nil p))))
def c2104 : List Lit := [(899, false), (909, true), (13, true), (891, false)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c981, c1320, c1346, c1334, c1335, c1350, c1329, c1330, c1321, c257, c249, c1316] c2104 (by decide) p (sat_cons (step981 p h) (sat_cons (step1320 p h) (sat_cons (step1346 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step1350 p h) (sat_cons (step1329 p h) (sat_cons (step1330 p h) (sat_cons (step1321 p h) (sat_cons (step257 p h) (sat_cons (step249 p h) (sat_cons (step1316 p h) (sat_nil p)))))))))))))
def c2105 : List Lit := [(98, true), (76, true), (97, false), (107, false)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c1016, c820, c819, c2019] c2105 (by decide) p (sat_cons (step1016 p h) (sat_cons (step820 p h) (sat_cons (step819 p h) (sat_cons (step2019 p h) (sat_nil p)))))
def c2106 : List Lit := [(90, true), (1063, true), (1053, false), (86, true), (1043, false), (85, false), (73, false)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1588, c1619, c1605, c1593, c1595, c1602, c699, c1623, c1584, c1589] c2106 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1588 p h) (sat_cons (step1619 p h) (sat_cons (step1605 p h) (sat_cons (step1593 p h) (sat_cons (step1595 p h) (sat_cons (step1602 p h) (sat_cons (step699 p h) (sat_cons (step1623 p h) (sat_cons (step1584 p h) (sat_cons (step1589 p h) (sat_nil p))))))))))))
def c2107 : List Lit := [(1049, false), (1075, true), (1053, false), (85, false), (1025, false), (77, true), (73, false)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1556, c1570, c1645, c1599, c1622, c1623, c1652, c1602, c1571, c1594, c1557, c696, c1555] c2107 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1556 p h) (sat_cons (step1570 p h) (sat_cons (step1645 p h) (sat_cons (step1599 p h) (sat_cons (step1622 p h) (sat_cons (step1623 p h) (sat_cons (step1652 p h) (sat_cons (step1602 p h) (sat_cons (step1571 p h) (sat_cons (step1594 p h) (sat_cons (step1557 p h) (sat_cons (step696 p h) (sat_cons (step1555 p h) (sat_nil p)))))))))))))))
def c2108 : List Lit := [(1075, true), (1053, false), (86, true), (1043, false), (85, false), (1025, false), (77, true), (73, false)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1588, c2107, c1589, c1584, c695, c699, c1555, c1594, c1557, c1602, c1571, c1618, c1652] c2108 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1588 p h) (sat_cons (step2107 p h) (sat_cons (step1589 p h) (sat_cons (step1584 p h) (sat_cons (step695 p h) (sat_cons (step699 p h) (sat_cons (step1555 p h) (sat_cons (step1594 p h) (sat_cons (step1557 p h) (sat_cons (step1602 p h) (sat_cons (step1571 p h) (sat_cons (step1618 p h) (sat_cons (step1652 p h) (sat_nil p)))))))))))))))
def c2109 : List Lit := [(1101, true), (1091, false), (95, true)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c1015, c1697, c1676, c1683, c1713, c1709, c1686, c1684, c1698, c1677, c1679, c1693, c814, c825] c2109 (by decide) p (sat_cons (step1015 p h) (sat_cons (step1697 p h) (sat_cons (step1676 p h) (sat_cons (step1683 p h) (sat_cons (step1713 p h) (sat_cons (step1709 p h) (sat_cons (step1686 p h) (sat_cons (step1684 p h) (sat_cons (step1698 p h) (sat_cons (step1677 p h) (sat_cons (step1679 p h) (sat_cons (step1693 p h) (sat_cons (step814 p h) (sat_cons (step825 p h) (sat_nil p)))))))))))))))
def c2110 : List Lit := [(1053, true), (96, false)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c1015, c815, c1596, c1597, c799] c2110 (by decide) p (sat_cons (step1015 p h) (sat_cons (step815 p h) (sat_cons (step1596 p h) (sat_cons (step1597 p h) (sat_cons (step799 p h) (sat_nil p))))))
def c2111 : List Lit := [(1025, false), (1039, true), (77, true), (1043, false), (1075, true), (85, false), (73, false), (1053, false)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c2108, c1571, c694, c1557, c1555] c2111 (by decide) p (sat_cons (step2108 p h) (sat_cons (step1571 p h) (sat_cons (step694 p h) (sat_cons (step1557 p h) (sat_cons (step1555 p h) (sat_nil p))))))
def c2112 : List Lit := [(79, false), (1046, true), (85, false), (73, false)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c694, c695, c1584] c2112 (by decide) p (sat_cons (step694 p h) (sat_cons (step695 p h) (sat_cons (step1584 p h) (sat_nil p))))
def c2113 : List Lit := [(1075, true), (1062, false), (1053, false), (90, true), (76, true), (72, false), (1032, false), (86, true), (85, false), (73, false)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c1000, c2085, c1645, c1652, c2106, c1571, c1579, c1580, c2081, c1544, c492, c625, c449] c2113 (by decide) p (sat_cons (step1000 p h) (sat_cons (step2085 p h) (sat_cons (step1645 p h) (sat_cons (step1652 p h) (sat_cons (step2106 p h) (sat_cons (step1571 p h) (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step2081 p h) (sat_cons (step1544 p h) (sat_cons (step492 p h) (sat_cons (step625 p h) (sat_cons (step449 p h) (sat_nil p))))))))))))))
def c2114 : List Lit := [(69, false), (1043, true), (76, true), (72, false)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c1000, c1580, c1579, c492, c625, c449] c2114 (by decide) p (sat_cons (step1000 p h) (sat_cons (step1580 p h) (sat_cons (step1579 p h) (sat_cons (step492 p h) (sat_cons (step625 p h) (sat_cons (step449 p h) (sat_nil p)))))))
def c2115 : List Lit := [(1124, true), (1107, false), (84, true), (83, false)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c1026, c1731, c1753, c1750, c1732, c1741, c1742, c1726, c1740, c1737, c1738, c922, c962, c927, c930] c2115 (by decide) p (sat_cons (step1026 p h) (sat_cons (step1731 p h) (sat_cons (step1753 p h) (sat_cons (step1750 p h) (sat_cons (step1732 p h) (sat_cons (step1741 p h) (sat_cons (step1742 p h) (sat_cons (step1726 p h) (sat_cons (step1740 p h) (sat_cons (step1737 p h) (sat_cons (step1738 p h) (sat_cons (step922 p h) (sat_cons (step962 p h) (sat_cons (step927 p h) (sat_cons (step930 p h) (sat_nil p))))))))))))))))
def c2116 : List Lit := [(974, true), (963, false), (957, false), (55, false), (125, false)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c2066, c1443, c1467, c1471, c1459, c1446, c2064, c1437, c410] c2116 (by decide) p (sat_cons (step2066 p h) (sat_cons (step1443 p h) (sat_cons (step1467 p h) (sat_cons (step1471 p h) (sat_cons (step1459 p h) (sat_cons (step1446 p h) (sat_cons (step2064 p h) (sat_cons (step1437 p h) (sat_cons (step410 p h) (sat_nil p))))))))))
def c2117 : List Lit := [(51, false), (934, true), (52, false), (121, false), (55, false)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c984, c397, c386, c388, c1393, c285] c2117 (by decide) p (sat_cons (step984 p h) (sat_cons (step397 p h) (sat_cons (step386 p h) (sat_cons (step388 p h) (sat_cons (step1393 p h) (sat_cons (step285 p h) (sat_nil p)))))))
def c2118 : List Lit := [(26, false), (5, true), (931, true)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c978, c1389, c1388, c227, c261] c2118 (by decide) p (sat_cons (step978 p h) (sat_cons (step1389 p h) (sat_cons (step1388 p h) (sat_cons (step227 p h) (sat_cons (step261 p h) (sat_nil p))))))
def c2119 : List Lit := [(919, true), (27, true), (26, true), (872, false), (901, false)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c979, c1327, c1335, c1341, c1301, c1368, c1374, c1342, c1346, c1302, c1338, c1318, c1286, c1328, c1315, c1279, c233, c236] c2119 (by decide) p (sat_cons (step979 p h) (sat_cons (step1327 p h) (sat_cons (step1335 p h) (sat_cons (step1341 p h) (sat_cons (step1301 p h) (sat_cons (step1368 p h) (sat_cons (step1374 p h) (sat_cons (step1342 p h) (sat_cons (step1346 p h) (sat_cons (step1302 p h) (sat_cons (step1338 p h) (sat_cons (step1318 p h) (sat_cons (step1286 p h) (sat_cons (step1328 p h) (sat_cons (step1315 p h) (sat_cons (step1279 p h) (sat_cons (step233 p h) (sat_cons (step236 p h) (sat_nil p)))))))))))))))))))
def c2120 : List Lit := [(1095, true), (108, false), (90, false)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c1695, c1697, c1693, c1690, c867] c2120 (by decide) p (sat_cons (step1695 p h) (sat_cons (step1697 p h) (sat_cons (step1693 p h) (sat_cons (step1690 p h) (sat_cons (step867 p h) (sat_nil p))))))
def c2121 : List Lit := [(109, true), (84, true), (1096, true)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c1018, c1696, c1692, c1694, c1698, c1689, c1690, c869, c849] c2121 (by decide) p (sat_cons (step1018 p h) (sat_cons (step1696 p h) (sat_cons (step1692 p h) (sat_cons (step1694 p h) (sat_cons (step1698 p h) (sat_cons (step1689 p h) (sat_cons (step1690 p h) (sat_cons (step869 p h) (sat_cons (step849 p h) (sat_nil p))))))))))
def c2122 : List Lit := [(90, false), (1115, true), (88, false), (1096, true)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c1018, c1738, c1737, c1700, c763, c1689, c1691, c1698, c693, c1693, c849, c867] c2122 (by decide) p (sat_cons (step1018 p h) (sat_cons (step1738 p h) (sat_cons (step1737 p h) (sat_cons (step1700 p h) (sat_cons (step763 p h) (sat_cons (step1689 p h) (sat_cons (step1691 p h) (sat_cons (step1698 p h) (sat_cons (step693 p h) (sat_cons (step1693 p h) (sat_cons (step849 p h) (sat_cons (step867 p h) (sat_nil p)))))))))))))
def c2123 : List Lit := [(1115, true), (51, false), (55, true), (116, true), (125, false)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c1028, c1737, c1738, c962, c926, c958] c2123 (by decide) p (sat_cons (step1028 p h) (sat_cons (step1737 p h) (sat_cons (step1738 p h) (sat_cons (step962 p h) (sat_cons (step926 p h) (sat_cons (step958 p h) (sat_nil p)))))))
def c2124 : List Lit := [(1053, true), (1089, true), (95, true), (30, false)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c1017, c1596, c1597, c2110, c1677, c1687, c1678, c794, c832, c840] c2124 (by decide) p (sat_cons (step1017 p h) (sat_cons (step1596 p h) (sat_cons (step1597 p h) (sat_cons (step2110 p h) (sat_cons (step1677 p h) (sat_cons (step1687 p h) (sat_cons (step1678 p h) (sat_cons (step794 p h) (sat_cons (step832 p h) (sat_cons (step840 p h) (sat_nil p)))))))))))
def c2125 : List Lit := [(908, true), (891, false)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c976, c1320, c1349, c1345, c1321, c1332, c1315, c1316, c1329, c1330, c208, c249, c195] c2125 (by decide) p (sat_cons (step976 p h) (sat_cons (step1320 p h) (sat_cons (step1349 p h) (sat_cons (step1345 p h) (sat_cons (step1321 p h) (sat_cons (step1332 p h) (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step1329 p h) (sat_cons (step1330 p h) (sat_cons (step208 p h) (sat_cons (step249 p h) (sat_cons (step195 p h) (sat_nil p))))))))))))))
def c2126 : List Lit := [(901, true), (32, false), (22, false)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c1329, c1330, c249] c2126 (by decide) p (sat_cons (step1329 p h) (sat_cons (step1330 p h) (sat_cons (step249 p h) (sat_nil p))))
def c2127 : List Lit := [(1060, false), (1074, true), (1124, false), (70, false), (72, true), (1158, true), (1032, false), (82, false), (1091, false)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c1543, c2081, c1571, c1650, c1658, c1797, c1576, c1772, c2082, c2109, c1545, c477] c2127 (by decide) p (sat_cons (step1543 p h) (sat_cons (step2081 p h) (sat_cons (step1571 p h) (sat_cons (step1650 p h) (sat_cons (step1658 p h) (sat_cons (step1797 p h) (sat_cons (step1576 p h) (sat_cons (step1772 p h) (sat_cons (step2082 p h) (sat_cons (step2109 p h) (sat_cons (step1545 p h) (sat_cons (step477 p h) (sat_nil p)))))))))))))
def c2128 : List Lit := [(95, false), (1053, true), (1022, true), (82, false), (23, true)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c1014, c1597, c1596, c793, c813, c477, c483, c1545] c2128 (by decide) p (sat_cons (step1014 p h) (sat_cons (step1597 p h) (sat_cons (step1596 p h) (sat_cons (step793 p h) (sat_cons (step813 p h) (sat_cons (step477 p h) (sat_cons (step483 p h) (sat_cons (step1545 p h) (sat_nil p)))))))))
def c2129 : List Lit := [(1096, true), (1043, true), (105, true)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c1018, c1580, c1579, c1689, c1700, c1698, c1691, c1693, c685, c843, c850] c2129 (by decide) p (sat_cons (step1018 p h) (sat_cons (step1580 p h) (sat_cons (step1579 p h) (sat_cons (step1689 p h) (sat_cons (step1700 p h) (sat_cons (step1698 p h) (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step685 p h) (sat_cons (step843 p h) (sat_cons (step850 p h) (sat_nil p))))))))))))
def c2130 : List Lit := [(1053, true), (1022, true), (1089, true), (82, false), (30, false), (23, true)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c2128, c2124] c2130 (by decide) p (sat_cons (step2128 p h) (sat_cons (step2124 p h) (sat_nil p)))
def c2131 : List Lit := [(869, true), (26, false), (1, false), (9, false), (97, false), (114, false)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c969, c1267, c1268, c34, c548, c64, c62] c2131 (by decide) p (sat_cons (step969 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step34 p h) (sat_cons (step548 p h) (sat_cons (step64 p h) (sat_cons (step62 p h) (sat_nil p))))))))
def c2132 : List Lit := [(107, false), (96, false), (97, false)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c1015, c825, c814] c2132 (by decide) p (sat_cons (step1015 p h) (sat_cons (step825 p h) (sat_cons (step814 p h) (sat_nil p))))
def c2133 : List Lit := [(1100, true), (97, false), (1091, false)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c1697, c1704, c1708, c1698, c1683, c1693, c1675, c2132] c2133 (by decide) p (sat_cons (step1697 p h) (sat_cons (step1704 p h) (sat_cons (step1708 p h) (sat_cons (step1698 p h) (sat_cons (step1683 p h) (sat_cons (step1693 p h) (sat_cons (step1675 p h) (sat_cons (step2132 p h) (sat_nil p)))))))))
def c2134 : List Lit := [(115, true), (251, true), (89, true), (76, true), (114, false)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c1024, c900, c901, c951, c2022] c2134 (by decide) p (sat_cons (step1024 p h) (sat_cons (step900 p h) (sat_cons (step901 p h) (sat_cons (step951 p h) (sat_cons (step2022 p h) (sat_nil p))))))
def c2135 : List Lit := [(1028, false), (76, true), (77, false), (1044, true), (1039, true), (80, false), (87, false)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c1000, c2086, c1561, c1562, c1571, c1553, c2081, c619, c1543, c1544, c1581, c480, c622, c450] c2135 (by decide) p (sat_cons (step1000 p h) (sat_cons (step2086 p h) (sat_cons (step1561 p h) (sat_cons (step1562 p h) (sat_cons (step1571 p h) (sat_cons (step1553 p h) (sat_cons (step2081 p h) (sat_cons (step619 p h) (sat_cons (step1543 p h) (sat_cons (step1544 p h) (sat_cons (step1581 p h) (sat_cons (step480 p h) (sat_cons (step622 p h) (sat_cons (step450 p h) (sat_nil p)))))))))))))))
def c2136 : List Lit := [(76, true), (77, false), (1044, true), (1039, true), (85, true), (75, true), (86, false), (87, false)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c1009, c1002, c727, c2135, c1552, c511, c518] c2136 (by decide) p (sat_cons (step1009 p h) (sat_cons (step1002 p h) (sat_cons (step727 p h) (sat_cons (step2135 p h) (sat_cons (step1552 p h) (sat_cons (step511 p h) (sat_cons (step518 p h) (sat_nil p))))))))
def c2137 : List Lit := [(77, false), (97, false), (1044, true), (1039, true), (85, true), (75, true), (86, false), (87, false)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c2136, c560, c554, c1552, c1544, c1561, c2081, c1571] c2137 (by decide) p (sat_cons (step2136 p h) (sat_cons (step560 p h) (sat_cons (step554 p h) (sat_cons (step1552 p h) (sat_cons (step1544 p h) (sat_cons (step1561 p h) (sat_cons (step2081 p h) (sat_cons (step1571 p h) (sat_nil p)))))))))
def c2138 : List Lit := [(97, false), (1044, true), (1039, true), (85, true), (75, true), (86, false), (87, false)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c1009, c1000, c1550, c2086, c1560, c727, c2137, c1554, c1555, c1559, c1562, c619, c1571, c1552, c1581, c2081, c1543, c1544, c471, c551, c622, c450] c2138 (by decide) p (sat_cons (step1009 p h) (sat_cons (step1000 p h) (sat_cons (step1550 p h) (sat_cons (step2086 p h) (sat_cons (step1560 p h) (sat_cons (step727 p h) (sat_cons (step2137 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step1559 p h) (sat_cons (step1562 p h) (sat_cons (step619 p h) (sat_cons (step1571 p h) (sat_cons (step1552 p h) (sat_cons (step1581 p h) (sat_cons (step2081 p h) (sat_cons (step1543 p h) (sat_cons (step1544 p h) (sat_cons (step471 p h) (sat_cons (step551 p h) (sat_cons (step622 p h) (sat_cons (step450 p h) (sat_nil p)))))))))))))))))))))))
def c2139 : List Lit := [(909, true), (30, true), (13, false), (82, false), (17, true)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1332, c1313, c1320, c1350, c1346, c1323, c1333, c1314, c1331, c129] c2139 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1332 p h) (sat_cons (step1313 p h) (sat_cons (step1320 p h) (sat_cons (step1350 p h) (sat_cons (step1346 p h) (sat_cons (step1323 p h) (sat_cons (step1333 p h) (sat_cons (step1314 p h) (sat_cons (step1331 p h) (sat_cons (step129 p h) (sat_nil p))))))))))))
def c2140 : List Lit := [(872, true), (2, true), (4, true)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c966, c1264, c1275, c1273, c1266, c1267, c1268, c3, c30] c2140 (by decide) p (sat_cons (step966 p h) (sat_cons (step1264 p h) (sat_cons (step1275 p h) (sat_cons (step1273 p h) (sat_cons (step1266 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step3 p h) (sat_cons (step30 p h) (sat_nil p))))))))))
def c2141 : List Lit := [(1, false), (26, false), (870, true), (2, true)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c966, c3, c34, c31, c1269] c2141 (by decide) p (sat_cons (step966 p h) (sat_cons (step3 p h) (sat_cons (step34 p h) (sat_cons (step31 p h) (sat_cons (step1269 p h) (sat_nil p))))))
def c2142 : List Lit := [(26, false), (36, false), (9, false), (873, true), (2, true), (4, true), (19, false)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c969, c1264, c1274, c2141, c1266, c1276, c1267, c1268, c164, c64, c40, c63] c2142 (by decide) p (sat_cons (step969 p h) (sat_cons (step1264 p h) (sat_cons (step1274 p h) (sat_cons (step2141 p h) (sat_cons (step1266 p h) (sat_cons (step1276 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step164 p h) (sat_cons (step64 p h) (sat_cons (step40 p h) (sat_cons (step63 p h) (sat_nil p)))))))))))))
def c2143 : List Lit := [(77, false), (1022, true), (70, false), (82, false)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c480, c474, c1545] c2143 (by decide) p (sat_cons (step480 p h) (sat_cons (step474 p h) (sat_cons (step1545 p h) (sat_nil p))))
def c2144 : List Lit := [(1, false), (6, false), (2, true)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c966, c3, c4, c1959] c2144 (by decide) p (sat_cons (step966 p h) (sat_cons (step3 p h) (sat_cons (step4 p h) (sat_cons (step1959 p h) (sat_nil p)))))
def c2145 : List Lit := [(939, true), (45, false), (6, false)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1403, c337] c2145 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step337 p h) (sat_nil p))))
def c2146 : List Lit := [(982, true), (59, false), (939, false), (931, false)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c984, c1396, c1410, c1421, c2073, c1422, c1411, c1425, c1405, c1406, c1485, c1397, c2069, c1391, c1392, c1445, c313, c286, c368, c1438] c2146 (by decide) p (sat_cons (step984 p h) (sat_cons (step1396 p h) (sat_cons (step1410 p h) (sat_cons (step1421 p h) (sat_cons (step2073 p h) (sat_cons (step1422 p h) (sat_cons (step1411 p h) (sat_cons (step1425 p h) (sat_cons (step1405 p h) (sat_cons (step1406 p h) (sat_cons (step1485 p h) (sat_cons (step1397 p h) (sat_cons (step2069 p h) (sat_cons (step1391 p h) (sat_cons (step1392 p h) (sat_cons (step1445 p h) (sat_cons (step313 p h) (sat_cons (step286 p h) (sat_cons (step368 p h) (sat_cons (step1438 p h) (sat_nil p)))))))))))))))))))))
def c2147 : List Lit := [(972, true), (45, false), (6, false)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c1463, c2069, c2066, c1443, c1451, c1441, c344] c2147 (by decide) p (sat_cons (step1463 p h) (sat_cons (step2069 p h) (sat_cons (step2066 p h) (sat_cons (step1443 p h) (sat_cons (step1451 p h) (sat_cons (step1441 p h) (sat_cons (step344 p h) (sat_nil p))))))))
def c2148 : List Lit := [(13, true), (70, true), (1043, true)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c1006, c1580, c1579, c641, c640, c2009] c2148 (by decide) p (sat_cons (step1006 p h) (sat_cons (step1580 p h) (sat_cons (step1579 p h) (sat_cons (step641 p h) (sat_cons (step640 p h) (sat_cons (step2009 p h) (sat_nil p)))))))
def c2149 : List Lit := [(10, true), (885, true), (4, true), (129, true)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c1278, c1286, c10, c2140, c1302] c2149 (by decide) p (sat_cons (step1278 p h) (sat_cons (step1286 p h) (sat_cons (step10 p h) (sat_cons (step2140 p h) (sat_cons (step1302 p h) (sat_nil p))))))
def c2150 : List Lit := [(909, true), (13, true), (59, false), (30, true), (891, false)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c981, c1330, c1332, c1320, c1350, c1346, c1321, c1333, c1315, c1331, c214, c258] c2150 (by decide) p (sat_cons (step981 p h) (sat_cons (step1330 p h) (sat_cons (step1332 p h) (sat_cons (step1320 p h) (sat_cons (step1350 p h) (sat_cons (step1346 p h) (sat_cons (step1321 p h) (sat_cons (step1333 p h) (sat_cons (step1315 p h) (sat_cons (step1331 p h) (sat_cons (step214 p h) (sat_cons (step258 p h) (sat_nil p)))))))))))))
def c2151 : List Lit := [(893, true), (13, true), (159, true), (59, false), (30, true), (36, true)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c976, c981, c1315, c1316, c209, c195, c258, c254] c2151 (by decide) p (sat_cons (step976 p h) (sat_cons (step981 p h) (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step209 p h) (sat_cons (step195 p h) (sat_cons (step258 p h) (sat_cons (step254 p h) (sat_nil p)))))))))
def c2152 : List Lit := [(4, true), (884, true), (3, false), (6, false)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c1301, c1275, c1264, c1266, c1272, c14, c1297, c1282, c1284] c2152 (by decide) p (sat_cons (step1301 p h) (sat_cons (step1275 p h) (sat_cons (step1264 p h) (sat_cons (step1266 p h) (sat_cons (step1272 p h) (sat_cons (step14 p h) (sat_cons (step1297 p h) (sat_cons (step1282 p h) (sat_cons (step1284 p h) (sat_nil p))))))))))
end B112E057
