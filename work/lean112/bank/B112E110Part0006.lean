import B112E110Part0005
namespace B112E110
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1685 : List Lit := [(317, false), (345, false)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c1307, c702] c1685 (by decide) p (sat_cons (step1307 p h) (sat_cons (step702 p h) (sat_nil p)))
def c1686 : List Lit := [(291, false), (347, false)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c1305, c706] c1686 (by decide) p (sat_cons (step1305 p h) (sat_cons (step706 p h) (sat_nil p)))
def c1687 : List Lit := [(417, false), (431, false)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c1309, c752] c1687 (by decide) p (sat_cons (step1309 p h) (sat_cons (step752 p h) (sat_nil p)))
def c1688 : List Lit := [(405, false), (463, false)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c1304, c772] c1688 (by decide) p (sat_cons (step1304 p h) (sat_cons (step772 p h) (sat_nil p)))
def c1689 : List Lit := [(349, false), (465, false)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c776, c774] c1689 (by decide) p (sat_cons (step776 p h) (sat_cons (step774 p h) (sat_nil p)))
def c1690 : List Lit := [(1518, false), (1536, true)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c1375, c960] c1690 (by decide) p (sat_cons (step1375 p h) (sat_cons (step960 p h) (sat_nil p)))
def c1691 : List Lit := [(1519, false), (1537, true)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c1375, c961] c1691 (by decide) p (sat_cons (step1375 p h) (sat_cons (step961 p h) (sat_nil p)))
def c1692 : List Lit := [(1520, false), (1538, true)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c1375, c962] c1692 (by decide) p (sat_cons (step1375 p h) (sat_cons (step962 p h) (sat_nil p)))
def c1693 : List Lit := [(1521, false), (1539, true)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c1375, c963] c1693 (by decide) p (sat_cons (step1375 p h) (sat_cons (step963 p h) (sat_nil p)))
def c1694 : List Lit := [(1522, false), (1540, true)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c1375, c964] c1694 (by decide) p (sat_cons (step1375 p h) (sat_cons (step964 p h) (sat_nil p)))
def c1695 : List Lit := [(1560, false), (1565, true)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1014] c1695 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1014 p h) (sat_nil p)))
def c1696 : List Lit := [(1561, false), (1566, true)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1015] c1696 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c1697 : List Lit := [(1562, false), (1567, true)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c1334, c1016] c1697 (by decide) p (sat_cons (step1334 p h) (sat_cons (step1016 p h) (sat_nil p)))
def c1698 : List Lit := [(1588, false), (1597, true)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1072] c1698 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1072 p h) (sat_nil p)))
def c1699 : List Lit := [(1589, false), (1598, true)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1073] c1699 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1073 p h) (sat_nil p)))
def c1700 : List Lit := [(1590, false), (1599, true)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1074] c1700 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1074 p h) (sat_nil p)))
def c1701 : List Lit := [(1591, false), (1600, true)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1075] c1701 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1075 p h) (sat_nil p)))
def c1702 : List Lit := [(1565, false), (1597, true)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c1336, c1076] c1702 (by decide) p (sat_cons (step1336 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c1703 : List Lit := [(1566, false), (1598, true)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c1336, c1082] c1703 (by decide) p (sat_cons (step1336 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c1704 : List Lit := [(1567, false), (1599, true)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c1336, c1088] c1704 (by decide) p (sat_cons (step1336 p h) (sat_cons (step1088 p h) (sat_nil p)))
def c1705 : List Lit := [(1659, false), (1676, true)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1210] c1705 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1210 p h) (sat_nil p)))
def c1706 : List Lit := [(1660, false), (1677, true)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1211] c1706 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1211 p h) (sat_nil p)))
def c1707 : List Lit := [(1661, false), (1678, true)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1212] c1707 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1212 p h) (sat_nil p)))
def c1708 : List Lit := [(1662, false), (1679, true)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1213] c1708 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1213 p h) (sat_nil p)))
def c1709 : List Lit := [(1663, false), (1680, true)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1214] c1709 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1214 p h) (sat_nil p)))
def c1710 : List Lit := [(1536, false), (1682, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1249] c1710 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1249 p h) (sat_nil p)))
def c1711 : List Lit := [(1537, false), (1681, false)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1250] c1711 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1250 p h) (sat_nil p)))
def c1712 : List Lit := [(1538, false), (1680, false)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1251] c1712 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1251 p h) (sat_nil p)))
def c1713 : List Lit := [(1539, false), (1679, false)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1252] c1713 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1252 p h) (sat_nil p)))
def c1714 : List Lit := [(1540, false), (1678, false)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1253] c1714 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1253 p h) (sat_nil p)))
def c1715 : List Lit := [(1541, false), (1677, false)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1254] c1715 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1254 p h) (sat_nil p)))
def c1716 : List Lit := [(1542, false), (1676, false)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1255] c1716 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1255 p h) (sat_nil p)))
def c1717 : List Lit := [(7, true), (1590, true), (64, false), (23, true), (20, false), (1573, false), (39, true), (40, false)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c1586, c1617, c451, c1343, c1040, c1031, c1411, c1060, c1449, c1045] c1717 (by decide) p (sat_cons (step1586 p h) (sat_cons (step1617 p h) (sat_cons (step451 p h) (sat_cons (step1343 p h) (sat_cons (step1040 p h) (sat_cons (step1031 p h) (sat_cons (step1411 p h) (sat_cons (step1060 p h) (sat_cons (step1449 p h) (sat_cons (step1045 p h) (sat_nil p)))))))))))
def c1718 : List Lit := [(14, false), (11, false), (71, true), (16, true), (133, true)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1551, c31, c47] c1718 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1551 p h) (sat_cons (step31 p h) (sat_cons (step47 p h) (sat_nil p)))))
def c1719 : List Lit := [(1518, true), (1492, false), (1504, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c918, c930, c938, c941, c933, c895, c919, c1340] c1719 (by decide) p (sat_cons (step918 p h) (sat_cons (step930 p h) (sat_cons (step938 p h) (sat_cons (step941 p h) (sat_cons (step933 p h) (sat_cons (step895 p h) (sat_cons (step919 p h) (sat_cons (step1340 p h) (sat_nil p)))))))))
def c1720 : List Lit := [(1433, true), (13, false)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c803, c804, c1554, c45] c1720 (by decide) p (sat_cons (step803 p h) (sat_cons (step804 p h) (sat_cons (step1554 p h) (sat_cons (step45 p h) (sat_nil p)))))
def c1721 : List Lit := [(11, true), (1429, true), (1430, true), (40, false)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c1324, c786, c788, c1479, c790, c800, c782, c1320, c23, c1317, c1547, c1540, c1545, c37, c629, c630, c1680, c631] c1721 (by decide) p (sat_cons (step1324 p h) (sat_cons (step786 p h) (sat_cons (step788 p h) (sat_cons (step1479 p h) (sat_cons (step790 p h) (sat_cons (step800 p h) (sat_cons (step782 p h) (sat_cons (step1320 p h) (sat_cons (step23 p h) (sat_cons (step1317 p h) (sat_cons (step1547 p h) (sat_cons (step1540 p h) (sat_cons (step1545 p h) (sat_cons (step37 p h) (sat_cons (step629 p h) (sat_cons (step630 p h) (sat_cons (step1680 p h) (sat_cons (step631 p h) (sat_nil p)))))))))))))))))))
def c1722 : List Lit := [(11, false), (1462, true), (1445, false), (40, false), (44, false), (13, false)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c1549, c31, c39, c1554, c805, c814, c839, c857, c1323, c789, c782, c783, c23, c1546, c1547, c50, c1545, c640, c629, c641, c633, c646, c635, c659, c1684] c1722 (by decide) p (sat_cons (step1549 p h) (sat_cons (step31 p h) (sat_cons (step39 p h) (sat_cons (step1554 p h) (sat_cons (step805 p h) (sat_cons (step814 p h) (sat_cons (step839 p h) (sat_cons (step857 p h) (sat_cons (step1323 p h) (sat_cons (step789 p h) (sat_cons (step782 p h) (sat_cons (step783 p h) (sat_cons (step23 p h) (sat_cons (step1546 p h) (sat_cons (step1547 p h) (sat_cons (step50 p h) (sat_cons (step1545 p h) (sat_cons (step640 p h) (sat_cons (step629 p h) (sat_cons (step641 p h) (sat_cons (step633 p h) (sat_cons (step646 p h) (sat_cons (step635 p h) (sat_cons (step659 p h) (sat_cons (step1684 p h) (sat_nil p))))))))))))))))))))))))))
def c1723 : List Lit := [(1462, true), (1445, false), (40, false), (44, false), (13, false)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c1720, c811, c834, c830, c866, c1722, c862, c1721] c1723 (by decide) p (sat_cons (step1720 p h) (sat_cons (step811 p h) (sat_cons (step834 p h) (sat_cons (step830 p h) (sat_cons (step866 p h) (sat_cons (step1722 p h) (sat_cons (step862 p h) (sat_cons (step1721 p h) (sat_nil p)))))))))
def c1724 : List Lit := [(11, true), (1429, true)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c1324, c786, c788, c790, c800, c782, c783, c1320, c1317, c17, c1547, c1540, c1545, c37, c629, c630, c1680, c631] c1724 (by decide) p (sat_cons (step1324 p h) (sat_cons (step786 p h) (sat_cons (step788 p h) (sat_cons (step790 p h) (sat_cons (step800 p h) (sat_cons (step782 p h) (sat_cons (step783 p h) (sat_cons (step1320 p h) (sat_cons (step1317 p h) (sat_cons (step17 p h) (sat_cons (step1547 p h) (sat_cons (step1540 p h) (sat_cons (step1545 p h) (sat_cons (step37 p h) (sat_cons (step629 p h) (sat_cons (step630 p h) (sat_cons (step1680 p h) (sat_cons (step631 p h) (sat_nil p)))))))))))))))))))
def c1725 : List Lit := [(1649, true), (86, false), (82, false), (107, true), (84, false), (1632, false), (115, true)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c1132, c1141, c1150, c1152, c1175, c1171, c1144, c1153, c1134, c1151, c1453, c493] c1725 (by decide) p (sat_cons (step1132 p h) (sat_cons (step1141 p h) (sat_cons (step1150 p h) (sat_cons (step1152 p h) (sat_cons (step1175 p h) (sat_cons (step1171 p h) (sat_cons (step1144 p h) (sat_cons (step1153 p h) (sat_cons (step1134 p h) (sat_cons (step1151 p h) (sat_cons (step1453 p h) (sat_cons (step493 p h) (sat_nil p)))))))))))))
def c1726 : List Lit := [(44, false), (1461, true), (1462, true), (1441, false), (31, false), (40, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c824, c1495, c1723, c825, c785, c831, c788, c856, c1323] c1726 (by decide) p (sat_cons (step824 p h) (sat_cons (step1495 p h) (sat_cons (step1723 p h) (sat_cons (step825 p h) (sat_cons (step785 p h) (sat_cons (step831 p h) (sat_cons (step788 p h) (sat_cons (step856 p h) (sat_cons (step1323 p h) (sat_nil p))))))))))
def c1727 : List Lit := [(1518, true), (1494, false), (40, false), (44, true), (30, true)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c878, c899, c1520, c941, c889, c932, c882, c919, c910, c911, c176, c1593] c1727 (by decide) p (sat_cons (step878 p h) (sat_cons (step899 p h) (sat_cons (step1520 p h) (sat_cons (step941 p h) (sat_cons (step889 p h) (sat_cons (step932 p h) (sat_cons (step882 p h) (sat_cons (step919 p h) (sat_cons (step910 p h) (sat_cons (step911 p h) (sat_cons (step176 p h) (sat_cons (step1593 p h) (sat_nil p)))))))))))))
def c1728 : List Lit := [(1626, true), (1618, false), (96, true)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c1101, c1111, c1118, c1122, c1114, c1363, c1103] c1728 (by decide) p (sat_cons (step1101 p h) (sat_cons (step1111 p h) (sat_cons (step1118 p h) (sat_cons (step1122 p h) (sat_cons (step1114 p h) (sat_cons (step1363 p h) (sat_cons (step1103 p h) (sat_nil p))))))))
def c1729 : List Lit := [(84, true), (1599, true), (64, true), (97, false), (35, false)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c1001, c1008, c1695, c1078, c1040, c1413, c1042, c381, c1531, c1372, c1367, c1083, c1051] c1729 (by decide) p (sat_cons (step1001 p h) (sat_cons (step1008 p h) (sat_cons (step1695 p h) (sat_cons (step1078 p h) (sat_cons (step1040 p h) (sat_cons (step1413 p h) (sat_cons (step1042 p h) (sat_cons (step381 p h) (sat_cons (step1531 p h) (sat_cons (step1372 p h) (sat_cons (step1367 p h) (sat_cons (step1083 p h) (sat_cons (step1051 p h) (sat_nil p))))))))))))))
def c1730 : List Lit := [(1579, true), (78, false), (77, false), (88, false)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c1036, c1037, c259, c292, c1631] c1730 (by decide) p (sat_cons (step1036 p h) (sat_cons (step1037 p h) (sat_cons (step259 p h) (sat_cons (step292 p h) (sat_cons (step1631 p h) (sat_nil p))))))
def c1731 : List Lit := [(1450, true), (80, true), (1443, false)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c822, c1464, c834, c1560, c809, c806] c1731 (by decide) p (sat_cons (step822 p h) (sat_cons (step1464 p h) (sat_cons (step834 p h) (sat_cons (step1560 p h) (sat_cons (step809 p h) (sat_cons (step806 p h) (sat_nil p)))))))
def c1732 : List Lit := [(1518, true), (42, true), (1504, false), (35, false)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c884, c887, c895, c927, c945, c941, c896, c930, c888, c916, c886, c1463] c1732 (by decide) p (sat_cons (step884 p h) (sat_cons (step887 p h) (sat_cons (step895 p h) (sat_cons (step927 p h) (sat_cons (step945 p h) (sat_cons (step941 p h) (sat_cons (step896 p h) (sat_cons (step930 p h) (sat_cons (step888 p h) (sat_cons (step916 p h) (sat_cons (step886 p h) (sat_cons (step1463 p h) (sat_nil p)))))))))))))
def c1733 : List Lit := [(1445, false), (1460, true)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c1328, c830, c834, c855, c811, c1323, c1720, c788, c785] c1733 (by decide) p (sat_cons (step1328 p h) (sat_cons (step830 p h) (sat_cons (step834 p h) (sat_cons (step855 p h) (sat_cons (step811 p h) (sat_cons (step1323 p h) (sat_cons (step1720 p h) (sat_cons (step788 p h) (sat_cons (step785 p h) (sat_nil p))))))))))
def c1734 : List Lit := [(1519, true), (1504, false), (1443, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c820, c819, c1569, c96, c878, c899, c1460, c887, c889, c1340, c884, c882, c942, c933, c919, c910, c911, c130, c176, c163, c1594] c1734 (by decide) p (sat_cons (step820 p h) (sat_cons (step819 p h) (sat_cons (step1569 p h) (sat_cons (step96 p h) (sat_cons (step878 p h) (sat_cons (step899 p h) (sat_cons (step1460 p h) (sat_cons (step887 p h) (sat_cons (step889 p h) (sat_cons (step1340 p h) (sat_cons (step884 p h) (sat_cons (step882 p h) (sat_cons (step942 p h) (sat_cons (step933 p h) (sat_cons (step919 p h) (sat_cons (step910 p h) (sat_cons (step911 p h) (sat_cons (step130 p h) (sat_cons (step176 p h) (sat_cons (step163 p h) (sat_cons (step1594 p h) (sat_nil p))))))))))))))))))))))
def c1735 : List Lit := [(64, false), (1571, true), (84, false), (99, false)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c461, c1343, c1615] c1735 (by decide) p (sat_cons (step461 p h) (sat_cons (step1343 p h) (sat_cons (step1615 p h) (sat_nil p))))
def c1736 : List Lit := [(1624, true), (1617, false)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c1107, c1116, c1120, c1110, c1363, c1102] c1736 (by decide) p (sat_cons (step1107 p h) (sat_cons (step1116 p h) (sat_cons (step1120 p h) (sat_cons (step1110 p h) (sat_cons (step1363 p h) (sat_cons (step1102 p h) (sat_nil p)))))))
def c1737 : List Lit := [(1632, true), (100, false), (96, false)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c1135, c1136, c505, c409, c1668] c1737 (by decide) p (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step505 p h) (sat_cons (step409 p h) (sat_cons (step1668 p h) (sat_nil p))))))
def c1738 : List Lit := [(109, false), (110, false), (97, true), (96, false)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c1668, c505] c1738 (by decide) p (sat_cons (step1668 p h) (sat_cons (step505 p h) (sat_nil p)))
def c1739 : List Lit := [(108, false), (110, false), (1639, true), (96, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c509, c508, c1148] c1739 (by decide) p (sat_cons (step509 p h) (sat_cons (step508 p h) (sat_cons (step1148 p h) (sat_nil p))))
def c1740 : List Lit := [(110, false), (104, false), (1644, true), (71, true), (115, true), (44, true), (96, false)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c1150, c1158, c1739, c1671, c1147, c1148, c1156, c450, c1151, c556, c545, c1672] c1740 (by decide) p (sat_cons (step1150 p h) (sat_cons (step1158 p h) (sat_cons (step1739 p h) (sat_cons (step1671 p h) (sat_cons (step1147 p h) (sat_cons (step1148 p h) (sat_cons (step1156 p h) (sat_cons (step450 p h) (sat_cons (step1151 p h) (sat_cons (step556 p h) (sat_cons (step545 p h) (sat_cons (step1672 p h) (sat_nil p)))))))))))))
def c1741 : List Lit := [(108, false), (109, false), (1639, true), (96, false)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c506, c507, c1148] c1741 (by decide) p (sat_cons (step506 p h) (sat_cons (step507 p h) (sat_cons (step1148 p h) (sat_nil p))))
def c1742 : List Lit := [(107, true), (71, true), (115, true), (44, true), (100, false), (96, false), (1650, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c1512, c1176, c1737, c1144, c1150, c1132, c1142, c1141, c1172, c1134, c1158, c1740, c1137, c1741, c409, c1668] c1742 (by decide) p (sat_cons (step1512 p h) (sat_cons (step1176 p h) (sat_cons (step1737 p h) (sat_cons (step1144 p h) (sat_cons (step1150 p h) (sat_cons (step1132 p h) (sat_cons (step1142 p h) (sat_cons (step1141 p h) (sat_cons (step1172 p h) (sat_cons (step1134 p h) (sat_cons (step1158 p h) (sat_cons (step1740 p h) (sat_cons (step1137 p h) (sat_cons (step1741 p h) (sat_cons (step409 p h) (sat_cons (step1668 p h) (sat_nil p)))))))))))))))))
def c1743 : List Lit := [(117, false), (1630, true), (113, false), (95, false)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c1133, c1132, c1425, c556, c564, c1676] c1743 (by decide) p (sat_cons (step1133 p h) (sat_cons (step1132 p h) (sat_cons (step1425 p h) (sat_cons (step556 p h) (sat_cons (step564 p h) (sat_cons (step1676 p h) (sat_nil p)))))))
def c1744 : List Lit := [(64, false), (72, false), (115, false), (107, false)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c466, c250, c1615] c1744 (by decide) p (sat_cons (step466 p h) (sat_cons (step250 p h) (sat_cons (step1615 p h) (sat_nil p))))
def c1745 : List Lit := [(1630, true), (86, false), (82, false), (84, false)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c1132, c1133, c1453, c492] c1745 (by decide) p (sat_cons (step1132 p h) (sat_cons (step1133 p h) (sat_cons (step1453 p h) (sat_cons (step492 p h) (sat_nil p)))))
def c1746 : List Lit := [(1626, true), (80, true), (1611, false), (96, true)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c1097, c1101, c1109, c1130, c1126, c1100, c1112, c1354, c1103] c1746 (by decide) p (sat_cons (step1097 p h) (sat_cons (step1101 p h) (sat_cons (step1109 p h) (sat_cons (step1130 p h) (sat_cons (step1126 p h) (sat_cons (step1100 p h) (sat_cons (step1112 p h) (sat_cons (step1354 p h) (sat_cons (step1103 p h) (sat_nil p))))))))))
def c1747 : List Lit := [(1632, true), (113, false), (115, false)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c1135, c1136, c521, c1666, c512] c1747 (by decide) p (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step521 p h) (sat_cons (step1666 p h) (sat_cons (step512 p h) (sat_nil p))))))
def c1748 : List Lit := [(1518, true), (30, true), (42, true)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c884, c887, c878, c948, c1520, c901, c886, c888] c1748 (by decide) p (sat_cons (step884 p h) (sat_cons (step887 p h) (sat_cons (step878 p h) (sat_cons (step948 p h) (sat_cons (step1520 p h) (sat_cons (step901 p h) (sat_cons (step886 p h) (sat_cons (step888 p h) (sat_nil p)))))))))
end B112E110
