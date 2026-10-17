import B112E055Part0001
namespace B112E055
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2070 : List Lit := [(118, true), (91, true), (1822, true), (121, false), (85, false)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c1781, c1751, c1748, c1749, c1750, c1753, c910, c1777, c1744, c1745, c1764, c1766, c1761, c1758, c941, c878, c924, c944] c2070 (by decide) p (sat_cons (step1781 p h) (sat_cons (step1751 p h) (sat_cons (step1748 p h) (sat_cons (step1749 p h) (sat_cons (step1750 p h) (sat_cons (step1753 p h) (sat_cons (step910 p h) (sat_cons (step1777 p h) (sat_cons (step1744 p h) (sat_cons (step1745 p h) (sat_cons (step1764 p h) (sat_cons (step1766 p h) (sat_cons (step1761 p h) (sat_cons (step1758 p h) (sat_cons (step941 p h) (sat_cons (step878 p h) (sat_cons (step924 p h) (sat_cons (step944 p h) (sat_nil p)))))))))))))))))))
def c2071 : List Lit := [(118, false), (1791, true), (1822, true)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c1993, c1713, c1712, c2017, c833, c1758, c842, c1766, c1235, c1777, c839, c1750, c884, c1747] c2071 (by decide) p (sat_cons (step1993 p h) (sat_cons (step1713 p h) (sat_cons (step1712 p h) (sat_cons (step2017 p h) (sat_cons (step833 p h) (sat_cons (step1758 p h) (sat_cons (step842 p h) (sat_cons (step1766 p h) (sat_cons (step1235 p h) (sat_cons (step1777 p h) (sat_cons (step839 p h) (sat_cons (step1750 p h) (sat_cons (step884 p h) (sat_cons (step1747 p h) (sat_nil p)))))))))))))))
def c2072 : List Lit := [(1785, false), (1831, true), (85, false)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c2022, c1802, c1727, c1728, c2050, c1797, c1715, c1717, c1709, c2071, c1748, c2070, c1750, c724, c1777, c1761, c1764] c2072 (by decide) p (sat_cons (step2022 p h) (sat_cons (step1802 p h) (sat_cons (step1727 p h) (sat_cons (step1728 p h) (sat_cons (step2050 p h) (sat_cons (step1797 p h) (sat_cons (step1715 p h) (sat_cons (step1717 p h) (sat_cons (step1709 p h) (sat_cons (step2071 p h) (sat_cons (step1748 p h) (sat_cons (step2070 p h) (sat_cons (step1750 p h) (sat_cons (step724 p h) (sat_cons (step1777 p h) (sat_cons (step1761 p h) (sat_cons (step1764 p h) (sat_nil p))))))))))))))))))
def c2073 : List Lit := [(118, true), (1822, true)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c1976, c1781, c1751, c1748, c1749, c1750, c1753, c1777, c1744, c1745, c1764, c1766, c1761, c1762, c1758, c1759, c913, c941, c878, c855, c924, c949, c931, c1268, c1267, c1271] c2073 (by decide) p (sat_cons (step1976 p h) (sat_cons (step1781 p h) (sat_cons (step1751 p h) (sat_cons (step1748 p h) (sat_cons (step1749 p h) (sat_cons (step1750 p h) (sat_cons (step1753 p h) (sat_cons (step1777 p h) (sat_cons (step1744 p h) (sat_cons (step1745 p h) (sat_cons (step1764 p h) (sat_cons (step1766 p h) (sat_cons (step1761 p h) (sat_cons (step1762 p h) (sat_cons (step1758 p h) (sat_cons (step1759 p h) (sat_cons (step913 p h) (sat_cons (step941 p h) (sat_cons (step878 p h) (sat_cons (step855 p h) (sat_cons (step924 p h) (sat_cons (step949 p h) (sat_cons (step931 p h) (sat_cons (step1268 p h) (sat_cons (step1267 p h) (sat_cons (step1271 p h) (sat_nil p)))))))))))))))))))))))))))
def c2074 : List Lit := [(1807, false), (1747, true), (106, false), (1822, true), (85, true)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c1781, c1750, c1753, c1777, c1744, c1745, c1764, c1766, c1761, c1762, c1759, c941, c855, c929, c703, c704, c1594, c1599, c1604] c2074 (by decide) p (sat_cons (step1781 p h) (sat_cons (step1750 p h) (sat_cons (step1753 p h) (sat_cons (step1777 p h) (sat_cons (step1744 p h) (sat_cons (step1745 p h) (sat_cons (step1764 p h) (sat_cons (step1766 p h) (sat_cons (step1761 p h) (sat_cons (step1762 p h) (sat_cons (step1759 p h) (sat_cons (step941 p h) (sat_cons (step855 p h) (sat_cons (step929 p h) (sat_cons (step703 p h) (sat_cons (step704 p h) (sat_cons (step1594 p h) (sat_cons (step1599 p h) (sat_cons (step1604 p h) (sat_nil p))))))))))))))))))))
def c2075 : List Lit := [(1817, true), (121, false), (120, false), (118, false)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c1764, c1766, c1761, c1758, c913, c887, c924, c892] c2075 (by decide) p (sat_cons (step1764 p h) (sat_cons (step1766 p h) (sat_cons (step1761 p h) (sat_cons (step1758 p h) (sat_cons (step913 p h) (sat_cons (step887 p h) (sat_cons (step924 p h) (sat_cons (step892 p h) (sat_nil p)))))))))
def c2076 : List Lit := [(125, false), (126, true), (1805, true), (1747, true), (106, false), (85, true)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c1745, c1744, c855, c929, c703, c704, c1594, c1599, c1604] c2076 (by decide) p (sat_cons (step1745 p h) (sat_cons (step1744 p h) (sat_cons (step855 p h) (sat_cons (step929 p h) (sat_cons (step703 p h) (sat_cons (step704 p h) (sat_cons (step1594 p h) (sat_cons (step1599 p h) (sat_cons (step1604 p h) (sat_nil p))))))))))
def c2077 : List Lit := [(127, false), (1805, true), (121, false), (120, false), (1747, true), (106, false), (118, false), (1818, true), (85, true)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c1744, c913, c941, c2076, c1762, c1767, c1758, c887, c924, c892] c2077 (by decide) p (sat_cons (step1744 p h) (sat_cons (step913 p h) (sat_cons (step941 p h) (sat_cons (step2076 p h) (sat_cons (step1762 p h) (sat_cons (step1767 p h) (sat_cons (step1758 p h) (sat_cons (step887 p h) (sat_cons (step924 p h) (sat_cons (step892 p h) (sat_nil p)))))))))))
def c2078 : List Lit := [(121, false), (1747, true), (106, false), (1822, true), (85, true)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c2074, c1747, c2073, c1773, c1765, c2075, c1777, c1752, c1744, c2077, c1763, c940, c2076] c2078 (by decide) p (sat_cons (step2074 p h) (sat_cons (step1747 p h) (sat_cons (step2073 p h) (sat_cons (step1773 p h) (sat_cons (step1765 p h) (sat_cons (step2075 p h) (sat_cons (step1777 p h) (sat_cons (step1752 p h) (sat_cons (step1744 p h) (sat_cons (step2077 p h) (sat_cons (step1763 p h) (sat_cons (step940 p h) (sat_cons (step2076 p h) (sat_nil p))))))))))))))
def c2079 : List Lit := [(1807, true), (1791, true)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c1993, c1713, c1712, c1747, c1748, c884, c833, c842, c839, c1235] c2079 (by decide) p (sat_cons (step1993 p h) (sat_cons (step1713 p h) (sat_cons (step1712 p h) (sat_cons (step1747 p h) (sat_cons (step1748 p h) (sat_cons (step884 p h) (sat_cons (step833 p h) (sat_cons (step842 p h) (sat_cons (step839 p h) (sat_cons (step1235 p h) (sat_nil p)))))))))))
def c2080 : List Lit := [(1813, false), (1807, false), (106, false), (1747, true), (1823, true), (85, true)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c1750, c1778, c1766, c1782, c1753, c1744, c1767, c1762, c2076, c942, c1761] c2080 (by decide) p (sat_cons (step1750 p h) (sat_cons (step1778 p h) (sat_cons (step1766 p h) (sat_cons (step1782 p h) (sat_cons (step1753 p h) (sat_cons (step1744 p h) (sat_cons (step1767 p h) (sat_cons (step1762 p h) (sat_cons (step2076 p h) (sat_cons (step942 p h) (sat_cons (step1761 p h) (sat_nil p))))))))))))
def c2081 : List Lit := [(127, true), (1807, false), (106, false), (1747, true), (1823, true), (85, true)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c2080, c1759, c1750, c1778, c1765, c1761, c1763, c1764, c1782, c1753, c1744, c2076, c940] c2081 (by decide) p (sat_cons (step2080 p h) (sat_cons (step1759 p h) (sat_cons (step1750 p h) (sat_cons (step1778 p h) (sat_cons (step1765 p h) (sat_cons (step1761 p h) (sat_cons (step1763 p h) (sat_cons (step1764 p h) (sat_cons (step1782 p h) (sat_cons (step1753 p h) (sat_cons (step1744 p h) (sat_cons (step2076 p h) (sat_cons (step940 p h) (sat_nil p))))))))))))))
def c2082 : List Lit := [(120, false), (127, false), (121, false), (123, false), (110, false)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c886, c924, c913, c892] c2082 (by decide) p (sat_cons (step886 p h) (sat_cons (step924 p h) (sat_cons (step913 p h) (sat_cons (step892 p h) (sat_nil p)))))
def c2083 : List Lit := [(1808, false), (1823, true), (127, false), (121, false)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1785, c1751, c1754, c1782, c1744, c1745, c1764, c941, c878, c1762, c855, c931, c872, c1267, c1252, c1270, c1255, c1272, c1256, c1280] c2083 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1785 p h) (sat_cons (step1751 p h) (sat_cons (step1754 p h) (sat_cons (step1782 p h) (sat_cons (step1744 p h) (sat_cons (step1745 p h) (sat_cons (step1764 p h) (sat_cons (step941 p h) (sat_cons (step878 p h) (sat_cons (step1762 p h) (sat_cons (step855 p h) (sat_cons (step931 p h) (sat_cons (step872 p h) (sat_cons (step1267 p h) (sat_cons (step1252 p h) (sat_cons (step1270 p h) (sat_cons (step1255 p h) (sat_cons (step1272 p h) (sat_cons (step1256 p h) (sat_cons (step1280 p h) (sat_nil p))))))))))))))))))))))
def c2084 : List Lit := [(1813, false), (1823, true), (127, false), (121, false), (1807, false)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1750, c1778, c1766, c1767, c1782, c1762, c1753, c943, c1744, c1745, c878, c855, c931, c872, c1267, c1252, c1270, c1255, c1272, c1256, c1280] c2084 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1750 p h) (sat_cons (step1778 p h) (sat_cons (step1766 p h) (sat_cons (step1767 p h) (sat_cons (step1782 p h) (sat_cons (step1762 p h) (sat_cons (step1753 p h) (sat_cons (step943 p h) (sat_cons (step1744 p h) (sat_cons (step1745 p h) (sat_cons (step878 p h) (sat_cons (step855 p h) (sat_cons (step931 p h) (sat_cons (step872 p h) (sat_cons (step1267 p h) (sat_cons (step1252 p h) (sat_cons (step1270 p h) (sat_cons (step1255 p h) (sat_cons (step1272 p h) (sat_cons (step1256 p h) (sat_cons (step1280 p h) (sat_nil p)))))))))))))))))))))))
def c2085 : List Lit := [(1823, true), (127, false), (121, false), (1791, true)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c2079, c1713, c2083, c2084, c1758, c2017, c2082, c1749] c2085 (by decide) p (sat_cons (step2079 p h) (sat_cons (step1713 p h) (sat_cons (step2083 p h) (sat_cons (step2084 p h) (sat_cons (step1758 p h) (sat_cons (step2017 p h) (sat_cons (step2082 p h) (sat_cons (step1749 p h) (sat_nil p)))))))))
def c2086 : List Lit := [(125, false), (117, true), (126, true), (115, false), (116, false)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c1952, c855, c931, c872, c1267, c1252, c1270, c1255, c1272, c1256, c1280] c2086 (by decide) p (sat_cons (step1952 p h) (sat_cons (step855 p h) (sat_cons (step931 p h) (sat_cons (step872 p h) (sat_cons (step1267 p h) (sat_cons (step1252 p h) (sat_cons (step1270 p h) (sat_cons (step1255 p h) (sat_cons (step1272 p h) (sat_cons (step1256 p h) (sat_cons (step1280 p h) (sat_nil p))))))))))))
def c2087 : List Lit := [(1798, true), (230, true), (1742, true), (106, true), (121, false)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c1710, c1717, c1724, c1728, c1720, c1701, c1703, c1711, c1699, c1696, c818, c784, c580, c583, c1596] c2087 (by decide) p (sat_cons (step1710 p h) (sat_cons (step1717 p h) (sat_cons (step1724 p h) (sat_cons (step1728 p h) (sat_cons (step1720 p h) (sat_cons (step1701 p h) (sat_cons (step1703 p h) (sat_cons (step1711 p h) (sat_cons (step1699 p h) (sat_cons (step1696 p h) (sat_cons (step818 p h) (sat_cons (step784 p h) (sat_cons (step580 p h) (sat_cons (step583 p h) (sat_cons (step1596 p h) (sat_nil p))))))))))))))))
def c2088 : List Lit := [(105, true), (99, false), (91, true), (108, false), (236, true), (85, true)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c1008, c830, c832, c818, c789] c2088 (by decide) p (sat_cons (step1008 p h) (sat_cons (step830 p h) (sat_cons (step832 p h) (sat_cons (step818 p h) (sat_cons (step789 p h) (sat_nil p))))))
def c2089 : List Lit := [(104, false), (86, false), (105, true), (232, true), (123, false)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c641, c795] c2089 (by decide) p (sat_cons (step641 p h) (sat_cons (step795 p h) (sat_nil p)))
def c2090 : List Lit := [(77, true), (1731, true), (75, true), (78, false), (91, false), (84, true), (200, true)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1571, c1565, c1566, c1573, c507, c1563, c425] c2090 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1571 p h) (sat_cons (step1565 p h) (sat_cons (step1566 p h) (sat_cons (step1573 p h) (sat_cons (step507 p h) (sat_cons (step1563 p h) (sat_cons (step425 p h) (sat_nil p)))))))))
def c2091 : List Lit := [(1666, false), (1702, true), (51, false), (1656, false), (1609, false), (1646, false), (45, true), (121, false)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c2006, c1382, c1525, c1489, c1448, c1456, c1481, c1485, c1488, c1459, c1531, c1449, c1387, c330, c2035] c2091 (by decide) p (sat_cons (step2006 p h) (sat_cons (step1382 p h) (sat_cons (step1525 p h) (sat_cons (step1489 p h) (sat_cons (step1448 p h) (sat_cons (step1456 p h) (sat_cons (step1481 p h) (sat_cons (step1485 p h) (sat_cons (step1488 p h) (sat_cons (step1459 p h) (sat_cons (step1531 p h) (sat_cons (step1449 p h) (sat_cons (step1387 p h) (sat_cons (step330 p h) (sat_cons (step2035 p h) (sat_nil p))))))))))))))))
def c2092 : List Lit := [(1702, true), (51, false), (1656, false), (1609, false), (1634, false), (59, false), (45, true), (121, false)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c2006, c1942, c1448, c1456, c1480, c1382, c1431, c1525, c1498, c1433, c2091, c1468, c1460, c1461, c367, c338, c1417, c1421, c1426] c2092 (by decide) p (sat_cons (step2006 p h) (sat_cons (step1942 p h) (sat_cons (step1448 p h) (sat_cons (step1456 p h) (sat_cons (step1480 p h) (sat_cons (step1382 p h) (sat_cons (step1431 p h) (sat_cons (step1525 p h) (sat_cons (step1498 p h) (sat_cons (step1433 p h) (sat_cons (step2091 p h) (sat_cons (step1468 p h) (sat_cons (step1460 p h) (sat_cons (step1461 p h) (sat_cons (step367 p h) (sat_cons (step338 p h) (sat_cons (step1417 p h) (sat_cons (step1421 p h) (sat_cons (step1426 p h) (sat_nil p))))))))))))))))))))
def c2093 : List Lit := [(79, true), (75, true), (73, false), (71, true), (197, true), (85, true), (89, true)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c992, c994, c439, c460, c393] c2093 (by decide) p (sat_cons (step992 p h) (sat_cons (step994 p h) (sat_cons (step439 p h) (sat_cons (step460 p h) (sat_cons (step393 p h) (sat_nil p))))))
def c2094 : List Lit := [(1643, true), (166, true), (40, true), (45, false)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c1417, c1428, c1426, c1419, c1420, c308, c270] c2094 (by decide) p (sat_cons (step1417 p h) (sat_cons (step1428 p h) (sat_cons (step1426 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step308 p h) (sat_cons (step270 p h) (sat_nil p))))))))
def c2095 : List Lit := [(31, false), (30, true), (34, false), (37, false), (159, true)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c248, c230] c2095 (by decide) p (sat_cons (step248 p h) (sat_cons (step230 p h) (sat_nil p)))
def c2096 : List Lit := [(12, true), (5, false), (1585, true), (131, true)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c1320, c1316, c1305, c1307, c1313, c1324, c1300, c1302, c1298, c1, c41, c17] c2096 (by decide) p (sat_cons (step1320 p h) (sat_cons (step1316 p h) (sat_cons (step1305 p h) (sat_cons (step1307 p h) (sat_cons (step1313 p h) (sat_cons (step1324 p h) (sat_cons (step1300 p h) (sat_cons (step1302 p h) (sat_cons (step1298 p h) (sat_cons (step1 p h) (sat_cons (step41 p h) (sat_cons (step17 p h) (sat_nil p)))))))))))))
def c2097 : List Lit := [(1571, false), (12, false), (5, false), (1585, true), (130, true), (136, true), (13, false), (26, false)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c1328, c1300, c1303, c1324, c63, c1313, c9, c1306, c28, c31, c56] c2097 (by decide) p (sat_cons (step1328 p h) (sat_cons (step1300 p h) (sat_cons (step1303 p h) (sat_cons (step1324 p h) (sat_cons (step63 p h) (sat_cons (step1313 p h) (sat_cons (step9 p h) (sat_cons (step1306 p h) (sat_cons (step28 p h) (sat_cons (step31 p h) (sat_cons (step56 p h) (sat_nil p))))))))))))
def c2098 : List Lit := [(1585, true), (130, true), (131, true), (136, true), (140, true), (13, false), (26, false)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c2035, c2004, c2096, c2097, c1298, c71, c15, c16, c28] c2098 (by decide) p (sat_cons (step2035 p h) (sat_cons (step2004 p h) (sat_cons (step2096 p h) (sat_cons (step2097 p h) (sat_cons (step1298 p h) (sat_cons (step71 p h) (sat_cons (step15 p h) (sat_cons (step16 p h) (sat_cons (step28 p h) (sat_nil p))))))))))
def c2099 : List Lit := [(2, false), (13, false), (130, true), (1, true), (12, false)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c63, c9] c2099 (by decide) p (sat_cons (step63 p h) (sat_cons (step9 p h) (sat_nil p)))
def c2100 : List Lit := [(21, true), (1596, true), (140, true), (10, true), (13, false), (12, false)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c1342, c1338, c1340, c1344, c125, c1336, c91, c148] c2100 (by decide) p (sat_cons (step1342 p h) (sat_cons (step1338 p h) (sat_cons (step1340 p h) (sat_cons (step1344 p h) (sat_cons (step125 p h) (sat_cons (step1336 p h) (sat_cons (step91 p h) (sat_cons (step148 p h) (sat_nil p)))))))))
def c2101 : List Lit := [(1754, true), (100, false), (104, false), (89, true)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c1609, c1619, c1617, c1610, c1612, c2062] c2101 (by decide) p (sat_cons (step1609 p h) (sat_cons (step1619 p h) (sat_cons (step1617 p h) (sat_cons (step1610 p h) (sat_cons (step1612 p h) (sat_cons (step2062 p h) (sat_nil p)))))))
def c2102 : List Lit := [(11, true), (1571, true), (131, true)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c1298, c1297, c15, c16, c1885] c2102 (by decide) p (sat_cons (step1298 p h) (sat_cons (step1297 p h) (sat_cons (step15 p h) (sat_cons (step16 p h) (sat_cons (step1885 p h) (sat_nil p))))))
def c2103 : List Lit := [(69, false), (71, false), (72, false), (197, true)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c428, c394] c2103 (by decide) p (sat_cons (step428 p h) (sat_cons (step394 p h) (sat_nil p)))
def c2104 : List Lit := [(1671, true), (64, false), (43, true), (57, true)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c1460, c1468, c1474, c1477, c1471, c1453, c1455, c1462, c1450, c1447, c1448, c349, c345, c312] c2104 (by decide) p (sat_cons (step1460 p h) (sat_cons (step1468 p h) (sat_cons (step1474 p h) (sat_cons (step1477 p h) (sat_cons (step1471 p h) (sat_cons (step1453 p h) (sat_cons (step1455 p h) (sat_cons (step1462 p h) (sat_cons (step1450 p h) (sat_cons (step1447 p h) (sat_cons (step1448 p h) (sat_cons (step349 p h) (sat_cons (step345 p h) (sat_cons (step312 p h) (sat_nil p)))))))))))))))
def c2105 : List Lit := [(1830, true)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c2022, c1792, c1796, c2073, c2071, c1723, c1715] c2105 (by decide) p (sat_cons (step2022 p h) (sat_cons (step1792 p h) (sat_cons (step1796 p h) (sat_cons (step2073 p h) (sat_cons (step2071 p h) (sat_cons (step1723 p h) (sat_cons (step1715 p h) (sat_nil p))))))))
def c2106 : List Lit := [(1573, true), (1, false), (5, false)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c1300, c1302, c1298, c1] c2106 (by decide) p (sat_cons (step1300 p h) (sat_cons (step1302 p h) (sat_cons (step1298 p h) (sat_cons (step1 p h) (sat_nil p)))))
def c2107 : List Lit := [(1, false), (3, true), (5, true)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c956, c2] c2107 (by decide) p (sat_cons (step956 p h) (sat_cons (step2 p h) (sat_nil p)))
def c2108 : List Lit := [(1, false), (5, true), (2, true)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c956, c3] c2108 (by decide) p (sat_cons (step956 p h) (sat_cons (step3 p h) (sat_nil p)))
def c2109 : List Lit := [(4, false), (13, true), (71, true), (40, true), (23, true)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c957, c25] c2109 (by decide) p (sat_cons (step957 p h) (sat_cons (step25 p h) (sat_nil p)))
def c2110 : List Lit := [(4, false), (71, true), (23, true), (2, true), (40, true)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c957, c26] c2110 (by decide) p (sat_cons (step957 p h) (sat_cons (step26 p h) (sat_nil p)))
def c2111 : List Lit := [(6, false), (45, true), (8, true), (5, true)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c958, c44] c2111 (by decide) p (sat_cons (step958 p h) (sat_cons (step44 p h) (sat_nil p)))
def c2112 : List Lit := [(6, false), (3, true), (45, true), (5, true)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c958, c45] c2112 (by decide) p (sat_cons (step958 p h) (sat_cons (step45 p h) (sat_nil p)))
def c2113 : List Lit := [(7, false), (5, true), (18, true), (77, true)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c959, c50] c2113 (by decide) p (sat_cons (step959 p h) (sat_cons (step50 p h) (sat_nil p)))
def c2114 : List Lit := [(7, false), (5, true), (8, true), (77, true)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c959, c51] c2114 (by decide) p (sat_cons (step959 p h) (sat_cons (step51 p h) (sat_nil p)))
def c2115 : List Lit := [(29, true), (20, true), (9, false), (79, true)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c960, c61] c2115 (by decide) p (sat_cons (step960 p h) (sat_cons (step61 p h) (sat_nil p)))
def c2116 : List Lit := [(9, false), (29, true), (8, true), (79, true)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c960, c62] c2116 (by decide) p (sat_cons (step960 p h) (sat_cons (step62 p h) (sat_nil p)))
def c2117 : List Lit := [(10, false), (16, true), (12, true), (13, true)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c961, c67] c2117 (by decide) p (sat_cons (step961 p h) (sat_cons (step67 p h) (sat_nil p)))
def c2118 : List Lit := [(10, false), (16, true), (13, true), (2, true)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c961, c68] c2118 (by decide) p (sat_cons (step961 p h) (sat_cons (step68 p h) (sat_nil p)))
def c2119 : List Lit := [(10, false), (16, true), (2, true), (12, true)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c961, c69] c2119 (by decide) p (sat_cons (step961 p h) (sat_cons (step69 p h) (sat_nil p)))
def c2120 : List Lit := [(10, false), (12, true), (2, true), (13, true)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c961, c70] c2120 (by decide) p (sat_cons (step961 p h) (sat_cons (step70 p h) (sat_nil p)))
def c2121 : List Lit := [(3, true), (11, false), (81, true), (31, true), (14, true)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c962, c81] c2121 (by decide) p (sat_cons (step962 p h) (sat_cons (step81 p h) (sat_nil p)))
def c2122 : List Lit := [(12, true), (81, true), (14, true), (11, false), (3, true)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c962, c82] c2122 (by decide) p (sat_cons (step962 p h) (sat_cons (step82 p h) (sat_nil p)))
def c2123 : List Lit := [(12, true), (3, true), (31, true), (11, false), (14, true)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c962, c83] c2123 (by decide) p (sat_cons (step962 p h) (sat_cons (step83 p h) (sat_nil p)))
def c2124 : List Lit := [(20, true), (17, false), (16, true), (89, true)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c964, c152] c2124 (by decide) p (sat_cons (step964 p h) (sat_cons (step152 p h) (sat_nil p)))
def c2125 : List Lit := [(17, false), (20, true), (12, true), (89, true)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c964, c153] c2125 (by decide) p (sat_cons (step964 p h) (sat_cons (step153 p h) (sat_nil p)))
def c2126 : List Lit := [(17, false), (16, true), (12, true), (89, true)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c964, c154] c2126 (by decide) p (sat_cons (step964 p h) (sat_cons (step154 p h) (sat_nil p)))
def c2127 : List Lit := [(19, false), (20, true), (13, true), (18, true)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c965, c166] c2127 (by decide) p (sat_cons (step965 p h) (sat_cons (step166 p h) (sat_nil p)))
def c2128 : List Lit := [(19, false), (20, true), (13, true), (16, true)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c965, c167] c2128 (by decide) p (sat_cons (step965 p h) (sat_cons (step167 p h) (sat_nil p)))
def c2129 : List Lit := [(19, false), (16, true), (13, true), (18, true)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c965, c168] c2129 (by decide) p (sat_cons (step965 p h) (sat_cons (step168 p h) (sat_nil p)))
def c2130 : List Lit := [(22, false), (32, true), (23, true)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c966, c185] c2130 (by decide) p (sat_cons (step966 p h) (sat_cons (step185 p h) (sat_nil p)))
def c2131 : List Lit := [(22, false), (23, true), (24, true)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c966, c186] c2131 (by decide) p (sat_cons (step966 p h) (sat_cons (step186 p h) (sat_nil p)))
def c2132 : List Lit := [(25, false), (21, true), (29, true), (23, true)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c967, c203] c2132 (by decide) p (sat_cons (step967 p h) (sat_cons (step203 p h) (sat_nil p)))
def c2133 : List Lit := [(26, false), (34, true), (5, true)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c968, c205] c2133 (by decide) p (sat_cons (step968 p h) (sat_cons (step205 p h) (sat_nil p)))
end B112E055
