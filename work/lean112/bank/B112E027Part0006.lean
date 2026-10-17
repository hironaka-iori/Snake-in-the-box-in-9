import B112E027Part0005
namespace B112E027
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1834 : List Lit := [(52, true), (1521, false), (1479, false), (69, false), (68, false), (1666, false), (1596, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1125, c1762, c1380, c1238, c1799, c1804, c1126, c1163, c1763, c1161, c1373, c314, c1230, c1153, c1173, c1154] c1834 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1125 p h) (sat_cons (step1762 p h) (sat_cons (step1380 p h) (sat_cons (step1238 p h) (sat_cons (step1799 p h) (sat_cons (step1804 p h) (sat_cons (step1126 p h) (sat_cons (step1163 p h) (sat_cons (step1763 p h) (sat_cons (step1161 p h) (sat_cons (step1373 p h) (sat_cons (step314 p h) (sat_cons (step1230 p h) (sat_cons (step1153 p h) (sat_cons (step1173 p h) (sat_cons (step1154 p h) (sat_nil p))))))))))))))))))
def c1835 : List Lit := [(1575, true), (69, false), (68, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1170, c1173, c1163, c1154, c1161, c1153, c314] c1835 (by decide) p (sat_cons (step1170 p h) (sat_cons (step1173 p h) (sat_cons (step1163 p h) (sat_cons (step1154 p h) (sat_cons (step1161 p h) (sat_cons (step1153 p h) (sat_cons (step314 p h) (sat_nil p))))))))
def c1836 : List Lit := [(1521, false), (1479, false), (69, false), (68, false), (1666, false), (83, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c1835, c1817, c1746, c1558, c1834, c1125, c1828, c1762, c1747, c1380, c1231] c1836 (by decide) p (sat_cons (step1835 p h) (sat_cons (step1817 p h) (sat_cons (step1746 p h) (sat_cons (step1558 p h) (sat_cons (step1834 p h) (sat_cons (step1125 p h) (sat_cons (step1828 p h) (sat_cons (step1762 p h) (sat_cons (step1747 p h) (sat_cons (step1380 p h) (sat_cons (step1231 p h) (sat_nil p))))))))))))
def c1837 : List Lit := [(1576, true), (59, true), (69, false), (68, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1155, c1177, c1174, c1156, c1163, c1153, c1161, c314] c1837 (by decide) p (sat_cons (step1155 p h) (sat_cons (step1177 p h) (sat_cons (step1174 p h) (sat_cons (step1156 p h) (sat_cons (step1163 p h) (sat_cons (step1153 p h) (sat_cons (step1161 p h) (sat_cons (step314 p h) (sat_nil p)))))))))
def c1838 : List Lit := [(1479, false), (69, false), (68, false), (1520, false), (1666, false), (83, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c1588, c1817, c1746, c1124, c1761, c1386, c1836, c1504, c1837, c1238, c1239, c1380, c1747, c1762, c1828, c1125, c1793] c1838 (by decide) p (sat_cons (step1588 p h) (sat_cons (step1817 p h) (sat_cons (step1746 p h) (sat_cons (step1124 p h) (sat_cons (step1761 p h) (sat_cons (step1386 p h) (sat_cons (step1836 p h) (sat_cons (step1504 p h) (sat_cons (step1837 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step1380 p h) (sat_cons (step1747 p h) (sat_cons (step1762 p h) (sat_cons (step1828 p h) (sat_cons (step1125 p h) (sat_cons (step1793 p h) (sat_nil p))))))))))))))))))
def c1839 : List Lit := [(68, false), (1520, false), (1666, false), (83, false), (57, false), (89, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1748, c1833, c1835, c1838, c1800, c1562, c1790, c1747, c1798, c1231, c1504, c1380, c1799, c1762, c1740] c1839 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1748 p h) (sat_cons (step1833 p h) (sat_cons (step1835 p h) (sat_cons (step1838 p h) (sat_cons (step1800 p h) (sat_cons (step1562 p h) (sat_cons (step1790 p h) (sat_cons (step1747 p h) (sat_cons (step1798 p h) (sat_cons (step1231 p h) (sat_cons (step1504 p h) (sat_cons (step1380 p h) (sat_cons (step1799 p h) (sat_cons (step1762 p h) (sat_cons (step1740 p h) (sat_nil p)))))))))))))))))
def c1840 : List Lit := [(1521, false), (1550, true), (1593, true), (83, false), (57, false), (89, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1740, c1558, c1799, c1125, c1790, c1800] c1840 (by decide) p (sat_cons (step1740 p h) (sat_cons (step1558 p h) (sat_cons (step1799 p h) (sat_cons (step1125 p h) (sat_cons (step1790 p h) (sat_cons (step1800 p h) (sat_nil p)))))))
def c1841 : List Lit := [(1597, false), (1520, false), (1666, false), (83, false), (57, false), (89, false)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c1839, c1157, c1165, c1170, c1813, c1748, c1588, c1231, c1380, c1762, c1840, c1504, c1155, c1798, c1174, c1790, c1239, c1800, c1386, c1124, c1761] c1841 (by decide) p (sat_cons (step1839 p h) (sat_cons (step1157 p h) (sat_cons (step1165 p h) (sat_cons (step1170 p h) (sat_cons (step1813 p h) (sat_cons (step1748 p h) (sat_cons (step1588 p h) (sat_cons (step1231 p h) (sat_cons (step1380 p h) (sat_cons (step1762 p h) (sat_cons (step1840 p h) (sat_cons (step1504 p h) (sat_cons (step1155 p h) (sat_cons (step1798 p h) (sat_cons (step1174 p h) (sat_cons (step1790 p h) (sat_cons (step1239 p h) (sat_cons (step1800 p h) (sat_cons (step1386 p h) (sat_cons (step1124 p h) (sat_cons (step1761 p h) (sat_nil p))))))))))))))))))))))
def c1842 : List Lit := [(1493, false), (1534, true), (1520, false), (52, true)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1056, c1059, c1083, c1106, c1048, c1049, c1102, c1040, c1088, c1566] c1842 (by decide) p (sat_cons (step1056 p h) (sat_cons (step1059 p h) (sat_cons (step1083 p h) (sat_cons (step1106 p h) (sat_cons (step1048 p h) (sat_cons (step1049 p h) (sat_cons (step1102 p h) (sat_cons (step1040 p h) (sat_cons (step1088 p h) (sat_cons (step1566 p h) (sat_nil p)))))))))))
def c1843 : List Lit := [(347, false), (13, false), (69, false), (65, true), (70, false), (74, false), (67, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c793, c1704, c1723, c731, c918, c697, c848, c850, c694, c845, c816, c692, c828, c829, c814, c691, c827, c823, c824, c809, c58, c826, c821, c326, c1528, c308, c1610, c303, c316, c1816, c334] c1843 (by decide) p (sat_cons (step793 p h) (sat_cons (step1704 p h) (sat_cons (step1723 p h) (sat_cons (step731 p h) (sat_cons (step918 p h) (sat_cons (step697 p h) (sat_cons (step848 p h) (sat_cons (step850 p h) (sat_cons (step694 p h) (sat_cons (step845 p h) (sat_cons (step816 p h) (sat_cons (step692 p h) (sat_cons (step828 p h) (sat_cons (step829 p h) (sat_cons (step814 p h) (sat_cons (step691 p h) (sat_cons (step827 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step809 p h) (sat_cons (step58 p h) (sat_cons (step826 p h) (sat_cons (step821 p h) (sat_cons (step326 p h) (sat_cons (step1528 p h) (sat_cons (step308 p h) (sat_cons (step1610 p h) (sat_cons (step303 p h) (sat_cons (step316 p h) (sat_cons (step1816 p h) (sat_cons (step334 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1844 : List Lit := [(77, true), (73, false), (74, false), (1585, true)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c1185, c1181, c1183, c1187, c323] c1844 (by decide) p (sat_cons (step1185 p h) (sat_cons (step1181 p h) (sat_cons (step1183 p h) (sat_cons (step1187 p h) (sat_cons (step323 p h) (sat_nil p))))))
def c1845 : List Lit := [(22, false), (81, false), (21, true), (140, true), (40, true), (89, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c123, c432] c1845 (by decide) p (sat_cons (step123 p h) (sat_cons (step432 p h) (sat_nil p)))
def c1846 : List Lit := [(22, true), (1458, true), (11, false), (317, true), (36, true), (38, false), (32, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c750, c739, c735, c734, c748, c746, c742, c741, c1619, c966, c163, c176, c1621, c180, c108] c1846 (by decide) p (sat_cons (step750 p h) (sat_cons (step739 p h) (sat_cons (step735 p h) (sat_cons (step734 p h) (sat_cons (step748 p h) (sat_cons (step746 p h) (sat_cons (step742 p h) (sat_cons (step741 p h) (sat_cons (step1619 p h) (sat_cons (step966 p h) (sat_cons (step163 p h) (sat_cons (step176 p h) (sat_cons (step1621 p h) (sat_cons (step180 p h) (sat_cons (step108 p h) (sat_nil p))))))))))))))))
def c1847 : List Lit := [(84, false), (54, false), (1592, true), (89, false)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c414, c416, c1190, c1193, c1198] c1847 (by decide) p (sat_cons (step414 p h) (sat_cons (step416 p h) (sat_cons (step1190 p h) (sat_cons (step1193 p h) (sat_cons (step1198 p h) (sat_nil p))))))
def c1848 : List Lit := [(104, false), (108, true), (36, true), (222, true), (84, true), (65, true)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c569, c568, c1674, c1447] c1848 (by decide) p (sat_cons (step569 p h) (sat_cons (step568 p h) (sat_cons (step1674 p h) (sat_cons (step1447 p h) (sat_nil p)))))
def c1849 : List Lit := [(37, true), (156, true), (38, false), (20, true)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c180, c179, c1623, c1424] c1849 (by decide) p (sat_cons (step180 p h) (sat_cons (step179 p h) (sat_cons (step1623 p h) (sat_cons (step1424 p h) (sat_nil p)))))
def c1850 : List Lit := [(1479, true), (142, true), (17, true)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1724, c1729, c1578, c1516, c937] c1850 (by decide) p (sat_cons (step1724 p h) (sat_cons (step1729 p h) (sat_cons (step1578 p h) (sat_cons (step1516 p h) (sat_cons (step937 p h) (sat_nil p))))))
def c1851 : List Lit := [(41, false), (35, false), (39, false), (140, true), (157, true), (1480, true), (17, true), (81, false), (89, false)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c969, c1725, c990, c983, c189, c1567, c937, c1516, c1010, c992, c989, c970, c980, c964, c1523, c432, c123] c1851 (by decide) p (sat_cons (step969 p h) (sat_cons (step1725 p h) (sat_cons (step990 p h) (sat_cons (step983 p h) (sat_cons (step189 p h) (sat_cons (step1567 p h) (sat_cons (step937 p h) (sat_cons (step1516 p h) (sat_cons (step1010 p h) (sat_cons (step992 p h) (sat_cons (step989 p h) (sat_cons (step970 p h) (sat_cons (step980 p h) (sat_cons (step964 p h) (sat_cons (step1523 p h) (sat_cons (step432 p h) (sat_cons (step123 p h) (sat_nil p))))))))))))))))))
def c1852 : List Lit := [(343, false), (54, true), (1534, true), (1496, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c783, c1702, c788, c762, c793, c760, c1723, c757, c918, c1533, c850, c1504, c818, c1638, c805, c1639, c799, c798] c1852 (by decide) p (sat_cons (step783 p h) (sat_cons (step1702 p h) (sat_cons (step788 p h) (sat_cons (step762 p h) (sat_cons (step793 p h) (sat_cons (step760 p h) (sat_cons (step1723 p h) (sat_cons (step757 p h) (sat_cons (step918 p h) (sat_cons (step1533 p h) (sat_cons (step850 p h) (sat_cons (step1504 p h) (sat_cons (step818 p h) (sat_cons (step1638 p h) (sat_cons (step805 p h) (sat_cons (step1639 p h) (sat_cons (step799 p h) (sat_cons (step798 p h) (sat_nil p)))))))))))))))))))
def c1853 : List Lit := [(1521, true), (170, true), (52, false), (54, true)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c1065, c1075, c1073, c1066, c1068, c1553] c1853 (by decide) p (sat_cons (step1065 p h) (sat_cons (step1075 p h) (sat_cons (step1073 p h) (sat_cons (step1066 p h) (sat_cons (step1068 p h) (sat_cons (step1553 p h) (sat_nil p)))))))
def c1854 : List Lit := [(1521, false), (1534, true), (1496, false)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1042, c1045, c1102, c1079, c1533, c1084, c1106, c209, c1697, c1061, c1046, c1043, c1038, c1037, c214, c198, c207] c1854 (by decide) p (sat_cons (step1042 p h) (sat_cons (step1045 p h) (sat_cons (step1102 p h) (sat_cons (step1079 p h) (sat_cons (step1533 p h) (sat_cons (step1084 p h) (sat_cons (step1106 p h) (sat_cons (step209 p h) (sat_cons (step1697 p h) (sat_cons (step1061 p h) (sat_cons (step1046 p h) (sat_cons (step1043 p h) (sat_cons (step1038 p h) (sat_cons (step1037 p h) (sat_cons (step214 p h) (sat_cons (step198 p h) (sat_cons (step207 p h) (sat_nil p))))))))))))))))))
def c1855 : List Lit := [(54, true), (1534, true), (1496, false)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1854, c1065, c1852, c1072, c780, c1795, c770, c1853, c767] c1855 (by decide) p (sat_cons (step1854 p h) (sat_cons (step1065 p h) (sat_cons (step1852 p h) (sat_cons (step1072 p h) (sat_cons (step780 p h) (sat_cons (step1795 p h) (sat_cons (step770 p h) (sat_cons (step1853 p h) (sat_cons (step767 p h) (sat_nil p))))))))))
def c1856 : List Lit := [(19, false), (1480, true), (20, false), (38, false), (145, true)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1010, c1516, c937, c1512, c1725, c990, c979, c108, c1616, c977, c148, c94] c1856 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1010 p h) (sat_cons (step1516 p h) (sat_cons (step937 p h) (sat_cons (step1512 p h) (sat_cons (step1725 p h) (sat_cons (step990 p h) (sat_cons (step979 p h) (sat_cons (step108 p h) (sat_cons (step1616 p h) (sat_cons (step977 p h) (sat_cons (step148 p h) (sat_cons (step94 p h) (sat_nil p))))))))))))))
def c1857 : List Lit := [(1480, true), (17, true), (1466, false), (20, false), (38, false), (145, true)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c1725, c1856, c993, c965, c970] c1857 (by decide) p (sat_cons (step1725 p h) (sat_cons (step1856 p h) (sat_cons (step993 p h) (sat_cons (step965 p h) (sat_cons (step970 p h) (sat_nil p))))))
def c1858 : List Lit := [(108, true), (1654, true), (35, false), (38, false), (172, false)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c768, c769, c780, c783, c788, c793, c1723, c918, c850, c818, c805, c799, c798, c1639, c244, c243, c916, c911, c906, c901, c898, c897, c908, c889, c885, c1787, c173, c1848] c1858 (by decide) p (sat_cons (step768 p h) (sat_cons (step769 p h) (sat_cons (step780 p h) (sat_cons (step783 p h) (sat_cons (step788 p h) (sat_cons (step793 p h) (sat_cons (step1723 p h) (sat_cons (step918 p h) (sat_cons (step850 p h) (sat_cons (step818 p h) (sat_cons (step805 p h) (sat_cons (step799 p h) (sat_cons (step798 p h) (sat_cons (step1639 p h) (sat_cons (step244 p h) (sat_cons (step243 p h) (sat_cons (step916 p h) (sat_cons (step911 p h) (sat_cons (step906 p h) (sat_cons (step901 p h) (sat_cons (step898 p h) (sat_cons (step897 p h) (sat_cons (step908 p h) (sat_cons (step889 p h) (sat_cons (step885 p h) (sat_cons (step1787 p h) (sat_cons (step173 p h) (sat_cons (step1848 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1859 : List Lit := [(85, false), (20, false), (1460, true), (38, false)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c107, c110, c970, c965] c1859 (by decide) p (sat_cons (step107 p h) (sat_cons (step110 p h) (sat_cons (step970 p h) (sat_cons (step965 p h) (sat_nil p)))))
def c1860 : List Lit := [(1653, true), (35, false), (38, false), (172, false)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c768, c769, c780, c783, c788, c793, c1723, c918, c850, c818, c805, c799, c798, c1639, c244, c243, c916, c911, c906, c901, c898, c897, c908, c889, c885, c1598, c1597, c173] c1860 (by decide) p (sat_cons (step768 p h) (sat_cons (step769 p h) (sat_cons (step780 p h) (sat_cons (step783 p h) (sat_cons (step788 p h) (sat_cons (step793 p h) (sat_cons (step1723 p h) (sat_cons (step918 p h) (sat_cons (step850 p h) (sat_cons (step818 p h) (sat_cons (step805 p h) (sat_cons (step799 p h) (sat_cons (step798 p h) (sat_cons (step1639 p h) (sat_cons (step244 p h) (sat_cons (step243 p h) (sat_cons (step916 p h) (sat_cons (step911 p h) (sat_cons (step906 p h) (sat_cons (step901 p h) (sat_cons (step898 p h) (sat_cons (step897 p h) (sat_cons (step908 p h) (sat_cons (step889 p h) (sat_cons (step885 p h) (sat_cons (step1598 p h) (sat_cons (step1597 p h) (sat_cons (step173 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1861 : List Lit := [(1521, true), (56, true), (175, true), (60, false), (58, true)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c1068, c1071, c1504, c1073, c1069, c1638, c1064, c268, c235] c1861 (by decide) p (sat_cons (step1068 p h) (sat_cons (step1071 p h) (sat_cons (step1504 p h) (sat_cons (step1073 p h) (sat_cons (step1069 p h) (sat_cons (step1638 p h) (sat_cons (step1064 p h) (sat_cons (step268 p h) (sat_cons (step235 p h) (sat_nil p))))))))))
def c1862 : List Lit := [(142, false), (1628, true), (97, true), (100, true), (88, false), (102, true), (92, false), (95, false), (90, false)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c131, c712, c462, c713, c1267, c721, c1275, c724, c1264, c729, c515, c795, c528, c1723, c864, c916, c868, c913, c874, c877] c1862 (by decide) p (sat_cons (step131 p h) (sat_cons (step712 p h) (sat_cons (step462 p h) (sat_cons (step713 p h) (sat_cons (step1267 p h) (sat_cons (step721 p h) (sat_cons (step1275 p h) (sat_cons (step724 p h) (sat_cons (step1264 p h) (sat_cons (step729 p h) (sat_cons (step515 p h) (sat_cons (step795 p h) (sat_cons (step528 p h) (sat_cons (step1723 p h) (sat_cons (step864 p h) (sat_cons (step916 p h) (sat_cons (step868 p h) (sat_cons (step913 p h) (sat_cons (step874 p h) (sat_cons (step877 p h) (sat_nil p)))))))))))))))))))))
def c1863 : List Lit := [(96, false), (214, true), (100, true), (1616, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c1255, c1254, c515, c528] c1863 (by decide) p (sat_cons (step1255 p h) (sat_cons (step1254 p h) (sat_cons (step515 p h) (sat_cons (step528 p h) (sat_nil p)))))
def c1864 : List Lit := [(1520, true), (58, true), (88, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c1070, c1812, c1067, c262] c1864 (by decide) p (sat_cons (step1070 p h) (sat_cons (step1812 p h) (sat_cons (step1067 p h) (sat_cons (step262 p h) (sat_nil p)))))
def c1865 : List Lit := [(1518, true), (58, true), (87, true), (88, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c1067, c1068, c266, c258, c774, c772, c1700] c1865 (by decide) p (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_cons (step266 p h) (sat_cons (step258 p h) (sat_cons (step774 p h) (sat_cons (step772 p h) (sat_cons (step1700 p h) (sat_nil p))))))))
def c1866 : List Lit := [(1665, false), (1685, true), (1479, false), (1598, false), (52, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c1224, c1379, c1385, c1763, c1232, c1126, c1173, c1799, c1155, c1504] c1866 (by decide) p (sat_cons (step1224 p h) (sat_cons (step1379 p h) (sat_cons (step1385 p h) (sat_cons (step1763 p h) (sat_cons (step1232 p h) (sat_cons (step1126 p h) (sat_cons (step1173 p h) (sat_cons (step1799 p h) (sat_cons (step1155 p h) (sat_cons (step1504 p h) (sat_nil p)))))))))))
def c1867 : List Lit := [(1535, true), (1522, false), (52, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c1056, c1059, c1085, c1097, c1103, c1090, c1045, c1566, c1040] c1867 (by decide) p (sat_cons (step1056 p h) (sat_cons (step1059 p h) (sat_cons (step1085 p h) (sat_cons (step1097 p h) (sat_cons (step1103 p h) (sat_cons (step1090 p h) (sat_cons (step1045 p h) (sat_cons (step1566 p h) (sat_cons (step1040 p h) (sat_nil p))))))))))
def c1868 : List Lit := [(1627, true), (100, false), (97, true), (102, true), (90, false)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1265, c1274, c1272, c1264, c1267, c545] c1868 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1265 p h) (sat_cons (step1274 p h) (sat_cons (step1272 p h) (sat_cons (step1264 p h) (sat_cons (step1267 p h) (sat_cons (step545 p h) (sat_nil p))))))))
def c1869 : List Lit := [(1479, true), (88, true), (17, true)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c1724, c1850, c1823, c131] c1869 (by decide) p (sat_cons (step1724 p h) (sat_cons (step1850 p h) (sat_cons (step1823 p h) (sat_cons (step131 p h) (sat_nil p)))))
def c1870 : List Lit := [(1639, false), (233, true), (1654, true)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1301, c1304, c1325, c1294, c1314, c1311, c1312, c610, c608] c1870 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1301 p h) (sat_cons (step1304 p h) (sat_cons (step1325 p h) (sat_cons (step1294 p h) (sat_cons (step1314 p h) (sat_cons (step1311 p h) (sat_cons (step1312 p h) (sat_cons (step610 p h) (sat_cons (step608 p h) (sat_nil p)))))))))))
def c1871 : List Lit := [(1639, false), (1654, true), (92, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1301, c1304, c1870, c1325, c1294, c606, c1314, c1316, c1311, c1309, c610, c590, c607] c1871 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1301 p h) (sat_cons (step1304 p h) (sat_cons (step1870 p h) (sat_cons (step1325 p h) (sat_cons (step1294 p h) (sat_cons (step606 p h) (sat_cons (step1314 p h) (sat_cons (step1316 p h) (sat_cons (step1311 p h) (sat_cons (step1309 p h) (sat_cons (step610 p h) (sat_cons (step590 p h) (sat_cons (step607 p h) (sat_nil p)))))))))))))))
def c1872 : List Lit := [(100, false), (1627, true), (97, false), (102, true), (90, false)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c546, c544, c1267, c1263, c1272] c1872 (by decide) p (sat_cons (step546 p h) (sat_cons (step544 p h) (sat_cons (step1267 p h) (sat_cons (step1263 p h) (sat_cons (step1272 p h) (sat_nil p))))))
def c1873 : List Lit := [(1520, true), (88, true), (90, false)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c1070, c1864, c1067, c1068, c272] c1873 (by decide) p (sat_cons (step1070 p h) (sat_cons (step1864 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_cons (step272 p h) (sat_nil p))))))
def c1874 : List Lit := [(1627, true), (97, true), (102, true), (88, true), (90, false), (99, true)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1868, c1272, c536, c1267] c1874 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1868 p h) (sat_cons (step1272 p h) (sat_cons (step536 p h) (sat_cons (step1267 p h) (sat_nil p))))))
def c1875 : List Lit := [(1479, false), (1665, false), (1533, false), (1598, false), (52, true)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c1125, c1866, c1762] c1875 (by decide) p (sat_cons (step1125 p h) (sat_cons (step1866 p h) (sat_cons (step1762 p h) (sat_nil p))))
def c1876 : List Lit := [(1534, true), (157, true), (15, false), (1463, true), (1520, false), (52, true)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c1795, c1842, c1035, c1036, c1031, c1567, c1029] c1876 (by decide) p (sat_cons (step1795 p h) (sat_cons (step1842 p h) (sat_cons (step1035 p h) (sat_cons (step1036 p h) (sat_cons (step1031 p h) (sat_cons (step1567 p h) (sat_cons (step1029 p h) (sat_nil p))))))))
def c1877 : List Lit := [(1535, true), (1496, false), (1521, false), (52, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1042, c1045, c1056, c1059, c1084, c1107, c1103, c1046, c1089, c1043, c1566] c1877 (by decide) p (sat_cons (step1042 p h) (sat_cons (step1045 p h) (sat_cons (step1056 p h) (sat_cons (step1059 p h) (sat_cons (step1084 p h) (sat_cons (step1107 p h) (sat_cons (step1103 p h) (sat_cons (step1046 p h) (sat_cons (step1089 p h) (sat_cons (step1043 p h) (sat_cons (step1566 p h) (sat_nil p))))))))))))
def c1878 : List Lit := [(423, true), (1626, true), (88, true), (92, false), (90, false), (99, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c867, c868, c866, c864, c541, c1266, c1271, c1262, c1263, c544, c517, c528] c1878 (by decide) p (sat_cons (step867 p h) (sat_cons (step868 p h) (sat_cons (step866 p h) (sat_cons (step864 p h) (sat_cons (step541 p h) (sat_cons (step1266 p h) (sat_cons (step1271 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step544 p h) (sat_cons (step517 p h) (sat_cons (step528 p h) (sat_nil p)))))))))))))
def c1879 : List Lit := [(1472, true), (19, true), (142, true), (1463, true), (15, false), (17, true), (88, true)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c965, c970, c996, c993, c971, c978, c980, c966, c976, c972, c1805, c95, c138] c1879 (by decide) p (sat_cons (step965 p h) (sat_cons (step970 p h) (sat_cons (step996 p h) (sat_cons (step993 p h) (sat_cons (step971 p h) (sat_cons (step978 p h) (sat_cons (step980 p h) (sat_cons (step966 p h) (sat_cons (step976 p h) (sat_cons (step972 p h) (sat_cons (step1805 p h) (sat_cons (step95 p h) (sat_cons (step138 p h) (sat_nil p))))))))))))))
def c1880 : List Lit := [(1496, true), (1463, true), (15, false), (157, true), (35, false)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c1035, c1036, c1567] c1880 (by decide) p (sat_cons (step1035 p h) (sat_cons (step1036 p h) (sat_cons (step1567 p h) (sat_nil p))))
def c1881 : List Lit := [(1625, true), (88, true), (92, false), (90, false)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1270, c1266, c1564] c1881 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1270 p h) (sat_cons (step1266 p h) (sat_cons (step1564 p h) (sat_nil p)))))
def c1882 : List Lit := [(315, false), (69, true), (68, false), (74, false), (1452, true), (40, true), (36, true), (35, false), (39, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c748, c1695, c790, c738, c793, c1704, c737, c1723, c731, c736, c918, c697, c848, c850, c695, c845, c816, c689, c829, c814, c1776, c824, c808, c327, c807, c1778] c1882 (by decide) p (sat_cons (step748 p h) (sat_cons (step1695 p h) (sat_cons (step790 p h) (sat_cons (step738 p h) (sat_cons (step793 p h) (sat_cons (step1704 p h) (sat_cons (step737 p h) (sat_cons (step1723 p h) (sat_cons (step731 p h) (sat_cons (step736 p h) (sat_cons (step918 p h) (sat_cons (step697 p h) (sat_cons (step848 p h) (sat_cons (step850 p h) (sat_cons (step695 p h) (sat_cons (step845 p h) (sat_cons (step816 p h) (sat_cons (step689 p h) (sat_cons (step829 p h) (sat_cons (step814 p h) (sat_cons (step1776 p h) (sat_cons (step824 p h) (sat_cons (step808 p h) (sat_cons (step327 p h) (sat_cons (step807 p h) (sat_cons (step1778 p h) (sat_nil p)))))))))))))))))))))))))))
def c1883 : List Lit := [(1621, true), (100, true), (87, true), (92, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1263, c517, c528, c532, c1713] c1883 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step517 p h) (sat_cons (step528 p h) (sat_cons (step532 p h) (sat_cons (step1713 p h) (sat_nil p)))))))
def c1884 : List Lit := [(1520, true), (87, true), (58, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c1070, c1812, c1067, c1068, c268, c258, c774, c772, c1700] c1884 (by decide) p (sat_cons (step1070 p h) (sat_cons (step1812 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_cons (step268 p h) (sat_cons (step258 p h) (sat_cons (step774 p h) (sat_cons (step772 p h) (sat_cons (step1700 p h) (sat_nil p))))))))))
def c1885 : List Lit := [(1571, false), (1576, true), (1479, false), (1664, false), (1598, false), (52, true)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c1170, c1174, c1232, c1155, c1384, c1504, c1763, c1799, c1126] c1885 (by decide) p (sat_cons (step1170 p h) (sat_cons (step1174 p h) (sat_cons (step1232 p h) (sat_cons (step1155 p h) (sat_cons (step1384 p h) (sat_cons (step1504 p h) (sat_cons (step1763 p h) (sat_cons (step1799 p h) (sat_cons (step1126 p h) (sat_nil p))))))))))
def c1886 : List Lit := [(69, false), (1576, true), (1479, false), (1664, false), (1598, false), (52, true)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c1885, c1165, c1157, c1835, c1837, c1232, c1504, c1384, c1799, c1763, c1126] c1886 (by decide) p (sat_cons (step1885 p h) (sat_cons (step1165 p h) (sat_cons (step1157 p h) (sat_cons (step1835 p h) (sat_cons (step1837 p h) (sat_cons (step1232 p h) (sat_cons (step1504 p h) (sat_cons (step1384 p h) (sat_cons (step1799 p h) (sat_cons (step1763 p h) (sat_cons (step1126 p h) (sat_nil p))))))))))))
def c1887 : List Lit := [(17, false), (15, false), (135, true), (261, true), (24, true), (1452, true), (1472, true), (20, true)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c92, c1543, c78, c990, c974, c983] c1887 (by decide) p (sat_cons (step92 p h) (sat_cons (step1543 p h) (sat_cons (step78 p h) (sat_cons (step990 p h) (sat_cons (step974 p h) (sat_cons (step983 p h) (sat_nil p)))))))
def c1888 : List Lit := [(24, true), (15, false), (1472, true), (25, true), (87, true), (17, true), (92, false)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c969, c990, c983, c972, c974, c980, c981, c993, c976, c970, c146, c964, c965, c1805, c80, c94, c129, c149, c710, c716, c714, c719, c1691] c1888 (by decide) p (sat_cons (step969 p h) (sat_cons (step990 p h) (sat_cons (step983 p h) (sat_cons (step972 p h) (sat_cons (step974 p h) (sat_cons (step980 p h) (sat_cons (step981 p h) (sat_cons (step993 p h) (sat_cons (step976 p h) (sat_cons (step970 p h) (sat_cons (step146 p h) (sat_cons (step964 p h) (sat_cons (step965 p h) (sat_cons (step1805 p h) (sat_cons (step80 p h) (sat_cons (step94 p h) (sat_cons (step129 p h) (sat_cons (step149 p h) (sat_cons (step710 p h) (sat_cons (step716 p h) (sat_cons (step714 p h) (sat_cons (step719 p h) (sat_cons (step1691 p h) (sat_nil p))))))))))))))))))))))))
def c1889 : List Lit := [(275, false), (21, true), (24, false), (15, false), (1465, true), (25, true), (20, true)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c714, c1690, c1691, c712, c718, c139, c717, c95, c1617, c977, c154] c1889 (by decide) p (sat_cons (step714 p h) (sat_cons (step1690 p h) (sat_cons (step1691 p h) (sat_cons (step712 p h) (sat_cons (step718 p h) (sat_cons (step139 p h) (sat_cons (step717 p h) (sat_cons (step95 p h) (sat_cons (step1617 p h) (sat_cons (step977 p h) (sat_cons (step154 p h) (sat_nil p))))))))))))
def c1890 : List Lit := [(23, false), (15, false), (1472, true), (25, true), (87, true), (17, true), (92, false), (20, true)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c1888, c969, c990, c979, c116, c1889, c710, c129, c80, c965, c970, c993, c978, c976, c146, c95, c139, c149, c712, c716, c713, c719, c1691] c1890 (by decide) p (sat_cons (step1888 p h) (sat_cons (step969 p h) (sat_cons (step990 p h) (sat_cons (step979 p h) (sat_cons (step116 p h) (sat_cons (step1889 p h) (sat_cons (step710 p h) (sat_cons (step129 p h) (sat_cons (step80 p h) (sat_cons (step965 p h) (sat_cons (step970 p h) (sat_cons (step993 p h) (sat_cons (step978 p h) (sat_cons (step976 p h) (sat_cons (step146 p h) (sat_cons (step95 p h) (sat_cons (step139 p h) (sat_cons (step149 p h) (sat_cons (step712 p h) (sat_cons (step716 p h) (sat_cons (step713 p h) (sat_cons (step719 p h) (sat_cons (step1691 p h) (sat_nil p))))))))))))))))))))))))
def c1891 : List Lit := [(15, false), (1472, true), (25, true), (87, true), (17, true), (92, false), (20, true)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c969, c990, c983, c1888, c1890, c973, c980, c981, c993, c976, c970, c146, c95, c964, c149, c1805, c716, c139, c719, c712, c1691, c713] c1891 (by decide) p (sat_cons (step969 p h) (sat_cons (step990 p h) (sat_cons (step983 p h) (sat_cons (step1888 p h) (sat_cons (step1890 p h) (sat_cons (step973 p h) (sat_cons (step980 p h) (sat_cons (step981 p h) (sat_cons (step993 p h) (sat_cons (step976 p h) (sat_cons (step970 p h) (sat_cons (step146 p h) (sat_cons (step95 p h) (sat_cons (step964 p h) (sat_cons (step149 p h) (sat_cons (step1805 p h) (sat_cons (step716 p h) (sat_cons (step139 p h) (sat_cons (step719 p h) (sat_cons (step712 p h) (sat_cons (step1691 p h) (sat_cons (step713 p h) (sat_nil p)))))))))))))))))))))))
def c1892 : List Lit := [(1480, true), (25, true), (87, true), (17, true), (92, false), (20, true)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c969, c1725, c1730, c1891, c937, c1526, c1516, c1010, c992, c989, c970, c978, c980, c964, c965, c976, c972, c973, c119, c96, c139, c712, c713, c1690, c721, c710, c724, c129, c1693, c74, c697, c927, c695, c929, c689, c954, c943, c935, c26, c41] c1892 (by decide) p (sat_cons (step969 p h) (sat_cons (step1725 p h) (sat_cons (step1730 p h) (sat_cons (step1891 p h) (sat_cons (step937 p h) (sat_cons (step1526 p h) (sat_cons (step1516 p h) (sat_cons (step1010 p h) (sat_cons (step992 p h) (sat_cons (step989 p h) (sat_cons (step970 p h) (sat_cons (step978 p h) (sat_cons (step980 p h) (sat_cons (step964 p h) (sat_cons (step965 p h) (sat_cons (step976 p h) (sat_cons (step972 p h) (sat_cons (step973 p h) (sat_cons (step119 p h) (sat_cons (step96 p h) (sat_cons (step139 p h) (sat_cons (step712 p h) (sat_cons (step713 p h) (sat_cons (step1690 p h) (sat_cons (step721 p h) (sat_cons (step710 p h) (sat_cons (step724 p h) (sat_cons (step129 p h) (sat_cons (step1693 p h) (sat_cons (step74 p h) (sat_cons (step697 p h) (sat_cons (step927 p h) (sat_cons (step695 p h) (sat_cons (step929 p h) (sat_cons (step689 p h) (sat_cons (step954 p h) (sat_cons (step943 p h) (sat_cons (step935 p h) (sat_cons (step26 p h) (sat_cons (step41 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c1893 : List Lit := [(94, true), (1622, true), (214, true), (215, true), (100, true), (87, true)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c528, c532, c1264] c1893 (by decide) p (sat_cons (step528 p h) (sat_cons (step532 p h) (sat_cons (step1264 p h) (sat_nil p))))
def c1894 : List Lit := [(102, false), (1588, true), (83, false), (85, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c406, c403, c1191] c1894 (by decide) p (sat_cons (step406 p h) (sat_cons (step403 p h) (sat_cons (step1191 p h) (sat_nil p))))
def c1895 : List Lit := [(1522, true), (54, true), (82, false), (57, true), (58, true), (87, true)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c1065, c1067, c1076, c1074, c1066, c1069, c225, c257] c1895 (by decide) p (sat_cons (step1065 p h) (sat_cons (step1067 p h) (sat_cons (step1076 p h) (sat_cons (step1074 p h) (sat_cons (step1066 p h) (sat_cons (step1069 p h) (sat_cons (step225 p h) (sat_cons (step257 p h) (sat_nil p)))))))))
def c1896 : List Lit := [(92, false), (1664, true), (1624, false), (1618, false), (100, true), (87, true)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c1883, c1272, c1283, c1347, c1319, c1321, c1314, c1316, c1302, c1311, c1312, c1309, c1294, c610, c590, c607] c1896 (by decide) p (sat_cons (step1883 p h) (sat_cons (step1272 p h) (sat_cons (step1283 p h) (sat_cons (step1347 p h) (sat_cons (step1319 p h) (sat_cons (step1321 p h) (sat_cons (step1314 p h) (sat_cons (step1316 p h) (sat_cons (step1302 p h) (sat_cons (step1311 p h) (sat_cons (step1312 p h) (sat_cons (step1309 p h) (sat_cons (step1294 p h) (sat_cons (step610 p h) (sat_cons (step590 p h) (sat_cons (step607 p h) (sat_nil p)))))))))))))))))
def c1897 : List Lit := [(1621, true), (82, false), (100, true), (87, true)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1263, c514, c532, c528, c1713] c1897 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step514 p h) (sat_cons (step532 p h) (sat_cons (step528 p h) (sat_cons (step1713 p h) (sat_nil p)))))))
end B112E027
