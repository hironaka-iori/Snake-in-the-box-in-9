import B112E024Part0007
namespace B112E024
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1874 : List Lit := [(1682, true), (110, true), (53, false), (93, false)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1712, c1204, c382, c1196] c1874 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1712 p h) (sat_cons (step1204 p h) (sat_cons (step382 p h) (sat_cons (step1196 p h) (sat_nil p))))))
def c1875 : List Lit := [(1689, true), (99, true), (89, true), (1593, true), (105, true)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c1049, c1042, c1759, c1418, c1214, c1216, c1831, c1212, c753, c1755, c754, c555, c759, c763, c760, c764, c1656, c765, c770] c1875 (by decide) p (sat_cons (step1049 p h) (sat_cons (step1042 p h) (sat_cons (step1759 p h) (sat_cons (step1418 p h) (sat_cons (step1214 p h) (sat_cons (step1216 p h) (sat_cons (step1831 p h) (sat_cons (step1212 p h) (sat_cons (step753 p h) (sat_cons (step1755 p h) (sat_cons (step754 p h) (sat_cons (step555 p h) (sat_cons (step759 p h) (sat_cons (step763 p h) (sat_cons (step760 p h) (sat_cons (step764 p h) (sat_cons (step1656 p h) (sat_cons (step765 p h) (sat_cons (step770 p h) (sat_nil p))))))))))))))))))))
def c1876 : List Lit := [(56, false), (53, false), (69, false), (93, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c260, c242, c1581] c1876 (by decide) p (sat_cons (step260 p h) (sat_cons (step242 p h) (sat_cons (step1581 p h) (sat_nil p))))
def c1877 : List Lit := [(53, false), (1537, true), (1601, true), (93, false)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1061, c1053, c1709, c1876, c943, c1345, c1420, c1580] c1877 (by decide) p (sat_cons (step1061 p h) (sat_cons (step1053 p h) (sat_cons (step1709 p h) (sat_cons (step1876 p h) (sat_cons (step943 p h) (sat_cons (step1345 p h) (sat_cons (step1420 p h) (sat_cons (step1580 p h) (sat_nil p)))))))))
def c1878 : List Lit := [(1536, true), (1601, true), (93, false)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c941, c942, c261, c1420, c1580] c1878 (by decide) p (sat_cons (step941 p h) (sat_cons (step942 p h) (sat_cons (step261 p h) (sat_cons (step1420 p h) (sat_cons (step1580 p h) (sat_nil p))))))
def c1879 : List Lit := [(1539, true), (1601, true), (93, false)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c1878, c945, c947, c1877, c939] c1879 (by decide) p (sat_cons (step1878 p h) (sat_cons (step945 p h) (sat_cons (step947 p h) (sat_cons (step1877 p h) (sat_cons (step939 p h) (sat_nil p))))))
def c1880 : List Lit := [(1689, true), (113, true)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c1214, c1216, c1212, c1755] c1880 (by decide) p (sat_cons (step1214 p h) (sat_cons (step1216 p h) (sat_cons (step1212 p h) (sat_cons (step1755 p h) (sat_nil p)))))
def c1881 : List Lit := [(1666, true), (1593, true), (105, true)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1049, c1042, c1759, c1161, c1165, c1167, c1163, c1159, c477] c1881 (by decide) p (sat_cons (step1049 p h) (sat_cons (step1042 p h) (sat_cons (step1759 p h) (sat_cons (step1161 p h) (sat_cons (step1165 p h) (sat_cons (step1167 p h) (sat_cons (step1163 p h) (sat_cons (step1159 p h) (sat_cons (step477 p h) (sat_nil p))))))))))
def c1882 : List Lit := [(98, false), (1673, false), (1642, false), (1539, false), (50, true), (61, false), (95, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c478, c466, c1209, c833, c1216, c1866, c1675, c1687, c1252, c1291] c1882 (by decide) p (sat_cons (step478 p h) (sat_cons (step466 p h) (sat_cons (step1209 p h) (sat_cons (step833 p h) (sat_cons (step1216 p h) (sat_cons (step1866 p h) (sat_cons (step1675 p h) (sat_cons (step1687 p h) (sat_cons (step1252 p h) (sat_cons (step1291 p h) (sat_nil p)))))))))))
def c1883 : List Lit := [(1689, true), (1673, false), (1659, true), (1642, false), (1539, false), (50, true), (61, false), (95, false), (94, true), (105, true)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1681, c1290, c1688, c1882, c1214, c1216, c1407, c1777, c1796, c1211, c1212, c1208, c1209, c570, c1149, c479, c468, c1643, c1151, c1154, c1163, c833, c563, c1145, c835, c1866, c1414, c1687, c1736, c1291, c1007, c1682, c1663, c1184, c844, c1813, c848, c1171, c838, c823, c1160, c829, c815, c405, c1457] c1883 (by decide) p (sat_cons (step1681 p h) (sat_cons (step1290 p h) (sat_cons (step1688 p h) (sat_cons (step1882 p h) (sat_cons (step1214 p h) (sat_cons (step1216 p h) (sat_cons (step1407 p h) (sat_cons (step1777 p h) (sat_cons (step1796 p h) (sat_cons (step1211 p h) (sat_cons (step1212 p h) (sat_cons (step1208 p h) (sat_cons (step1209 p h) (sat_cons (step570 p h) (sat_cons (step1149 p h) (sat_cons (step479 p h) (sat_cons (step468 p h) (sat_cons (step1643 p h) (sat_cons (step1151 p h) (sat_cons (step1154 p h) (sat_cons (step1163 p h) (sat_cons (step833 p h) (sat_cons (step563 p h) (sat_cons (step1145 p h) (sat_cons (step835 p h) (sat_cons (step1866 p h) (sat_cons (step1414 p h) (sat_cons (step1687 p h) (sat_cons (step1736 p h) (sat_cons (step1291 p h) (sat_cons (step1007 p h) (sat_cons (step1682 p h) (sat_cons (step1663 p h) (sat_cons (step1184 p h) (sat_cons (step844 p h) (sat_cons (step1813 p h) (sat_cons (step848 p h) (sat_cons (step1171 p h) (sat_cons (step838 p h) (sat_cons (step823 p h) (sat_cons (step1160 p h) (sat_cons (step829 p h) (sat_cons (step815 p h) (sat_cons (step405 p h) (sat_cons (step1457 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c1884 : List Lit := [(1673, false), (1659, true), (1642, false), (1539, false), (50, true), (61, false), (95, false), (94, true), (105, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c1468, c1671, c1686, c1292, c1253, c1676, c1218, c1883, c1675, c1252, c1291, c1687, c1672, c1866, c1736, c833, c1414, c468, c1209, c1210, c1217, c1211, c1212, c563, c576, c1643] c1884 (by decide) p (sat_cons (step1468 p h) (sat_cons (step1671 p h) (sat_cons (step1686 p h) (sat_cons (step1292 p h) (sat_cons (step1253 p h) (sat_cons (step1676 p h) (sat_cons (step1218 p h) (sat_cons (step1883 p h) (sat_cons (step1675 p h) (sat_cons (step1252 p h) (sat_cons (step1291 p h) (sat_cons (step1687 p h) (sat_cons (step1672 p h) (sat_cons (step1866 p h) (sat_cons (step1736 p h) (sat_cons (step833 p h) (sat_cons (step1414 p h) (sat_cons (step468 p h) (sat_cons (step1209 p h) (sat_cons (step1210 p h) (sat_cons (step1217 p h) (sat_cons (step1211 p h) (sat_cons (step1212 p h) (sat_cons (step563 p h) (sat_cons (step576 p h) (sat_cons (step1643 p h) (sat_nil p)))))))))))))))))))))))))))
def c1885 : List Lit := [(25, false), (1707, true), (1673, true), (1593, true), (105, true)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c1418, c1148, c1150, c1049, c1042, c1759, c467, c468, c466, c1163, c1209, c1159, c1168, c1178, c1183, c1248, c1151, c1676, c1149, c1708] c1885 (by decide) p (sat_cons (step1418 p h) (sat_cons (step1148 p h) (sat_cons (step1150 p h) (sat_cons (step1049 p h) (sat_cons (step1042 p h) (sat_cons (step1759 p h) (sat_cons (step467 p h) (sat_cons (step468 p h) (sat_cons (step466 p h) (sat_cons (step1163 p h) (sat_cons (step1209 p h) (sat_cons (step1159 p h) (sat_cons (step1168 p h) (sat_cons (step1178 p h) (sat_cons (step1183 p h) (sat_cons (step1248 p h) (sat_cons (step1151 p h) (sat_cons (step1676 p h) (sat_cons (step1149 p h) (sat_cons (step1708 p h) (sat_nil p)))))))))))))))))))))
def c1886 : List Lit := [(1667, false), (115, true), (1707, true), (1673, true), (94, true)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c1209, c1148, c1150, c1178, c1183, c1248, c1151, c1676, c1149, c1708] c1886 (by decide) p (sat_cons (step1209 p h) (sat_cons (step1148 p h) (sat_cons (step1150 p h) (sat_cons (step1178 p h) (sat_cons (step1183 p h) (sat_cons (step1248 p h) (sat_cons (step1151 p h) (sat_cons (step1676 p h) (sat_cons (step1149 p h) (sat_cons (step1708 p h) (sat_nil p)))))))))))
def c1887 : List Lit := [(43, false), (41, false), (35, false)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c1567, c210] c1887 (by decide) p (sat_cons (step1567 p h) (sat_cons (step210 p h) (sat_nil p)))
def c1888 : List Lit := [(1555, true), (1539, false), (50, true)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c1724, c927, c975, c1739, c1736, c967, c886, c887, c1414, c936, c1887, c925, c926, c934, c933, c929, c963, c1473, c980, c906, c1438, c901, c1564] c1888 (by decide) p (sat_cons (step1724 p h) (sat_cons (step927 p h) (sat_cons (step975 p h) (sat_cons (step1739 p h) (sat_cons (step1736 p h) (sat_cons (step967 p h) (sat_cons (step886 p h) (sat_cons (step887 p h) (sat_cons (step1414 p h) (sat_cons (step936 p h) (sat_cons (step1887 p h) (sat_cons (step925 p h) (sat_cons (step926 p h) (sat_cons (step934 p h) (sat_cons (step933 p h) (sat_cons (step929 p h) (sat_cons (step963 p h) (sat_cons (step1473 p h) (sat_cons (step980 p h) (sat_cons (step906 p h) (sat_cons (step1438 p h) (sat_cons (step901 p h) (sat_cons (step1564 p h) (sat_nil p))))))))))))))))))))))))
def c1889 : List Lit := [(39, false), (41, false), (35, false)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c1564, c182] c1889 (by decide) p (sat_cons (step1564 p h) (sat_cons (step182 p h) (sat_nil p)))
def c1890 : List Lit := [(1532, true), (1510, true), (43, true), (33, false), (50, true)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c925, c927, c936, c934, c926, c929, c1473] c1890 (by decide) p (sat_cons (step925 p h) (sat_cons (step927 p h) (sat_cons (step936 p h) (sat_cons (step934 p h) (sat_cons (step926 p h) (sat_cons (step929 p h) (sat_cons (step1473 p h) (sat_nil p))))))))
def c1891 : List Lit := [(27, true), (1502, true)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c884, c883, c1555, c1556, c1337] c1891 (by decide) p (sat_cons (step884 p h) (sat_cons (step883 p h) (sat_cons (step1555 p h) (sat_cons (step1556 p h) (sat_cons (step1337 p h) (sat_nil p))))))
def c1892 : List Lit := [(1662, false), (1707, true), (1673, true), (1593, true), (105, true)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c1418, c1148, c1150, c1179, c1049, c1042, c1759, c1161, c1170, c1171, c1886, c1163, c479] c1892 (by decide) p (sat_cons (step1418 p h) (sat_cons (step1148 p h) (sat_cons (step1150 p h) (sat_cons (step1179 p h) (sat_cons (step1049 p h) (sat_cons (step1042 p h) (sat_cons (step1759 p h) (sat_cons (step1161 p h) (sat_cons (step1170 p h) (sat_cons (step1171 p h) (sat_cons (step1886 p h) (sat_cons (step1163 p h) (sat_cons (step479 p h) (sat_nil p))))))))))))))
def c1893 : List Lit := [(1502, true), (44, false), (16, false), (35, false), (1473, false), (1482, true)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c884, c1891, c151, c148, c829, c819, c838, c821, c854, c850, c824, c841, c816, c831, c87] c1893 (by decide) p (sat_cons (step884 p h) (sat_cons (step1891 p h) (sat_cons (step151 p h) (sat_cons (step148 p h) (sat_cons (step829 p h) (sat_cons (step819 p h) (sat_cons (step838 p h) (sat_cons (step821 p h) (sat_cons (step854 p h) (sat_cons (step850 p h) (sat_cons (step824 p h) (sat_cons (step841 p h) (sat_cons (step816 p h) (sat_cons (step831 p h) (sat_cons (step87 p h) (sat_nil p))))))))))))))))
def c1894 : List Lit := [(1705, true), (1666, false), (94, true)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c1148, c1150, c1177, c1680, c1241, c1182, c1675, c1151, c1796, c1149] c1894 (by decide) p (sat_cons (step1148 p h) (sat_cons (step1150 p h) (sat_cons (step1177 p h) (sat_cons (step1680 p h) (sat_cons (step1241 p h) (sat_cons (step1182 p h) (sat_cons (step1675 p h) (sat_cons (step1151 p h) (sat_cons (step1796 p h) (sat_cons (step1149 p h) (sat_nil p)))))))))))
def c1895 : List Lit := [(88, true), (85, true), (91, false), (96, false), (1628, true), (93, false)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c1609, c1607, c349, c345, c455, c1092, c1089, c1100] c1895 (by decide) p (sat_cons (step1609 p h) (sat_cons (step1607 p h) (sat_cons (step349 p h) (sat_cons (step345 p h) (sat_cons (step455 p h) (sat_cons (step1092 p h) (sat_cons (step1089 p h) (sat_cons (step1100 p h) (sat_nil p)))))))))
def c1896 : List Lit := [(99, true), (1667, true), (1662, true), (1593, true), (105, true)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c1049, c1042, c1759, c1158, c1160, c1168, c477, c1163] c1896 (by decide) p (sat_cons (step1049 p h) (sat_cons (step1042 p h) (sat_cons (step1759 p h) (sat_cons (step1158 p h) (sat_cons (step1160 p h) (sat_cons (step1168 p h) (sat_cons (step477 p h) (sat_cons (step1163 p h) (sat_nil p)))))))))
def c1897 : List Lit := [(1667, true), (99, true), (1593, true), (105, true)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c1161, c1170, c1896] c1897 (by decide) p (sat_cons (step1161 p h) (sat_cons (step1170 p h) (sat_cons (step1896 p h) (sat_nil p))))
def c1898 : List Lit := [(1473, false), (91, false), (1480, true), (1628, true), (93, false)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c1813, c844, c835, c1863, c838, c848, c829, c823, c815, c816, c1457, c1771, c399, c402, c1092, c1089, c1100] c1898 (by decide) p (sat_cons (step1813 p h) (sat_cons (step844 p h) (sat_cons (step835 p h) (sat_cons (step1863 p h) (sat_cons (step838 p h) (sat_cons (step848 p h) (sat_cons (step829 p h) (sat_cons (step823 p h) (sat_cons (step815 p h) (sat_cons (step816 p h) (sat_cons (step1457 p h) (sat_cons (step1771 p h) (sat_cons (step399 p h) (sat_cons (step402 p h) (sat_cons (step1092 p h) (sat_cons (step1089 p h) (sat_cons (step1100 p h) (sat_nil p))))))))))))))))))
def c1899 : List Lit := [(18, false), (1653, true), (88, false), (91, false), (1627, true)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c399, c402, c1088, c1090, c1097, c1099, c1092, c1089, c1852] c1899 (by decide) p (sat_cons (step399 p h) (sat_cons (step402 p h) (sat_cons (step1088 p h) (sat_cons (step1090 p h) (sat_cons (step1097 p h) (sat_cons (step1099 p h) (sat_cons (step1092 p h) (sat_cons (step1089 p h) (sat_cons (step1852 p h) (sat_nil p))))))))))
def c1900 : List Lit := [(1689, true), (1675, true), (99, true), (89, false), (1653, false), (61, false), (95, false), (94, true), (105, true)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c1214, c1216, c1777, c1796, c1212, c1209, c1149, c509, c478, c1154, c1163, c1160, c1189, c1171] c1900 (by decide) p (sat_cons (step1214 p h) (sat_cons (step1216 p h) (sat_cons (step1777 p h) (sat_cons (step1796 p h) (sat_cons (step1212 p h) (sat_cons (step1209 p h) (sat_cons (step1149 p h) (sat_cons (step509 p h) (sat_cons (step478 p h) (sat_cons (step1154 p h) (sat_cons (step1163 p h) (sat_cons (step1160 p h) (sat_cons (step1189 p h) (sat_cons (step1171 p h) (sat_nil p)))))))))))))))
def c1901 : List Lit := [(1682, true), (110, false), (108, true), (86, false), (93, false)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c1195, c1206, c1204, c1197, c1198, c391, c1479] c1901 (by decide) p (sat_cons (step1195 p h) (sat_cons (step1206 p h) (sat_cons (step1204 p h) (sat_cons (step1197 p h) (sat_cons (step1198 p h) (sat_cons (step391 p h) (sat_cons (step1479 p h) (sat_nil p))))))))
def c1902 : List Lit := [(1619, true), (86, true), (1605, true), (93, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c1066, c1059, c1056, c1593, c1061, c1053, c285, c1077, c1069, c1048, c1045, c1587, c1054, c1057, c1443, c1385, c1084, c1078, c1382, c1596, c297, c1598, c1451, c1597, c777, c728, c1658, c729, c703, c735, c699, c740, c696, c1654, c686, c726, c685, c716, c684, c709, c245, c708, c1876, c278] c1902 (by decide) p (sat_cons (step1066 p h) (sat_cons (step1059 p h) (sat_cons (step1056 p h) (sat_cons (step1593 p h) (sat_cons (step1061 p h) (sat_cons (step1053 p h) (sat_cons (step285 p h) (sat_cons (step1077 p h) (sat_cons (step1069 p h) (sat_cons (step1048 p h) (sat_cons (step1045 p h) (sat_cons (step1587 p h) (sat_cons (step1054 p h) (sat_cons (step1057 p h) (sat_cons (step1443 p h) (sat_cons (step1385 p h) (sat_cons (step1084 p h) (sat_cons (step1078 p h) (sat_cons (step1382 p h) (sat_cons (step1596 p h) (sat_cons (step297 p h) (sat_cons (step1598 p h) (sat_cons (step1451 p h) (sat_cons (step1597 p h) (sat_cons (step777 p h) (sat_cons (step728 p h) (sat_cons (step1658 p h) (sat_cons (step729 p h) (sat_cons (step703 p h) (sat_cons (step735 p h) (sat_cons (step699 p h) (sat_cons (step740 p h) (sat_cons (step696 p h) (sat_cons (step1654 p h) (sat_cons (step686 p h) (sat_cons (step726 p h) (sat_cons (step685 p h) (sat_cons (step716 p h) (sat_cons (step684 p h) (sat_cons (step709 p h) (sat_cons (step245 p h) (sat_cons (step708 p h) (sat_cons (step1876 p h) (sat_cons (step278 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c1903 : List Lit := [(1682, false), (1674, true), (1708, true), (1653, false), (1666, false), (61, false), (95, false), (94, true), (105, true)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c1148, c1153, c1865, c478, c479, c1159, c1163, c1168, c1183, c1188, c1253, c1154, c1223, c1149, c1796] c1903 (by decide) p (sat_cons (step1148 p h) (sat_cons (step1153 p h) (sat_cons (step1865 p h) (sat_cons (step478 p h) (sat_cons (step479 p h) (sat_cons (step1159 p h) (sat_cons (step1163 p h) (sat_cons (step1168 p h) (sat_cons (step1183 p h) (sat_cons (step1188 p h) (sat_cons (step1253 p h) (sat_cons (step1154 p h) (sat_cons (step1223 p h) (sat_cons (step1149 p h) (sat_cons (step1796 p h) (sat_nil p))))))))))))))))
def c1904 : List Lit := [(1682, true), (86, false), (88, true), (93, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c1752, c391, c1196, c1751, c1204, c1199] c1904 (by decide) p (sat_cons (step1752 p h) (sat_cons (step391 p h) (sat_cons (step1196 p h) (sat_cons (step1751 p h) (sat_cons (step1204 p h) (sat_cons (step1199 p h) (sat_nil p)))))))
def c1905 : List Lit := [(1708, true), (1682, false), (1653, false), (1694, false), (1666, false), (61, false), (95, false), (94, true), (105, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1903] c1905 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1903 p h) (sat_nil p)))
def c1906 : List Lit := [(1463, true), (12, false), (18, false)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c815, c816, c32] c1906 (by decide) p (sat_cons (step815 p h) (sat_cons (step816 p h) (sat_cons (step32 p h) (sat_nil p))))
def c1907 : List Lit := [(1481, true), (1622, true), (86, false), (88, true), (93, false)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c1772, c1535, c1462, c829, c837, c853, c826, c1906, c823, c824, c849, c818, c840, c838, c831, c1733, c111, c817, c1543, c36, c88, c1089] c1907 (by decide) p (sat_cons (step1772 p h) (sat_cons (step1535 p h) (sat_cons (step1462 p h) (sat_cons (step829 p h) (sat_cons (step837 p h) (sat_cons (step853 p h) (sat_cons (step826 p h) (sat_cons (step1906 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step849 p h) (sat_cons (step818 p h) (sat_cons (step840 p h) (sat_cons (step838 p h) (sat_cons (step831 p h) (sat_cons (step1733 p h) (sat_cons (step111 p h) (sat_cons (step817 p h) (sat_cons (step1543 p h) (sat_cons (step36 p h) (sat_cons (step88 p h) (sat_cons (step1089 p h) (sat_nil p)))))))))))))))))))))))
def c1908 : List Lit := [(18, false), (19, true), (81, false), (1482, true), (88, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c1535, c1500, c1462, c1485, c829, c858, c837] c1908 (by decide) p (sat_cons (step1535 p h) (sat_cons (step1500 p h) (sat_cons (step1462 p h) (sat_cons (step1485 p h) (sat_cons (step829 p h) (sat_cons (step858 p h) (sat_cons (step837 p h) (sat_nil p))))))))
def c1909 : List Lit := [(1613, true), (69, false)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c1076, c1077, c1596, c304] c1909 (by decide) p (sat_cons (step1076 p h) (sat_cons (step1077 p h) (sat_cons (step1596 p h) (sat_cons (step304 p h) (sat_nil p)))))
def c1910 : List Lit := [(25, false), (15, false), (1464, true), (19, false)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c76, c79, c817] c1910 (by decide) p (sat_cons (step76 p h) (sat_cons (step79 p h) (sat_cons (step817 p h) (sat_nil p))))
def c1911 : List Lit := [(1555, true), (55, true), (51, false), (1539, false), (69, false), (54, true)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c1724, c1720, c975, c1888, c240, c238, c943, c940, c951, c955, c960, c980, c1437, c913, c883, c891] c1911 (by decide) p (sat_cons (step1724 p h) (sat_cons (step1720 p h) (sat_cons (step975 p h) (sat_cons (step1888 p h) (sat_cons (step240 p h) (sat_cons (step238 p h) (sat_cons (step943 p h) (sat_cons (step940 p h) (sat_cons (step951 p h) (sat_cons (step955 p h) (sat_cons (step960 p h) (sat_cons (step980 p h) (sat_cons (step1437 p h) (sat_cons (step913 p h) (sat_cons (step883 p h) (sat_cons (step891 p h) (sat_nil p)))))))))))))))))
def c1912 : List Lit := [(1705, true), (1653, false), (1670, false), (1682, false), (1665, false)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c1222, c1237, c1241, c1223, c1181, c1796, c1153, c1147] c1912 (by decide) p (sat_cons (step1222 p h) (sat_cons (step1237 p h) (sat_cons (step1241 p h) (sat_cons (step1223 p h) (sat_cons (step1181 p h) (sat_cons (step1796 p h) (sat_cons (step1153 p h) (sat_cons (step1147 p h) (sat_nil p)))))))))
def c1913 : List Lit := [(89, false), (81, false), (90, true), (86, false), (88, true), (93, false)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c453, c338, c1606] c1913 (by decide) p (sat_cons (step453 p h) (sat_cons (step338 p h) (sat_cons (step1606 p h) (sat_nil p))))
def c1914 : List Lit := [(91, false), (86, false), (88, true), (93, false)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c1607, c454] c1914 (by decide) p (sat_cons (step1607 p h) (sat_cons (step454 p h) (sat_nil p)))
def c1915 : List Lit := [(1672, true), (1621, true), (1653, false), (86, false), (105, true)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c1088, c1087, c1488, c1153, c1161, c1164, c1186, c1182, c1154, c1165, c1167, c1163, c1159, c1430, c1749] c1915 (by decide) p (sat_cons (step1088 p h) (sat_cons (step1087 p h) (sat_cons (step1488 p h) (sat_cons (step1153 p h) (sat_cons (step1161 p h) (sat_cons (step1164 p h) (sat_cons (step1186 p h) (sat_cons (step1182 p h) (sat_cons (step1154 p h) (sat_cons (step1165 p h) (sat_cons (step1167 p h) (sat_cons (step1163 p h) (sat_cons (step1159 p h) (sat_cons (step1430 p h) (sat_cons (step1749 p h) (sat_nil p))))))))))))))))
def c1916 : List Lit := [(1502, true), (29, false), (20, false)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c883, c884, c159] c1916 (by decide) p (sat_cons (step883 p h) (sat_cons (step884 p h) (sat_cons (step159 p h) (sat_nil p))))
def c1917 : List Lit := [(81, false), (1464, true), (18, false), (88, true)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c1535, c1500, c36, c817] c1917 (by decide) p (sat_cons (step1535 p h) (sat_cons (step1500 p h) (sat_cons (step36 p h) (sat_cons (step817 p h) (sat_nil p)))))
def c1918 : List Lit := [(81, true), (1624, false), (1642, true), (50, false), (54, true)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c1088, c1726, c1097, c1717] c1918 (by decide) p (sat_cons (step1088 p h) (sat_cons (step1726 p h) (sat_cons (step1097 p h) (sat_cons (step1717 p h) (sat_nil p)))))
def c1919 : List Lit := [(1593, true), (50, false)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c1048, c1049, c1046, c1042, c1043, c1444, c265, c1582] c1919 (by decide) p (sat_cons (step1048 p h) (sat_cons (step1049 p h) (sat_cons (step1046 p h) (sat_cons (step1042 p h) (sat_cons (step1043 p h) (sat_cons (step1444 p h) (sat_cons (step265 p h) (sat_cons (step1582 p h) (sat_nil p)))))))))
def c1920 : List Lit := [(115, true), (96, false), (1690, true)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c1209, c1708] c1920 (by decide) p (sat_cons (step1209 p h) (sat_cons (step1708 p h) (sat_nil p)))
def c1921 : List Lit := [(110, true), (93, false), (1682, true), (98, false)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1712, c1204, c393, c1196] c1921 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1712 p h) (sat_cons (step1204 p h) (sat_cons (step393 p h) (sat_cons (step1196 p h) (sat_nil p))))))
def c1922 : List Lit := [(107, false), (110, false), (93, false), (98, false)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c549, c393, c1628] c1922 (by decide) p (sat_cons (step549 p h) (sat_cons (step393 p h) (sat_cons (step1628 p h) (sat_nil p))))
def c1923 : List Lit := [(93, false), (1682, true), (98, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c1206, c1921, c1922, c1196, c1197, c1204, c1870, c1198] c1923 (by decide) p (sat_cons (step1206 p h) (sat_cons (step1921 p h) (sat_cons (step1922 p h) (sat_cons (step1196 p h) (sat_cons (step1197 p h) (sat_cons (step1204 p h) (sat_cons (step1870 p h) (sat_cons (step1198 p h) (sat_nil p)))))))))
def c1924 : List Lit := [(84, false), (1627, true), (91, false), (96, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c349, c345, c348, c1091, c1089, c1099] c1924 (by decide) p (sat_cons (step349 p h) (sat_cons (step345 p h) (sat_cons (step348 p h) (sat_cons (step1091 p h) (sat_cons (step1089 p h) (sat_cons (step1099 p h) (sat_nil p)))))))
def c1925 : List Lit := [(1627, true), (91, false), (99, false), (96, false), (98, false)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c1924, c1609, c1612, c417, c420, c489, c1089, c1090, c1099] c1925 (by decide) p (sat_cons (step1924 p h) (sat_cons (step1609 p h) (sat_cons (step1612 p h) (sat_cons (step417 p h) (sat_cons (step420 p h) (sat_cons (step489 p h) (sat_cons (step1089 p h) (sat_cons (step1090 p h) (sat_cons (step1099 p h) (sat_nil p))))))))))
def c1926 : List Lit := [(107, true), (88, true), (1682, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c1196, c1751, c1204, c1199] c1926 (by decide) p (sat_cons (step1196 p h) (sat_cons (step1751 p h) (sat_cons (step1204 p h) (sat_cons (step1199 p h) (sat_nil p)))))
def c1927 : List Lit := [(71, false), (55, false), (1627, false), (1593, false), (1644, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c1782, c1420, c1070] c1927 (by decide) p (sat_cons (step1782 p h) (sat_cons (step1420 p h) (sat_cons (step1070 p h) (sat_nil p))))
def c1928 : List Lit := [(1539, true), (53, false), (1491, false), (54, true), (1627, false), (1706, false), (1593, false)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c938, c947, c1499, c941, c942, c1005, c258, c1686, c1580, c1303, c1927] c1928 (by decide) p (sat_cons (step938 p h) (sat_cons (step947 p h) (sat_cons (step1499 p h) (sat_cons (step941 p h) (sat_cons (step942 p h) (sat_cons (step1005 p h) (sat_cons (step258 p h) (sat_cons (step1686 p h) (sat_cons (step1580 p h) (sat_cons (step1303 p h) (sat_cons (step1927 p h) (sat_nil p))))))))))))
def c1929 : List Lit := [(1677, true), (1627, true), (99, false), (88, false), (95, true), (1656, true), (98, false)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c1195, c1196, c419, c422, c1088, c1090, c1097, c1099, c1092, c1089, c392, c1732, c1616] c1929 (by decide) p (sat_cons (step1195 p h) (sat_cons (step1196 p h) (sat_cons (step419 p h) (sat_cons (step422 p h) (sat_cons (step1088 p h) (sat_cons (step1090 p h) (sat_cons (step1097 p h) (sat_cons (step1099 p h) (sat_cons (step1092 p h) (sat_cons (step1089 p h) (sat_cons (step392 p h) (sat_cons (step1732 p h) (sat_cons (step1616 p h) (sat_nil p))))))))))))))
def c1930 : List Lit := [(108, false), (1627, true), (99, false), (88, false), (95, true), (1656, true), (98, false)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c419, c422, c1088, c1090, c1097, c1099, c1092, c1089, c385, c1732, c1616] c1930 (by decide) p (sat_cons (step419 p h) (sat_cons (step422 p h) (sat_cons (step1088 p h) (sat_cons (step1090 p h) (sat_cons (step1097 p h) (sat_cons (step1099 p h) (sat_cons (step1092 p h) (sat_cons (step1089 p h) (sat_cons (step385 p h) (sat_cons (step1732 p h) (sat_cons (step1616 p h) (sat_nil p))))))))))))
def c1931 : List Lit := [(1627, true), (99, false), (88, false), (1682, true), (95, true), (1656, true), (98, false)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c1206, c1929, c1204, c1198, c1199, c1930, c1197, c1479, c392, c389, c1091, c1087, c1099, c1097, c1089, c1092, c415] c1931 (by decide) p (sat_cons (step1206 p h) (sat_cons (step1929 p h) (sat_cons (step1204 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step1930 p h) (sat_cons (step1197 p h) (sat_cons (step1479 p h) (sat_cons (step392 p h) (sat_cons (step389 p h) (sat_cons (step1091 p h) (sat_cons (step1087 p h) (sat_cons (step1099 p h) (sat_cons (step1097 p h) (sat_cons (step1089 p h) (sat_cons (step1092 p h) (sat_cons (step415 p h) (sat_nil p))))))))))))))))))
def c1932 : List Lit := [(1463, false), (1480, true), (95, true)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c852, c826, c823, c824, c848, c818, c835, c837, c832, c833, c829, c1910, c133, c1548] c1932 (by decide) p (sat_cons (step852 p h) (sat_cons (step826 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step848 p h) (sat_cons (step818 p h) (sat_cons (step835 p h) (sat_cons (step837 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step829 p h) (sat_cons (step1910 p h) (sat_cons (step133 p h) (sat_cons (step1548 p h) (sat_nil p)))))))))))))))
def c1933 : List Lit := [(35, false), (19, false), (20, false), (1521, true), (28, true), (13, false)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c87, c1543, c1471, c110, c1414, c885, c917, c894] c1933 (by decide) p (sat_cons (step87 p h) (sat_cons (step1543 p h) (sat_cons (step1471 p h) (sat_cons (step110 p h) (sat_cons (step1414 p h) (sat_cons (step885 p h) (sat_cons (step917 p h) (sat_cons (step894 p h) (sat_nil p)))))))))
def c1934 : List Lit := [(22, false), (1555, true), (1556, true), (12, true), (13, false), (14, false), (1480, true)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1536, c844, c836, c1421, c145, c146, c1547, c884, c924, c124, c1422, c833, c834, c994, c989, c835, c838, c1553, c1719, c848, c830, c91, c893, c821, c818, c73, c1933, c886, c888, c1714, c892, c110, c917, c1540, c908, c190, c899] c1934 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1536 p h) (sat_cons (step844 p h) (sat_cons (step836 p h) (sat_cons (step1421 p h) (sat_cons (step145 p h) (sat_cons (step146 p h) (sat_cons (step1547 p h) (sat_cons (step884 p h) (sat_cons (step924 p h) (sat_cons (step124 p h) (sat_cons (step1422 p h) (sat_cons (step833 p h) (sat_cons (step834 p h) (sat_cons (step994 p h) (sat_cons (step989 p h) (sat_cons (step835 p h) (sat_cons (step838 p h) (sat_cons (step1553 p h) (sat_cons (step1719 p h) (sat_cons (step848 p h) (sat_cons (step830 p h) (sat_cons (step91 p h) (sat_cons (step893 p h) (sat_cons (step821 p h) (sat_cons (step818 p h) (sat_cons (step73 p h) (sat_cons (step1933 p h) (sat_cons (step886 p h) (sat_cons (step888 p h) (sat_cons (step1714 p h) (sat_cons (step892 p h) (sat_cons (step110 p h) (sat_cons (step917 p h) (sat_cons (step1540 p h) (sat_cons (step908 p h) (sat_cons (step190 p h) (sat_cons (step899 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1935 : List Lit := [(1473, true), (1463, true), (95, true)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c816, c815, c832, c833, c132, c74, c1548] c1935 (by decide) p (sat_cons (step816 p h) (sat_cons (step815 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step132 p h) (sat_cons (step74 p h) (sat_cons (step1548 p h) (sat_nil p))))))))
def c1936 : List Lit := [(16, true), (30, false), (19, false), (28, true), (20, false)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c1543, c1542, c110, c160, c165, c655, c656, c1644] c1936 (by decide) p (sat_cons (step1543 p h) (sat_cons (step1542 p h) (sat_cons (step110 p h) (sat_cons (step160 p h) (sat_cons (step165 p h) (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step1644 p h) (sat_nil p)))))))))
def c1937 : List Lit := [(24, false), (1480, true), (22, false), (30, false)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c844, c836, c1421, c815, c823, c848, c835, c1453, c832, c141] c1937 (by decide) p (sat_cons (step844 p h) (sat_cons (step836 p h) (sat_cons (step1421 p h) (sat_cons (step815 p h) (sat_cons (step823 p h) (sat_cons (step848 p h) (sat_cons (step835 p h) (sat_cons (step1453 p h) (sat_cons (step832 p h) (sat_cons (step141 p h) (sat_nil p)))))))))))
end B112E024
