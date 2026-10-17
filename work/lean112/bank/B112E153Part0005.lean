import B112E153Part0004
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1867 : List Lit := [(1051, true), (88, false), (89, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1206, c1201, c1202, c1198, c401, c382, c1784] c1867 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1206 p h) (sat_cons (step1201 p h) (sat_cons (step1202 p h) (sat_cons (step1198 p h) (sat_cons (step401 p h) (sat_cons (step382 p h) (sat_cons (step1784 p h) (sat_nil p)))))))))
def c1868 : List Lit := [(1037, false), (1100, false), (1099, false), (955, false), (88, false), (89, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c1615, c918, c1383, c1856, c1059, c1384, c1855, c1052, c1828, c931, c1676, c919, c1576, c1687, c1688, c912, c44, c905, c874, c33, c881, c875] c1868 (by decide) p (sat_cons (step1615 p h) (sat_cons (step918 p h) (sat_cons (step1383 p h) (sat_cons (step1856 p h) (sat_cons (step1059 p h) (sat_cons (step1384 p h) (sat_cons (step1855 p h) (sat_cons (step1052 p h) (sat_cons (step1828 p h) (sat_cons (step931 p h) (sat_cons (step1676 p h) (sat_cons (step919 p h) (sat_cons (step1576 p h) (sat_cons (step1687 p h) (sat_cons (step1688 p h) (sat_cons (step912 p h) (sat_cons (step44 p h) (sat_cons (step905 p h) (sat_cons (step874 p h) (sat_cons (step33 p h) (sat_cons (step881 p h) (sat_cons (step875 p h) (sat_nil p)))))))))))))))))))))))
def c1869 : List Lit := [(890, true), (852, false), (15, false), (20, false), (867, false)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c918, c1828, c931, c919, c887, c912, c1573, c905, c869, c30] c1869 (by decide) p (sat_cons (step918 p h) (sat_cons (step1828 p h) (sat_cons (step931 p h) (sat_cons (step919 p h) (sat_cons (step887 p h) (sat_cons (step912 p h) (sat_cons (step1573 p h) (sat_cons (step905 p h) (sat_cons (step869 p h) (sat_cons (step30 p h) (sat_nil p)))))))))))
def c1870 : List Lit := [(13, true), (26, false), (18, false), (27, false)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c1686, c1685, c69] c1870 (by decide) p (sat_cons (step1686 p h) (sat_cons (step1685 p h) (sat_cons (step69 p h) (sat_nil p))))
def c1871 : List Lit := [(93, false), (1066, true), (1011, true), (96, true), (92, false), (21, false), (89, true)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c354, c357, c1111, c1200, c1770, c1771, c1636, c377, c1241, c1202, c1210] c1871 (by decide) p (sat_cons (step354 p h) (sat_cons (step357 p h) (sat_cons (step1111 p h) (sat_cons (step1200 p h) (sat_cons (step1770 p h) (sat_cons (step1771 p h) (sat_cons (step1636 p h) (sat_cons (step377 p h) (sat_cons (step1241 p h) (sat_cons (step1202 p h) (sat_cons (step1210 p h) (sat_nil p))))))))))))
def c1872 : List Lit := [(1060, true), (1057, false), (109, false), (86, false), (1002, true)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c1661, c1666, c1221, c1075, c1213, c1669] c1872 (by decide) p (sat_cons (step1661 p h) (sat_cons (step1666 p h) (sat_cons (step1221 p h) (sat_cons (step1075 p h) (sat_cons (step1213 p h) (sat_cons (step1669 p h) (sat_nil p)))))))
def c1873 : List Lit := [(1008, true), (1088, true)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1106, c1641, c1268, c1271, c1281, c1262, c1254, c1251, c1252, c1603, c634, c1806] c1873 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1106 p h) (sat_cons (step1641 p h) (sat_cons (step1268 p h) (sat_cons (step1271 p h) (sat_cons (step1281 p h) (sat_cons (step1262 p h) (sat_cons (step1254 p h) (sat_cons (step1251 p h) (sat_cons (step1252 p h) (sat_cons (step1603 p h) (sat_cons (step634 p h) (sat_cons (step1806 p h) (sat_nil p))))))))))))))
def c1874 : List Lit := [(1089, true), (109, false), (994, true), (115, true), (1008, true)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1254, c1641, c1268, c1106, c1282, c1285, c1271, c1255, c1257, c1262, c1253, c1248, c1249, c634, c496, c1763, c1076, c230] c1874 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1254 p h) (sat_cons (step1641 p h) (sat_cons (step1268 p h) (sat_cons (step1106 p h) (sat_cons (step1282 p h) (sat_cons (step1285 p h) (sat_cons (step1271 p h) (sat_cons (step1255 p h) (sat_cons (step1257 p h) (sat_cons (step1262 p h) (sat_cons (step1253 p h) (sat_cons (step1248 p h) (sat_cons (step1249 p h) (sat_cons (step634 p h) (sat_cons (step496 p h) (sat_cons (step1763 p h) (sat_cons (step1076 p h) (sat_cons (step230 p h) (sat_nil p))))))))))))))))))))
def c1875 : List Lit := [(1059, true), (1089, true), (1081, false)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c1218, c1220, c1215, c1216, c1212, c1213, c432, c1663, c448, c1271, c1793, c1282, c440, c1256, c1249] c1875 (by decide) p (sat_cons (step1218 p h) (sat_cons (step1220 p h) (sat_cons (step1215 p h) (sat_cons (step1216 p h) (sat_cons (step1212 p h) (sat_cons (step1213 p h) (sat_cons (step432 p h) (sat_cons (step1663 p h) (sat_cons (step448 p h) (sat_cons (step1271 p h) (sat_cons (step1793 p h) (sat_cons (step1282 p h) (sat_cons (step440 p h) (sat_cons (step1256 p h) (sat_cons (step1249 p h) (sat_nil p))))))))))))))))
def c1876 : List Lit := [(1059, true), (1002, true)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c1218, c1220, c1215, c1216, c1212, c1213, c432, c448, c1669, c1791, c1075, c491] c1876 (by decide) p (sat_cons (step1218 p h) (sat_cons (step1220 p h) (sat_cons (step1215 p h) (sat_cons (step1216 p h) (sat_cons (step1212 p h) (sat_cons (step1213 p h) (sat_cons (step432 p h) (sat_cons (step448 p h) (sat_cons (step1669 p h) (sat_cons (step1791 p h) (sat_cons (step1075 p h) (sat_cons (step491 p h) (sat_nil p)))))))))))))
def c1877 : List Lit := [(71, false), (86, false), (109, false), (1072, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c489, c490, c1250] c1877 (by decide) p (sat_cons (step489 p h) (sat_cons (step490 p h) (sat_cons (step1250 p h) (sat_nil p))))
def c1878 : List Lit := [(1059, true), (109, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c1218, c1220, c1215, c1216, c1212, c1213, c432, c448, c1791] c1878 (by decide) p (sat_cons (step1218 p h) (sat_cons (step1220 p h) (sat_cons (step1215 p h) (sat_cons (step1216 p h) (sat_cons (step1212 p h) (sat_cons (step1213 p h) (sat_cons (step432 p h) (sat_cons (step448 p h) (sat_cons (step1791 p h) (sat_nil p))))))))))
def c1879 : List Lit := [(1087, true)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c1276, c1280, c1268, c1270, c1254, c1265, c1266, c1262, c1251, c586, c649, c1806] c1879 (by decide) p (sat_cons (step1276 p h) (sat_cons (step1280 p h) (sat_cons (step1268 p h) (sat_cons (step1270 p h) (sat_cons (step1254 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step1262 p h) (sat_cons (step1251 p h) (sat_cons (step586 p h) (sat_cons (step649 p h) (sat_cons (step1806 p h) (sat_nil p)))))))))))))
def c1880 : List Lit := [(103, false), (1072, true), (109, false), (86, false)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c499, c498, c1250] c1880 (by decide) p (sat_cons (step499 p h) (sat_cons (step498 p h) (sat_cons (step1250 p h) (sat_nil p))))
def c1881 : List Lit := [(1060, true), (71, false), (1057, false), (109, false), (1090, true)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1219, c1221, c1212, c1213, c491, c492, c493, c1217, c1250, c1663, c1668] c1881 (by decide) p (sat_cons (step1219 p h) (sat_cons (step1221 p h) (sat_cons (step1212 p h) (sat_cons (step1213 p h) (sat_cons (step491 p h) (sat_cons (step492 p h) (sat_cons (step493 p h) (sat_cons (step1217 p h) (sat_cons (step1250 p h) (sat_cons (step1663 p h) (sat_cons (step1668 p h) (sat_nil p))))))))))))
def c1882 : List Lit := [(103, false), (1072, true), (71, false), (109, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c492, c493, c1250] c1882 (by decide) p (sat_cons (step492 p h) (sat_cons (step493 p h) (sat_cons (step1250 p h) (sat_nil p))))
def c1883 : List Lit := [(1071, true), (89, true), (107, false), (109, true)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1248, c1249, c569, c1796] c1883 (by decide) p (sat_cons (step1248 p h) (sat_cons (step1249 p h) (sat_cons (step569 p h) (sat_cons (step1796 p h) (sat_nil p)))))
def c1884 : List Lit := [(1001, true), (108, false), (109, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c1088, c1092, c1082, c1069, c1075, c1067, c1747, c221] c1884 (by decide) p (sat_cons (step1088 p h) (sat_cons (step1092 p h) (sat_cons (step1082 p h) (sat_cons (step1069 p h) (sat_cons (step1075 p h) (sat_cons (step1067 p h) (sat_cons (step1747 p h) (sat_cons (step221 p h) (sat_nil p)))))))))
def c1885 : List Lit := [(112, false), (89, true), (107, false), (109, true)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c1798, c1796, c1541] c1885 (by decide) p (sat_cons (step1798 p h) (sat_cons (step1796 p h) (sat_cons (step1541 p h) (sat_nil p))))
def c1886 : List Lit := [(35, false), (29, false), (108, false), (109, true)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c89, c1704] c1886 (by decide) p (sat_cons (step89 p h) (sat_cons (step1704 p h) (sat_nil p)))
def c1887 : List Lit := [(975, true), (89, true), (955, false), (954, false)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1058, c1052, c1828, c1676, c919, c1688, c912, c1869, c905, c878, c33, c875] c1887 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1058 p h) (sat_cons (step1052 p h) (sat_cons (step1828 p h) (sat_cons (step1676 p h) (sat_cons (step919 p h) (sat_cons (step1688 p h) (sat_cons (step912 p h) (sat_cons (step1869 p h) (sat_cons (step905 p h) (sat_cons (step878 p h) (sat_cons (step33 p h) (sat_cons (step875 p h) (sat_nil p))))))))))))))
def c1888 : List Lit := [(12, true), (858, true)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c1576, c879, c875, c877, c878, c1548, c887, c869, c1573] c1888 (by decide) p (sat_cons (step1576 p h) (sat_cons (step879 p h) (sat_cons (step875 p h) (sat_cons (step877 p h) (sat_cons (step878 p h) (sat_cons (step1548 p h) (sat_cons (step887 p h) (sat_cons (step869 p h) (sat_cons (step1573 p h) (sat_nil p))))))))))
def c1889 : List Lit := [(113, false), (68, false), (73, false), (107, false)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c216, c561, c228, c1749] c1889 (by decide) p (sat_cons (step216 p h) (sat_cons (step561 p h) (sat_cons (step228 p h) (sat_cons (step1749 p h) (sat_nil p)))))
def c1890 : List Lit := [(1079, true), (115, false), (107, false)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1263, c1603, c597, c1807] c1890 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step1603 p h) (sat_cons (step597 p h) (sat_cons (step1807 p h) (sat_nil p))))))
def c1891 : List Lit := [(1084, true), (1079, false), (102, true), (115, false), (108, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c1273, c1271, c1265, c600, c1800, c586, c585, c1264] c1891 (by decide) p (sat_cons (step1273 p h) (sat_cons (step1271 p h) (sat_cons (step1265 p h) (sat_cons (step600 p h) (sat_cons (step1800 p h) (sat_cons (step586 p h) (sat_cons (step585 p h) (sat_cons (step1264 p h) (sat_nil p)))))))))
def c1892 : List Lit := [(115, false), (1084, true), (29, false), (1057, true)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c1216, c1215, c415, c1890, c1891] c1892 (by decide) p (sat_cons (step1216 p h) (sat_cons (step1215 p h) (sat_cons (step415 p h) (sat_cons (step1890 p h) (sat_cons (step1891 p h) (sat_nil p))))))
def c1893 : List Lit := [(1083, true)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1270, c1265, c1262, c1263, c1590, c587, c1806] c1893 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1270 p h) (sat_cons (step1265 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step1590 p h) (sat_cons (step587 p h) (sat_cons (step1806 p h) (sat_nil p)))))))))
def c1894 : List Lit := [(20, false), (12, false), (881, true), (873, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c1683, c31, c33, c893, c905, c900, c913, c920] c1894 (by decide) p (sat_cons (step1683 p h) (sat_cons (step31 p h) (sat_cons (step33 p h) (sat_cons (step893 p h) (sat_cons (step905 p h) (sat_cons (step900 p h) (sat_cons (step913 p h) (sat_cons (step920 p h) (sat_nil p)))))))))
def c1895 : List Lit := [(12, false), (881, true), (873, false)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c910, c923, c1683, c1894, c896, c898, c901, c920, c893, c913, c32, c905] c1895 (by decide) p (sat_cons (step910 p h) (sat_cons (step923 p h) (sat_cons (step1683 p h) (sat_cons (step1894 p h) (sat_cons (step896 p h) (sat_cons (step898 p h) (sat_cons (step901 p h) (sat_cons (step920 p h) (sat_cons (step893 p h) (sat_cons (step913 p h) (sat_cons (step32 p h) (sat_cons (step905 p h) (sat_nil p)))))))))))))
def c1896 : List Lit := [(880, true), (32, false), (873, false)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c910, c917, c919, c913, c898, c900, c904, c895, c893, c55, c39, c1694] c1896 (by decide) p (sat_cons (step910 p h) (sat_cons (step917 p h) (sat_cons (step919 p h) (sat_cons (step913 p h) (sat_cons (step898 p h) (sat_cons (step900 p h) (sat_cons (step904 p h) (sat_cons (step895 p h) (sat_cons (step893 p h) (sat_cons (step55 p h) (sat_cons (step39 p h) (sat_cons (step1694 p h) (sat_nil p)))))))))))))
def c1897 : List Lit := [(24, false), (867, true), (32, false)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c900, c893, c898, c895, c55, c39, c1694] c1897 (by decide) p (sat_cons (step900 p h) (sat_cons (step893 p h) (sat_cons (step898 p h) (sat_cons (step895 p h) (sat_cons (step55 p h) (sat_cons (step39 p h) (sat_cons (step1694 p h) (sat_nil p))))))))
def c1898 : List Lit := [(891, true), (880, false), (873, false)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c1829, c932, c1895, c1888] c1898 (by decide) p (sat_cons (step1829 p h) (sat_cons (step932 p h) (sat_cons (step1895 p h) (sat_cons (step1888 p h) (sat_nil p)))))
def c1899 : List Lit := [(92, false), (82, false), (20, false), (21, false), (89, false), (1019, true), (935, true)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c350, c354, c994, c1125, c298] c1899 (by decide) p (sat_cons (step350 p h) (sat_cons (step354 p h) (sat_cons (step994 p h) (sat_cons (step1125 p h) (sat_cons (step298 p h) (sat_nil p))))))
def c1900 : List Lit := [(873, false), (975, true), (944, false), (912, false)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c1632, c1027, c1058, c1829, c910, c916, c1898, c1895, c1896, c1888, c939, c931, c1619, c1052, c1033] c1900 (by decide) p (sat_cons (step1632 p h) (sat_cons (step1027 p h) (sat_cons (step1058 p h) (sat_cons (step1829 p h) (sat_cons (step910 p h) (sat_cons (step916 p h) (sat_cons (step1898 p h) (sat_cons (step1895 p h) (sat_cons (step1896 p h) (sat_cons (step1888 p h) (sat_cons (step939 p h) (sat_cons (step931 p h) (sat_cons (step1619 p h) (sat_cons (step1052 p h) (sat_cons (step1033 p h) (sat_nil p))))))))))))))))
def c1901 : List Lit := [(903, false), (916, true), (921, true), (46, true), (117, false)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c955, c958, c977, c949, c950, c974, c941, c961, c1592, c1709, c1710, c1507, c952] c1901 (by decide) p (sat_cons (step955 p h) (sat_cons (step958 p h) (sat_cons (step977 p h) (sat_cons (step949 p h) (sat_cons (step950 p h) (sat_cons (step974 p h) (sat_cons (step941 p h) (sat_cons (step961 p h) (sat_cons (step1592 p h) (sat_cons (step1709 p h) (sat_cons (step1710 p h) (sat_cons (step1507 p h) (sat_cons (step952 p h) (sat_nil p))))))))))))))
def c1902 : List Lit := [(37, false), (32, false), (114, true), (113, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c97, c1706] c1902 (by decide) p (sat_cons (step97 p h) (sat_cons (step1706 p h) (sat_nil p)))
def c1903 : List Lit := [(956, true), (944, false), (902, false), (37, true), (46, true), (117, false)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c942, c947, c955, c958, c1842, c1038, c975, c977, c974, c948, c961, c943, c952, c1592, c1709, c1710, c1507] c1903 (by decide) p (sat_cons (step942 p h) (sat_cons (step947 p h) (sat_cons (step955 p h) (sat_cons (step958 p h) (sat_cons (step1842 p h) (sat_cons (step1038 p h) (sat_cons (step975 p h) (sat_cons (step977 p h) (sat_cons (step974 p h) (sat_cons (step948 p h) (sat_cons (step961 p h) (sat_cons (step943 p h) (sat_cons (step952 p h) (sat_cons (step1592 p h) (sat_cons (step1709 p h) (sat_cons (step1710 p h) (sat_cons (step1507 p h) (sat_nil p))))))))))))))))))
def c1904 : List Lit := [(910, true), (38, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c952, c953, c1591] c1904 (by decide) p (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step1591 p h) (sat_nil p))))
def c1905 : List Lit := [(1025, true), (1008, false), (109, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c1114, c1143, c1139, c1115, c1109, c1770, c1648] c1905 (by decide) p (sat_cons (step1114 p h) (sat_cons (step1143 p h) (sat_cons (step1139 p h) (sat_cons (step1115 p h) (sat_cons (step1109 p h) (sat_cons (step1770 p h) (sat_cons (step1648 p h) (sat_nil p))))))))
def c1906 : List Lit := [(39, false), (29, false), (32, false)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c1712, c79] c1906 (by decide) p (sat_cons (step1712 p h) (sat_cons (step79 p h) (sat_nil p)))
def c1907 : List Lit := [(41, true), (38, false), (43, false)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c1709, c1710, c1507] c1907 (by decide) p (sat_cons (step1709 p h) (sat_cons (step1710 p h) (sat_cons (step1507 p h) (sat_nil p))))
def c1908 : List Lit := [(57, true), (944, true), (114, true), (73, false), (107, false)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c1861, c984, c1833, c1003, c992, c994, c1000, c1001, c164, c1012, c996, c1751, c990, c215, c1646, c983, c1720] c1908 (by decide) p (sat_cons (step1861 p h) (sat_cons (step984 p h) (sat_cons (step1833 p h) (sat_cons (step1003 p h) (sat_cons (step992 p h) (sat_cons (step994 p h) (sat_cons (step1000 p h) (sat_cons (step1001 p h) (sat_cons (step164 p h) (sat_cons (step1012 p h) (sat_cons (step996 p h) (sat_cons (step1751 p h) (sat_cons (step990 p h) (sat_cons (step215 p h) (sat_cons (step1646 p h) (sat_cons (step983 p h) (sat_cons (step1720 p h) (sat_nil p))))))))))))))))))
def c1909 : List Lit := [(927, true), (60, false), (51, true), (55, false)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c1646, c983, c1720] c1909 (by decide) p (sat_cons (step1646 p h) (sat_cons (step983 p h) (sat_cons (step1720 p h) (sat_nil p))))
def c1910 : List Lit := [(920, true), (37, true), (912, false)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c942, c944, c958, c973, c970, c945, c961, c943, c1904] c1910 (by decide) p (sat_cons (step942 p h) (sat_cons (step944 p h) (sat_cons (step958 p h) (sat_cons (step973 p h) (sat_cons (step970 p h) (sat_cons (step945 p h) (sat_cons (step961 p h) (sat_cons (step943 p h) (sat_cons (step1904 p h) (sat_nil p))))))))))
def c1911 : List Lit := [(37, true), (903, false), (922, true), (912, false)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c958, c980, c951, c942, c943, c950, c1904, c978, c961] c1911 (by decide) p (sat_cons (step958 p h) (sat_cons (step980 p h) (sat_cons (step951 p h) (sat_cons (step942 p h) (sat_cons (step943 p h) (sat_cons (step950 p h) (sat_cons (step1904 p h) (sat_cons (step978 p h) (sat_cons (step961 p h) (sat_nil p))))))))))
def c1912 : List Lit := [(112, false), (114, true), (117, false), (107, false), (109, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c457, c1795] c1912 (by decide) p (sat_cons (step457 p h) (sat_cons (step1795 p h) (sat_nil p)))
def c1913 : List Lit := [(891, true), (873, false)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c910, c916, c1829, c1898, c935, c1895, c917, c919, c875, c913, c898, c900, c904, c905, c895, c896, c893, c55, c34, c1694, c1689, c36, c43, c868, c874, c1573, c881, c888] c1913 (by decide) p (sat_cons (step910 p h) (sat_cons (step916 p h) (sat_cons (step1829 p h) (sat_cons (step1898 p h) (sat_cons (step935 p h) (sat_cons (step1895 p h) (sat_cons (step917 p h) (sat_cons (step919 p h) (sat_cons (step875 p h) (sat_cons (step913 p h) (sat_cons (step898 p h) (sat_cons (step900 p h) (sat_cons (step904 p h) (sat_cons (step905 p h) (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step893 p h) (sat_cons (step55 p h) (sat_cons (step34 p h) (sat_cons (step1694 p h) (sat_cons (step1689 p h) (sat_cons (step36 p h) (sat_cons (step43 p h) (sat_cons (step868 p h) (sat_cons (step874 p h) (sat_cons (step1573 p h) (sat_cons (step881 p h) (sat_cons (step888 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1914 : List Lit := [(103, false), (111, false), (106, true), (107, false), (109, true)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c1790, c440] c1914 (by decide) p (sat_cons (step1790 p h) (sat_cons (step440 p h) (sat_nil p)))
def c1915 : List Lit := [(1024, true), (109, true)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c1134, c1138, c1126, c1128, c1112, c1124, c1120, c1109, c321, c1770] c1915 (by decide) p (sat_cons (step1134 p h) (sat_cons (step1138 p h) (sat_cons (step1126 p h) (sat_cons (step1128 p h) (sat_cons (step1112 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1109 p h) (sat_cons (step321 p h) (sat_cons (step1770 p h) (sat_nil p)))))))))))
def c1916 : List Lit := [(902, false), (921, true), (37, true), (912, false)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c958, c977, c942, c947, c948, c974, c943, c961, c1904] c1916 (by decide) p (sat_cons (step958 p h) (sat_cons (step977 p h) (sat_cons (step942 p h) (sat_cons (step947 p h) (sat_cons (step948 p h) (sat_cons (step974 p h) (sat_cons (step943 p h) (sat_cons (step961 p h) (sat_cons (step1904 p h) (sat_nil p))))))))))
def c1917 : List Lit := [(38, false), (42, false), (35, false), (916, true), (46, true)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c1904, c118, c962, c957] c1917 (by decide) p (sat_cons (step1904 p h) (sat_cons (step118 p h) (sat_cons (step962 p h) (sat_cons (step957 p h) (sat_nil p)))))
def c1918 : List Lit := [(75, false), (63, false), (988, true), (200, true), (183, true), (940, true), (117, false)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c1588, c1758, c1756, c176, c178, c247, c992, c183, c1002, c997, c249, c1734] c1918 (by decide) p (sat_cons (step1588 p h) (sat_cons (step1758 p h) (sat_cons (step1756 p h) (sat_cons (step176 p h) (sat_cons (step178 p h) (sat_cons (step247 p h) (sat_cons (step992 p h) (sat_cons (step183 p h) (sat_cons (step1002 p h) (sat_cons (step997 p h) (sat_cons (step249 p h) (sat_cons (step1734 p h) (sat_nil p)))))))))))))
def c1919 : List Lit := [(71, false), (65, false), (108, false), (109, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c1747, c221] c1919 (by decide) p (sat_cons (step1747 p h) (sat_cons (step221 p h) (sat_nil p)))
def c1920 : List Lit := [(1009, false), (1026, true), (109, true)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c1148, c1117, c1118, c1144, c1109, c1770, c1648] c1920 (by decide) p (sat_cons (step1148 p h) (sat_cons (step1117 p h) (sat_cons (step1118 p h) (sat_cons (step1144 p h) (sat_cons (step1109 p h) (sat_cons (step1770 p h) (sat_cons (step1648 p h) (sat_nil p))))))))
def c1921 : List Lit := [(68, false), (81, false), (114, true), (73, false), (107, false)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c216, c227, c1749] c1921 (by decide) p (sat_cons (step216 p h) (sat_cons (step227 p h) (sat_cons (step1749 p h) (sat_nil p))))
def c1922 : List Lit := [(65, false), (67, true), (52, false), (29, false), (108, false)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c405, c219, c1742] c1922 (by decide) p (sat_cons (step405 p h) (sat_cons (step219 p h) (sat_cons (step1742 p h) (sat_nil p))))
def c1923 : List Lit := [(921, true), (903, false), (912, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c949, c958, c977, c974, c950, c961, c941, c1904] c1923 (by decide) p (sat_cons (step949 p h) (sat_cons (step958 p h) (sat_cons (step977 p h) (sat_cons (step974 p h) (sat_cons (step950 p h) (sat_cons (step961 p h) (sat_cons (step941 p h) (sat_cons (step1904 p h) (sat_nil p)))))))))
def c1924 : List Lit := [(903, false), (921, true), (37, true)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c979, c942, c950, c977, c951, c960, c943, c1904] c1924 (by decide) p (sat_cons (step979 p h) (sat_cons (step942 p h) (sat_cons (step950 p h) (sat_cons (step977 p h) (sat_cons (step951 p h) (sat_cons (step960 p h) (sat_cons (step943 p h) (sat_cons (step1904 p h) (sat_nil p)))))))))
def c1925 : List Lit := [(1035, true), (94, false), (81, true), (1001, false), (109, true)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c1106, c1905, c1165, c1172, c1920, c1585, c1108] c1925 (by decide) p (sat_cons (step1106 p h) (sat_cons (step1905 p h) (sat_cons (step1165 p h) (sat_cons (step1172 p h) (sat_cons (step1920 p h) (sat_cons (step1585 p h) (sat_cons (step1108 p h) (sat_nil p))))))))
def c1926 : List Lit := [(1034, true), (94, false), (1001, false), (109, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c1915, c1164, c1171, c1905, c1585, c1107] c1926 (by decide) p (sat_cons (step1915 p h) (sat_cons (step1164 p h) (sat_cons (step1171 p h) (sat_cons (step1905 p h) (sat_cons (step1585 p h) (sat_cons (step1107 p h) (sat_nil p)))))))
def c1927 : List Lit := [(915, true), (46, true), (42, false), (35, false)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c955, c959, c961, c957, c952, c119] c1927 (by decide) p (sat_cons (step955 p h) (sat_cons (step959 p h) (sat_cons (step961 p h) (sat_cons (step957 p h) (sat_cons (step952 p h) (sat_cons (step119 p h) (sat_nil p)))))))
def c1928 : List Lit := [(1028, true), (1016, false), (86, true), (91, true), (1047, true), (1008, false), (94, false)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c1124, c1129, c1109, c1115, c1150, c1146, c1116, c1130, c1111, c1125, c366, c1604] c1928 (by decide) p (sat_cons (step1124 p h) (sat_cons (step1129 p h) (sat_cons (step1109 p h) (sat_cons (step1115 p h) (sat_cons (step1150 p h) (sat_cons (step1146 p h) (sat_cons (step1116 p h) (sat_cons (step1130 p h) (sat_cons (step1111 p h) (sat_cons (step1125 p h) (sat_cons (step366 p h) (sat_cons (step1604 p h) (sat_nil p)))))))))))))
def c1929 : List Lit := [(89, true), (20, false), (52, false), (56, true), (55, false)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c1687, c1688, c1729, c1728, c1500, c1678, c155, c153, c1612, c46, c709, c721, c715, c722, c717, c723, c1812, c733] c1929 (by decide) p (sat_cons (step1687 p h) (sat_cons (step1688 p h) (sat_cons (step1729 p h) (sat_cons (step1728 p h) (sat_cons (step1500 p h) (sat_cons (step1678 p h) (sat_cons (step155 p h) (sat_cons (step153 p h) (sat_cons (step1612 p h) (sat_cons (step46 p h) (sat_cons (step709 p h) (sat_cons (step721 p h) (sat_cons (step715 p h) (sat_cons (step722 p h) (sat_cons (step717 p h) (sat_cons (step723 p h) (sat_cons (step1812 p h) (sat_cons (step733 p h) (sat_nil p)))))))))))))))))))
def c1930 : List Lit := [(1072, false), (1091, true), (118, false), (96, false), (1082, false)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c1269, c1290, c1259, c1260, c1287, c1251, c1272, c1263, c1603, c596, c1807] c1930 (by decide) p (sat_cons (step1269 p h) (sat_cons (step1290 p h) (sat_cons (step1259 p h) (sat_cons (step1260 p h) (sat_cons (step1287 p h) (sat_cons (step1251 p h) (sat_cons (step1272 p h) (sat_cons (step1263 p h) (sat_cons (step1603 p h) (sat_cons (step596 p h) (sat_cons (step1807 p h) (sat_nil p))))))))))))
end B112E153
