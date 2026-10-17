import B112E259Part0004
namespace B112E259
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1860 : List Lit := [(323, false), (337, false)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c1552, c749] c1860 (by decide) p (sat_cons (step1552 p h) (sat_cons (step749 p h) (sat_nil p)))
def c1861 : List Lit := [(311, false), (339, false)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c1548, c753] c1861 (by decide) p (sat_cons (step1548 p h) (sat_cons (step753 p h) (sat_nil p)))
def c1862 : List Lit := [(285, false), (341, false)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c1545, c758] c1862 (by decide) p (sat_cons (step1545 p h) (sat_cons (step758 p h) (sat_nil p)))
def c1863 : List Lit := [(361, false), (363, false)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c1563, c774] c1863 (by decide) p (sat_cons (step1563 p h) (sat_cons (step774 p h) (sat_nil p)))
def c1864 : List Lit := [(355, false), (367, false)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c1551, c781] c1864 (by decide) p (sat_cons (step1551 p h) (sat_cons (step781 p h) (sat_nil p)))
def c1865 : List Lit := [(381, false), (395, false)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c1550, c797] c1865 (by decide) p (sat_cons (step1550 p h) (sat_cons (step797 p h) (sat_nil p)))
def c1866 : List Lit := [(369, false), (397, false)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c1547, c801] c1866 (by decide) p (sat_cons (step1547 p h) (sat_cons (step801 p h) (sat_nil p)))
def c1867 : List Lit := [(425, false), (453, false)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c1546, c832] c1867 (by decide) p (sat_cons (step1546 p h) (sat_cons (step832 p h) (sat_nil p)))
def c1868 : List Lit := [(399, false), (455, false)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c1544, c836] c1868 (by decide) p (sat_cons (step1544 p h) (sat_cons (step836 p h) (sat_nil p)))
def c1869 : List Lit := [(343, false), (457, false)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c841, c839] c1869 (by decide) p (sat_cons (step841 p h) (sat_cons (step839 p h) (sat_nil p)))
def c1870 : List Lit := [(1019, true), (985, false)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c1716, c1266] c1870 (by decide) p (sat_cons (step1716 p h) (sat_cons (step1266 p h) (sat_nil p)))
def c1871 : List Lit := [(1020, true), (986, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c1716, c1270] c1871 (by decide) p (sat_cons (step1716 p h) (sat_cons (step1270 p h) (sat_nil p)))
def c1872 : List Lit := [(987, false), (1021, true)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c1716, c1272] c1872 (by decide) p (sat_cons (step1716 p h) (sat_cons (step1272 p h) (sat_nil p)))
def c1873 : List Lit := [(988, false), (1022, true)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c1716, c1275] c1873 (by decide) p (sat_cons (step1716 p h) (sat_cons (step1275 p h) (sat_nil p)))
def c1874 : List Lit := [(1035, true), (959, false)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1717, c1276] c1874 (by decide) p (sat_cons (step1717 p h) (sat_cons (step1276 p h) (sat_nil p)))
def c1875 : List Lit := [(1036, true), (960, false)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c1717, c1281] c1875 (by decide) p (sat_cons (step1717 p h) (sat_cons (step1281 p h) (sat_nil p)))
def c1876 : List Lit := [(1037, true), (961, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c1717, c1286] c1876 (by decide) p (sat_cons (step1717 p h) (sat_cons (step1286 p h) (sat_nil p)))
def c1877 : List Lit := [(962, false), (1038, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1717, c1291] c1877 (by decide) p (sat_cons (step1717 p h) (sat_cons (step1291 p h) (sat_nil p)))
def c1878 : List Lit := [(963, false), (1039, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c1717, c1296] c1878 (by decide) p (sat_cons (step1717 p h) (sat_cons (step1296 p h) (sat_nil p)))
def c1879 : List Lit := [(964, false), (1040, true)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c1717, c1301] c1879 (by decide) p (sat_cons (step1717 p h) (sat_cons (step1301 p h) (sat_nil p)))
def c1880 : List Lit := [(965, false), (1041, true)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c1717, c1305] c1880 (by decide) p (sat_cons (step1717 p h) (sat_cons (step1305 p h) (sat_nil p)))
def c1881 : List Lit := [(966, false), (1042, true)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1717, c1308] c1881 (by decide) p (sat_cons (step1717 p h) (sat_cons (step1308 p h) (sat_nil p)))
def c1882 : List Lit := [(903, false), (1044, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1311] c1882 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1311 p h) (sat_nil p)))
def c1883 : List Lit := [(904, false), (1043, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1312] c1883 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1312 p h) (sat_nil p)))
def c1884 : List Lit := [(905, false), (1042, false)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1313] c1884 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1313 p h) (sat_nil p)))
def c1885 : List Lit := [(906, false), (1041, false)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1314] c1885 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1314 p h) (sat_nil p)))
def c1886 : List Lit := [(907, false), (1040, false)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1315] c1886 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1315 p h) (sat_nil p)))
def c1887 : List Lit := [(908, false), (1039, false)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1316] c1887 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1316 p h) (sat_nil p)))
def c1888 : List Lit := [(909, false), (1038, false)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1317] c1888 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1317 p h) (sat_nil p)))
def c1889 : List Lit := [(910, false), (1037, false)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1318] c1889 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1318 p h) (sat_nil p)))
def c1890 : List Lit := [(911, false), (1036, false)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1319] c1890 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1319 p h) (sat_nil p)))
def c1891 : List Lit := [(912, false), (1035, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1320] c1891 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1320 p h) (sat_nil p)))
def c1892 : List Lit := [(1510, false), (1649, false)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1496] c1892 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1496 p h) (sat_nil p)))
def c1893 : List Lit := [(34, false), (17, false), (16, false)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c1764, c1515] c1893 (by decide) p (sat_cons (step1764 p h) (sat_cons (step1515 p h) (sat_nil p)))
def c1894 : List Lit := [(841, false), (887, true), (873, false), (28, false), (19, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c1016, c1040, c989, c969, c972, c985, c147, c1035, c996, c1020, c998] c1894 (by decide) p (sat_cons (step1016 p h) (sat_cons (step1040 p h) (sat_cons (step989 p h) (sat_cons (step969 p h) (sat_cons (step972 p h) (sat_cons (step985 p h) (sat_cons (step147 p h) (sat_cons (step1035 p h) (sat_cons (step996 p h) (sat_cons (step1020 p h) (sat_cons (step998 p h) (sat_nil p))))))))))))
def c1895 : List Lit := [(887, true), (873, false), (19, false), (28, false)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c1894, c967, c146, c149, c971, c996, c985, c998, c1035, c1020] c1895 (by decide) p (sat_cons (step1894 p h) (sat_cons (step967 p h) (sat_cons (step146 p h) (sat_cons (step149 p h) (sat_cons (step971 p h) (sat_cons (step996 p h) (sat_cons (step985 p h) (sat_cons (step998 p h) (sat_cons (step1035 p h) (sat_cons (step1020 p h) (sat_nil p)))))))))))
def c1896 : List Lit := [(831, true), (812, false), (789, false), (28, false), (810, false), (19, false)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c898, c913, c868, c930, c936, c914, c869, c899, c858, c893, c850, c128] c1896 (by decide) p (sat_cons (step898 p h) (sat_cons (step913 p h) (sat_cons (step868 p h) (sat_cons (step930 p h) (sat_cons (step936 p h) (sat_cons (step914 p h) (sat_cons (step869 p h) (sat_cons (step899 p h) (sat_cons (step858 p h) (sat_cons (step893 p h) (sat_cons (step850 p h) (sat_cons (step128 p h) (sat_nil p)))))))))))))
def c1897 : List Lit := [(927, true), (63, false), (64, false), (18, true)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c1122, c1124, c1119, c1120, c1116, c372, c1806, c361] c1897 (by decide) p (sat_cons (step1122 p h) (sat_cons (step1124 p h) (sat_cons (step1119 p h) (sat_cons (step1120 p h) (sat_cons (step1116 p h) (sat_cons (step372 p h) (sat_cons (step1806 p h) (sat_cons (step361 p h) (sat_nil p)))))))))
def c1898 : List Lit := [(932, true), (63, false), (85, false), (95, false), (60, false), (64, false), (187, true), (18, true), (82, false), (15, true)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c1897, c1131, c1127, c1134, c1113, c304, c471, c1791, c1793, c1530, c358, c1118, c374, c1806, c361] c1898 (by decide) p (sat_cons (step1897 p h) (sat_cons (step1131 p h) (sat_cons (step1127 p h) (sat_cons (step1134 p h) (sat_cons (step1113 p h) (sat_cons (step304 p h) (sat_cons (step471 p h) (sat_cons (step1791 p h) (sat_cons (step1793 p h) (sat_cons (step1530 p h) (sat_cons (step358 p h) (sat_cons (step1118 p h) (sat_cons (step374 p h) (sat_cons (step1806 p h) (sat_cons (step361 p h) (sat_nil p))))))))))))))))
def c1899 : List Lit := [(84, false), (60, false), (82, false)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c1814, c456] c1899 (by decide) p (sat_cons (step1814 p h) (sat_cons (step456 p h) (sat_nil p)))
def c1900 : List Lit := [(873, true), (58, false), (63, false)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c1008, c1010, c1006, c1002, c278] c1900 (by decide) p (sat_cons (step1008 p h) (sat_cons (step1010 p h) (sat_cons (step1006 p h) (sat_cons (step1002 p h) (sat_cons (step278 p h) (sat_nil p))))))
def c1901 : List Lit := [(832, true), (810, false), (19, false), (28, false), (790, false), (812, false)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c898, c913, c873, c943, c937, c874, c914, c858, c899, c850, c893, c128] c1901 (by decide) p (sat_cons (step898 p h) (sat_cons (step913 p h) (sat_cons (step873 p h) (sat_cons (step943 p h) (sat_cons (step937 p h) (sat_cons (step874 p h) (sat_cons (step914 p h) (sat_cons (step858 p h) (sat_cons (step899 p h) (sat_cons (step850 p h) (sat_cons (step893 p h) (sat_cons (step128 p h) (sat_nil p)))))))))))))
def c1902 : List Lit := [(843, true), (19, false), (28, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c969, c971, c967, c146] c1902 (by decide) p (sat_cons (step969 p h) (sat_cons (step971 p h) (sat_cons (step967 p h) (sat_cons (step146 p h) (sat_nil p)))))
def c1903 : List Lit := [(928, true), (72, false), (63, false), (66, true)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c1117, c1127, c1125, c1118, c1119, c361] c1903 (by decide) p (sat_cons (step1117 p h) (sat_cons (step1127 p h) (sat_cons (step1125 p h) (sat_cons (step1118 p h) (sat_cons (step1119 p h) (sat_cons (step361 p h) (sat_nil p)))))))
def c1904 : List Lit := [(954, true), (56, false), (75, true), (83, true), (84, true), (945, false), (19, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c1150, c1154, c1162, c1174, c1178, c1165, c1151, c1155, c1146, c1816, c432, c423, c1744] c1904 (by decide) p (sat_cons (step1150 p h) (sat_cons (step1154 p h) (sat_cons (step1162 p h) (sat_cons (step1174 p h) (sat_cons (step1178 p h) (sat_cons (step1165 p h) (sat_cons (step1151 p h) (sat_cons (step1155 p h) (sat_cons (step1146 p h) (sat_cons (step1816 p h) (sat_cons (step432 p h) (sat_cons (step423 p h) (sat_cons (step1744 p h) (sat_nil p))))))))))))))
def c1905 : List Lit := [(802, true), (1, true), (60, false), (10, true), (61, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c847, c850, c858, c870, c874, c861, c859, c848, c852, c853, c842, c32, c1727] c1905 (by decide) p (sat_cons (step847 p h) (sat_cons (step850 p h) (sat_cons (step858 p h) (sat_cons (step870 p h) (sat_cons (step874 p h) (sat_cons (step861 p h) (sat_cons (step859 p h) (sat_cons (step848 p h) (sat_cons (step852 p h) (sat_cons (step853 p h) (sat_cons (step842 p h) (sat_cons (step32 p h) (sat_cons (step1727 p h) (sat_nil p))))))))))))))
def c1906 : List Lit := [(5, false), (10, true), (60, false), (798, true), (1, false)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c21, c23, c852, c853, c862] c1906 (by decide) p (sat_cons (step21 p h) (sat_cons (step23 p h) (sat_cons (step852 p h) (sat_cons (step853 p h) (sat_cons (step862 p h) (sat_nil p))))))
def c1907 : List Lit := [(921, false), (1041, true), (66, true), (954, false)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c1880, c1210, c1117, c1124, c1139, c1140, c1204, c1127, c1125, c1302, c1118, c1119, c1870, c1234, c1220, c1222, c1217, c1218, c524, c364, c1830] c1907 (by decide) p (sat_cons (step1880 p h) (sat_cons (step1210 p h) (sat_cons (step1117 p h) (sat_cons (step1124 p h) (sat_cons (step1139 p h) (sat_cons (step1140 p h) (sat_cons (step1204 p h) (sat_cons (step1127 p h) (sat_cons (step1125 p h) (sat_cons (step1302 p h) (sat_cons (step1118 p h) (sat_cons (step1119 p h) (sat_cons (step1870 p h) (sat_cons (step1234 p h) (sat_cons (step1220 p h) (sat_cons (step1222 p h) (sat_cons (step1217 p h) (sat_cons (step1218 p h) (sat_cons (step524 p h) (sat_cons (step364 p h) (sat_cons (step1830 p h) (sat_nil p))))))))))))))))))))))
def c1908 : List Lit := [(15, true), (17, true), (807, false), (817, false), (908, true), (874, false), (873, false), (801, false)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c1017, c1029, c1090, c938, c919, c889, c888, c884, c914, c937, c1085, c1030, c1895, c1021, c1777, c998, c996] c1908 (by decide) p (sat_cons (step1017 p h) (sat_cons (step1029 p h) (sat_cons (step1090 p h) (sat_cons (step938 p h) (sat_cons (step919 p h) (sat_cons (step889 p h) (sat_cons (step888 p h) (sat_cons (step884 p h) (sat_cons (step914 p h) (sat_cons (step937 p h) (sat_cons (step1085 p h) (sat_cons (step1030 p h) (sat_cons (step1895 p h) (sat_cons (step1021 p h) (sat_cons (step1777 p h) (sat_cons (step998 p h) (sat_cons (step996 p h) (sat_nil p))))))))))))))))))
def c1909 : List Lit := [(90, false), (128, true), (147, true), (94, false), (30, false), (28, true)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c1732, c515, c520, c62, c177, c1760] c1909 (by decide) p (sat_cons (step1732 p h) (sat_cons (step515 p h) (sat_cons (step520 p h) (sat_cons (step62 p h) (sat_cons (step177 p h) (sat_cons (step1760 p h) (sat_nil p)))))))
def c1910 : List Lit := [(887, true), (28, true), (19, false), (871, false), (74, false)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c1008, c1777, c996, c998, c1020, c1743, c1732, c1030, c1035, c1021, c1025, c985, c1011, c1001, c969, c971, c1002, c994, c967, c398, c399, c1774, c1775, c1525, c1762, c1844, c820, c821, c823, c829, c830, c1867, c833, c815, c1869, c807, c755, c757, c806, c752, c697, c803, c721, c664, c536, c710, c659, c701, c657, c700, c654, c1909, c1830, c1759, c364, c62] c1910 (by decide) p (sat_cons (step1008 p h) (sat_cons (step1777 p h) (sat_cons (step996 p h) (sat_cons (step998 p h) (sat_cons (step1020 p h) (sat_cons (step1743 p h) (sat_cons (step1732 p h) (sat_cons (step1030 p h) (sat_cons (step1035 p h) (sat_cons (step1021 p h) (sat_cons (step1025 p h) (sat_cons (step985 p h) (sat_cons (step1011 p h) (sat_cons (step1001 p h) (sat_cons (step969 p h) (sat_cons (step971 p h) (sat_cons (step1002 p h) (sat_cons (step994 p h) (sat_cons (step967 p h) (sat_cons (step398 p h) (sat_cons (step399 p h) (sat_cons (step1774 p h) (sat_cons (step1775 p h) (sat_cons (step1525 p h) (sat_cons (step1762 p h) (sat_cons (step1844 p h) (sat_cons (step820 p h) (sat_cons (step821 p h) (sat_cons (step823 p h) (sat_cons (step829 p h) (sat_cons (step830 p h) (sat_cons (step1867 p h) (sat_cons (step833 p h) (sat_cons (step815 p h) (sat_cons (step1869 p h) (sat_cons (step807 p h) (sat_cons (step755 p h) (sat_cons (step757 p h) (sat_cons (step806 p h) (sat_cons (step752 p h) (sat_cons (step697 p h) (sat_cons (step803 p h) (sat_cons (step721 p h) (sat_cons (step664 p h) (sat_cons (step536 p h) (sat_cons (step710 p h) (sat_cons (step659 p h) (sat_cons (step701 p h) (sat_cons (step657 p h) (sat_cons (step700 p h) (sat_cons (step654 p h) (sat_cons (step1909 p h) (sat_cons (step1830 p h) (sat_cons (step1759 p h) (sat_cons (step364 p h) (sat_cons (step62 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1911 : List Lit := [(44, false), (115, false), (104, true), (223, true)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c1774, c1775, c1605] c1911 (by decide) p (sat_cons (step1774 p h) (sat_cons (step1775 p h) (sat_cons (step1605 p h) (sat_nil p))))
def c1912 : List Lit := [(45, false), (44, true), (100, true), (116, false), (212, true), (153, true), (157, true), (161, true), (165, true), (48, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c1847, c210, c212, c585, c1767, c219, c194, c1770, c1834, c203, c551, c1839] c1912 (by decide) p (sat_cons (step1847 p h) (sat_cons (step210 p h) (sat_cons (step212 p h) (sat_cons (step585 p h) (sat_cons (step1767 p h) (sat_cons (step219 p h) (sat_cons (step194 p h) (sat_cons (step1770 p h) (sat_cons (step1834 p h) (sat_cons (step203 p h) (sat_cons (step551 p h) (sat_cons (step1839 p h) (sat_nil p)))))))))))))
def c1913 : List Lit := [(52, false), (964, false), (104, true), (873, false), (114, false), (106, false), (212, true), (214, true), (223, true), (218, true), (153, true), (156, true), (157, true), (161, true), (165, true), (169, true), (159, true), (828, false), (48, true)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c996, c1780, c1781, c225, c207, c1847, c1772, c562, c1837, c556, c1769, c200, c1778, c582, c1911, c994, c1001, c1025, c1912, c1766, c975, c195, c980, c1835, c983, c1225, c552, c1036, c1838, c1061, c1227, c1884, c1231, c1303, c1233, c1871] c1913 (by decide) p (sat_cons (step996 p h) (sat_cons (step1780 p h) (sat_cons (step1781 p h) (sat_cons (step225 p h) (sat_cons (step207 p h) (sat_cons (step1847 p h) (sat_cons (step1772 p h) (sat_cons (step562 p h) (sat_cons (step1837 p h) (sat_cons (step556 p h) (sat_cons (step1769 p h) (sat_cons (step200 p h) (sat_cons (step1778 p h) (sat_cons (step582 p h) (sat_cons (step1911 p h) (sat_cons (step994 p h) (sat_cons (step1001 p h) (sat_cons (step1025 p h) (sat_cons (step1912 p h) (sat_cons (step1766 p h) (sat_cons (step975 p h) (sat_cons (step195 p h) (sat_cons (step980 p h) (sat_cons (step1835 p h) (sat_cons (step983 p h) (sat_cons (step1225 p h) (sat_cons (step552 p h) (sat_cons (step1036 p h) (sat_cons (step1838 p h) (sat_cons (step1061 p h) (sat_cons (step1227 p h) (sat_cons (step1884 p h) (sat_cons (step1231 p h) (sat_cons (step1303 p h) (sat_cons (step1233 p h) (sat_cons (step1871 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1914 : List Lit := [(116, true), (997, false), (830, false), (871, false), (960, false), (214, true), (218, true), (156, true), (169, true), (159, true), (48, true)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c1250, c225, c1580, c1780, c1259, c1003, c206, c1011, c1773, c977, c563, c1836, c1228, c555, c1229, c1768, c1232, c974, c201, c1267, c981, c1779, c1283, c984, c997, c1888, c999, c1075, c1026, c1043] c1914 (by decide) p (sat_cons (step1250 p h) (sat_cons (step225 p h) (sat_cons (step1580 p h) (sat_cons (step1780 p h) (sat_cons (step1259 p h) (sat_cons (step1003 p h) (sat_cons (step206 p h) (sat_cons (step1011 p h) (sat_cons (step1773 p h) (sat_cons (step977 p h) (sat_cons (step563 p h) (sat_cons (step1836 p h) (sat_cons (step1228 p h) (sat_cons (step555 p h) (sat_cons (step1229 p h) (sat_cons (step1768 p h) (sat_cons (step1232 p h) (sat_cons (step974 p h) (sat_cons (step201 p h) (sat_cons (step1267 p h) (sat_cons (step981 p h) (sat_cons (step1779 p h) (sat_cons (step1283 p h) (sat_cons (step984 p h) (sat_cons (step997 p h) (sat_cons (step1888 p h) (sat_cons (step999 p h) (sat_cons (step1075 p h) (sat_cons (step1026 p h) (sat_cons (step1043 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1915 : List Lit := [(104, true), (801, false), (810, false), (871, false), (932, false), (114, false), (106, false), (212, true), (214, true), (223, true), (218, true), (153, true), (156, true), (157, true), (161, true), (165, true), (169, true), (159, true), (28, true), (947, false)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.TreeRup.prove_clause [c912, c935, c1008, c1167, c1194, c1777, c996, c1242, c1575, c1914, c1847, c1848, c1911, c226, c994, c1781, c1001, c207, c1025, c1772, c562, c1837, c556, c1769, c200, c1778, c582, c1912, c1766, c975, c195, c1835, c1225, c552, c1838, c1227, c202, c1231, c1771, c1233, c978, c1871, c981, c1283, c984, c1888, c1042, c1074, c1081, c1887, c936, c1288, c1284, c913, c1195, c1872, c896, c1172, c1236, c893, c1150, c1222, c1755, c480] c1915 (by decide) p (sat_cons (step912 p h) (sat_cons (step935 p h) (sat_cons (step1008 p h) (sat_cons (step1167 p h) (sat_cons (step1194 p h) (sat_cons (step1777 p h) (sat_cons (step996 p h) (sat_cons (step1242 p h) (sat_cons (step1575 p h) (sat_cons (step1914 p h) (sat_cons (step1847 p h) (sat_cons (step1848 p h) (sat_cons (step1911 p h) (sat_cons (step226 p h) (sat_cons (step994 p h) (sat_cons (step1781 p h) (sat_cons (step1001 p h) (sat_cons (step207 p h) (sat_cons (step1025 p h) (sat_cons (step1772 p h) (sat_cons (step562 p h) (sat_cons (step1837 p h) (sat_cons (step556 p h) (sat_cons (step1769 p h) (sat_cons (step200 p h) (sat_cons (step1778 p h) (sat_cons (step582 p h) (sat_cons (step1912 p h) (sat_cons (step1766 p h) (sat_cons (step975 p h) (sat_cons (step195 p h) (sat_cons (step1835 p h) (sat_cons (step1225 p h) (sat_cons (step552 p h) (sat_cons (step1838 p h) (sat_cons (step1227 p h) (sat_cons (step202 p h) (sat_cons (step1231 p h) (sat_cons (step1771 p h) (sat_cons (step1233 p h) (sat_cons (step978 p h) (sat_cons (step1871 p h) (sat_cons (step981 p h) (sat_cons (step1283 p h) (sat_cons (step984 p h) (sat_cons (step1888 p h) (sat_cons (step1042 p h) (sat_cons (step1074 p h) (sat_cons (step1081 p h) (sat_cons (step1887 p h) (sat_cons (step936 p h) (sat_cons (step1288 p h) (sat_cons (step1284 p h) (sat_cons (step913 p h) (sat_cons (step1195 p h) (sat_cons (step1872 p h) (sat_cons (step896 p h) (sat_cons (step1172 p h) (sat_cons (step1236 p h) (sat_cons (step893 p h) (sat_cons (step1150 p h) (sat_cons (step1222 p h) (sat_cons (step1755 p h) (sat_cons (step480 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1916 : List Lit := [(790, true), (2, true), (76, false), (55, false), (14, false)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c843, c846, c848, c844, c16, c1727, c1721, c246] c1916 (by decide) p (sat_cons (step843 p h) (sat_cons (step846 p h) (sat_cons (step848 p h) (sat_cons (step844 p h) (sat_cons (step16 p h) (sat_cons (step1727 p h) (sat_cons (step1721 p h) (sat_cons (step246 p h) (sat_nil p)))))))))
def c1917 : List Lit := [(6, false), (60, false), (5, true), (55, false)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c1727, c296] c1917 (by decide) p (sat_cons (step1727 p h) (sat_cons (step296 p h) (sat_nil p)))
def c1918 : List Lit := [(6, false), (60, false), (55, false), (14, false)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c29, c1727, c296] c1918 (by decide) p (sat_cons (step29 p h) (sat_cons (step1727 p h) (sat_cons (step296 p h) (sat_nil p))))
def c1919 : List Lit := [(27, false), (88, false), (28, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c1755, c1756, c1521] c1919 (by decide) p (sat_cons (step1755 p h) (sat_cons (step1756 p h) (sat_cons (step1521 p h) (sat_nil p))))
def c1920 : List Lit := [(21, false), (22, true), (57, false)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c1746, c1748, c1503] c1920 (by decide) p (sat_cons (step1746 p h) (sat_cons (step1748 p h) (sat_cons (step1503 p h) (sat_nil p))))
def c1921 : List Lit := [(19, false), (55, false), (87, false), (28, true)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c1743, c398] c1921 (by decide) p (sat_cons (step1743 p h) (sat_cons (step398 p h) (sat_nil p)))
def c1922 : List Lit := [(834, false), (962, false), (87, false), (28, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c1877, c1888, c1777, c996, c998, c1019, c1028, c1095, c1096, c1887, c1034, c1292, c985, c1870, c969, c1234, c967, c1220, c1762, c1217, c535] c1922 (by decide) p (sat_cons (step1877 p h) (sat_cons (step1888 p h) (sat_cons (step1777 p h) (sat_cons (step996 p h) (sat_cons (step998 p h) (sat_cons (step1019 p h) (sat_cons (step1028 p h) (sat_cons (step1095 p h) (sat_cons (step1096 p h) (sat_cons (step1887 p h) (sat_cons (step1034 p h) (sat_cons (step1292 p h) (sat_cons (step985 p h) (sat_cons (step1870 p h) (sat_cons (step969 p h) (sat_cons (step1234 p h) (sat_cons (step967 p h) (sat_cons (step1220 p h) (sat_cons (step1762 p h) (sat_cons (step1217 p h) (sat_cons (step535 p h) (sat_nil p))))))))))))))))))))))
def c1923 : List Lit := [(19, false), (832, false), (854, false), (962, false), (87, false), (28, true)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c1877, c1888, c1086, c1036, c1777, c996, c998, c1743, c1921, c405, c1002, c1010, c1020, c1025, c1035, c1001, c1085, c994, c1887, c1774, c1775, c1525, c1292, c1243, c1264, c1576, c1584] c1923 (by decide) p (sat_cons (step1877 p h) (sat_cons (step1888 p h) (sat_cons (step1086 p h) (sat_cons (step1036 p h) (sat_cons (step1777 p h) (sat_cons (step996 p h) (sat_cons (step998 p h) (sat_cons (step1743 p h) (sat_cons (step1921 p h) (sat_cons (step405 p h) (sat_cons (step1002 p h) (sat_cons (step1010 p h) (sat_cons (step1020 p h) (sat_cons (step1025 p h) (sat_cons (step1035 p h) (sat_cons (step1001 p h) (sat_cons (step1085 p h) (sat_cons (step994 p h) (sat_cons (step1887 p h) (sat_cons (step1774 p h) (sat_cons (step1775 p h) (sat_cons (step1525 p h) (sat_cons (step1292 p h) (sat_cons (step1243 p h) (sat_cons (step1264 p h) (sat_cons (step1576 p h) (sat_cons (step1584 p h) (sat_nil p))))))))))))))))))))))))))))
end B112E259
