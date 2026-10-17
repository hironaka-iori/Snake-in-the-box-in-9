import B112E121Part0001
namespace B112E121
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1852 : List Lit := [(963, true), (51, false), (59, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c1288, c1285, c491, c1809] c1852 (by decide) p (sat_cons (step1288 p h) (sat_cons (step1285 p h) (sat_cons (step491 p h) (sat_cons (step1809 p h) (sat_nil p)))))
def c1853 : List Lit := [(119, true), (101, true), (1116, true), (247, true)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c933, c1563, c1553, c1554, c874, c1561, c870, c869, c1555, c1723] c1853 (by decide) p (sat_cons (step933 p h) (sat_cons (step1563 p h) (sat_cons (step1553 p h) (sat_cons (step1554 p h) (sat_cons (step874 p h) (sat_cons (step1561 p h) (sat_cons (step870 p h) (sat_cons (step869 p h) (sat_cons (step1555 p h) (sat_cons (step1723 p h) (sat_nil p)))))))))))
def c1854 : List Lit := [(1093, true), (103, true), (100, true), (57, false), (109, true)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c926, c1505, c1507, c1516, c1514, c1506, c1509, c820, c824] c1854 (by decide) p (sat_cons (step926 p h) (sat_cons (step1505 p h) (sat_cons (step1507 p h) (sat_cons (step1516 p h) (sat_cons (step1514 p h) (sat_cons (step1506 p h) (sat_cons (step1509 p h) (sat_cons (step820 p h) (sat_cons (step824 p h) (sat_nil p))))))))))
def c1855 : List Lit := [(47, false), (877, true), (14, true), (13, false), (71, false)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c156, c141, c1105, c1100, c1110] c1855 (by decide) p (sat_cons (step156 p h) (sat_cons (step141 p h) (sat_cons (step1105 p h) (sat_cons (step1100 p h) (sat_cons (step1110 p h) (sat_nil p))))))
def c1856 : List Lit := [(1107, true), (93, false), (92, true)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c930, c1545, c1547, c1542, c1539, c856, c855] c1856 (by decide) p (sat_cons (step930 p h) (sat_cons (step1545 p h) (sat_cons (step1547 p h) (sat_cons (step1542 p h) (sat_cons (step1539 p h) (sat_cons (step856 p h) (sat_cons (step855 p h) (sat_nil p))))))))
def c1857 : List Lit := [(71, false), (77, false), (1044, true), (92, true), (93, false)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c912, c1829, c542, c535] c1857 (by decide) p (sat_cons (step912 p h) (sat_cons (step1829 p h) (sat_cons (step542 p h) (sat_cons (step535 p h) (sat_nil p)))))
def c1858 : List Lit := [(89, false), (92, true), (1080, true), (107, false)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c920, c640, c717, c719, c1492] c1858 (by decide) p (sat_cons (step920 p h) (sat_cons (step640 p h) (sat_cons (step717 p h) (sat_cons (step719 p h) (sat_cons (step1492 p h) (sat_nil p))))))
def c1859 : List Lit := [(1001, true), (980, false), (904, false), (968, false), (13, false), (71, false)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c1345, c1847, c1201, c110, c131, c146, c1086, c1100, c1104, c1094, c1109, c1120] c1859 (by decide) p (sat_cons (step1345 p h) (sat_cons (step1847 p h) (sat_cons (step1201 p h) (sat_cons (step110 p h) (sat_cons (step131 p h) (sat_cons (step146 p h) (sat_cons (step1086 p h) (sat_cons (step1100 p h) (sat_cons (step1104 p h) (sat_cons (step1094 p h) (sat_cons (step1109 p h) (sat_cons (step1120 p h) (sat_nil p)))))))))))))
def c1860 : List Lit := [(119, true), (1116, true), (1121, true), (1105, false), (92, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c930, c1563, c1553, c1554, c1560, c1561, c1572, c1555, c1548, c1539, c854, c875] c1860 (by decide) p (sat_cons (step930 p h) (sat_cons (step1563 p h) (sat_cons (step1553 p h) (sat_cons (step1554 p h) (sat_cons (step1560 p h) (sat_cons (step1561 p h) (sat_cons (step1572 p h) (sat_cons (step1555 p h) (sat_cons (step1548 p h) (sat_cons (step1539 p h) (sat_cons (step854 p h) (sat_cons (step875 p h) (sat_nil p)))))))))))))
def c1861 : List Lit := [(1108, true), (111, false), (119, false), (118, true)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c1542, c1546, c1548, c1544, c1540, c851] c1861 (by decide) p (sat_cons (step1542 p h) (sat_cons (step1546 p h) (sat_cons (step1548 p h) (sat_cons (step1544 p h) (sat_cons (step1540 p h) (sat_cons (step851 p h) (sat_nil p)))))))
def c1862 : List Lit := [(1105, false), (1121, true), (119, true), (92, true)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c1545, c1860, c1570] c1862 (by decide) p (sat_cons (step1545 p h) (sat_cons (step1860 p h) (sat_cons (step1570 p h) (sat_nil p))))
def c1863 : List Lit := [(110, false), (115, false), (87, true), (94, false)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c929, c846, c857] c1863 (by decide) p (sat_cons (step929 p h) (sat_cons (step846 p h) (sat_cons (step857 p h) (sat_nil p))))
def c1864 : List Lit := [(125, false), (1105, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c934, c1543, c1542, c878, c860] c1864 (by decide) p (sat_cons (step934 p h) (sat_cons (step1543 p h) (sat_cons (step1542 p h) (sat_cons (step878 p h) (sat_cons (step860 p h) (sat_nil p))))))
def c1865 : List Lit := [(1079, false), (1098, true), (109, true), (105, true), (98, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c926, c1507, c1510, c1533, c1494, c1499, c1500, c1529, c1495, c1513, c1800, c1504, c822] c1865 (by decide) p (sat_cons (step926 p h) (sat_cons (step1507 p h) (sat_cons (step1510 p h) (sat_cons (step1533 p h) (sat_cons (step1494 p h) (sat_cons (step1499 p h) (sat_cons (step1500 p h) (sat_cons (step1529 p h) (sat_cons (step1495 p h) (sat_cons (step1513 p h) (sat_cons (step1800 p h) (sat_cons (step1504 p h) (sat_cons (step822 p h) (sat_nil p))))))))))))))
def c1866 : List Lit := [(106, false), (96, false), (107, false), (105, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c926, c822, c834] c1866 (by decide) p (sat_cons (step926 p h) (sat_cons (step822 p h) (sat_cons (step834 p h) (sat_nil p))))
def c1867 : List Lit := [(72, true), (71, false), (1001, true), (968, false), (92, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c912, c537, c535, c1847, c1680, c160, c165, c1153, c1138, c1240, c1160, c1146, c1758, c1171, c1770, c1859, c1322] c1867 (by decide) p (sat_cons (step912 p h) (sat_cons (step537 p h) (sat_cons (step535 p h) (sat_cons (step1847 p h) (sat_cons (step1680 p h) (sat_cons (step160 p h) (sat_cons (step165 p h) (sat_cons (step1153 p h) (sat_cons (step1138 p h) (sat_cons (step1240 p h) (sat_cons (step1160 p h) (sat_cons (step1146 p h) (sat_cons (step1758 p h) (sat_cons (step1171 p h) (sat_cons (step1770 p h) (sat_cons (step1859 p h) (sat_cons (step1322 p h) (sat_nil p))))))))))))))))))
def c1868 : List Lit := [(969, true), (951, false), (53, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c1271, c1277, c1306, c1303, c1278, c1288, c1273, c1286, c1852] c1868 (by decide) p (sat_cons (step1271 p h) (sat_cons (step1277 p h) (sat_cons (step1306 p h) (sat_cons (step1303 p h) (sat_cons (step1278 p h) (sat_cons (step1288 p h) (sat_cons (step1273 p h) (sat_cons (step1286 p h) (sat_cons (step1852 p h) (sat_nil p))))))))))
def c1869 : List Lit := [(25, true), (900, true), (61, true), (60, false)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c892, c1163, c1153, c1154, c1161, c1155, c1156, c348, c369, c376] c1869 (by decide) p (sat_cons (step892 p h) (sat_cons (step1163 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step1161 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step348 p h) (sat_cons (step369 p h) (sat_cons (step376 p h) (sat_nil p)))))))))))
def c1870 : List Lit := [(1, true), (876, false), (914, true), (13, true)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c881, c1206, c1125, c1097, c1087, c1088, c1094, c1095, c10, c1120, c1089, c1200, c23, c1166, c1153, c1160] c1870 (by decide) p (sat_cons (step881 p h) (sat_cons (step1206 p h) (sat_cons (step1125 p h) (sat_cons (step1097 p h) (sat_cons (step1087 p h) (sat_cons (step1088 p h) (sat_cons (step1094 p h) (sat_cons (step1095 p h) (sat_cons (step10 p h) (sat_cons (step1120 p h) (sat_cons (step1089 p h) (sat_cons (step1200 p h) (sat_cons (step23 p h) (sat_cons (step1166 p h) (sat_cons (step1153 p h) (sat_cons (step1160 p h) (sat_nil p)))))))))))))))))
def c1871 : List Lit := [(871, false), (877, true), (914, true), (13, true), (14, true)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c880, c1103, c1112, c1109, c1870, c1, c1836, c1110, c1102, c1105, c27] c1871 (by decide) p (sat_cons (step880 p h) (sat_cons (step1103 p h) (sat_cons (step1112 p h) (sat_cons (step1109 p h) (sat_cons (step1870 p h) (sat_cons (step1 p h) (sat_cons (step1836 p h) (sat_cons (step1110 p h) (sat_cons (step1102 p h) (sat_cons (step1105 p h) (sat_cons (step27 p h) (sat_nil p))))))))))))
def c1872 : List Lit := [(877, false), (914, true), (13, false)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c1206, c1116, c1121, c1200, c1094, c1166, c1170, c1086, c1160, c1146, c1153, c1138, c111] c1872 (by decide) p (sat_cons (step1206 p h) (sat_cons (step1116 p h) (sat_cons (step1121 p h) (sat_cons (step1200 p h) (sat_cons (step1094 p h) (sat_cons (step1166 p h) (sat_cons (step1170 p h) (sat_cons (step1086 p h) (sat_cons (step1160 p h) (sat_cons (step1146 p h) (sat_cons (step1153 p h) (sat_cons (step1138 p h) (sat_cons (step111 p h) (sat_nil p))))))))))))))
def c1873 : List Lit := [(863, true), (11, false), (872, true), (13, false)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c1086, c1087, c93, c1836, c1102] c1873 (by decide) p (sat_cons (step1086 p h) (sat_cons (step1087 p h) (sat_cons (step93 p h) (sat_cons (step1836 p h) (sat_cons (step1102 p h) (sat_nil p))))))
def c1874 : List Lit := [(914, true), (13, false), (871, false), (14, true)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1103, c1109, c1872, c1112, c1110, c1105, c1873, c1094, c1120, c1200, c1166, c1170, c1160, c1146, c1153, c1138, c147] c1874 (by decide) p (sat_cons (step1103 p h) (sat_cons (step1109 p h) (sat_cons (step1872 p h) (sat_cons (step1112 p h) (sat_cons (step1110 p h) (sat_cons (step1105 p h) (sat_cons (step1873 p h) (sat_cons (step1094 p h) (sat_cons (step1120 p h) (sat_cons (step1200 p h) (sat_cons (step1166 p h) (sat_cons (step1170 p h) (sat_cons (step1160 p h) (sat_cons (step1146 p h) (sat_cons (step1153 p h) (sat_cons (step1138 p h) (sat_cons (step147 p h) (sat_nil p))))))))))))))))))
def c1875 : List Lit := [(980, true), (13, false), (10, false), (968, false), (53, true)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c1778, c1322, c1868, c1770, c1268, c1758, c139, c1240] c1875 (by decide) p (sat_cons (step1778 p h) (sat_cons (step1322 p h) (sat_cons (step1868 p h) (sat_cons (step1770 p h) (sat_cons (step1268 p h) (sat_cons (step1758 p h) (sat_cons (step139 p h) (sat_cons (step1240 p h) (sat_nil p)))))))))
def c1876 : List Lit := [(47, false), (904, true), (13, false), (10, false), (92, true)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c902, c424, c1679, c134, c1153, c1138, c1160, c1146, c1171] c1876 (by decide) p (sat_cons (step902 p h) (sat_cons (step424 p h) (sat_cons (step1679 p h) (sat_cons (step134 p h) (sat_cons (step1153 p h) (sat_cons (step1138 p h) (sat_cons (step1160 p h) (sat_cons (step1146 p h) (sat_cons (step1171 p h) (sat_nil p))))))))))
def c1877 : List Lit := [(899, false), (1, true), (13, false), (10, false), (875, false), (914, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1087, c1094, c1119, c1194, c1166, c1171, c1200, c1146, c1124, c1138, c1097, c95, c1088] c1877 (by decide) p (sat_cons (step1087 p h) (sat_cons (step1094 p h) (sat_cons (step1119 p h) (sat_cons (step1194 p h) (sat_cons (step1166 p h) (sat_cons (step1171 p h) (sat_cons (step1200 p h) (sat_cons (step1146 p h) (sat_cons (step1124 p h) (sat_cons (step1138 p h) (sat_cons (step1097 p h) (sat_cons (step95 p h) (sat_cons (step1088 p h) (sat_nil p))))))))))))))
def c1878 : List Lit := [(13, false), (871, true), (14, false), (914, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c1101, c1836, c1100, c128, c121, c1153, c1104, c1160, c1106, c1877] c1878 (by decide) p (sat_cons (step1101 p h) (sat_cons (step1836 p h) (sat_cons (step1100 p h) (sat_cons (step128 p h) (sat_cons (step121 p h) (sat_cons (step1153 p h) (sat_cons (step1104 p h) (sat_cons (step1160 p h) (sat_cons (step1106 p h) (sat_cons (step1877 p h) (sat_nil p)))))))))))
def c1879 : List Lit := [(899, true), (14, false)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1160, c1791] c1879 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1160 p h) (sat_cons (step1791 p h) (sat_nil p))))
def c1880 : List Lit := [(880, true), (871, false), (10, false)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c880, c1108, c1115, c1119, c1109, c1094, c1104, c1087, c1, c27] c1880 (by decide) p (sat_cons (step880 p h) (sat_cons (step1108 p h) (sat_cons (step1115 p h) (sat_cons (step1119 p h) (sat_cons (step1109 p h) (sat_cons (step1094 p h) (sat_cons (step1104 p h) (sat_cons (step1087 p h) (sat_cons (step1 p h) (sat_cons (step27 p h) (sat_nil p)))))))))))
def c1881 : List Lit := [(872, false), (13, true), (899, false), (914, true)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c880, c1166, c1200, c1116, c1111, c1112, c1115, c1870, c1104, c1194, c1, c31, c1171, c1139, c1146] c1881 (by decide) p (sat_cons (step880 p h) (sat_cons (step1166 p h) (sat_cons (step1200 p h) (sat_cons (step1116 p h) (sat_cons (step1111 p h) (sat_cons (step1112 p h) (sat_cons (step1115 p h) (sat_cons (step1870 p h) (sat_cons (step1104 p h) (sat_cons (step1194 p h) (sat_cons (step1 p h) (sat_cons (step31 p h) (sat_cons (step1171 p h) (sat_cons (step1139 p h) (sat_cons (step1146 p h) (sat_nil p))))))))))))))))
def c1882 : List Lit := [(1, true), (871, false), (13, false), (881, true), (14, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c1108, c1124, c1097, c1087, c1088, c1094, c100, c1120, c1104, c1109] c1882 (by decide) p (sat_cons (step1108 p h) (sat_cons (step1124 p h) (sat_cons (step1097 p h) (sat_cons (step1087 p h) (sat_cons (step1088 p h) (sat_cons (step1094 p h) (sat_cons (step100 p h) (sat_cons (step1120 p h) (sat_cons (step1104 p h) (sat_cons (step1109 p h) (sat_nil p)))))))))))
def c1883 : List Lit := [(872, false), (13, false), (881, true), (14, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1116, c1111, c1112, c1120, c1104, c1094, c100, c1086] c1883 (by decide) p (sat_cons (step1116 p h) (sat_cons (step1111 p h) (sat_cons (step1112 p h) (sat_cons (step1120 p h) (sat_cons (step1104 p h) (sat_cons (step1094 p h) (sat_cons (step100 p h) (sat_cons (step1086 p h) (sat_nil p)))))))))
def c1884 : List Lit := [(13, false), (888, true), (881, true), (14, false), (9, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c880, c1101, c1883, c1882, c1102, c1, c127, c28, c1140] c1884 (by decide) p (sat_cons (step880 p h) (sat_cons (step1101 p h) (sat_cons (step1883 p h) (sat_cons (step1882 p h) (sat_cons (step1102 p h) (sat_cons (step1 p h) (sat_cons (step127 p h) (sat_cons (step28 p h) (sat_cons (step1140 p h) (sat_nil p))))))))))
def c1885 : List Lit := [(14, false), (9, true), (914, true)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c887, c885, c1101, c1108, c1114, c1189, c1879, c1166, c1176, c1200, c1149, c1884, c1881, c1102, c1880, c1194, c1171, c1144, c1146, c1141, c1142, c1138, c1139, c325, c194, c179, c73, c87, c28, c1104, c1870, c1109] c1885 (by decide) p (sat_cons (step887 p h) (sat_cons (step885 p h) (sat_cons (step1101 p h) (sat_cons (step1108 p h) (sat_cons (step1114 p h) (sat_cons (step1189 p h) (sat_cons (step1879 p h) (sat_cons (step1166 p h) (sat_cons (step1176 p h) (sat_cons (step1200 p h) (sat_cons (step1149 p h) (sat_cons (step1884 p h) (sat_cons (step1881 p h) (sat_cons (step1102 p h) (sat_cons (step1880 p h) (sat_cons (step1194 p h) (sat_cons (step1171 p h) (sat_cons (step1144 p h) (sat_cons (step1146 p h) (sat_cons (step1141 p h) (sat_cons (step1142 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step325 p h) (sat_cons (step194 p h) (sat_cons (step179 p h) (sat_cons (step73 p h) (sat_cons (step87 p h) (sat_cons (step28 p h) (sat_cons (step1104 p h) (sat_cons (step1870 p h) (sat_cons (step1109 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1886 : List Lit := [(9, true), (914, true)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c881, c1206, c1101, c1885, c1874, c1871, c1116, c1121, c1200, c1092, c1094, c1166, c1089, c1086, c1160, c10, c1153, c23] c1886 (by decide) p (sat_cons (step881 p h) (sat_cons (step1206 p h) (sat_cons (step1101 p h) (sat_cons (step1885 p h) (sat_cons (step1874 p h) (sat_cons (step1871 p h) (sat_cons (step1116 p h) (sat_cons (step1121 p h) (sat_cons (step1200 p h) (sat_cons (step1092 p h) (sat_cons (step1094 p h) (sat_cons (step1166 p h) (sat_cons (step1089 p h) (sat_cons (step1086 p h) (sat_cons (step1160 p h) (sat_cons (step10 p h) (sat_cons (step1153 p h) (sat_cons (step23 p h) (sat_nil p)))))))))))))))))))
def c1887 : List Lit := [(13, true), (14, true), (914, true)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c885, c1886, c1836, c1087, c1094, c1103, c1106, c1119, c1194, c1167, c1206, c1121, c1871, c1870, c1100, c1107, c1105, c37, c73, c72, c1670, c1156, c1158, c1161, c1171, c1153, c1144, c254, c1142] c1887 (by decide) p (sat_cons (step885 p h) (sat_cons (step1886 p h) (sat_cons (step1836 p h) (sat_cons (step1087 p h) (sat_cons (step1094 p h) (sat_cons (step1103 p h) (sat_cons (step1106 p h) (sat_cons (step1119 p h) (sat_cons (step1194 p h) (sat_cons (step1167 p h) (sat_cons (step1206 p h) (sat_cons (step1121 p h) (sat_cons (step1871 p h) (sat_cons (step1870 p h) (sat_cons (step1100 p h) (sat_cons (step1107 p h) (sat_cons (step1105 p h) (sat_cons (step37 p h) (sat_cons (step73 p h) (sat_cons (step72 p h) (sat_cons (step1670 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1161 p h) (sat_cons (step1171 p h) (sat_cons (step1153 p h) (sat_cons (step1144 p h) (sat_cons (step254 p h) (sat_cons (step1142 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1888 : List Lit := [(899, true), (9, false)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c890, c1158, c1160, c1155, c1156, c1152, c348, c337, c338, c1666] c1888 (by decide) p (sat_cons (step890 p h) (sat_cons (step1158 p h) (sat_cons (step1160 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1152 p h) (sat_cons (step348 p h) (sat_cons (step337 p h) (sat_cons (step338 p h) (sat_cons (step1666 p h) (sat_nil p)))))))))))
def c1889 : List Lit := [(10, false), (25, false), (13, false), (874, true)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c128, c123, c1105] c1889 (by decide) p (sat_cons (step128 p h) (sat_cons (step123 p h) (sat_cons (step1105 p h) (sat_nil p))))
def c1890 : List Lit := [(871, false), (13, false), (914, true)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c1886, c1888, c1166, c1200, c1836, c1882, c1874] c1890 (by decide) p (sat_cons (step1886 p h) (sat_cons (step1888 p h) (sat_cons (step1166 p h) (sat_cons (step1200 p h) (sat_cons (step1836 p h) (sat_cons (step1882 p h) (sat_cons (step1874 p h) (sat_nil p))))))))
def c1891 : List Lit := [(13, false), (914, true)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c1886, c1888, c1836, c1890, c1100, c1878, c1877, c1103, c1106] c1891 (by decide) p (sat_cons (step1886 p h) (sat_cons (step1888 p h) (sat_cons (step1836 p h) (sat_cons (step1890 p h) (sat_cons (step1100 p h) (sat_cons (step1878 p h) (sat_cons (step1877 p h) (sat_cons (step1103 p h) (sat_cons (step1106 p h) (sat_nil p))))))))))
def c1892 : List Lit := [(11, false), (10, false), (914, true)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c887, c886, c885, c1891, c1887, c1886, c1836, c1087, c1094, c1118, c1189, c1168, c81, c37, c179, c79, c73, c72, c311, c1670, c1153, c1156, c1162, c1161, c1157, c1172, c329, c1144, c1141] c1892 (by decide) p (sat_cons (step887 p h) (sat_cons (step886 p h) (sat_cons (step885 p h) (sat_cons (step1891 p h) (sat_cons (step1887 p h) (sat_cons (step1886 p h) (sat_cons (step1836 p h) (sat_cons (step1087 p h) (sat_cons (step1094 p h) (sat_cons (step1118 p h) (sat_cons (step1189 p h) (sat_cons (step1168 p h) (sat_cons (step81 p h) (sat_cons (step37 p h) (sat_cons (step179 p h) (sat_cons (step79 p h) (sat_cons (step73 p h) (sat_cons (step72 p h) (sat_cons (step311 p h) (sat_cons (step1670 p h) (sat_cons (step1153 p h) (sat_cons (step1156 p h) (sat_cons (step1162 p h) (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step1172 p h) (sat_cons (step329 p h) (sat_cons (step1144 p h) (sat_cons (step1141 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1893 : List Lit := [(889, true), (914, true)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c887, c1891, c1887, c1886, c1141, c1142, c84, c325, c179] c1893 (by decide) p (sat_cons (step887 p h) (sat_cons (step1891 p h) (sat_cons (step1887 p h) (sat_cons (step1886 p h) (sat_cons (step1141 p h) (sat_cons (step1142 p h) (sat_cons (step84 p h) (sat_cons (step325 p h) (sat_cons (step179 p h) (sat_nil p))))))))))
def c1894 : List Lit := [(914, true)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c1886, c1836, c1087, c1094, c1888, c1893, c1144, c1171, c1194, c1119, c1106, c1108, c1104, c1100, c1892] c1894 (by decide) p (sat_cons (step1886 p h) (sat_cons (step1836 p h) (sat_cons (step1087 p h) (sat_cons (step1094 p h) (sat_cons (step1888 p h) (sat_cons (step1893 p h) (sat_cons (step1144 p h) (sat_cons (step1171 p h) (sat_cons (step1194 p h) (sat_cons (step1119 p h) (sat_cons (step1106 p h) (sat_cons (step1108 p h) (sat_cons (step1104 p h) (sat_cons (step1100 p h) (sat_cons (step1892 p h) (sat_nil p))))))))))))))))
def c1895 : List Lit := [(887, true), (10, false), (9, false), (13, true)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c885, c1138, c1139, c38, c194, c73] c1895 (by decide) p (sat_cons (step885 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step38 p h) (sat_cons (step194 p h) (sat_cons (step73 p h) (sat_nil p)))))))
def c1896 : List Lit := [(968, true), (955, false), (92, true)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1849, c1299, c1272, c1852] c1896 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1849 p h) (sat_cons (step1299 p h) (sat_cons (step1272 p h) (sat_cons (step1852 p h) (sat_nil p))))))
def c1897 : List Lit := [(887, false), (875, false), (1002, true), (24, false), (889, false), (9, false), (14, false), (968, false), (13, true)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c887, c890, c1777, c1356, c1836, c1087, c1094, c1119, c1197, c84, c179, c329, c1155, c328, c325, c1790, c1147, c1196, c1203, c1178, c1351, c1124, c1164, c1322, c1095, c1154, c1770, c1090, c215, c339, c1758, c187, c1239] c1897 (by decide) p (sat_cons (step887 p h) (sat_cons (step890 p h) (sat_cons (step1777 p h) (sat_cons (step1356 p h) (sat_cons (step1836 p h) (sat_cons (step1087 p h) (sat_cons (step1094 p h) (sat_cons (step1119 p h) (sat_cons (step1197 p h) (sat_cons (step84 p h) (sat_cons (step179 p h) (sat_cons (step329 p h) (sat_cons (step1155 p h) (sat_cons (step328 p h) (sat_cons (step325 p h) (sat_cons (step1790 p h) (sat_cons (step1147 p h) (sat_cons (step1196 p h) (sat_cons (step1203 p h) (sat_cons (step1178 p h) (sat_cons (step1351 p h) (sat_cons (step1124 p h) (sat_cons (step1164 p h) (sat_cons (step1322 p h) (sat_cons (step1095 p h) (sat_cons (step1154 p h) (sat_cons (step1770 p h) (sat_cons (step1090 p h) (sat_cons (step215 p h) (sat_cons (step339 p h) (sat_cons (step1758 p h) (sat_cons (step187 p h) (sat_cons (step1239 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c1898 : List Lit := [(71, false), (14, false), (13, true), (77, false), (92, true)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c912, c539, c537] c1898 (by decide) p (sat_cons (step912 p h) (sat_cons (step539 p h) (sat_cons (step537 p h) (sat_nil p))))
def c1899 : List Lit := [(897, true), (887, true), (13, true)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c888, c1139, c1138, c1155, c1156, c356, c197, c205] c1899 (by decide) p (sat_cons (step888 p h) (sat_cons (step1139 p h) (sat_cons (step1138 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step356 p h) (sat_cons (step197 p h) (sat_cons (step205 p h) (sat_nil p)))))))))
def c1900 : List Lit := [(30, true), (887, true), (13, true)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c888, c1139, c1138, c204, c205, c1682] c1900 (by decide) p (sat_cons (step888 p h) (sat_cons (step1139 p h) (sat_cons (step1138 p h) (sat_cons (step204 p h) (sat_cons (step205 p h) (sat_cons (step1682 p h) (sat_nil p)))))))
def c1901 : List Lit := [(19, false), (25, false), (43, false), (15, false), (13, true)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c888, c353, c204, c205, c1682] c1901 (by decide) p (sat_cons (step888 p h) (sat_cons (step353 p h) (sat_cons (step204 p h) (sat_cons (step205 p h) (sat_cons (step1682 p h) (sat_nil p))))))
def c1902 : List Lit := [(8, false), (876, true), (15, false), (9, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c38, c41, c1100, c1104, c1109] c1902 (by decide) p (sat_cons (step38 p h) (sat_cons (step41 p h) (sat_cons (step1100 p h) (sat_cons (step1104 p h) (sat_cons (step1109 p h) (sat_nil p))))))
def c1903 : List Lit := [(69, false), (8, false), (9, false), (73, true), (87, true)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c911, c517, c1659] c1903 (by decide) p (sat_cons (step911 p h) (sat_cons (step517 p h) (sat_cons (step1659 p h) (sat_nil p))))
def c1904 : List Lit := [(889, true), (26, false), (14, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1142, c325] c1904 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1142 p h) (sat_cons (step325 p h) (sat_nil p))))
def c1905 : List Lit := [(1, false), (8, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c880, c1] c1905 (by decide) p (sat_cons (step880 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1906 : List Lit := [(1, false), (2, true)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c880, c2] c1906 (by decide) p (sat_cons (step880 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1907 : List Lit := [(33, true), (3, false), (13, true)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c881, c8] c1907 (by decide) p (sat_cons (step881 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1908 : List Lit := [(7, true), (33, true), (3, false)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c881, c9] c1908 (by decide) p (sat_cons (step881 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1909 : List Lit := [(3, false), (7, true), (13, true)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c881, c10] c1909 (by decide) p (sat_cons (step881 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1910 : List Lit := [(6, true), (4, false), (20, true)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c882, c12] c1910 (by decide) p (sat_cons (step882 p h) (sat_cons (step12 p h) (sat_nil p)))
def c1911 : List Lit := [(2, true), (4, false), (20, true)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c882, c13] c1911 (by decide) p (sat_cons (step882 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1912 : List Lit := [(6, true), (4, false), (2, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c882, c14] c1912 (by decide) p (sat_cons (step882 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1913 : List Lit := [(7, true), (21, true), (5, false)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c883, c16] c1913 (by decide) p (sat_cons (step883 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1914 : List Lit := [(6, true), (21, true), (5, false)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c883, c17] c1914 (by decide) p (sat_cons (step883 p h) (sat_cons (step17 p h) (sat_nil p)))
def c1915 : List Lit := [(6, true), (7, true), (5, false)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c883, c18] c1915 (by decide) p (sat_cons (step883 p h) (sat_cons (step18 p h) (sat_nil p)))
end B112E121
