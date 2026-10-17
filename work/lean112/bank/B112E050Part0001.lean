import B112E050Part0000
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1880 : List Lit := [(1731, true), (85, false), (1653, true)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c881, c883, c1419, c1420, c364, c358, c366, c367, c350, c1774, c1251] c1880 (by decide) p (sat_cons (step881 p h) (sat_cons (step883 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step364 p h) (sat_cons (step358 p h) (sat_cons (step366 p h) (sat_cons (step367 p h) (sat_cons (step350 p h) (sat_cons (step1774 p h) (sat_cons (step1251 p h) (sat_nil p))))))))))))
def c1881 : List Lit := [(1634, true)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c864, c1214, c1218, c1206, c1208, c1192, c1204, c1200, c1201, c1190, c102, c151, c133] c1881 (by decide) p (sat_cons (step864 p h) (sat_cons (step1214 p h) (sat_cons (step1218 p h) (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step1192 p h) (sat_cons (step1204 p h) (sat_cons (step1200 p h) (sat_cons (step1201 p h) (sat_cons (step1190 p h) (sat_cons (step102 p h) (sat_cons (step151 p h) (sat_cons (step133 p h) (sat_nil p))))))))))))))
def c1882 : List Lit := [(1666, true)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c1881, c1283] c1882 (by decide) p (sat_cons (step1881 p h) (sat_cons (step1283 p h) (sat_nil p)))
def c1883 : List Lit := [(1572, true)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c849, c1115, c1858, c1855, c1104, c1107, c1108, c1098, c23, c20] c1883 (by decide) p (sat_cons (step849 p h) (sat_cons (step1115 p h) (sat_cons (step1858 p h) (sat_cons (step1855 p h) (sat_cons (step1104 p h) (sat_cons (step1107 p h) (sat_cons (step1108 p h) (sat_cons (step1098 p h) (sat_cons (step23 p h) (sat_cons (step20 p h) (sat_nil p)))))))))))
def c1884 : List Lit := [(1605, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c1883, c1874] c1884 (by decide) p (sat_cons (step1883 p h) (sat_cons (step1874 p h) (sat_nil p)))
def c1885 : List Lit := [(1686, true)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1882, c1317] c1885 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1882 p h) (sat_cons (step1317 p h) (sat_nil p))))
def c1886 : List Lit := [(1860, false)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c1885, c1748, c1737] c1886 (by decide) p (sat_cons (step1885 p h) (sat_cons (step1748 p h) (sat_cons (step1737 p h) (sat_nil p))))
def c1887 : List Lit := [(1595, true), (87, false)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c853, c1867, c1154, c1141, c1143, c1132, c1139, c1135, c1862, c70, c29, c34] c1887 (by decide) p (sat_cons (step853 p h) (sat_cons (step1867 p h) (sat_cons (step1154 p h) (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1132 p h) (sat_cons (step1139 p h) (sat_cons (step1135 p h) (sat_cons (step1862 p h) (sat_cons (step70 p h) (sat_cons (step29 p h) (sat_cons (step34 p h) (sat_nil p)))))))))))))
def c1888 : List Lit := [(16, false), (1590, true), (87, false)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c856, c1143, c1135, c1141, c1139, c29, c70, c68] c1888 (by decide) p (sat_cons (step856 p h) (sat_cons (step1143 p h) (sat_cons (step1135 p h) (sat_cons (step1141 p h) (sat_cons (step1139 p h) (sat_cons (step29 p h) (sat_cons (step70 p h) (sat_cons (step68 p h) (sat_nil p)))))))))
def c1889 : List Lit := [(1636, true), (1619, false)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c860, c1197, c1226, c1223, c1198, c1206, c1208, c1190, c1204, c1200, c1201, c102, c151, c108] c1889 (by decide) p (sat_cons (step860 p h) (sat_cons (step1197 p h) (sat_cons (step1226 p h) (sat_cons (step1223 p h) (sat_cons (step1198 p h) (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step1190 p h) (sat_cons (step1204 p h) (sat_cons (step1200 p h) (sat_cons (step1201 p h) (sat_cons (step102 p h) (sat_cons (step151 p h) (sat_cons (step108 p h) (sat_nil p)))))))))))))))
def c1890 : List Lit := [(10, false), (1630, true)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c849, c1208, c1200, c1206, c1203, c22, c165] c1890 (by decide) p (sat_cons (step849 p h) (sat_cons (step1208 p h) (sat_cons (step1200 p h) (sat_cons (step1206 p h) (sat_cons (step1203 p h) (sat_cons (step22 p h) (sat_cons (step165 p h) (sat_nil p))))))))
def c1891 : List Lit := [(36, false), (46, false), (39, false), (21, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c861, c115, c118, c109] c1891 (by decide) p (sat_cons (step861 p h) (sat_cons (step115 p h) (sat_cons (step118 p h) (sat_cons (step109 p h) (sat_nil p)))))
def c1892 : List Lit := [(1773, true), (102, false), (27, false)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1522, c572] c1892 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step572 p h) (sat_nil p))))
def c1893 : List Lit := [(91, true), (1744, true), (87, false)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c886, c1444, c1433, c1435, c1442, c1436, c1437, c485, c369, c447] c1893 (by decide) p (sat_cons (step886 p h) (sat_cons (step1444 p h) (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1442 p h) (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step485 p h) (sat_cons (step369 p h) (sat_cons (step447 p h) (sat_nil p)))))))))))
def c1894 : List Lit := [(1743, true), (87, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c886, c1439, c1441, c1436, c1437, c1434, c485, c369, c447] c1894 (by decide) p (sat_cons (step886 p h) (sat_cons (step1439 p h) (sat_cons (step1441 p h) (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step1434 p h) (sat_cons (step485 p h) (sat_cons (step369 p h) (sat_cons (step447 p h) (sat_nil p))))))))))
def c1895 : List Lit := [(7, false), (1721, true), (80, false), (85, false)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c318, c316, c313, c1388, c1384, c1393] c1895 (by decide) p (sat_cons (step318 p h) (sat_cons (step316 p h) (sat_cons (step313 p h) (sat_cons (step1388 p h) (sat_cons (step1384 p h) (sat_cons (step1393 p h) (sat_nil p)))))))
def c1896 : List Lit := [(1573, true), (1556, false)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c849, c1102, c1859, c1118, c1105, c1855, c1098, c1107, c1108, c23, c20] c1896 (by decide) p (sat_cons (step849 p h) (sat_cons (step1102 p h) (sat_cons (step1859 p h) (sat_cons (step1118 p h) (sat_cons (step1105 p h) (sat_cons (step1855 p h) (sat_cons (step1098 p h) (sat_cons (step1107 p h) (sat_cons (step1108 p h) (sat_cons (step23 p h) (sat_cons (step20 p h) (sat_nil p))))))))))))
def c1897 : List Lit := [(1660, true), (67, true), (65, false), (66, false), (62, true), (54, true)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c874, c1250, c1252, c1235, c1238, c1270, c1266, c1239, c1253, c1255, c1237, c1251, c1247, c203, c238, c244] c1897 (by decide) p (sat_cons (step874 p h) (sat_cons (step1250 p h) (sat_cons (step1252 p h) (sat_cons (step1235 p h) (sat_cons (step1238 p h) (sat_cons (step1270 p h) (sat_cons (step1266 p h) (sat_cons (step1239 p h) (sat_cons (step1253 p h) (sat_cons (step1255 p h) (sat_cons (step1237 p h) (sat_cons (step1251 p h) (sat_cons (step1247 p h) (sat_cons (step203 p h) (sat_cons (step238 p h) (sat_cons (step244 p h) (sat_nil p)))))))))))))))))
def c1898 : List Lit := [(1596, true), (1580, false), (87, false)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c1864, c1159, c1155, c1133, c1888, c1862] c1898 (by decide) p (sat_cons (step1864 p h) (sat_cons (step1159 p h) (sat_cons (step1155 p h) (sat_cons (step1133 p h) (sat_cons (step1888 p h) (sat_cons (step1862 p h) (sat_nil p)))))))
def c1899 : List Lit := [(63, false), (1732, true), (65, false), (66, false), (73, false)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c873, c238, c233, c347, c348, c1421] c1899 (by decide) p (sat_cons (step873 p h) (sat_cons (step238 p h) (sat_cons (step233 p h) (sat_cons (step347 p h) (sat_cons (step348 p h) (sat_cons (step1421 p h) (sat_nil p)))))))
def c1900 : List Lit := [(72, false), (1718, true), (80, false), (85, false)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c332, c334, c1388] c1900 (by decide) p (sat_cons (step332 p h) (sat_cons (step334 p h) (sat_cons (step1388 p h) (sat_nil p))))
def c1901 : List Lit := [(1655, true), (1732, true), (69, false), (73, false), (62, true)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c878, c1250, c1253, c1255, c1251, c1247, c294, c285, c347, c348, c1421] c1901 (by decide) p (sat_cons (step878 p h) (sat_cons (step1250 p h) (sat_cons (step1253 p h) (sat_cons (step1255 p h) (sat_cons (step1251 p h) (sat_cons (step1247 p h) (sat_cons (step294 p h) (sat_cons (step285 p h) (sat_cons (step347 p h) (sat_cons (step348 p h) (sat_cons (step1421 p h) (sat_nil p))))))))))))
def c1902 : List Lit := [(1832, true), (1799, false), (103, true), (96, true), (94, true), (1782, false), (1774, false), (123, true)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c892, c1584, c1598, c1607, c1519, c1528, c1533, c1542, c1563, c1666, c1661, c1564, c1568, c1608, c1545, c1531, c1602, c1599, c1534, c1520, c1586, c1590, c1592, c830, c612, c670, c1587] c1902 (by decide) p (sat_cons (step892 p h) (sat_cons (step1584 p h) (sat_cons (step1598 p h) (sat_cons (step1607 p h) (sat_cons (step1519 p h) (sat_cons (step1528 p h) (sat_cons (step1533 p h) (sat_cons (step1542 p h) (sat_cons (step1563 p h) (sat_cons (step1666 p h) (sat_cons (step1661 p h) (sat_cons (step1564 p h) (sat_cons (step1568 p h) (sat_cons (step1608 p h) (sat_cons (step1545 p h) (sat_cons (step1531 p h) (sat_cons (step1602 p h) (sat_cons (step1599 p h) (sat_cons (step1534 p h) (sat_cons (step1520 p h) (sat_cons (step1586 p h) (sat_cons (step1590 p h) (sat_cons (step1592 p h) (sat_cons (step830 p h) (sat_cons (step612 p h) (sat_cons (step670 p h) (sat_cons (step1587 p h) (sat_nil p))))))))))))))))))))))))))))
def c1903 : List Lit := [(1717, true), (1709, true)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c880, c1373, c1372, c1386, c1387, c298, c275, c305] c1903 (by decide) p (sat_cons (step880 p h) (sat_cons (step1373 p h) (sat_cons (step1372 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step298 p h) (sat_cons (step275 p h) (sat_cons (step305 p h) (sat_nil p)))))))))
def c1904 : List Lit := [(1618, false), (7, false), (1635, true), (27, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c860, c1222, c1194, c1195, c1219, c1190, c1206, c1208, c135, c108, c1204, c1201, c102] c1904 (by decide) p (sat_cons (step860 p h) (sat_cons (step1222 p h) (sat_cons (step1194 p h) (sat_cons (step1195 p h) (sat_cons (step1219 p h) (sat_cons (step1190 p h) (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step135 p h) (sat_cons (step108 p h) (sat_cons (step1204 p h) (sat_cons (step1201 p h) (sat_cons (step102 p h) (sat_nil p))))))))))))))
def c1905 : List Lit := [(67, true), (64, true), (65, false), (66, false), (56, false), (62, true), (1660, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c874, c1897, c244, c206] c1905 (by decide) p (sat_cons (step874 p h) (sat_cons (step1897 p h) (sat_cons (step244 p h) (sat_cons (step206 p h) (sat_nil p)))))
def c1906 : List Lit := [(1717, true), (74, false), (83, true), (69, false)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c880, c1823, c1822, c1097, c1386, c1387, c298, c305, c303, c275, c315, c289, c1820, c1016, c913, c1019, c916, c1026, c917, c1028, c919, c1047, c956, c1091, c1007, c1095] c1906 (by decide) p (sat_cons (step880 p h) (sat_cons (step1823 p h) (sat_cons (step1822 p h) (sat_cons (step1097 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step298 p h) (sat_cons (step305 p h) (sat_cons (step303 p h) (sat_cons (step275 p h) (sat_cons (step315 p h) (sat_cons (step289 p h) (sat_cons (step1820 p h) (sat_cons (step1016 p h) (sat_cons (step913 p h) (sat_cons (step1019 p h) (sat_cons (step916 p h) (sat_cons (step1026 p h) (sat_cons (step917 p h) (sat_cons (step1028 p h) (sat_cons (step919 p h) (sat_cons (step1047 p h) (sat_cons (step956 p h) (sat_cons (step1091 p h) (sat_cons (step1007 p h) (sat_cons (step1095 p h) (sat_nil p)))))))))))))))))))))))))))
def c1907 : List Lit := [(57, false), (56, false), (1645, true), (65, false)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c206, c203, c1237] c1907 (by decide) p (sat_cons (step206 p h) (sat_cons (step203 p h) (sat_cons (step1237 p h) (sat_nil p))))
def c1908 : List Lit := [(1689, true), (1659, false)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c1881, c1884, c1883, c858, c1285, c1320, c1329, c1291, c1875, c1169, c1896, c1867, c1099, c1141, c1143, c1138, c1139, c1136, c79, c1904, c81, c1187] c1908 (by decide) p (sat_cons (step1881 p h) (sat_cons (step1884 p h) (sat_cons (step1883 p h) (sat_cons (step858 p h) (sat_cons (step1285 p h) (sat_cons (step1320 p h) (sat_cons (step1329 p h) (sat_cons (step1291 p h) (sat_cons (step1875 p h) (sat_cons (step1169 p h) (sat_cons (step1896 p h) (sat_cons (step1867 p h) (sat_cons (step1099 p h) (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1136 p h) (sat_cons (step79 p h) (sat_cons (step1904 p h) (sat_cons (step81 p h) (sat_cons (step1187 p h) (sat_nil p)))))))))))))))))))))))
def c1909 : List Lit := [(1741, true), (51, false), (57, true), (54, false)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c869, c1436, c1437, c464, c191, c187] c1909 (by decide) p (sat_cons (step869 p h) (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step464 p h) (sat_cons (step191 p h) (sat_cons (step187 p h) (sat_nil p)))))))
def c1910 : List Lit := [(1771, true), (56, false), (75, true), (1707, true)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c870, c1369, c1370, c237, c1518, c1519, c211, c209, c196] c1910 (by decide) p (sat_cons (step870 p h) (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step237 p h) (sat_cons (step1518 p h) (sat_cons (step1519 p h) (sat_cons (step211 p h) (sat_cons (step209 p h) (sat_cons (step196 p h) (sat_nil p))))))))))
def c1911 : List Lit := [(97, false), (1790, true), (1771, false), (64, true), (56, false), (66, false)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c875, c211, c249, c656, c658, c657, c1521, c1536, c1532, c1527, c1541, c1557] c1911 (by decide) p (sat_cons (step875 p h) (sat_cons (step211 p h) (sat_cons (step249 p h) (sat_cons (step656 p h) (sat_cons (step658 p h) (sat_cons (step657 p h) (sat_cons (step1521 p h) (sat_cons (step1536 p h) (sat_cons (step1532 p h) (sat_cons (step1527 p h) (sat_cons (step1541 p h) (sat_cons (step1557 p h) (sat_nil p)))))))))))))
def c1912 : List Lit := [(1662, false), (1692, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1881, c1883, c858, c1323, c1288, c1294, c1332, c1875, c1169, c1896, c1867, c1099, c1141, c1143, c1138, c1139, c1136, c79, c1904, c81, c1187] c1912 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1881 p h) (sat_cons (step1883 p h) (sat_cons (step858 p h) (sat_cons (step1323 p h) (sat_cons (step1288 p h) (sat_cons (step1294 p h) (sat_cons (step1332 p h) (sat_cons (step1875 p h) (sat_cons (step1169 p h) (sat_cons (step1896 p h) (sat_cons (step1867 p h) (sat_cons (step1099 p h) (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1136 p h) (sat_cons (step79 p h) (sat_cons (step1904 p h) (sat_cons (step81 p h) (sat_cons (step1187 p h) (sat_nil p)))))))))))))))))))))))
def c1913 : List Lit := [(28, false), (21, false), (30, false)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c858, c79, c81] c1913 (by decide) p (sat_cons (step858 p h) (sat_cons (step79 p h) (sat_cons (step81 p h) (sat_nil p))))
def c1914 : List Lit := [(28, true), (33, false), (1596, true)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c853, c1868, c1142, c1138, c1141, c1144, c1155, c1135, c1132, c1862, c28, c34, c1140, c70] c1914 (by decide) p (sat_cons (step853 p h) (sat_cons (step1868 p h) (sat_cons (step1142 p h) (sat_cons (step1138 p h) (sat_cons (step1141 p h) (sat_cons (step1144 p h) (sat_cons (step1155 p h) (sat_cons (step1135 p h) (sat_cons (step1132 p h) (sat_cons (step1862 p h) (sat_cons (step28 p h) (sat_cons (step34 p h) (sat_cons (step1140 p h) (sat_cons (step70 p h) (sat_nil p)))))))))))))))
def c1915 : List Lit := [(1618, true), (1596, true)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c853, c1868, c1146, c1186, c1187, c1914, c1913, c1136, c1137, c1143, c1144, c1155, c1139, c1132, c1862, c70, c28, c34] c1915 (by decide) p (sat_cons (step853 p h) (sat_cons (step1868 p h) (sat_cons (step1146 p h) (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step1914 p h) (sat_cons (step1913 p h) (sat_cons (step1136 p h) (sat_cons (step1137 p h) (sat_cons (step1143 p h) (sat_cons (step1144 p h) (sat_cons (step1155 p h) (sat_cons (step1139 p h) (sat_cons (step1132 p h) (sat_cons (step1862 p h) (sat_cons (step70 p h) (sat_cons (step28 p h) (sat_cons (step34 p h) (sat_nil p)))))))))))))))))))
def c1916 : List Lit := [(44, false), (1637, true), (7, false), (27, false), (1618, false)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c135, c136, c137, c1190, c1200, c1204, c1195, c1209, c1224] c1916 (by decide) p (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step137 p h) (sat_cons (step1190 p h) (sat_cons (step1200 p h) (sat_cons (step1204 p h) (sat_cons (step1195 p h) (sat_cons (step1209 p h) (sat_cons (step1224 p h) (sat_nil p))))))))))
def c1917 : List Lit := [(10, false), (45, false), (42, false)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c849, c22, c165] c1917 (by decide) p (sat_cons (step849 p h) (sat_cons (step22 p h) (sat_cons (step165 p h) (sat_nil p))))
def c1918 : List Lit := [(96, false), (64, true), (56, false), (65, false), (1580, true)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c854, c855, c874, c1126, c1125, c56, c209, c40, c44, c243, c519] c1918 (by decide) p (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step874 p h) (sat_cons (step1126 p h) (sat_cons (step1125 p h) (sat_cons (step56 p h) (sat_cons (step209 p h) (sat_cons (step40 p h) (sat_cons (step44 p h) (sat_cons (step243 p h) (sat_cons (step519 p h) (sat_nil p))))))))))))
def c1919 : List Lit := [(35, false), (1796, true), (123, false), (44, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c860, c106, c733, c735, c1572] c1919 (by decide) p (sat_cons (step860 p h) (sat_cons (step106 p h) (sat_cons (step733 p h) (sat_cons (step735 p h) (sat_cons (step1572 p h) (sat_nil p))))))
def c1920 : List Lit := [(113, true), (1817, true), (1807, false), (123, false)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c895, c1595, c1612, c1581, c1570, c1572, c1578, c1579, c1608, c1573, c1574, c1599, c755, c766, c1585, c707, c796] c1920 (by decide) p (sat_cons (step895 p h) (sat_cons (step1595 p h) (sat_cons (step1612 p h) (sat_cons (step1581 p h) (sat_cons (step1570 p h) (sat_cons (step1572 p h) (sat_cons (step1578 p h) (sat_cons (step1579 p h) (sat_cons (step1608 p h) (sat_cons (step1573 p h) (sat_cons (step1574 p h) (sat_cons (step1599 p h) (sat_cons (step755 p h) (sat_cons (step766 p h) (sat_cons (step1585 p h) (sat_cons (step707 p h) (sat_cons (step796 p h) (sat_nil p))))))))))))))))))
def c1921 : List Lit := [(1797, true), (114, true), (111, false), (113, false)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c895, c1573, c1574, c701, c766, c709] c1921 (by decide) p (sat_cons (step895 p h) (sat_cons (step1573 p h) (sat_cons (step1574 p h) (sat_cons (step701 p h) (sat_cons (step766 p h) (sat_cons (step709 p h) (sat_nil p)))))))
def c1922 : List Lit := [(1795, true), (1797, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c1573, c1570, c1571, c1921, c753] c1922 (by decide) p (sat_cons (step1573 p h) (sat_cons (step1570 p h) (sat_cons (step1571 p h) (sat_cons (step1921 p h) (sat_cons (step753 p h) (sat_nil p))))))
def c1923 : List Lit := [(1631, true), (44, false), (39, true), (123, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c1201, c1211, c1209, c1202, c1204, c154] c1923 (by decide) p (sat_cons (step1201 p h) (sat_cons (step1211 p h) (sat_cons (step1209 p h) (sat_cons (step1202 p h) (sat_cons (step1204 p h) (sat_cons (step154 p h) (sat_nil p)))))))
def c1924 : List Lit := [(1632, false), (1658, false), (1623, true), (44, false), (1691, true), (123, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c1883, c1216, c1297, c1340, c1170, c1915, c1194, c1195, c1221, c1190, c1304, c141, c1331, c1099, c1875, c1896] c1924 (by decide) p (sat_cons (step1883 p h) (sat_cons (step1216 p h) (sat_cons (step1297 p h) (sat_cons (step1340 p h) (sat_cons (step1170 p h) (sat_cons (step1915 p h) (sat_cons (step1194 p h) (sat_cons (step1195 p h) (sat_cons (step1221 p h) (sat_cons (step1190 p h) (sat_cons (step1304 p h) (sat_cons (step141 p h) (sat_cons (step1331 p h) (sat_cons (step1099 p h) (sat_cons (step1875 p h) (sat_cons (step1896 p h) (sat_nil p)))))))))))))))))
def c1925 : List Lit := [(42, false), (1608, true), (1623, true), (44, false), (123, false)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c143, c152, c1099, c1190, c1896, c1195, c1176, c1915] c1925 (by decide) p (sat_cons (step143 p h) (sat_cons (step152 p h) (sat_cons (step1099 p h) (sat_cons (step1190 p h) (sat_cons (step1896 p h) (sat_cons (step1195 p h) (sat_cons (step1176 p h) (sat_cons (step1915 p h) (sat_nil p)))))))))
def c1926 : List Lit := [(1658, false), (1623, true), (44, false), (1691, true), (39, true), (123, false)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c1923, c1215, c1290, c1348, c1924, c1925, c1202, c1212, c1204, c144, c153, c1099, c1190, c1896, c1195, c1176, c1915] c1926 (by decide) p (sat_cons (step1923 p h) (sat_cons (step1215 p h) (sat_cons (step1290 p h) (sat_cons (step1348 p h) (sat_cons (step1924 p h) (sat_cons (step1925 p h) (sat_cons (step1202 p h) (sat_cons (step1212 p h) (sat_cons (step1204 p h) (sat_cons (step144 p h) (sat_cons (step153 p h) (sat_cons (step1099 p h) (sat_cons (step1190 p h) (sat_cons (step1896 p h) (sat_cons (step1195 p h) (sat_cons (step1176 p h) (sat_cons (step1915 p h) (sat_nil p))))))))))))))))))
def c1927 : List Lit := [(1658, true), (102, true), (80, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c872, c1260, c1264, c1252, c1254, c1240, c1250, c1246, c1232, c229, c221] c1927 (by decide) p (sat_cons (step872 p h) (sat_cons (step1260 p h) (sat_cons (step1264 p h) (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step1240 p h) (sat_cons (step1250 p h) (sat_cons (step1246 p h) (sat_cons (step1232 p h) (sat_cons (step229 p h) (sat_cons (step221 p h) (sat_nil p))))))))))))
def c1928 : List Lit := [(44, false), (122, false), (1691, true), (39, true), (123, false)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c1883, c800, c801, c1923, c1927, c1926, c1224, c1304, c1331, c1875, c1169, c1896, c1867, c1099, c1141, c138, c1139] c1928 (by decide) p (sat_cons (step1883 p h) (sat_cons (step800 p h) (sat_cons (step801 p h) (sat_cons (step1923 p h) (sat_cons (step1927 p h) (sat_cons (step1926 p h) (sat_cons (step1224 p h) (sat_cons (step1304 p h) (sat_cons (step1331 p h) (sat_cons (step1875 p h) (sat_cons (step1169 p h) (sat_cons (step1896 p h) (sat_cons (step1867 p h) (sat_cons (step1099 p h) (sat_cons (step1141 p h) (sat_cons (step138 p h) (sat_cons (step1139 p h) (sat_nil p))))))))))))))))))
def c1929 : List Lit := [(1595, true), (102, true), (44, true)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c857, c1867, c1154, c1141, c1143, c1132, c1139, c1135, c1862, c76, c70] c1929 (by decide) p (sat_cons (step857 p h) (sat_cons (step1867 p h) (sat_cons (step1154 p h) (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1132 p h) (sat_cons (step1139 p h) (sat_cons (step1135 p h) (sat_cons (step1862 p h) (sat_cons (step76 p h) (sat_cons (step70 p h) (sat_nil p))))))))))))
def c1930 : List Lit := [(1595, true), (159, true), (102, false), (44, true), (123, false)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c857, c1867, c1154, c1141, c1143, c1132, c1138, c1139, c1135, c1136, c1862, c577, c70, c1913, c78, c90] c1930 (by decide) p (sat_cons (step857 p h) (sat_cons (step1867 p h) (sat_cons (step1154 p h) (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1132 p h) (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step1862 p h) (sat_cons (step577 p h) (sat_cons (step70 p h) (sat_cons (step1913 p h) (sat_cons (step78 p h) (sat_cons (step90 p h) (sat_nil p)))))))))))))))))
def c1931 : List Lit := [(31, false), (88, true), (17, false), (108, true), (24, false), (27, true)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c1836, c86, c91, c941, c943, c946, c952, c933, c934, c931, c926, c929, c923, c64, c39, c1913] c1931 (by decide) p (sat_cons (step1836 p h) (sat_cons (step86 p h) (sat_cons (step91 p h) (sat_cons (step941 p h) (sat_cons (step943 p h) (sat_cons (step946 p h) (sat_cons (step952 p h) (sat_cons (step933 p h) (sat_cons (step934 p h) (sat_cons (step931 p h) (sat_cons (step926 p h) (sat_cons (step929 p h) (sat_cons (step923 p h) (sat_cons (step64 p h) (sat_cons (step39 p h) (sat_cons (step1913 p h) (sat_nil p)))))))))))))))))
def c1932 : List Lit := [(1630, true), (35, false), (7, false)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c860, c1206, c1208, c1204, c1201, c140, c102, c108] c1932 (by decide) p (sat_cons (step860 p h) (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step1204 p h) (sat_cons (step1201 p h) (sat_cons (step140 p h) (sat_cons (step102 p h) (sat_cons (step108 p h) (sat_nil p)))))))))
def c1933 : List Lit := [(43, true), (44, true), (1631, true), (169, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c863, c1207, c1204, c1205, c128, c1209, c1200, c130, c131, c1761] c1933 (by decide) p (sat_cons (step863 p h) (sat_cons (step1207 p h) (sat_cons (step1204 p h) (sat_cons (step1205 p h) (sat_cons (step128 p h) (sat_cons (step1209 p h) (sat_cons (step1200 p h) (sat_cons (step130 p h) (sat_cons (step131 p h) (sat_cons (step1761 p h) (sat_nil p)))))))))))
def c1934 : List Lit := [(128, false), (1812, true), (125, false), (1805, false), (46, false)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c823, c822, c1593, c1585, c1600] c1934 (by decide) p (sat_cons (step823 p h) (sat_cons (step822 p h) (sat_cons (step1593 p h) (sat_cons (step1585 p h) (sat_cons (step1600 p h) (sat_nil p))))))
def c1935 : List Lit := [(1812, true), (125, false), (127, true), (46, false)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c1588, c1597, c1934, c1589, c1591, c1594, c1600, c821, c1585] c1935 (by decide) p (sat_cons (step1588 p h) (sat_cons (step1597 p h) (sat_cons (step1934 p h) (sat_cons (step1589 p h) (sat_cons (step1591 p h) (sat_cons (step1594 p h) (sat_cons (step1600 p h) (sat_cons (step821 p h) (sat_cons (step1585 p h) (sat_nil p))))))))))
def c1936 : List Lit := [(1724, true), (1715, false)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1398, c1402, c1392, c1375, c1903] c1936 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1398 p h) (sat_cons (step1402 p h) (sat_cons (step1392 p h) (sat_cons (step1375 p h) (sat_cons (step1903 p h) (sat_nil p)))))))
def c1937 : List Lit := [(104, false), (125, true), (108, false), (94, true), (95, false)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c892, c617, c613] c1937 (by decide) p (sat_cons (step892 p h) (sat_cons (step617 p h) (sat_cons (step613 p h) (sat_nil p))))
def c1938 : List Lit := [(1807, true), (125, true), (81, true)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c901, c1590, c1592, c1587, c1588, c834, c812] c1938 (by decide) p (sat_cons (step901 p h) (sat_cons (step1590 p h) (sat_cons (step1592 p h) (sat_cons (step1587 p h) (sat_cons (step1588 p h) (sat_cons (step834 p h) (sat_cons (step812 p h) (sat_nil p))))))))
def c1939 : List Lit := [(35, false), (114, false), (44, true), (1802, true), (123, false), (115, true)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c1919, c736, c1583, c1575] c1939 (by decide) p (sat_cons (step1919 p h) (sat_cons (step736 p h) (sat_cons (step1583 p h) (sat_cons (step1575 p h) (sat_nil p)))))
def c1940 : List Lit := [(1725, true), (1708, false)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c1380, c1411, c1407, c1381, c1389, c1903] c1940 (by decide) p (sat_cons (step1380 p h) (sat_cons (step1411 p h) (sat_cons (step1407 p h) (sat_cons (step1381 p h) (sat_cons (step1389 p h) (sat_cons (step1903 p h) (sat_nil p)))))))
def c1941 : List Lit := [(1659, true), (61, false), (62, false), (1644, false)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1269, c1265, c1241, c1254, c1232, c1246, c221] c1941 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1269 p h) (sat_cons (step1265 p h) (sat_cons (step1241 p h) (sat_cons (step1254 p h) (sat_cons (step1232 p h) (sat_cons (step1246 p h) (sat_cons (step221 p h) (sat_nil p)))))))))
def c1942 : List Lit := [(34, true), (1630, true)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c864, c1208, c1200, c1206, c1204, c133, c134, c1762] c1942 (by decide) p (sat_cons (step864 p h) (sat_cons (step1208 p h) (sat_cons (step1200 p h) (sat_cons (step1206 p h) (sat_cons (step1204 p h) (sat_cons (step133 p h) (sat_cons (step134 p h) (sat_cons (step1762 p h) (sat_nil p)))))))))
def c1943 : List Lit := [(1807, true), (126, false), (128, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c1590, c1592, c1588, c834] c1943 (by decide) p (sat_cons (step1590 p h) (sat_cons (step1592 p h) (sat_cons (step1588 p h) (sat_cons (step834 p h) (sat_nil p)))))
end B112E050
