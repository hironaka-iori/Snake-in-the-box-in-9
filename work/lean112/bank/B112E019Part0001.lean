import B112E019Part0000
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1870 : List Lit := [(10, true), (7, false), (128, true), (17, true)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c853, c24, c22, c18, c1753] c1870 (by decide) p (sat_cons (step853 p h) (sat_cons (step24 p h) (sat_cons (step22 p h) (sat_cons (step18 p h) (sat_cons (step1753 p h) (sat_nil p))))))
def c1871 : List Lit := [(120, false), (1687, true), (109, false), (89, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c713, c714, c1596] c1871 (by decide) p (sat_cons (step713 p h) (sat_cons (step714 p h) (sat_cons (step1596 p h) (sat_nil p))))
def c1872 : List Lit := [(1703, true), (116, true), (233, true)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c1608, c1616, c1623, c1627, c1619, c1617, c1600, c1610, c1612, c1597, c1598, c739, c766, c748] c1872 (by decide) p (sat_cons (step1608 p h) (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step1627 p h) (sat_cons (step1619 p h) (sat_cons (step1617 p h) (sat_cons (step1600 p h) (sat_cons (step1610 p h) (sat_cons (step1612 p h) (sat_cons (step1597 p h) (sat_cons (step1598 p h) (sat_cons (step739 p h) (sat_cons (step766 p h) (sat_cons (step748 p h) (sat_nil p)))))))))))))))
def c1873 : List Lit := [(52, true), (1567, true), (117, true), (1559, false), (43, true), (355, true)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c877, c879, c1334, c1347, c1323, c1022, c1000, c998, c996, c1020, c1017, c1007, c1006, c1319, c1321, c248, c1322, c1325, c237, c1344, c1317, c269, c1336, c1330, c259, c262] c1873 (by decide) p (sat_cons (step877 p h) (sat_cons (step879 p h) (sat_cons (step1334 p h) (sat_cons (step1347 p h) (sat_cons (step1323 p h) (sat_cons (step1022 p h) (sat_cons (step1000 p h) (sat_cons (step998 p h) (sat_cons (step996 p h) (sat_cons (step1020 p h) (sat_cons (step1017 p h) (sat_cons (step1007 p h) (sat_cons (step1006 p h) (sat_cons (step1319 p h) (sat_cons (step1321 p h) (sat_cons (step248 p h) (sat_cons (step1322 p h) (sat_cons (step1325 p h) (sat_cons (step237 p h) (sat_cons (step1344 p h) (sat_cons (step1317 p h) (sat_cons (step269 p h) (sat_cons (step1336 p h) (sat_cons (step1330 p h) (sat_cons (step259 p h) (sat_cons (step262 p h) (sat_nil p)))))))))))))))))))))))))))
def c1874 : List Lit := [(1531, true), (154, true)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1283, c1285, c1280, c1281, c137, c142] c1874 (by decide) p (sat_cons (step1283 p h) (sat_cons (step1285 p h) (sat_cons (step1280 p h) (sat_cons (step1281 p h) (sat_cons (step137 p h) (sat_cons (step142 p h) (sat_nil p)))))))
def c1875 : List Lit := [(36, true), (35, true), (1546, true), (1536, false), (327, true)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c867, c869, c988, c971, c964, c963, c986, c983, c976, c973, c1282, c138, c153, c142, c156, c1287, c1289, c1315, c1297] c1875 (by decide) p (sat_cons (step867 p h) (sat_cons (step869 p h) (sat_cons (step988 p h) (sat_cons (step971 p h) (sat_cons (step964 p h) (sat_cons (step963 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step976 p h) (sat_cons (step973 p h) (sat_cons (step1282 p h) (sat_cons (step138 p h) (sat_cons (step153 p h) (sat_cons (step142 p h) (sat_cons (step156 p h) (sat_cons (step1287 p h) (sat_cons (step1289 p h) (sat_cons (step1315 p h) (sat_cons (step1297 p h) (sat_nil p))))))))))))))))))))
def c1876 : List Lit := [(1557, true), (46, false), (117, true), (176, true)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1331, c259, c262] c1876 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1331 p h) (sat_cons (step259 p h) (sat_cons (step262 p h) (sat_nil p)))))
def c1877 : List Lit := [(1668, true), (121, true), (98, false), (118, false)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1557, c1559, c1554, c1555, c504, c526, c521, c515, c537, c1109, c1110, c1113] c1877 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1557 p h) (sat_cons (step1559 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step504 p h) (sat_cons (step526 p h) (sat_cons (step521 p h) (sat_cons (step515 p h) (sat_cons (step537 p h) (sat_cons (step1109 p h) (sat_cons (step1110 p h) (sat_cons (step1113 p h) (sat_nil p))))))))))))))
def c1878 : List Lit := [(109, false), (1687, true), (120, false), (48, false)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c704, c705, c1596] c1878 (by decide) p (sat_cons (step704 p h) (sat_cons (step705 p h) (sat_cons (step1596 p h) (sat_nil p))))
def c1879 : List Lit := [(112, false), (233, true), (103, false), (115, false), (99, false)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c734, c595, c750] c1879 (by decide) p (sat_cons (step734 p h) (sat_cons (step595 p h) (sat_cons (step750 p h) (sat_nil p))))
def c1880 : List Lit := [(1644, true), (110, false), (107, false), (80, true)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1468, c1499, c1495, c1469, c1482, c1484, c1467, c1479, c1476, c1477, c469, c461, c431, c712, c477] c1880 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1468 p h) (sat_cons (step1499 p h) (sat_cons (step1495 p h) (sat_cons (step1469 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1467 p h) (sat_cons (step1479 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step469 p h) (sat_cons (step461 p h) (sat_cons (step431 p h) (sat_cons (step712 p h) (sat_cons (step477 p h) (sat_nil p)))))))))))))))))
def c1881 : List Lit := [(66, true), (109, true), (1622, true), (63, true), (107, false)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1458, c1429, c1422, c1424, c1428, c1454, c1436, c1438, c1433, c1430, c298, c318, c324] c1881 (by decide) p (sat_cons (step1458 p h) (sat_cons (step1429 p h) (sat_cons (step1422 p h) (sat_cons (step1424 p h) (sat_cons (step1428 p h) (sat_cons (step1454 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1433 p h) (sat_cons (step1430 p h) (sat_cons (step298 p h) (sat_cons (step318 p h) (sat_cons (step324 p h) (sat_nil p))))))))))))))
def c1882 : List Lit := [(69, false), (68, true), (78, true), (109, true), (1622, true), (63, true)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c1847, c1427, c1450, c1437, c328, c324, c1050, c1057, c1052, c337, c1434, c1435, c1436, c298, c1454, c1423, c1428] c1882 (by decide) p (sat_cons (step1847 p h) (sat_cons (step1427 p h) (sat_cons (step1450 p h) (sat_cons (step1437 p h) (sat_cons (step328 p h) (sat_cons (step324 p h) (sat_cons (step1050 p h) (sat_cons (step1057 p h) (sat_cons (step1052 p h) (sat_cons (step337 p h) (sat_cons (step1434 p h) (sat_cons (step1435 p h) (sat_cons (step1436 p h) (sat_cons (step298 p h) (sat_cons (step1454 p h) (sat_cons (step1423 p h) (sat_cons (step1428 p h) (sat_nil p))))))))))))))))))
def c1883 : List Lit := [(1645, true), (1627, false), (109, true), (80, true)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1471, c1504, c1500, c1472, c1482, c1484, c1467, c1479, c1476, c1477, c469, c461, c431, c477] c1883 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1471 p h) (sat_cons (step1504 p h) (sat_cons (step1500 p h) (sat_cons (step1472 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1467 p h) (sat_cons (step1479 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step469 p h) (sat_cons (step461 p h) (sat_cons (step431 p h) (sat_cons (step477 p h) (sat_nil p))))))))))))))))
def c1884 : List Lit := [(63, true), (1622, true), (71, true), (193, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c885, c1434, c1436, c1454, c346, c1427, c1428, c1450, c1423, c1437, c1439, c1435, c1430, c343, c298] c1884 (by decide) p (sat_cons (step885 p h) (sat_cons (step1434 p h) (sat_cons (step1436 p h) (sat_cons (step1454 p h) (sat_cons (step346 p h) (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step1450 p h) (sat_cons (step1423 p h) (sat_cons (step1437 p h) (sat_cons (step1439 p h) (sat_cons (step1435 p h) (sat_cons (step1430 p h) (sat_cons (step343 p h) (sat_cons (step298 p h) (sat_nil p))))))))))))))))
def c1885 : List Lit := [(1607, true), (62, false), (63, false)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c1422, c1423, c283] c1885 (by decide) p (sat_cons (step1422 p h) (sat_cons (step1423 p h) (sat_cons (step283 p h) (sat_nil p))))
def c1886 : List Lit := [(1688, false), (1694, false), (89, false), (109, false), (1706, true), (1686, false), (118, true)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1617, c1638, c1603, c1606, c1634, c1871, c1618, c1613] c1886 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1617 p h) (sat_cons (step1638 p h) (sat_cons (step1603 p h) (sat_cons (step1606 p h) (sat_cons (step1634 p h) (sat_cons (step1871 p h) (sat_cons (step1618 p h) (sat_cons (step1613 p h) (sat_nil p))))))))))
def c1887 : List Lit := [(1681, true), (99, true), (1676, false), (1673, false), (87, false)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c1810, c1578, c1582, c1574, c1557, c1559, c1564, c1554, c1555, c526, c504, c518, c496, c515, c1089, c1109, c1090, c1112, c1093, c1114, c1098, c1131, c1103, c1164, c1170] c1887 (by decide) p (sat_cons (step1810 p h) (sat_cons (step1578 p h) (sat_cons (step1582 p h) (sat_cons (step1574 p h) (sat_cons (step1557 p h) (sat_cons (step1559 p h) (sat_cons (step1564 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step526 p h) (sat_cons (step504 p h) (sat_cons (step518 p h) (sat_cons (step496 p h) (sat_cons (step515 p h) (sat_cons (step1089 p h) (sat_cons (step1109 p h) (sat_cons (step1090 p h) (sat_cons (step1112 p h) (sat_cons (step1093 p h) (sat_cons (step1114 p h) (sat_cons (step1098 p h) (sat_cons (step1131 p h) (sat_cons (step1103 p h) (sat_cons (step1164 p h) (sat_cons (step1170 p h) (sat_nil p))))))))))))))))))))))))))
def c1888 : List Lit := [(1668, true), (98, false), (87, false)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c1810, c1557, c1559, c1554, c1555, c526, c504, c518, c496, c515, c1089, c1109, c1090, c1112, c1093, c1114, c1098, c1131, c1103, c1164, c1170] c1888 (by decide) p (sat_cons (step1810 p h) (sat_cons (step1557 p h) (sat_cons (step1559 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step526 p h) (sat_cons (step504 p h) (sat_cons (step518 p h) (sat_cons (step496 p h) (sat_cons (step515 p h) (sat_cons (step1089 p h) (sat_cons (step1109 p h) (sat_cons (step1090 p h) (sat_cons (step1112 p h) (sat_cons (step1093 p h) (sat_cons (step1114 p h) (sat_cons (step1098 p h) (sat_cons (step1131 p h) (sat_cons (step1103 p h) (sat_cons (step1164 p h) (sat_cons (step1170 p h) (sat_nil p))))))))))))))))))))))
def c1889 : List Lit := [(91, false), (96, true), (92, false), (95, false), (98, false)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c1810, c526, c504, c515, c496, c1109, c1089, c1112, c1090, c1114, c1093, c1131, c1098, c1164, c1103, c1170] c1889 (by decide) p (sat_cons (step1810 p h) (sat_cons (step526 p h) (sat_cons (step504 p h) (sat_cons (step515 p h) (sat_cons (step496 p h) (sat_cons (step1109 p h) (sat_cons (step1089 p h) (sat_cons (step1112 p h) (sat_cons (step1090 p h) (sat_cons (step1114 p h) (sat_cons (step1093 p h) (sat_cons (step1131 p h) (sat_cons (step1098 p h) (sat_cons (step1164 p h) (sat_cons (step1103 p h) (sat_cons (step1170 p h) (sat_nil p)))))))))))))))))
def c1890 : List Lit := [(120, false), (116, false), (1696, false), (110, true), (109, true), (113, false), (241, true), (1705, true)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c812, c842, c830, c831, c1596, c1609, c1605, c1617, c1633] c1890 (by decide) p (sat_cons (step812 p h) (sat_cons (step842 p h) (sat_cons (step830 p h) (sat_cons (step831 p h) (sat_cons (step1596 p h) (sat_cons (step1609 p h) (sat_cons (step1605 p h) (sat_cons (step1617 p h) (sat_cons (step1633 p h) (sat_nil p))))))))))
def c1891 : List Lit := [(1622, true), (74, false), (63, true), (109, true), (192, true), (193, true), (107, false), (116, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c888, c1884, c1881, c337, c354, c383] c1891 (by decide) p (sat_cons (step888 p h) (sat_cons (step1884 p h) (sat_cons (step1881 p h) (sat_cons (step337 p h) (sat_cons (step354 p h) (sat_cons (step383 p h) (sat_nil p)))))))
def c1892 : List Lit := [(1553, true), (46, false), (43, false), (44, false), (105, true), (107, false)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1814, c879, c1322, c1324, c1319, c1320, c1316, c246, c172, c212, c222, c991, c992, c1002, c1003, c1022, c998, c1028, c996, c986, c237, c982, c269, c980, c195, c979, c188] c1892 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1814 p h) (sat_cons (step879 p h) (sat_cons (step1322 p h) (sat_cons (step1324 p h) (sat_cons (step1319 p h) (sat_cons (step1320 p h) (sat_cons (step1316 p h) (sat_cons (step246 p h) (sat_cons (step172 p h) (sat_cons (step212 p h) (sat_cons (step222 p h) (sat_cons (step991 p h) (sat_cons (step992 p h) (sat_cons (step1002 p h) (sat_cons (step1003 p h) (sat_cons (step1022 p h) (sat_cons (step998 p h) (sat_cons (step1028 p h) (sat_cons (step996 p h) (sat_cons (step986 p h) (sat_cons (step237 p h) (sat_cons (step982 p h) (sat_cons (step269 p h) (sat_cons (step980 p h) (sat_cons (step195 p h) (sat_cons (step979 p h) (sat_cons (step188 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1893 : List Lit := [(63, false), (184, true), (99, false)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c292, c293, c1772] c1893 (by decide) p (sat_cons (step292 p h) (sat_cons (step293 p h) (sat_cons (step1772 p h) (sat_nil p))))
def c1894 : List Lit := [(1607, true), (187, true), (107, false), (62, true), (105, true)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c1422, c1423, c306, c317] c1894 (by decide) p (sat_cons (step1422 p h) (sat_cons (step1423 p h) (sat_cons (step306 p h) (sat_cons (step317 p h) (sat_nil p)))))
def c1895 : List Lit := [(1629, true), (79, false), (99, false)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c1465, c1466, c387] c1895 (by decide) p (sat_cons (step1465 p h) (sat_cons (step1466 p h) (sat_cons (step387 p h) (sat_nil p))))
def c1896 : List Lit := [(1627, true), (74, false), (116, false)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c1462, c1463, c356] c1896 (by decide) p (sat_cons (step1462 p h) (sat_cons (step1463 p h) (sat_cons (step356 p h) (sat_nil p))))
def c1897 : List Lit := [(1538, true), (40, false), (99, false)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c1294, c1296, c1291, c1288, c160] c1897 (by decide) p (sat_cons (step1294 p h) (sat_cons (step1296 p h) (sat_cons (step1291 p h) (sat_cons (step1288 p h) (sat_cons (step160 p h) (sat_nil p))))))
def c1898 : List Lit := [(63, false), (64, false), (99, false), (100, true)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c291, c284] c1898 (by decide) p (sat_cons (step291 p h) (sat_cons (step284 p h) (sat_nil p)))
def c1899 : List Lit := [(1627, true), (119, true), (111, true), (70, false), (237, true), (59, false), (105, true), (116, false)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c1462, c1896, c366, c790] c1899 (by decide) p (sat_cons (step1462 p h) (sat_cons (step1896 p h) (sat_cons (step366 p h) (sat_cons (step790 p h) (sat_nil p)))))
def c1900 : List Lit := [(81, false), (88, true), (82, false), (89, false), (58, false), (109, true)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c431, c456, c477] c1900 (by decide) p (sat_cons (step431 p h) (sat_cons (step456 p h) (sat_cons (step477 p h) (sat_nil p))))
def c1901 : List Lit := [(118, true), (1705, true), (115, true), (119, true), (112, true), (241, true), (109, true)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c1609, c1598, c1600, c1629, c1618, c1612, c1613, c1617, c1620, c842, c1633, c1610, c1601, c812, c1599] c1901 (by decide) p (sat_cons (step1609 p h) (sat_cons (step1598 p h) (sat_cons (step1600 p h) (sat_cons (step1629 p h) (sat_cons (step1618 p h) (sat_cons (step1612 p h) (sat_cons (step1613 p h) (sat_cons (step1617 p h) (sat_cons (step1620 p h) (sat_cons (step842 p h) (sat_cons (step1633 p h) (sat_cons (step1610 p h) (sat_cons (step1601 p h) (sat_cons (step812 p h) (sat_cons (step1599 p h) (sat_nil p))))))))))))))))
def c1902 : List Lit := [(102, false), (110, false), (113, false), (118, false), (223, true), (101, true), (100, true)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c765, c675, c618] c1902 (by decide) p (sat_cons (step765 p h) (sat_cons (step675 p h) (sat_cons (step618 p h) (sat_nil p))))
def c1903 : List Lit := [(66, false), (1610, true), (62, false), (99, false)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c285, c286, c1428, c1423] c1903 (by decide) p (sat_cons (step285 p h) (sat_cons (step286 p h) (sat_cons (step1428 p h) (sat_cons (step1423 p h) (sat_nil p)))))
def c1904 : List Lit := [(1610, true), (62, false), (99, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c1426, c1903, c1422, c1424, c284, c1428] c1904 (by decide) p (sat_cons (step1426 p h) (sat_cons (step1903 p h) (sat_cons (step1422 p h) (sat_cons (step1424 p h) (sat_cons (step284 p h) (sat_cons (step1428 p h) (sat_nil p)))))))
def c1905 : List Lit := [(1639, true), (107, false), (109, true), (99, false)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1482, c1484, c1479, c1480, c1476, c1477, c472, c463, c652, c394, c484, c442, c1088, c1083, c1091, c1086, c1096] c1905 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step472 p h) (sat_cons (step463 p h) (sat_cons (step652 p h) (sat_cons (step394 p h) (sat_cons (step484 p h) (sat_cons (step442 p h) (sat_cons (step1088 p h) (sat_cons (step1083 p h) (sat_cons (step1091 p h) (sat_cons (step1086 p h) (sat_cons (step1096 p h) (sat_nil p)))))))))))))))))))
def c1906 : List Lit := [(86, true), (89, false), (79, true), (88, true), (105, true), (85, false), (109, true)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c1828, c484, c442, c1088, c1083, c1091, c1086, c1096] c1906 (by decide) p (sat_cons (step1828 p h) (sat_cons (step484 p h) (sat_cons (step442 p h) (sat_cons (step1088 p h) (sat_cons (step1083 p h) (sat_cons (step1091 p h) (sat_cons (step1086 p h) (sat_cons (step1096 p h) (sat_nil p)))))))))
def c1907 : List Lit := [(117, false), (1627, true), (415, false)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1175, c1463, c1462, c1103, c1169, c1173, c1030, c1025, c1020, c1015, c1012, c1011, c1808, c1106, c1068, c1063, c1061, c1059, c368, c369, c363] c1907 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1175 p h) (sat_cons (step1463 p h) (sat_cons (step1462 p h) (sat_cons (step1103 p h) (sat_cons (step1169 p h) (sat_cons (step1173 p h) (sat_cons (step1030 p h) (sat_cons (step1025 p h) (sat_cons (step1020 p h) (sat_cons (step1015 p h) (sat_cons (step1012 p h) (sat_cons (step1011 p h) (sat_cons (step1808 p h) (sat_cons (step1106 p h) (sat_cons (step1068 p h) (sat_cons (step1063 p h) (sat_cons (step1061 p h) (sat_cons (step1059 p h) (sat_cons (step368 p h) (sat_cons (step369 p h) (sat_cons (step363 p h) (sat_nil p)))))))))))))))))))))))
def c1908 : List Lit := [(1681, true), (118, false), (1673, false), (92, true), (216, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1555, c1557, c1582, c1586, c1571, c1558, c1560, c1563, c1556, c526, c521, c515] c1908 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1555 p h) (sat_cons (step1557 p h) (sat_cons (step1582 p h) (sat_cons (step1586 p h) (sat_cons (step1571 p h) (sat_cons (step1558 p h) (sat_cons (step1560 p h) (sat_cons (step1563 p h) (sat_cons (step1556 p h) (sat_cons (step526 p h) (sat_cons (step521 p h) (sat_cons (step515 p h) (sat_nil p))))))))))))))
def c1909 : List Lit := [(69, false), (109, true), (65, false), (190, true), (66, true), (107, true)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c883, c328, c1775, c322] c1909 (by decide) p (sat_cons (step883 p h) (sat_cons (step328 p h) (sat_cons (step1775 p h) (sat_cons (step322 p h) (sat_nil p)))))
def c1910 : List Lit := [(67, false), (188, true), (102, false), (77, true), (118, false)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c670, c313] c1910 (by decide) p (sat_cons (step670 p h) (sat_cons (step313 p h) (sat_nil p)))
def c1911 : List Lit := [(1557, true), (1554, true), (42, false), (331, false), (117, true)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1820, c1002, c1023, c1017, c1007, c1006, c1003, c998, c996, c1330, c1876, c260, c1317, c1325, c1319, c1320, c240, c241, c239] c1911 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1820 p h) (sat_cons (step1002 p h) (sat_cons (step1023 p h) (sat_cons (step1017 p h) (sat_cons (step1007 p h) (sat_cons (step1006 p h) (sat_cons (step1003 p h) (sat_cons (step998 p h) (sat_cons (step996 p h) (sat_cons (step1330 p h) (sat_cons (step1876 p h) (sat_cons (step260 p h) (sat_cons (step1317 p h) (sat_cons (step1325 p h) (sat_cons (step1319 p h) (sat_cons (step1320 p h) (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step239 p h) (sat_nil p)))))))))))))))))))))
def c1912 : List Lit := [(49, false), (1551, true), (42, false), (172, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c1320, c1319, c240, c241, c239] c1912 (by decide) p (sat_cons (step1320 p h) (sat_cons (step1319 p h) (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step239 p h) (sat_nil p))))))
def c1913 : List Lit := [(1621, true), (371, true), (105, true), (99, false)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c1047, c1038, c1036, c1893, c1427, c1045, c1043, c1040, c1453, c1449, c1904, c1428, c1438, c1422, c1423, c1430, c306, c316] c1913 (by decide) p (sat_cons (step1047 p h) (sat_cons (step1038 p h) (sat_cons (step1036 p h) (sat_cons (step1893 p h) (sat_cons (step1427 p h) (sat_cons (step1045 p h) (sat_cons (step1043 p h) (sat_cons (step1040 p h) (sat_cons (step1453 p h) (sat_cons (step1449 p h) (sat_cons (step1904 p h) (sat_cons (step1428 p h) (sat_cons (step1438 p h) (sat_cons (step1422 p h) (sat_cons (step1423 p h) (sat_cons (step1430 p h) (sat_cons (step306 p h) (sat_cons (step316 p h) (sat_nil p)))))))))))))))))))
def c1914 : List Lit := [(111, false), (116, false), (1689, true), (99, false)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c735, c737, c1599] c1914 (by decide) p (sat_cons (step735 p h) (sat_cons (step737 p h) (sat_cons (step1599 p h) (sat_nil p))))
def c1915 : List Lit := [(1565, true), (116, false), (113, false)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c1339, c1342, c1335, c1322, c1324, c1330, c1331, c1319, c1317, c799, c262, c223, c257] c1915 (by decide) p (sat_cons (step1339 p h) (sat_cons (step1342 p h) (sat_cons (step1335 p h) (sat_cons (step1322 p h) (sat_cons (step1324 p h) (sat_cons (step1330 p h) (sat_cons (step1331 p h) (sat_cons (step1319 p h) (sat_cons (step1317 p h) (sat_cons (step799 p h) (sat_cons (step262 p h) (sat_cons (step223 p h) (sat_cons (step257 p h) (sat_nil p))))))))))))))
def c1916 : List Lit := [(1699, true), (119, false), (118, true), (116, false)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1615, c1617, c1613, c1609, c831] c1916 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1615 p h) (sat_cons (step1617 p h) (sat_cons (step1613 p h) (sat_cons (step1609 p h) (sat_cons (step831 p h) (sat_nil p)))))))
def c1917 : List Lit := [(1680, true), (1673, false), (216, true), (94, true)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1577, c1581, c1571, c1557, c1559, c1563, c1554, c526, c516] c1917 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1577 p h) (sat_cons (step1581 p h) (sat_cons (step1571 p h) (sat_cons (step1557 p h) (sat_cons (step1559 p h) (sat_cons (step1563 p h) (sat_cons (step1554 p h) (sat_cons (step526 p h) (sat_cons (step516 p h) (sat_nil p)))))))))))
def c1918 : List Lit := [(1668, true), (98, false), (216, true), (94, true)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c1557, c1559, c1554, c526, c516] c1918 (by decide) p (sat_cons (step1557 p h) (sat_cons (step1559 p h) (sat_cons (step1554 p h) (sat_cons (step526 p h) (sat_cons (step516 p h) (sat_nil p))))))
def c1919 : List Lit := [(95, false), (98, false), (216, true), (94, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c516, c517, c1790] c1919 (by decide) p (sat_cons (step516 p h) (sat_cons (step517 p h) (sat_cons (step1790 p h) (sat_nil p))))
def c1920 : List Lit := [(1627, true), (113, false), (237, true), (111, true), (105, true), (116, false), (94, true)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c1462, c1896, c805, c794] c1920 (by decide) p (sat_cons (step1462 p h) (sat_cons (step1896 p h) (sat_cons (step805 p h) (sat_cons (step794 p h) (sat_nil p)))))
def c1921 : List Lit := [(79, false), (99, false), (85, false), (1630, true)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c390, c393, c1467] c1921 (by decide) p (sat_cons (step390 p h) (sat_cons (step393 p h) (sat_cons (step1467 p h) (sat_nil p))))
def c1922 : List Lit := [(92, false), (98, false), (91, false), (90, true), (84, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c504, c500] c1922 (by decide) p (sat_cons (step504 p h) (sat_cons (step500 p h) (sat_nil p)))
def c1923 : List Lit := [(1575, true), (1543, false), (175, true), (1531, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c1368, c1363, c1308, c1339, c1342, c1335, c1324, c1330, c1331, c1317, c262, c255, c194, c195, c1288, c1291, c1297] c1923 (by decide) p (sat_cons (step1368 p h) (sat_cons (step1363 p h) (sat_cons (step1308 p h) (sat_cons (step1339 p h) (sat_cons (step1342 p h) (sat_cons (step1335 p h) (sat_cons (step1324 p h) (sat_cons (step1330 p h) (sat_cons (step1331 p h) (sat_cons (step1317 p h) (sat_cons (step262 p h) (sat_cons (step255 p h) (sat_cons (step194 p h) (sat_cons (step195 p h) (sat_cons (step1288 p h) (sat_cons (step1291 p h) (sat_cons (step1297 p h) (sat_nil p))))))))))))))))))
def c1924 : List Lit := [(110, false), (107, true), (109, true), (231, true), (106, true), (121, true)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c904, c728, c730, c695, c1797] c1924 (by decide) p (sat_cons (step904 p h) (sat_cons (step728 p h) (sat_cons (step730 p h) (sat_cons (step695 p h) (sat_cons (step1797 p h) (sat_nil p))))))
def c1925 : List Lit := [(1681, true), (1666, false), (216, true), (213, true), (1673, false), (118, false), (113, true)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c894, c1557, c1568, c1586, c1582, c1908, c1560, c1571, c1563, c504, c501, c502, c490, c1783] c1925 (by decide) p (sat_cons (step894 p h) (sat_cons (step1557 p h) (sat_cons (step1568 p h) (sat_cons (step1586 p h) (sat_cons (step1582 p h) (sat_cons (step1908 p h) (sat_cons (step1560 p h) (sat_cons (step1571 p h) (sat_cons (step1563 p h) (sat_cons (step504 p h) (sat_cons (step501 p h) (sat_cons (step502 p h) (sat_cons (step490 p h) (sat_cons (step1783 p h) (sat_nil p)))))))))))))))
def c1926 : List Lit := [(82, true), (1640, true), (58, false), (208, true), (96, true), (106, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c1487, c1477, c1478, c1485, c1479, c1480, c458, c465] c1926 (by decide) p (sat_cons (step1487 p h) (sat_cons (step1477 p h) (sat_cons (step1478 p h) (sat_cons (step1485 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step458 p h) (sat_cons (step465 p h) (sat_nil p)))))))))
def c1927 : List Lit := [(1538, true), (162, true), (100, true), (99, false)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c1296, c1897, c1288, c170] c1927 (by decide) p (sat_cons (step1296 p h) (sat_cons (step1897 p h) (sat_cons (step1288 p h) (sat_cons (step170 p h) (sat_nil p)))))
def c1928 : List Lit := [(1551, true), (50, false), (115, false)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c1319, c1320, c232] c1928 (by decide) p (sat_cons (step1319 p h) (sat_cons (step1320 p h) (sat_cons (step232 p h) (sat_nil p))))
def c1929 : List Lit := [(1696, true), (116, false), (117, false)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c1611, c1612, c814] c1929 (by decide) p (sat_cons (step1611 p h) (sat_cons (step1612 p h) (sat_cons (step814 p h) (sat_nil p))))
def c1930 : List Lit := [(107, true), (1687, true), (109, true), (106, true), (121, true), (231, true)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c1924, c1596] c1930 (by decide) p (sat_cons (step1924 p h) (sat_cons (step1596 p h) (sat_nil p)))
def c1931 : List Lit := [(71, true), (1615, true), (70, true), (193, true)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c885, c346, c1435, c342] c1931 (by decide) p (sat_cons (step885 p h) (sat_cons (step346 p h) (sat_cons (step1435 p h) (sat_cons (step342 p h) (sat_nil p)))))
def c1932 : List Lit := [(75, false), (76, false), (77, true), (196, true), (116, false)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c356, c363] c1932 (by decide) p (sat_cons (step356 p h) (sat_cons (step363 p h) (sat_nil p)))
def c1933 : List Lit := [(1623, true), (71, true), (67, true), (63, true), (193, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c885, c1431, c1434, c1439, c346, c1427, c1451, c1440, c1435, c1442, c343, c1455, c1432, c1428, c298, c1423] c1933 (by decide) p (sat_cons (step885 p h) (sat_cons (step1431 p h) (sat_cons (step1434 p h) (sat_cons (step1439 p h) (sat_cons (step346 p h) (sat_cons (step1427 p h) (sat_cons (step1451 p h) (sat_cons (step1440 p h) (sat_cons (step1435 p h) (sat_cons (step1442 p h) (sat_cons (step343 p h) (sat_cons (step1455 p h) (sat_cons (step1432 p h) (sat_cons (step1428 p h) (sat_cons (step298 p h) (sat_cons (step1423 p h) (sat_nil p)))))))))))))))))
end B112E019
