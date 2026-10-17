import B112E034Part0000
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1843 : List Lit := [(1782, false), (1789, true)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c892, c1534, c1525, c1528, c1538, c1518, c1519, c1510, c1512, c1507, c1505, c510, c531, c526] c1843 (by decide) p (sat_cons (step892 p h) (sat_cons (step1534 p h) (sat_cons (step1525 p h) (sat_cons (step1528 p h) (sat_cons (step1538 p h) (sat_cons (step1518 p h) (sat_cons (step1519 p h) (sat_cons (step1510 p h) (sat_cons (step1512 p h) (sat_cons (step1507 p h) (sat_cons (step1505 p h) (sat_cons (step510 p h) (sat_cons (step531 p h) (sat_cons (step526 p h) (sat_nil p)))))))))))))))
def c1844 : List Lit := [(122, false), (118, false), (112, false), (45, true)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c898, c799, c625] c1844 (by decide) p (sat_cons (step898 p h) (sat_cons (step799 p h) (sat_cons (step625 p h) (sat_nil p))))
def c1845 : List Lit := [(111, false), (118, false), (112, false), (1782, true)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c619, c622, c1523] c1845 (by decide) p (sat_cons (step619 p h) (sat_cons (step622 p h) (sat_cons (step1523 p h) (sat_nil p))))
def c1846 : List Lit := [(1618, true), (39, false), (35, false), (37, true), (42, true)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c1205, c1208, c1215, c1217, c1210, c1207, c157] c1846 (by decide) p (sat_cons (step1205 p h) (sat_cons (step1208 p h) (sat_cons (step1215 p h) (sat_cons (step1217 p h) (sat_cons (step1210 p h) (sat_cons (step1207 p h) (sat_cons (step157 p h) (sat_nil p))))))))
def c1847 : List Lit := [(1618, true), (37, true), (38, false), (33, false), (42, true)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c1205, c1208, c1215, c1217, c1210, c1207, c153] c1847 (by decide) p (sat_cons (step1205 p h) (sat_cons (step1208 p h) (sat_cons (step1215 p h) (sat_cons (step1217 p h) (sat_cons (step1210 p h) (sat_cons (step1207 p h) (sat_cons (step153 p h) (sat_nil p))))))))
def c1848 : List Lit := [(1779, true), (102, false), (100, false)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c1518, c1519, c510] c1848 (by decide) p (sat_cons (step1518 p h) (sat_cons (step1519 p h) (sat_cons (step510 p h) (sat_nil p))))
def c1849 : List Lit := [(1747, true), (1737, false), (86, true)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c883, c1430, c1445, c1454, c1459, c1449, c1423, c1432, c1420, c1421, c368, c365] c1849 (by decide) p (sat_cons (step883 p h) (sat_cons (step1430 p h) (sat_cons (step1445 p h) (sat_cons (step1454 p h) (sat_cons (step1459 p h) (sat_cons (step1449 p h) (sat_cons (step1423 p h) (sat_cons (step1432 p h) (sat_cons (step1420 p h) (sat_cons (step1421 p h) (sat_cons (step368 p h) (sat_cons (step365 p h) (sat_nil p)))))))))))))
def c1850 : List Lit := [(99, true), (115, false), (93, false), (98, false), (96, true)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c890, c484, c487, c456] c1850 (by decide) p (sat_cons (step890 p h) (sat_cons (step484 p h) (sat_cons (step487 p h) (sat_cons (step456 p h) (sat_nil p)))))
def c1851 : List Lit := [(121, false), (125, false), (103, false), (119, true), (110, true)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c897, c794, c839] c1851 (by decide) p (sat_cons (step897 p h) (sat_cons (step794 p h) (sat_cons (step839 p h) (sat_nil p))))
def c1852 : List Lit := [(1727, true), (71, true)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c882, c1420, c1421, c360, c361, c1747] c1852 (by decide) p (sat_cons (step882 p h) (sat_cons (step1420 p h) (sat_cons (step1421 p h) (sat_cons (step360 p h) (sat_cons (step361 p h) (sat_cons (step1747 p h) (sat_nil p)))))))
def c1853 : List Lit := [(1540, true)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c29, c1779, c1091, c1092, c1] c1853 (by decide) p (sat_cons (step29 p h) (sat_cons (step1779 p h) (sat_cons (step1091 p h) (sat_cons (step1092 p h) (sat_cons (step1 p h) (sat_nil p))))))
def c1854 : List Lit := [(1545, true)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1817] c1854 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1817 p h) (sat_nil p)))
def c1855 : List Lit := [(1558, true)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1854, c1824] c1855 (by decide) p (sat_cons (step1854 p h) (sat_cons (step1824 p h) (sat_nil p)))
def c1856 : List Lit := [(80, false), (208, true), (108, false), (120, true), (74, false), (115, true)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c879, c358, c303, c304, c324] c1856 (by decide) p (sat_cons (step879 p h) (sat_cons (step358 p h) (sat_cons (step303 p h) (sat_cons (step304 p h) (sat_cons (step324 p h) (sat_nil p))))))
def c1857 : List Lit := [(1644, true), (52, true)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c1253, c1270, c1267, c1254, c1830] c1857 (by decide) p (sat_cons (step1253 p h) (sat_cons (step1270 p h) (sat_cons (step1267 p h) (sat_cons (step1254 p h) (sat_cons (step1830 p h) (sat_nil p))))))
def c1858 : List Lit := [(1581, false), (1622, false), (1685, true), (1644, false), (1628, false)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1246, c1280, c1306, c1328, c1167, c1323, c1307, c1285, c1247, c1241, c1174, c1831, c1825, c1818] c1858 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1246 p h) (sat_cons (step1280 p h) (sat_cons (step1306 p h) (sat_cons (step1328 p h) (sat_cons (step1167 p h) (sat_cons (step1323 p h) (sat_cons (step1307 p h) (sat_cons (step1285 p h) (sat_cons (step1247 p h) (sat_cons (step1241 p h) (sat_cons (step1174 p h) (sat_cons (step1831 p h) (sat_cons (step1825 p h) (sat_cons (step1818 p h) (sat_nil p))))))))))))))))
def c1859 : List Lit := [(1604, true), (101, true)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c858, c1191, c1192, c106, c105, c1726] c1859 (by decide) p (sat_cons (step858 p h) (sat_cons (step1191 p h) (sat_cons (step1192 p h) (sat_cons (step106 p h) (sat_cons (step105 p h) (sat_cons (step1726 p h) (sat_nil p)))))))
def c1860 : List Lit := [(1581, true), (1564, false)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c855, c1126, c1152, c1148, c1127, c1138, c1122, c1135, c1136, c80, c84] c1860 (by decide) p (sat_cons (step855 p h) (sat_cons (step1126 p h) (sat_cons (step1152 p h) (sat_cons (step1148 p h) (sat_cons (step1127 p h) (sat_cons (step1138 p h) (sat_cons (step1122 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step80 p h) (sat_cons (step84 p h) (sat_nil p))))))))))))
def c1861 : List Lit := [(1574, true), (18, false)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c855, c1135, c1136, c80, c84] c1861 (by decide) p (sat_cons (step855 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step80 p h) (sat_cons (step84 p h) (sat_nil p))))))
def c1862 : List Lit := [(18, false), (1577, true), (91, false)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c854, c855, c1139, c1861, c1141, c1132, c78, c45, c49, c1137, c80] c1862 (by decide) p (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step1139 p h) (sat_cons (step1861 p h) (sat_cons (step1141 p h) (sat_cons (step1132 p h) (sat_cons (step78 p h) (sat_cons (step45 p h) (sat_cons (step49 p h) (sat_cons (step1137 p h) (sat_cons (step80 p h) (sat_nil p))))))))))))
def c1863 : List Lit := [(25, true), (18, true), (1577, true), (16, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c855, c854, c1797, c1139, c1135, c1137, c1141, c80, c1132, c86, c78, c924, c47, c925, c915, c936, c918, c941, c922] c1863 (by decide) p (sat_cons (step855 p h) (sat_cons (step854 p h) (sat_cons (step1797 p h) (sat_cons (step1139 p h) (sat_cons (step1135 p h) (sat_cons (step1137 p h) (sat_cons (step1141 p h) (sat_cons (step80 p h) (sat_cons (step1132 p h) (sat_cons (step86 p h) (sat_cons (step78 p h) (sat_cons (step924 p h) (sat_cons (step47 p h) (sat_cons (step925 p h) (sat_cons (step915 p h) (sat_cons (step936 p h) (sat_cons (step918 p h) (sat_cons (step941 p h) (sat_cons (step922 p h) (sat_nil p))))))))))))))))))))
def c1864 : List Lit := [(1748, true), (1738, false), (86, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c883, c1430, c1446, c1455, c1460, c1450, c1423, c1432, c1420, c1421, c368, c365] c1864 (by decide) p (sat_cons (step883 p h) (sat_cons (step1430 p h) (sat_cons (step1446 p h) (sat_cons (step1455 p h) (sat_cons (step1460 p h) (sat_cons (step1450 p h) (sat_cons (step1423 p h) (sat_cons (step1432 p h) (sat_cons (step1420 p h) (sat_cons (step1421 p h) (sat_cons (step368 p h) (sat_cons (step365 p h) (sat_nil p)))))))))))))
def c1865 : List Lit := [(58, true), (74, false), (50, true), (52, true), (1645, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c870, c1253, c1268, c1259, c1256, c1257, c1258, c1261, c1271, c249, c235, c1254, c259] c1865 (by decide) p (sat_cons (step870 p h) (sat_cons (step1253 p h) (sat_cons (step1268 p h) (sat_cons (step1259 p h) (sat_cons (step1256 p h) (sat_cons (step1257 p h) (sat_cons (step1258 p h) (sat_cons (step1261 p h) (sat_cons (step1271 p h) (sat_cons (step249 p h) (sat_cons (step235 p h) (sat_cons (step1254 p h) (sat_cons (step259 p h) (sat_nil p))))))))))))))
def c1866 : List Lit := [(58, false), (1641, true), (74, false), (70, false), (115, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c879, c329, c325, c252, c247, c1255, c1261] c1866 (by decide) p (sat_cons (step879 p h) (sat_cons (step329 p h) (sat_cons (step325 p h) (sat_cons (step252 p h) (sat_cons (step247 p h) (sat_cons (step1255 p h) (sat_cons (step1261 p h) (sat_nil p))))))))
def c1867 : List Lit := [(1645, true), (52, true), (74, false), (70, false), (51, false), (115, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c1253, c1268, c1866, c1256, c1865, c1258, c1261, c207, c1271, c1254] c1867 (by decide) p (sat_cons (step1253 p h) (sat_cons (step1268 p h) (sat_cons (step1866 p h) (sat_cons (step1256 p h) (sat_cons (step1865 p h) (sat_cons (step1258 p h) (sat_cons (step1261 p h) (sat_cons (step207 p h) (sat_cons (step1271 p h) (sat_cons (step1254 p h) (sat_nil p)))))))))))
def c1868 : List Lit := [(57, true), (74, false), (70, false), (108, false), (115, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c879, c325, c326, c302] c1868 (by decide) p (sat_cons (step879 p h) (sat_cons (step325 p h) (sat_cons (step326 p h) (sat_cons (step302 p h) (sat_nil p)))))
def c1869 : List Lit := [(1616, true), (115, true)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c862, c1211, c1213, c1209, c1205, c1206, c143, c155] c1869 (by decide) p (sat_cons (step862 p h) (sat_cons (step1211 p h) (sat_cons (step1213 p h) (sat_cons (step1209 p h) (sat_cons (step1205 p h) (sat_cons (step1206 p h) (sat_cons (step143 p h) (sat_cons (step155 p h) (sat_nil p)))))))))
def c1870 : List Lit := [(1582, true), (1576, false), (91, false), (1564, false)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c1126, c1149, c1153, c1862, c1127, c1122] c1870 (by decide) p (sat_cons (step1126 p h) (sat_cons (step1149 p h) (sat_cons (step1153 p h) (sat_cons (step1862 p h) (sat_cons (step1127 p h) (sat_cons (step1122 p h) (sat_nil p)))))))
def c1871 : List Lit := [(1829, true), (1788, false), (1803, false), (1795, false), (109, true), (117, true), (115, true)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c896, c1582, c1558, c1563, c1600, c1624, c1629, c1606, c1601, c1843, c1564, c1583, c1523, c1559, c1576, c742, c621] c1871 (by decide) p (sat_cons (step896 p h) (sat_cons (step1582 p h) (sat_cons (step1558 p h) (sat_cons (step1563 p h) (sat_cons (step1600 p h) (sat_cons (step1624 p h) (sat_cons (step1629 p h) (sat_cons (step1606 p h) (sat_cons (step1601 p h) (sat_cons (step1843 p h) (sat_cons (step1564 p h) (sat_cons (step1583 p h) (sat_cons (step1523 p h) (sat_cons (step1559 p h) (sat_cons (step1576 p h) (sat_cons (step742 p h) (sat_cons (step621 p h) (sat_nil p))))))))))))))))))
def c1872 : List Lit := [(1805, true), (101, true), (115, true)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c900, c1571, c1572, c832, c833, c1778] c1872 (by decide) p (sat_cons (step900 p h) (sat_cons (step1571 p h) (sat_cons (step1572 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step1778 p h) (sat_nil p)))))))
def c1873 : List Lit := [(51, false), (1594, true), (16, true)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c1779, c29, c6, c1831, c1120, c1818, c1129, c1825, c1175, c1157, c1153, c1130, c1138, c1122, c1861] c1873 (by decide) p (sat_cons (step1779 p h) (sat_cons (step29 p h) (sat_cons (step6 p h) (sat_cons (step1831 p h) (sat_cons (step1120 p h) (sat_cons (step1818 p h) (sat_cons (step1129 p h) (sat_cons (step1825 p h) (sat_cons (step1175 p h) (sat_cons (step1157 p h) (sat_cons (step1153 p h) (sat_cons (step1130 p h) (sat_cons (step1138 p h) (sat_cons (step1122 p h) (sat_cons (step1861 p h) (sat_nil p))))))))))))))))
def c1874 : List Lit := [(1758, true), (120, false), (1740, false), (1711, false), (1727, false), (119, true)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1827, c881, c1423, c1458, c1391, c1402, c1485, c1480, c1403, c1464, c1394, c1426, c1386, c1417, c355, c352] c1874 (by decide) p (sat_cons (step1827 p h) (sat_cons (step881 p h) (sat_cons (step1423 p h) (sat_cons (step1458 p h) (sat_cons (step1391 p h) (sat_cons (step1402 p h) (sat_cons (step1485 p h) (sat_cons (step1480 p h) (sat_cons (step1403 p h) (sat_cons (step1464 p h) (sat_cons (step1394 p h) (sat_cons (step1426 p h) (sat_cons (step1386 p h) (sat_cons (step1417 p h) (sat_cons (step355 p h) (sat_cons (step352 p h) (sat_nil p)))))))))))))))))
def c1875 : List Lit := [(72, false), (1820, true), (1808, false), (1798, false), (35, false), (110, false)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c594, c596, c1555, c1568, c1564, c1584, c1608] c1875 (by decide) p (sat_cons (step594 p h) (sat_cons (step596 p h) (sat_cons (step1555 p h) (sat_cons (step1568 p h) (sat_cons (step1564 p h) (sat_cons (step1584 p h) (sat_cons (step1608 p h) (sat_nil p))))))))
def c1876 : List Lit := [(1819, true), (1808, false), (1811, false), (1798, false), (35, false), (110, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1602, c1607, c1584, c1564, c1568, c1555, c601] c1876 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1602 p h) (sat_cons (step1607 p h) (sat_cons (step1584 p h) (sat_cons (step1564 p h) (sat_cons (step1568 p h) (sat_cons (step1555 p h) (sat_cons (step601 p h) (sat_nil p)))))))))
def c1877 : List Lit := [(1617, true), (42, true), (115, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c862, c1208, c1212, c1214, c1210, c1205, c1206, c143, c155] c1877 (by decide) p (sat_cons (step862 p h) (sat_cons (step1208 p h) (sat_cons (step1212 p h) (sat_cons (step1214 p h) (sat_cons (step1210 p h) (sat_cons (step1205 p h) (sat_cons (step1206 p h) (sat_cons (step143 p h) (sat_cons (step155 p h) (sat_nil p))))))))))
def c1878 : List Lit := [(1623, true), (1617, false), (42, true), (108, true), (43, true), (1604, false)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c859, c1199, c1226, c1230, c1200, c1195, c125, c124, c1727, c1847] c1878 (by decide) p (sat_cons (step859 p h) (sat_cons (step1199 p h) (sat_cons (step1226 p h) (sat_cons (step1230 p h) (sat_cons (step1200 p h) (sat_cons (step1195 p h) (sat_cons (step125 p h) (sat_cons (step124 p h) (sat_cons (step1727 p h) (sat_cons (step1847 p h) (sat_nil p)))))))))))
def c1879 : List Lit := [(46, true), (49, true), (1633, true)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c867, c1249, c1238, c1240, c1247, c1242, c201, c200, c1736] c1879 (by decide) p (sat_cons (step867 p h) (sat_cons (step1249 p h) (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1247 p h) (sat_cons (step1242 p h) (sat_cons (step201 p h) (sat_cons (step200 p h) (sat_cons (step1736 p h) (sat_nil p))))))))))
def c1880 : List Lit := [(48, false), (44, false), (46, false), (49, true)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c867, c200, c197] c1880 (by decide) p (sat_cons (step867 p h) (sat_cons (step200 p h) (sat_cons (step197 p h) (sat_nil p))))
def c1881 : List Lit := [(51, false), (1594, true), (1572, false)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1779, c29, c1140, c6, c1831, c1119, c1818, c1126, c1825, c1175, c1153, c1149, c1127, c1141, c1122, c1861] c1881 (by decide) p (sat_cons (step1779 p h) (sat_cons (step29 p h) (sat_cons (step1140 p h) (sat_cons (step6 p h) (sat_cons (step1831 p h) (sat_cons (step1119 p h) (sat_cons (step1818 p h) (sat_cons (step1126 p h) (sat_cons (step1825 p h) (sat_cons (step1175 p h) (sat_cons (step1153 p h) (sat_cons (step1149 p h) (sat_cons (step1127 p h) (sat_cons (step1141 p h) (sat_cons (step1122 p h) (sat_cons (step1861 p h) (sat_nil p)))))))))))))))))
def c1882 : List Lit := [(73, false), (79, true), (70, false), (1737, false), (1709, false), (113, false), (1760, true), (36, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c878, c1827, c883, c1441, c652, c319, c334, c335, c1388, c1419, c1394, c1428, c1403, c1487, c1469, c1465, c1429, c1445, c1420, c1421, c1431, c368, c365] c1882 (by decide) p (sat_cons (step878 p h) (sat_cons (step1827 p h) (sat_cons (step883 p h) (sat_cons (step1441 p h) (sat_cons (step652 p h) (sat_cons (step319 p h) (sat_cons (step334 p h) (sat_cons (step335 p h) (sat_cons (step1388 p h) (sat_cons (step1419 p h) (sat_cons (step1394 p h) (sat_cons (step1428 p h) (sat_cons (step1403 p h) (sat_cons (step1487 p h) (sat_cons (step1469 p h) (sat_cons (step1465 p h) (sat_cons (step1429 p h) (sat_cons (step1445 p h) (sat_cons (step1420 p h) (sat_cons (step1421 p h) (sat_cons (step1431 p h) (sat_cons (step368 p h) (sat_cons (step365 p h) (sat_nil p))))))))))))))))))))))))
def c1883 : List Lit := [(1726, false), (1748, true), (1737, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c883, c1441, c1469, c1428, c1429, c1465, c1420, c1421, c1445, c1431, c368, c365] c1883 (by decide) p (sat_cons (step883 p h) (sat_cons (step1441 p h) (sat_cons (step1469 p h) (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step1465 p h) (sat_cons (step1420 p h) (sat_cons (step1421 p h) (sat_cons (step1445 p h) (sat_cons (step1431 p h) (sat_cons (step368 p h) (sat_cons (step365 p h) (sat_nil p)))))))))))))
def c1884 : List Lit := [(1738, false), (1725, false), (1748, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c883, c1425, c1460, c1442, c1446, c1465, c1431, c1426, c368, c1420, c1421, c365] c1884 (by decide) p (sat_cons (step883 p h) (sat_cons (step1425 p h) (sat_cons (step1460 p h) (sat_cons (step1442 p h) (sat_cons (step1446 p h) (sat_cons (step1465 p h) (sat_cons (step1431 p h) (sat_cons (step1426 p h) (sat_cons (step368 p h) (sat_cons (step1420 p h) (sat_cons (step1421 p h) (sat_cons (step365 p h) (sat_nil p)))))))))))))
def c1885 : List Lit := [(1701, true), (68, false)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c874, c1371, c1372, c267, c269] c1885 (by decide) p (sat_cons (step874 p h) (sat_cons (step1371 p h) (sat_cons (step1372 p h) (sat_cons (step267 p h) (sat_cons (step269 p h) (sat_nil p))))))
def c1886 : List Lit := [(1623, false), (1663, true), (1572, false), (1644, false), (1686, true)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c1275, c1312, c1313, c1337, c1280, c1881, c1244, c1241] c1886 (by decide) p (sat_cons (step1275 p h) (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step1337 p h) (sat_cons (step1280 p h) (sat_cons (step1881 p h) (sat_cons (step1244 p h) (sat_cons (step1241 p h) (sat_nil p)))))))))
def c1887 : List Lit := [(1641, true), (57, false), (115, true), (74, false), (70, false)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c1259, c1866, c1256, c1257, c1261, c249] c1887 (by decide) p (sat_cons (step1259 p h) (sat_cons (step1866 p h) (sat_cons (step1256 p h) (sat_cons (step1257 p h) (sat_cons (step1261 p h) (sat_cons (step249 p h) (sat_nil p)))))))
def c1888 : List Lit := [(1581, true), (1572, false)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c1140, c1146, c1148, c1141, c1124, c1861, c1122] c1888 (by decide) p (sat_cons (step1140 p h) (sat_cons (step1146 p h) (sat_cons (step1148 p h) (sat_cons (step1141 p h) (sat_cons (step1124 p h) (sat_cons (step1861 p h) (sat_cons (step1122 p h) (sat_nil p))))))))
def c1889 : List Lit := [(1582, true), (1577, false), (18, false), (21, true)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c854, c1861, c1147, c1149, c1144, c1126, c1134, c1118, c78, c44] c1889 (by decide) p (sat_cons (step854 p h) (sat_cons (step1861 p h) (sat_cons (step1147 p h) (sat_cons (step1149 p h) (sat_cons (step1144 p h) (sat_cons (step1126 p h) (sat_cons (step1134 p h) (sat_cons (step1118 p h) (sat_cons (step78 p h) (sat_cons (step44 p h) (sat_nil p)))))))))))
def c1890 : List Lit := [(36, true), (1617, true), (38, false), (33, false)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c1216, c1206, c1207, c1214, c154, c1209] c1890 (by decide) p (sat_cons (step1216 p h) (sat_cons (step1206 p h) (sat_cons (step1207 p h) (sat_cons (step1214 p h) (sat_cons (step154 p h) (sat_cons (step1209 p h) (sat_nil p)))))))
def c1891 : List Lit := [(1617, true), (38, false), (33, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c1890, c152, c153, c1205, c1209, c1214] c1891 (by decide) p (sat_cons (step1890 p h) (sat_cons (step152 p h) (sat_cons (step153 p h) (sat_cons (step1205 p h) (sat_cons (step1209 p h) (sat_cons (step1214 p h) (sat_nil p)))))))
def c1892 : List Lit := [(51, false), (1595, true), (1577, false), (1566, false)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c1779, c29, c6, c1831, c1119, c1818, c1127, c1825, c1154, c1176] c1892 (by decide) p (sat_cons (step1779 p h) (sat_cons (step29 p h) (sat_cons (step6 p h) (sat_cons (step1831 p h) (sat_cons (step1119 p h) (sat_cons (step1818 p h) (sat_cons (step1127 p h) (sat_cons (step1825 p h) (sat_cons (step1154 p h) (sat_cons (step1176 p h) (sat_nil p)))))))))))
def c1893 : List Lit := [(1583, true), (1566, false), (1577, false), (1574, false), (21, true)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c854, c1124, c1150, c1154, c1144, c1127, c1134, c1118, c77, c78, c1722] c1893 (by decide) p (sat_cons (step854 p h) (sat_cons (step1124 p h) (sat_cons (step1150 p h) (sat_cons (step1154 p h) (sat_cons (step1144 p h) (sat_cons (step1127 p h) (sat_cons (step1134 p h) (sat_cons (step1118 p h) (sat_cons (step77 p h) (sat_cons (step78 p h) (sat_cons (step1722 p h) (sat_nil p))))))))))))
def c1894 : List Lit := [(1617, true), (39, false), (42, true), (35, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c1208, c1212, c1214, c1210, c1206, c157] c1894 (by decide) p (sat_cons (step1208 p h) (sat_cons (step1212 p h) (sat_cons (step1214 p h) (sat_cons (step1210 p h) (sat_cons (step1206 p h) (sat_cons (step157 p h) (sat_nil p)))))))
def c1895 : List Lit := [(15, false), (1541, true)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c1779, c29, c2, c4, c1093] c1895 (by decide) p (sat_cons (step1779 p h) (sat_cons (step29 p h) (sat_cons (step2 p h) (sat_cons (step4 p h) (sat_cons (step1093 p h) (sat_nil p))))))
def c1896 : List Lit := [(23, false), (16, false)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c854, c77, c78, c1722] c1896 (by decide) p (sat_cons (step854 p h) (sat_cons (step77 p h) (sat_cons (step78 p h) (sat_cons (step1722 p h) (sat_nil p)))))
def c1897 : List Lit := [(40, true), (49, false), (36, true), (117, true), (39, false)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c1790, c205, c161, c967, c949, c968, c950, c972, c952, c980, c966, c983] c1897 (by decide) p (sat_cons (step1790 p h) (sat_cons (step205 p h) (sat_cons (step161 p h) (sat_cons (step967 p h) (sat_cons (step949 p h) (sat_cons (step968 p h) (sat_cons (step950 p h) (sat_cons (step972 p h) (sat_cons (step952 p h) (sat_cons (step980 p h) (sat_cons (step966 p h) (sat_cons (step983 p h) (sat_nil p)))))))))))))
def c1898 : List Lit := [(126, true), (1818, true), (122, true), (124, false), (1797, false), (46, false)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1596, c1581, c1578, c1571, c1573, c1577, c806, c1580, c1554, c1601, c1563] c1898 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1596 p h) (sat_cons (step1581 p h) (sat_cons (step1578 p h) (sat_cons (step1571 p h) (sat_cons (step1573 p h) (sat_cons (step1577 p h) (sat_cons (step806 p h) (sat_cons (step1580 p h) (sat_cons (step1554 p h) (sat_cons (step1601 p h) (sat_cons (step1563 p h) (sat_nil p)))))))))))))
def c1899 : List Lit := [(1819, true), (113, true), (1808, false), (34, true), (35, false)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c860, c133, c134, c1731, c1558, c1554, c1563, c1580, c1602, c1607, c1584, c1566, c1568, c1556, c601] c1899 (by decide) p (sat_cons (step860 p h) (sat_cons (step133 p h) (sat_cons (step134 p h) (sat_cons (step1731 p h) (sat_cons (step1558 p h) (sat_cons (step1554 p h) (sat_cons (step1563 p h) (sat_cons (step1580 p h) (sat_cons (step1602 p h) (sat_cons (step1607 p h) (sat_cons (step1584 p h) (sat_cons (step1566 p h) (sat_cons (step1568 p h) (sat_cons (step1556 p h) (sat_cons (step601 p h) (sat_nil p))))))))))))))))
def c1900 : List Lit := [(1775, true), (90, true)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c891, c1510, c1512, c1507, c1508, c1504, c474, c496] c1900 (by decide) p (sat_cons (step891 p h) (sat_cons (step1510 p h) (sat_cons (step1512 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step1504 p h) (sat_cons (step474 p h) (sat_cons (step496 p h) (sat_nil p)))))))))
def c1901 : List Lit := [(110, false), (109, false), (1821, true), (1798, false), (1808, false), (113, true), (35, false)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c597, c599, c1556, c1568, c1567, c1584, c1614] c1901 (by decide) p (sat_cons (step597 p h) (sat_cons (step599 p h) (sat_cons (step1556 p h) (sat_cons (step1568 p h) (sat_cons (step1567 p h) (sat_cons (step1584 p h) (sat_cons (step1614 p h) (sat_nil p))))))))
def c1902 : List Lit := [(1775, true), (109, false), (86, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c1510, c1900, c1507, c441] c1902 (by decide) p (sat_cons (step1510 p h) (sat_cons (step1900 p h) (sat_cons (step1507 p h) (sat_cons (step441 p h) (sat_nil p)))))
def c1903 : List Lit := [(1739, false), (1748, true)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c883, c1455, c1443, c1447, c1460, c1431, c1423, c368, c1420, c1421, c365] c1903 (by decide) p (sat_cons (step883 p h) (sat_cons (step1455 p h) (sat_cons (step1443 p h) (sat_cons (step1447 p h) (sat_cons (step1460 p h) (sat_cons (step1431 p h) (sat_cons (step1423 p h) (sat_cons (step368 p h) (sat_cons (step1420 p h) (sat_cons (step1421 p h) (sat_cons (step365 p h) (sat_nil p))))))))))))
def c1904 : List Lit := [(1788, true), (1781, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c891, c1524, c1533, c1537, c1527, c1510, c1512, c1507, c1508, c1504, c474, c1848, c494] c1904 (by decide) p (sat_cons (step891 p h) (sat_cons (step1524 p h) (sat_cons (step1533 p h) (sat_cons (step1537 p h) (sat_cons (step1527 p h) (sat_cons (step1510 p h) (sat_cons (step1512 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step1504 p h) (sat_cons (step474 p h) (sat_cons (step1848 p h) (sat_cons (step494 p h) (sat_nil p))))))))))))))
def c1905 : List Lit := [(1737, false), (1746, true), (1741, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c883, c1441, c1445, c1458, c1431, c1423, c368, c1420, c1421, c365] c1905 (by decide) p (sat_cons (step883 p h) (sat_cons (step1441 p h) (sat_cons (step1445 p h) (sat_cons (step1458 p h) (sat_cons (step1431 p h) (sat_cons (step1423 p h) (sat_cons (step368 p h) (sat_cons (step1420 p h) (sat_cons (step1421 p h) (sat_cons (step365 p h) (sat_nil p)))))))))))
def c1906 : List Lit := [(1789, true), (109, false), (98, true), (1781, false), (86, false)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c891, c1508, c1510, c1524, c1542, c1538, c1511, c1527, c1509, c441, c1848, c495] c1906 (by decide) p (sat_cons (step891 p h) (sat_cons (step1508 p h) (sat_cons (step1510 p h) (sat_cons (step1524 p h) (sat_cons (step1542 p h) (sat_cons (step1538 p h) (sat_cons (step1511 p h) (sat_cons (step1527 p h) (sat_cons (step1509 p h) (sat_cons (step441 p h) (sat_cons (step1848 p h) (sat_cons (step495 p h) (sat_nil p)))))))))))))
end B112E034
