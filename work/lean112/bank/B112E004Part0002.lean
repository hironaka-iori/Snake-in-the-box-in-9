import B112E004Part0001
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1862 : List Lit := [(265, true), (1, false), (12, true)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c776, c858, c860, c854, c842, c853, c836, c850, c2, c38, c3] c1862 (by decide) p (sat_cons (step776 p h) (sat_cons (step858 p h) (sat_cons (step860 p h) (sat_cons (step854 p h) (sat_cons (step842 p h) (sat_cons (step853 p h) (sat_cons (step836 p h) (sat_cons (step850 p h) (sat_cons (step2 p h) (sat_cons (step38 p h) (sat_cons (step3 p h) (sat_nil p))))))))))))
def c1863 : List Lit := [(255, false), (1, false), (12, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c1760, c1751, c776, c855, c856, c861, c853, c842, c850, c836, c38, c2, c3] c1863 (by decide) p (sat_cons (step1760 p h) (sat_cons (step1751 p h) (sat_cons (step776 p h) (sat_cons (step855 p h) (sat_cons (step856 p h) (sat_cons (step861 p h) (sat_cons (step853 p h) (sat_cons (step842 p h) (sat_cons (step850 p h) (sat_cons (step836 p h) (sat_cons (step38 p h) (sat_cons (step2 p h) (sat_cons (step3 p h) (sat_nil p))))))))))))))
def c1864 : List Lit := [(61, false), (1592, true), (39, true), (73, true), (51, false), (70, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c806, c479, c522, c523, c1387, c1390, c1398] c1864 (by decide) p (sat_cons (step806 p h) (sat_cons (step479 p h) (sat_cons (step522 p h) (sat_cons (step523 p h) (sat_cons (step1387 p h) (sat_cons (step1390 p h) (sat_cons (step1398 p h) (sat_nil p))))))))
def c1865 : List Lit := [(21, true), (1468, true), (1480, true), (24, true), (29, false), (265, false)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c1743, c1739, c783, c786, c789, c1147, c888, c940, c934, c910, c896, c895, c894, c889, c884, c868, c864, c862, c882, c879, c872, c869, c1136, c64, c66, c1133, c1856, c1141, c77, c1168, c150, c144, c1155, c103, c1150] c1865 (by decide) p (sat_cons (step1743 p h) (sat_cons (step1739 p h) (sat_cons (step783 p h) (sat_cons (step786 p h) (sat_cons (step789 p h) (sat_cons (step1147 p h) (sat_cons (step888 p h) (sat_cons (step940 p h) (sat_cons (step934 p h) (sat_cons (step910 p h) (sat_cons (step896 p h) (sat_cons (step895 p h) (sat_cons (step894 p h) (sat_cons (step889 p h) (sat_cons (step884 p h) (sat_cons (step868 p h) (sat_cons (step864 p h) (sat_cons (step862 p h) (sat_cons (step882 p h) (sat_cons (step879 p h) (sat_cons (step872 p h) (sat_cons (step869 p h) (sat_cons (step1136 p h) (sat_cons (step64 p h) (sat_cons (step66 p h) (sat_cons (step1133 p h) (sat_cons (step1856 p h) (sat_cons (step1141 p h) (sat_cons (step77 p h) (sat_cons (step1168 p h) (sat_cons (step150 p h) (sat_cons (step144 p h) (sat_cons (step1155 p h) (sat_cons (step103 p h) (sat_cons (step1150 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1866 : List Lit := [(5, false), (1512, true), (39, false), (38, true), (44, true), (51, false)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c194, c197, c1209, c1212, c1220] c1866 (by decide) p (sat_cons (step194 p h) (sat_cons (step197 p h) (sat_cons (step1209 p h) (sat_cons (step1212 p h) (sat_cons (step1220 p h) (sat_nil p))))))
def c1867 : List Lit := [(1530, true), (65, false), (73, false), (1581, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1789, c494, c1379] c1867 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1789 p h) (sat_cons (step494 p h) (sat_cons (step1379 p h) (sat_nil p)))))
def c1868 : List Lit := [(1612, true), (97, false)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1861, c1428, c1429, c587] c1868 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1861 p h) (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step587 p h) (sat_nil p))))))
def c1869 : List Lit := [(1610, true), (88, false), (97, false)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c1428, c1429, c587] c1869 (by decide) p (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step587 p h) (sat_nil p))))
def c1870 : List Lit := [(67, false), (71, false), (50, true), (44, false), (51, false)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c811, c524, c500, c518] c1870 (by decide) p (sat_cons (step811 p h) (sat_cons (step524 p h) (sat_cons (step500 p h) (sat_cons (step518 p h) (sat_nil p)))))
def c1871 : List Lit := [(1591, true), (73, true), (50, true), (44, false), (70, true), (51, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1385, c1395, c1397, c1390, c1870, c1387] c1871 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1385 p h) (sat_cons (step1395 p h) (sat_cons (step1397 p h) (sat_cons (step1390 p h) (sat_cons (step1870 p h) (sat_cons (step1387 p h) (sat_nil p))))))))
def c1872 : List Lit := [(61, false), (72, true), (42, false), (51, false)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c806, c218, c479] c1872 (by decide) p (sat_cons (step806 p h) (sat_cons (step218 p h) (sat_cons (step479 p h) (sat_nil p))))
def c1873 : List Lit := [(1690, true), (1649, false), (100, false), (52, false)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1603, c1859, c1527, c1500, c1523, c662, c1820, c1512, c1598, c1520, c1526] c1873 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1603 p h) (sat_cons (step1859 p h) (sat_cons (step1527 p h) (sat_cons (step1500 p h) (sat_cons (step1523 p h) (sat_cons (step662 p h) (sat_cons (step1820 p h) (sat_cons (step1512 p h) (sat_cons (step1598 p h) (sat_cons (step1520 p h) (sat_cons (step1526 p h) (sat_nil p)))))))))))))
def c1874 : List Lit := [(1602, true), (71, false), (15, true), (1490, true)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c815, c784, c1417, c1845, c558, c1777, c127, c130, c118, c1136, c1149, c1111, c1138, c1113, c1121, c1190, c1168, c1166, c1141, c1158, c1132, c1133, c1148, c72, c67] c1874 (by decide) p (sat_cons (step815 p h) (sat_cons (step784 p h) (sat_cons (step1417 p h) (sat_cons (step1845 p h) (sat_cons (step558 p h) (sat_cons (step1777 p h) (sat_cons (step127 p h) (sat_cons (step130 p h) (sat_cons (step118 p h) (sat_cons (step1136 p h) (sat_cons (step1149 p h) (sat_cons (step1111 p h) (sat_cons (step1138 p h) (sat_cons (step1113 p h) (sat_cons (step1121 p h) (sat_cons (step1190 p h) (sat_cons (step1168 p h) (sat_cons (step1166 p h) (sat_cons (step1141 p h) (sat_cons (step1158 p h) (sat_cons (step1132 p h) (sat_cons (step1133 p h) (sat_cons (step1148 p h) (sat_cons (step72 p h) (sat_cons (step67 p h) (sat_nil p))))))))))))))))))))))))))
def c1875 : List Lit := [(1455, true), (15, true), (42, false), (51, false)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c778, c1109, c1112, c1121, c1125, c1113, c1115, c1101, c1111, c1107, c1098, c48, c7, c197, c14] c1875 (by decide) p (sat_cons (step778 p h) (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1121 p h) (sat_cons (step1125 p h) (sat_cons (step1113 p h) (sat_cons (step1115 p h) (sat_cons (step1101 p h) (sat_cons (step1111 p h) (sat_cons (step1107 p h) (sat_cons (step1098 p h) (sat_cons (step48 p h) (sat_cons (step7 p h) (sat_cons (step197 p h) (sat_cons (step14 p h) (sat_nil p))))))))))))))))
def c1876 : List Lit := [(1500, true), (1507, true), (51, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c792, c1211, c1210, c1199, c1200, c153, c206, c162] c1876 (by decide) p (sat_cons (step792 p h) (sat_cons (step1211 p h) (sat_cons (step1210 p h) (sat_cons (step1199 p h) (sat_cons (step1200 p h) (sat_cons (step153 p h) (sat_cons (step206 p h) (sat_cons (step162 p h) (sat_nil p)))))))))
def c1877 : List Lit := [(1657, true), (1649, false), (100, false), (52, false)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1818, c1500, c662, c658, c1512, c1497, c1520, c1505, c1531] c1877 (by decide) p (sat_cons (step1818 p h) (sat_cons (step1500 p h) (sat_cons (step662 p h) (sat_cons (step658 p h) (sat_cons (step1512 p h) (sat_cons (step1497 p h) (sat_cons (step1520 p h) (sat_cons (step1505 p h) (sat_cons (step1531 p h) (sat_nil p))))))))))
def c1878 : List Lit := [(1663, true), (38, false), (1676, true), (1611, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c829, c1571, c1546, c1547, c1783, c726, c720, c1561, c1562, c1569, c1802, c1564] c1878 (by decide) p (sat_cons (step829 p h) (sat_cons (step1571 p h) (sat_cons (step1546 p h) (sat_cons (step1547 p h) (sat_cons (step1783 p h) (sat_cons (step726 p h) (sat_cons (step720 p h) (sat_cons (step1561 p h) (sat_cons (step1562 p h) (sat_cons (step1569 p h) (sat_cons (step1802 p h) (sat_cons (step1564 p h) (sat_nil p)))))))))))))
def c1879 : List Lit := [(1590, true), (73, true), (50, true), (51, false), (44, false)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1392, c1394, c1816, c1390, c1386, c500] c1879 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1392 p h) (sat_cons (step1394 p h) (sat_cons (step1816 p h) (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step500 p h) (sat_nil p))))))))
def c1880 : List Lit := [(109, false), (1603, true), (1550, false), (1612, false), (1691, false), (1595, false)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1677, c1824, c1827, c1420, c1136, c1444, c1799, c1479, c1183, c1645, c1347, c1671] c1880 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1677 p h) (sat_cons (step1824 p h) (sat_cons (step1827 p h) (sat_cons (step1420 p h) (sat_cons (step1136 p h) (sat_cons (step1444 p h) (sat_cons (step1799 p h) (sat_cons (step1479 p h) (sat_cons (step1183 p h) (sat_cons (step1645 p h) (sat_cons (step1347 p h) (sat_cons (step1671 p h) (sat_nil p))))))))))))))
def c1881 : List Lit := [(1692, false), (1550, false), (1612, false), (1595, false)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1677, c1841, c1337, c1670, c1439, c1478, c1640, c1646, c1671, c1479, c1347, c1444, c1183, c1420, c1774] c1881 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1677 p h) (sat_cons (step1841 p h) (sat_cons (step1337 p h) (sat_cons (step1670 p h) (sat_cons (step1439 p h) (sat_cons (step1478 p h) (sat_cons (step1640 p h) (sat_cons (step1646 p h) (sat_cons (step1671 p h) (sat_cons (step1479 p h) (sat_cons (step1347 p h) (sat_cons (step1444 p h) (sat_cons (step1183 p h) (sat_cons (step1420 p h) (sat_cons (step1774 p h) (sat_nil p)))))))))))))))))
def c1882 : List Lit := [(1658, true), (1650, false), (100, false), (102, true), (52, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c1511, c1521, c1528, c1532, c1524, c1503, c1513, c1500, c662] c1882 (by decide) p (sat_cons (step1511 p h) (sat_cons (step1521 p h) (sat_cons (step1528 p h) (sat_cons (step1532 p h) (sat_cons (step1524 p h) (sat_cons (step1503 p h) (sat_cons (step1513 p h) (sat_cons (step1500 p h) (sat_cons (step662 p h) (sat_nil p))))))))))
def c1883 : List Lit := [(1692, false), (1551, false), (1612, false), (1594, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1677, c1841, c1338, c1671, c1439, c1471, c1634, c1640, c1672, c1472, c1348, c1444, c1183, c1420, c1774] c1883 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1677 p h) (sat_cons (step1841 p h) (sat_cons (step1338 p h) (sat_cons (step1671 p h) (sat_cons (step1439 p h) (sat_cons (step1471 p h) (sat_cons (step1634 p h) (sat_cons (step1640 p h) (sat_cons (step1672 p h) (sat_cons (step1472 p h) (sat_cons (step1348 p h) (sat_cons (step1444 p h) (sat_cons (step1183 p h) (sat_cons (step1420 p h) (sat_cons (step1774 p h) (sat_nil p)))))))))))))))))
def c1884 : List Lit := [(73, true), (42, false), (51, false), (1594, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c806, c1400, c1392, c1388, c1390, c1391, c1394, c1404, c1386, c1382, c524, c218, c479] c1884 (by decide) p (sat_cons (step806 p h) (sat_cons (step1400 p h) (sat_cons (step1392 p h) (sat_cons (step1388 p h) (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step1394 p h) (sat_cons (step1404 p h) (sat_cons (step1386 p h) (sat_cons (step1382 p h) (sat_cons (step524 p h) (sat_cons (step218 p h) (sat_cons (step479 p h) (sat_nil p))))))))))))))
def c1885 : List Lit := [(61, false), (42, false), (51, false), (1590, true)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c806, c218, c479, c522, c523, c1386, c1389, c1394] c1885 (by decide) p (sat_cons (step806 p h) (sat_cons (step218 p h) (sat_cons (step479 p h) (sat_cons (step522 p h) (sat_cons (step523 p h) (sat_cons (step1386 p h) (sat_cons (step1389 p h) (sat_cons (step1394 p h) (sat_nil p)))))))))
def c1886 : List Lit := [(84, false), (1691, true), (105, false), (1664, false)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c1813, c820, c1834, c1550, c1558, c1586, c1595, c1525, c1529, c1519, c1503, c1505, c1511, c1512, c1500, c1497, c1498, c654, c592, c616, c603] c1886 (by decide) p (sat_cons (step1813 p h) (sat_cons (step820 p h) (sat_cons (step1834 p h) (sat_cons (step1550 p h) (sat_cons (step1558 p h) (sat_cons (step1586 p h) (sat_cons (step1595 p h) (sat_cons (step1525 p h) (sat_cons (step1529 p h) (sat_cons (step1519 p h) (sat_cons (step1503 p h) (sat_cons (step1505 p h) (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step1500 p h) (sat_cons (step1497 p h) (sat_cons (step1498 p h) (sat_cons (step654 p h) (sat_cons (step592 p h) (sat_cons (step616 p h) (sat_cons (step603 p h) (sat_nil p))))))))))))))))))))))
def c1887 : List Lit := [(1655, true), (109, false)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c820, c1525, c1529, c1519, c1503, c1505, c1511, c1512, c1500, c1497, c1498, c654, c600, c616, c603] c1887 (by decide) p (sat_cons (step820 p h) (sat_cons (step1525 p h) (sat_cons (step1529 p h) (sat_cons (step1519 p h) (sat_cons (step1503 p h) (sat_cons (step1505 p h) (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step1500 p h) (sat_cons (step1497 p h) (sat_cons (step1498 p h) (sat_cons (step654 p h) (sat_cons (step600 p h) (sat_cons (step616 p h) (sat_cons (step603 p h) (sat_nil p))))))))))))))))
def c1888 : List Lit := [(97, false), (102, false), (1610, true)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c818, c1429, c1869, c633, c574] c1888 (by decide) p (sat_cons (step818 p h) (sat_cons (step1429 p h) (sat_cons (step1869 p h) (sat_cons (step633 p h) (sat_cons (step574 p h) (sat_nil p))))))
def c1889 : List Lit := [(1651, true), (1610, true), (1644, true)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c826, c1428, c1504, c1517, c1519, c1515, c1511, c1512, c1888, c1501, c1502, c1506, c674, c1497, c704, c620] c1889 (by decide) p (sat_cons (step826 p h) (sat_cons (step1428 p h) (sat_cons (step1504 p h) (sat_cons (step1517 p h) (sat_cons (step1519 p h) (sat_cons (step1515 p h) (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step1888 p h) (sat_cons (step1501 p h) (sat_cons (step1502 p h) (sat_cons (step1506 p h) (sat_cons (step674 p h) (sat_cons (step1497 p h) (sat_cons (step704 p h) (sat_cons (step620 p h) (sat_nil p)))))))))))))))))
def c1890 : List Lit := [(1593, false), (1608, false), (1627, true), (1710, true), (1604, false), (1681, false)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c819, c1433, c1444, c1465, c1633, c1599, c1526, c1534, c1466, c1445, c1434, c1428, c1889, c1530, c1503, c1505, c1501, c1497, c1869, c1888, c578, c1511, c620, c1520, c1515] c1890 (by decide) p (sat_cons (step819 p h) (sat_cons (step1433 p h) (sat_cons (step1444 p h) (sat_cons (step1465 p h) (sat_cons (step1633 p h) (sat_cons (step1599 p h) (sat_cons (step1526 p h) (sat_cons (step1534 p h) (sat_cons (step1466 p h) (sat_cons (step1445 p h) (sat_cons (step1434 p h) (sat_cons (step1428 p h) (sat_cons (step1889 p h) (sat_cons (step1530 p h) (sat_cons (step1503 p h) (sat_cons (step1505 p h) (sat_cons (step1501 p h) (sat_cons (step1497 p h) (sat_cons (step1869 p h) (sat_cons (step1888 p h) (sat_cons (step578 p h) (sat_cons (step1511 p h) (sat_cons (step620 p h) (sat_cons (step1520 p h) (sat_cons (step1515 p h) (sat_nil p))))))))))))))))))))))))))
def c1891 : List Lit := [(120, false), (102, false), (1682, true), (111, false), (1664, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c833, c1557, c1582, c1850, c774, c1563, c1569, c1560, c1561, c758, c747] c1891 (by decide) p (sat_cons (step833 p h) (sat_cons (step1557 p h) (sat_cons (step1582 p h) (sat_cons (step1850 p h) (sat_cons (step774 p h) (sat_cons (step1563 p h) (sat_cons (step1569 p h) (sat_cons (step1560 p h) (sat_cons (step1561 p h) (sat_cons (step758 p h) (sat_cons (step747 p h) (sat_nil p))))))))))))
def c1892 : List Lit := [(119, true), (1676, true)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c833, c1567, c1563, c1565, c1569, c1560, c1561, c758, c747] c1892 (by decide) p (sat_cons (step833 p h) (sat_cons (step1567 p h) (sat_cons (step1563 p h) (sat_cons (step1565 p h) (sat_cons (step1569 p h) (sat_cons (step1560 p h) (sat_cons (step1561 p h) (sat_cons (step758 p h) (sat_cons (step747 p h) (sat_nil p))))))))))
def c1893 : List Lit := [(1593, false), (1626, true), (1649, false), (1710, true), (1604, false), (1681, false)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c1443, c1464, c1465, c1628, c1444, c1605, c1868, c1844] c1893 (by decide) p (sat_cons (step1443 p h) (sat_cons (step1464 p h) (sat_cons (step1465 p h) (sat_cons (step1628 p h) (sat_cons (step1444 p h) (sat_cons (step1605 p h) (sat_cons (step1868 p h) (sat_cons (step1844 p h) (sat_nil p)))))))))
def c1894 : List Lit := [(1612, true), (216, true), (102, true)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c818, c1431, c1861, c1868, c1428, c1429, c1725, c635, c575] c1894 (by decide) p (sat_cons (step818 p h) (sat_cons (step1431 p h) (sat_cons (step1861 p h) (sat_cons (step1868 p h) (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step1725 p h) (sat_cons (step635 p h) (sat_cons (step575 p h) (sat_nil p))))))))))
def c1895 : List Lit := [(1657, true), (1649, false), (102, true), (109, false)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c821, c1511, c1520, c1527, c1531, c1523, c1503, c1505, c1513, c1500, c1497, c1498, c616, c600, c668, c612] c1895 (by decide) p (sat_cons (step821 p h) (sat_cons (step1511 p h) (sat_cons (step1520 p h) (sat_cons (step1527 p h) (sat_cons (step1531 p h) (sat_cons (step1523 p h) (sat_cons (step1503 p h) (sat_cons (step1505 p h) (sat_cons (step1513 p h) (sat_cons (step1500 p h) (sat_cons (step1497 p h) (sat_cons (step1498 p h) (sat_cons (step616 p h) (sat_cons (step600 p h) (sat_cons (step668 p h) (sat_cons (step612 p h) (sat_nil p)))))))))))))))))
def c1896 : List Lit := [(101, false), (98, false), (89, true), (90, false), (91, false)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c821, c616, c668, c612] c1896 (by decide) p (sat_cons (step821 p h) (sat_cons (step616 p h) (sat_cons (step668 p h) (sat_cons (step612 p h) (sat_nil p)))))
def c1897 : List Lit := [(1589, true), (61, false), (39, true)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1393, c1389, c1386, c1793] c1897 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step1389 p h) (sat_cons (step1386 p h) (sat_cons (step1793 p h) (sat_nil p))))))
def c1898 : List Lit := [(56, false), (1526, true), (51, true), (55, false), (103, false)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c440, c434, c1244, c1239, c1249] c1898 (by decide) p (sat_cons (step440 p h) (sat_cons (step434 p h) (sat_cons (step1244 p h) (sat_cons (step1239 p h) (sat_cons (step1249 p h) (sat_nil p))))))
def c1899 : List Lit := [(1525, true), (51, true), (55, false), (103, false)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c1243, c1246, c1248, c1244, c1239, c429] c1899 (by decide) p (sat_cons (step1243 p h) (sat_cons (step1246 p h) (sat_cons (step1248 p h) (sat_cons (step1244 p h) (sat_cons (step1239 p h) (sat_cons (step429 p h) (sat_nil p)))))))
def c1900 : List Lit := [(1540, true), (53, true), (1530, false), (51, true), (55, false), (103, false)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c1254, c1262, c1899, c1283, c1279, c1898, c1265, c1255] c1900 (by decide) p (sat_cons (step1254 p h) (sat_cons (step1262 p h) (sat_cons (step1899 p h) (sat_cons (step1283 p h) (sat_cons (step1279 p h) (sat_cons (step1898 p h) (sat_cons (step1265 p h) (sat_cons (step1255 p h) (sat_nil p)))))))))
def c1901 : List Lit := [(1506, false), (1511, true), (1516, true), (34, false), (84, false)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c1218, c1219, c1232, c1210, c1203, c155, c156, c1201] c1901 (by decide) p (sat_cons (step1218 p h) (sat_cons (step1219 p h) (sat_cons (step1232 p h) (sat_cons (step1210 p h) (sat_cons (step1203 p h) (sat_cons (step155 p h) (sat_cons (step156 p h) (sat_cons (step1201 p h) (sat_nil p)))))))))
def c1902 : List Lit := [(1593, false), (1550, false), (1613, false), (1692, false), (109, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1677, c1841, c1337, c1670, c1646, c1824, c1420, c1445, c1466, c1640, c1671, c1347, c1183, c1799, c1467, c1136, c1450, c1827, c1421] c1902 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1677 p h) (sat_cons (step1841 p h) (sat_cons (step1337 p h) (sat_cons (step1670 p h) (sat_cons (step1646 p h) (sat_cons (step1824 p h) (sat_cons (step1420 p h) (sat_cons (step1445 p h) (sat_cons (step1466 p h) (sat_cons (step1640 p h) (sat_cons (step1671 p h) (sat_cons (step1347 p h) (sat_cons (step1183 p h) (sat_cons (step1799 p h) (sat_cons (step1467 p h) (sat_cons (step1136 p h) (sat_cons (step1450 p h) (sat_cons (step1827 p h) (sat_cons (step1421 p h) (sat_nil p)))))))))))))))))))))
def c1903 : List Lit := [(2, false), (11, true)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c776, c3] c1903 (by decide) p (sat_cons (step776 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1904 : List Lit := [(2, false), (1, true)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c776, c4] c1904 (by decide) p (sat_cons (step776 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1905 : List Lit := [(3, false), (8, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c777, c5] c1905 (by decide) p (sat_cons (step777 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1906 : List Lit := [(3, false), (1, true)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c777, c6] c1906 (by decide) p (sat_cons (step777 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1907 : List Lit := [(5, false), (7, true), (14, true), (39, true)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c778, c13] c1907 (by decide) p (sat_cons (step778 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1908 : List Lit := [(4, true), (5, false), (39, true), (14, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c778, c14] c1908 (by decide) p (sat_cons (step778 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1909 : List Lit := [(4, true), (5, false), (39, true), (7, true)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c778, c15] c1909 (by decide) p (sat_cons (step778 p h) (sat_cons (step15 p h) (sat_nil p)))
def c1910 : List Lit := [(4, true), (5, false), (14, true), (7, true)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c778, c16] c1910 (by decide) p (sat_cons (step778 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1911 : List Lit := [(4, true), (6, false), (7, true)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c779, c20] c1911 (by decide) p (sat_cons (step779 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1912 : List Lit := [(10, true), (12, false), (16, true), (49, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c780, c41] c1912 (by decide) p (sat_cons (step780 p h) (sat_cons (step41 p h) (sat_nil p)))
def c1913 : List Lit := [(13, false), (14, true), (9, true), (29, true), (50, true)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c781, c43] c1913 (by decide) p (sat_cons (step781 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1914 : List Lit := [(4, true), (14, true), (13, false), (29, true), (50, true)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c781, c44] c1914 (by decide) p (sat_cons (step781 p h) (sat_cons (step44 p h) (sat_nil p)))
def c1915 : List Lit := [(4, true), (13, false), (50, true), (29, true), (9, true)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c781, c45] c1915 (by decide) p (sat_cons (step781 p h) (sat_cons (step45 p h) (sat_nil p)))
def c1916 : List Lit := [(4, true), (13, false), (9, true), (14, true), (50, true)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c781, c46] c1916 (by decide) p (sat_cons (step781 p h) (sat_cons (step46 p h) (sat_nil p)))
def c1917 : List Lit := [(13, false), (4, true), (9, true), (14, true), (29, true)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c781, c47] c1917 (by decide) p (sat_cons (step781 p h) (sat_cons (step47 p h) (sat_nil p)))
def c1918 : List Lit := [(16, true), (55, true), (15, false)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c782, c53] c1918 (by decide) p (sat_cons (step782 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1919 : List Lit := [(8, true), (55, true), (15, false)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c782, c54] c1919 (by decide) p (sat_cons (step782 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1920 : List Lit := [(18, false), (19, true)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c783, c65] c1920 (by decide) p (sat_cons (step783 p h) (sat_cons (step65 p h) (sat_nil p)))
def c1921 : List Lit := [(18, false), (17, true)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c783, c66] c1921 (by decide) p (sat_cons (step783 p h) (sat_cons (step66 p h) (sat_nil p)))
def c1922 : List Lit := [(20, false), (23, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c784, c71] c1922 (by decide) p (sat_cons (step784 p h) (sat_cons (step71 p h) (sat_nil p)))
def c1923 : List Lit := [(20, false), (19, true)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c784, c72] c1923 (by decide) p (sat_cons (step784 p h) (sat_cons (step72 p h) (sat_nil p)))
def c1924 : List Lit := [(79, true), (4, true), (29, true), (21, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c785, c75] c1924 (by decide) p (sat_cons (step785 p h) (sat_cons (step75 p h) (sat_nil p)))
def c1925 : List Lit := [(17, true), (4, true), (21, false), (29, true)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c785, c76] c1925 (by decide) p (sat_cons (step785 p h) (sat_cons (step76 p h) (sat_nil p)))
end B112E004
