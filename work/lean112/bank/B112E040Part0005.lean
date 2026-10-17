import B112E040Part0004
namespace B112E040
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1845 : List Lit := [(1571, true), (1494, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1224] c1845 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1224 p h) (sat_nil p)))
def c1846 : List Lit := [(1613, false), (1618, true)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1288] c1846 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1288 p h) (sat_nil p)))
def c1847 : List Lit := [(1614, false), (1619, true)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1289] c1847 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1289 p h) (sat_nil p)))
def c1848 : List Lit := [(1605, false), (1618, true)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1290] c1848 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1290 p h) (sat_nil p)))
def c1849 : List Lit := [(1606, false), (1619, true)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1293] c1849 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1293 p h) (sat_nil p)))
def c1850 : List Lit := [(1618, false), (1627, true)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1547, c1297] c1850 (by decide) p (sat_cons (step1547 p h) (sat_cons (step1297 p h) (sat_nil p)))
def c1851 : List Lit := [(1619, false), (1628, true)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c1547, c1298] c1851 (by decide) p (sat_cons (step1547 p h) (sat_cons (step1298 p h) (sat_nil p)))
def c1852 : List Lit := [(1620, false), (1629, true)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c1547, c1299] c1852 (by decide) p (sat_cons (step1547 p h) (sat_cons (step1299 p h) (sat_nil p)))
def c1853 : List Lit := [(1594, false), (1627, true)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1300] c1853 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1300 p h) (sat_nil p)))
def c1854 : List Lit := [(1595, false), (1628, true)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1304] c1854 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1304 p h) (sat_nil p)))
def c1855 : List Lit := [(1596, false), (1628, true)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1551, c1307] c1855 (by decide) p (sat_cons (step1551 p h) (sat_cons (step1307 p h) (sat_nil p)))
def c1856 : List Lit := [(1596, false), (1629, true)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1308] c1856 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1308 p h) (sat_nil p)))
def c1857 : List Lit := [(1599, false), (1632, true)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1310] c1857 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1310 p h) (sat_nil p)))
def c1858 : List Lit := [(1688, true), (1679, false)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1397] c1858 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1397 p h) (sat_nil p)))
def c1859 : List Lit := [(1689, true), (1680, false)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1398] c1859 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1398 p h) (sat_nil p)))
def c1860 : List Lit := [(1681, false), (1690, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1399] c1860 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1399 p h) (sat_nil p)))
def c1861 : List Lit := [(1682, false), (1691, true)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1400] c1861 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1400 p h) (sat_nil p)))
def c1862 : List Lit := [(1683, false), (1692, true)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1401] c1862 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1401 p h) (sat_nil p)))
def c1863 : List Lit := [(1684, false), (1693, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1402] c1863 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1402 p h) (sat_nil p)))
def c1864 : List Lit := [(1690, false), (1708, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c1553, c1428] c1864 (by decide) p (sat_cons (step1553 p h) (sat_cons (step1428 p h) (sat_nil p)))
def c1865 : List Lit := [(1694, false), (1712, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c1553, c1429] c1865 (by decide) p (sat_cons (step1553 p h) (sat_cons (step1429 p h) (sat_nil p)))
def c1866 : List Lit := [(1695, false), (1713, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c1553, c1430] c1866 (by decide) p (sat_cons (step1553 p h) (sat_cons (step1430 p h) (sat_nil p)))
def c1867 : List Lit := [(1688, false), (1707, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1432] c1867 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1432 p h) (sat_nil p)))
def c1868 : List Lit := [(1689, false), (1708, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1433] c1868 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1433 p h) (sat_nil p)))
def c1869 : List Lit := [(1690, false), (1709, true)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1434] c1869 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1434 p h) (sat_nil p)))
def c1870 : List Lit := [(1691, false), (1710, true)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1435] c1870 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1435 p h) (sat_nil p)))
def c1871 : List Lit := [(1692, false), (1711, true)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1436] c1871 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1436 p h) (sat_nil p)))
def c1872 : List Lit := [(1693, false), (1712, true)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1437] c1872 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1437 p h) (sat_nil p)))
def c1873 : List Lit := [(1694, false), (1713, true)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1438] c1873 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1438 p h) (sat_nil p)))
def c1874 : List Lit := [(1707, true), (1627, false)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1439] c1874 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1439 p h) (sat_nil p)))
def c1875 : List Lit := [(1708, true), (1628, false)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1448] c1875 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1448 p h) (sat_nil p)))
def c1876 : List Lit := [(1566, false), (1715, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1465] c1876 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1465 p h) (sat_nil p)))
def c1877 : List Lit := [(1567, false), (1714, false)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1466] c1877 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1466 p h) (sat_nil p)))
def c1878 : List Lit := [(1568, false), (1713, false)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1467] c1878 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1467 p h) (sat_nil p)))
def c1879 : List Lit := [(1569, false), (1712, false)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1468] c1879 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1468 p h) (sat_nil p)))
def c1880 : List Lit := [(1570, false), (1711, false)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1469] c1880 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1469 p h) (sat_nil p)))
def c1881 : List Lit := [(1571, false), (1710, false)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1470] c1881 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1470 p h) (sat_nil p)))
def c1882 : List Lit := [(1572, false), (1709, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1471] c1882 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1471 p h) (sat_nil p)))
def c1883 : List Lit := [(1573, false), (1708, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1472] c1883 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1472 p h) (sat_nil p)))
def c1884 : List Lit := [(1574, false), (1707, false)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1473] c1884 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1473 p h) (sat_nil p)))
def c1885 : List Lit := [(1711, true), (1594, false), (108, false), (38, false)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1648, c1451, c1443, c1301, c1642, c1643, c603, c1359] c1885 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1648 p h) (sat_cons (step1451 p h) (sat_cons (step1443 p h) (sat_cons (step1301 p h) (sat_cons (step1642 p h) (sat_cons (step1643 p h) (sat_cons (step603 p h) (sat_cons (step1359 p h) (sat_nil p))))))))))
def c1886 : List Lit := [(88, false), (1691, true), (1663, false), (108, false), (38, false)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c601, c602, c604, c1325, c1624, c1362, c1411, c1367, c1387] c1886 (by decide) p (sat_cons (step601 p h) (sat_cons (step602 p h) (sat_cons (step604 p h) (sat_cons (step1325 p h) (sat_cons (step1624 p h) (sat_cons (step1362 p h) (sat_cons (step1411 p h) (sat_cons (step1367 p h) (sat_cons (step1387 p h) (sat_nil p))))))))))
def c1887 : List Lit := [(1675, false), (1665, false), (1647, false), (1691, true), (109, true)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c1359, c1367, c1333, c1861, c1391, c1388, c1370, c1406, c1360, c1340, c1344, c1334, c1317, c1604, c1329, c1315, c578] c1887 (by decide) p (sat_cons (step1359 p h) (sat_cons (step1367 p h) (sat_cons (step1333 p h) (sat_cons (step1861 p h) (sat_cons (step1391 p h) (sat_cons (step1388 p h) (sat_cons (step1370 p h) (sat_cons (step1406 p h) (sat_cons (step1360 p h) (sat_cons (step1340 p h) (sat_cons (step1344 p h) (sat_cons (step1334 p h) (sat_cons (step1317 p h) (sat_cons (step1604 p h) (sat_cons (step1329 p h) (sat_cons (step1315 p h) (sat_cons (step578 p h) (sat_nil p))))))))))))))))))
def c1888 : List Lit := [(1647, false), (1691, true), (109, true), (1675, false), (108, false), (38, false)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c1644, c1384, c1411, c1887, c1362, c1624, c609] c1888 (by decide) p (sat_cons (step1644 p h) (sat_cons (step1384 p h) (sat_cons (step1411 p h) (sat_cons (step1887 p h) (sat_cons (step1362 p h) (sat_cons (step1624 p h) (sat_cons (step609 p h) (sat_nil p))))))))
def c1889 : List Lit := [(1691, true), (109, true), (1675, false), (108, false), (38, false)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c1359, c1861, c1391, c1888, c1325, c605, c607, c1328, c1362, c1331, c1367, c1370, c1388, c1360, c1406, c1340, c1344, c1332, c1317, c1604, c1330, c1315, c578] c1889 (by decide) p (sat_cons (step1359 p h) (sat_cons (step1861 p h) (sat_cons (step1391 p h) (sat_cons (step1888 p h) (sat_cons (step1325 p h) (sat_cons (step605 p h) (sat_cons (step607 p h) (sat_cons (step1328 p h) (sat_cons (step1362 p h) (sat_cons (step1331 p h) (sat_cons (step1367 p h) (sat_cons (step1370 p h) (sat_cons (step1388 p h) (sat_cons (step1360 p h) (sat_cons (step1406 p h) (sat_cons (step1340 p h) (sat_cons (step1344 p h) (sat_cons (step1332 p h) (sat_cons (step1317 p h) (sat_cons (step1604 p h) (sat_cons (step1330 p h) (sat_cons (step1315 p h) (sat_cons (step578 p h) (sat_nil p))))))))))))))))))))))))
def c1890 : List Lit := [(1643, true), (105, false)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1319, c1604, c1314, c1315, c1311, c523, c1518, c1768] c1890 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1319 p h) (sat_cons (step1604 p h) (sat_cons (step1314 p h) (sat_cons (step1315 p h) (sat_cons (step1311 p h) (sat_cons (step523 p h) (sat_cons (step1518 p h) (sat_cons (step1768 p h) (sat_nil p))))))))))
def c1891 : List Lit := [(26, false), (28, false), (97, true), (98, false), (99, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c147, c564, c1774] c1891 (by decide) p (sat_cons (step147 p h) (sat_cons (step564 p h) (sat_cons (step1774 p h) (sat_nil p))))
def c1892 : List Lit := [(1641, true), (96, false), (24, false)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c1314, c1315, c534] c1892 (by decide) p (sat_cons (step1314 p h) (sat_cons (step1315 p h) (sat_cons (step534 p h) (sat_nil p))))
def c1893 : List Lit := [(1659, false), (1663, false), (1675, false), (1714, true), (1594, false), (108, false), (38, false)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c1644, c1384, c1853, c1446, c1421, c1422, c1454, c1388, c1301, c1367, c1642, c1362, c604] c1893 (by decide) p (sat_cons (step1644 p h) (sat_cons (step1384 p h) (sat_cons (step1853 p h) (sat_cons (step1446 p h) (sat_cons (step1421 p h) (sat_cons (step1422 p h) (sat_cons (step1454 p h) (sat_cons (step1388 p h) (sat_cons (step1301 p h) (sat_cons (step1367 p h) (sat_cons (step1642 p h) (sat_cons (step1362 p h) (sat_cons (step604 p h) (sat_nil p))))))))))))))
def c1894 : List Lit := [(1648, false), (1643, false), (105, true), (1663, false), (1675, false), (1714, true), (1594, false), (108, false), (38, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c1893, c1347, c1329, c1337, c1346, c1338, c1330, c609, c602, c1362, c1642, c1367, c1301, c1388, c1454, c1418] c1894 (by decide) p (sat_cons (step1893 p h) (sat_cons (step1347 p h) (sat_cons (step1329 p h) (sat_cons (step1337 p h) (sat_cons (step1346 p h) (sat_cons (step1338 p h) (sat_cons (step1330 p h) (sat_cons (step609 p h) (sat_cons (step602 p h) (sat_cons (step1362 p h) (sat_cons (step1642 p h) (sat_cons (step1367 p h) (sat_cons (step1301 p h) (sat_cons (step1388 p h) (sat_cons (step1454 p h) (sat_cons (step1418 p h) (sat_nil p)))))))))))))))))
def c1895 : List Lit := [(25, true), (29, true), (28, false), (39, false)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c1701, c1703, c1501] c1895 (by decide) p (sat_cons (step1701 p h) (sat_cons (step1703 p h) (sat_cons (step1501 p h) (sat_nil p))))
def c1896 : List Lit := [(25, false), (98, false), (1467, true), (1474, false), (28, false), (16, true), (1491, true), (22, false)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c969, c131, c141, c930, c972, c977, c980, c1007, c970, c1039, c1620] c1896 (by decide) p (sat_cons (step969 p h) (sat_cons (step131 p h) (sat_cons (step141 p h) (sat_cons (step930 p h) (sat_cons (step972 p h) (sat_cons (step977 p h) (sat_cons (step980 p h) (sat_cons (step1007 p h) (sat_cons (step970 p h) (sat_cons (step1039 p h) (sat_cons (step1620 p h) (sat_nil p))))))))))))
def c1897 : List Lit := [(88, false), (1648, false), (1643, false), (1693, true), (1663, false), (1675, false), (108, false), (38, false)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c602, c604, c1328, c1362, c1337, c1367, c1346, c1388, c1418] c1897 (by decide) p (sat_cons (step602 p h) (sat_cons (step604 p h) (sat_cons (step1328 p h) (sat_cons (step1362 p h) (sat_cons (step1337 p h) (sat_cons (step1367 p h) (sat_cons (step1346 p h) (sat_cons (step1388 p h) (sat_cons (step1418 p h) (sat_nil p))))))))))
def c1898 : List Lit := [(1648, false), (1643, false), (1713, true), (1663, false), (1675, false), (1594, false), (108, false), (38, false)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1445, c1644, c1384, c1336, c1345, c1897, c1642, c1301, c1453, c1412, c1417, c1388, c1346, c1367, c1337, c1362, c1328, c609] c1898 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1445 p h) (sat_cons (step1644 p h) (sat_cons (step1384 p h) (sat_cons (step1336 p h) (sat_cons (step1345 p h) (sat_cons (step1897 p h) (sat_cons (step1642 p h) (sat_cons (step1301 p h) (sat_cons (step1453 p h) (sat_cons (step1412 p h) (sat_cons (step1417 p h) (sat_cons (step1388 p h) (sat_cons (step1346 p h) (sat_cons (step1367 p h) (sat_cons (step1337 p h) (sat_cons (step1362 p h) (sat_cons (step1328 p h) (sat_cons (step609 p h) (sat_nil p))))))))))))))))))))
def c1899 : List Lit := [(29, false), (25, false), (28, false), (39, false), (36, true), (41, true)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c178, c176, c1717] c1899 (by decide) p (sat_cons (step178 p h) (sat_cons (step176 p h) (sat_cons (step1717 p h) (sat_nil p))))
def c1900 : List Lit := [(111, false), (105, true), (1648, false), (1713, true), (1680, false), (1594, false), (108, false), (38, false)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c609, c604, c1330, c1642, c1338, c1301, c1342, c1453, c1417] c1900 (by decide) p (sat_cons (step609 p h) (sat_cons (step604 p h) (sat_cons (step1330 p h) (sat_cons (step1642 p h) (sat_cons (step1338 p h) (sat_cons (step1301 p h) (sat_cons (step1342 p h) (sat_cons (step1453 p h) (sat_cons (step1417 p h) (sat_nil p))))))))))
def c1901 : List Lit := [(24, true), (98, false), (1472, false), (1481, true), (1461, false), (22, false)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c976, c1004, c995, c983, c984, c992, c1008, c977, c972, c1652, c138] c1901 (by decide) p (sat_cons (step976 p h) (sat_cons (step1004 p h) (sat_cons (step995 p h) (sat_cons (step983 p h) (sat_cons (step984 p h) (sat_cons (step992 p h) (sat_cons (step1008 p h) (sat_cons (step977 p h) (sat_cons (step972 p h) (sat_cons (step1652 p h) (sat_cons (step138 p h) (sat_nil p))))))))))))
def c1902 : List Lit := [(1475, false), (98, false), (1481, true), (16, true), (1491, true), (22, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c969, c976, c1003, c1008, c1039, c979, c977, c970, c972, c1652, c124, c930, c1620] c1902 (by decide) p (sat_cons (step969 p h) (sat_cons (step976 p h) (sat_cons (step1003 p h) (sat_cons (step1008 p h) (sat_cons (step1039 p h) (sat_cons (step979 p h) (sat_cons (step977 p h) (sat_cons (step970 p h) (sat_cons (step972 p h) (sat_cons (step1652 p h) (sat_cons (step124 p h) (sat_cons (step930 p h) (sat_cons (step1620 p h) (sat_nil p))))))))))))))
def c1903 : List Lit := [(25, false), (26, false), (98, false), (1467, true), (1474, false), (16, true), (1491, true), (22, false)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c969, c138, c128, c972, c930, c977, c980, c1007, c970, c1039, c1620] c1903 (by decide) p (sat_cons (step969 p h) (sat_cons (step138 p h) (sat_cons (step128 p h) (sat_cons (step972 p h) (sat_cons (step930 p h) (sat_cons (step977 p h) (sat_cons (step980 p h) (sat_cons (step1007 p h) (sat_cons (step970 p h) (sat_cons (step1039 p h) (sat_cons (step1620 p h) (sat_nil p))))))))))))
def c1904 : List Lit := [(1472, false), (98, false), (1467, true), (1480, true), (16, true), (1491, true), (22, false)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c969, c976, c1003, c989, c992, c1007, c982, c977, c1903, c972, c1652] c1904 (by decide) p (sat_cons (step969 p h) (sat_cons (step976 p h) (sat_cons (step1003 p h) (sat_cons (step989 p h) (sat_cons (step992 p h) (sat_cons (step1007 p h) (sat_cons (step982 p h) (sat_cons (step977 p h) (sat_cons (step1903 p h) (sat_cons (step972 p h) (sat_cons (step1652 p h) (sat_nil p))))))))))))
def c1905 : List Lit := [(26, false), (28, false), (107, true), (98, false), (109, false)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c565, c147, c1772] c1905 (by decide) p (sat_cons (step565 p h) (sat_cons (step147 p h) (sat_cons (step1772 p h) (sat_nil p))))
def c1906 : List Lit := [(1490, true), (1455, false), (16, true), (26, false), (1474, false), (22, false)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c969, c976, c1002, c1031, c1038, c1007, c979, c977, c970, c972, c1652, c120, c930, c1620] c1906 (by decide) p (sat_cons (step969 p h) (sat_cons (step976 p h) (sat_cons (step1002 p h) (sat_cons (step1031 p h) (sat_cons (step1038 p h) (sat_cons (step1007 p h) (sat_cons (step979 p h) (sat_cons (step977 p h) (sat_cons (step970 p h) (sat_cons (step972 p h) (sat_cons (step1652 p h) (sat_cons (step120 p h) (sat_cons (step930 p h) (sat_cons (step1620 p h) (sat_nil p)))))))))))))))
def c1907 : List Lit := [(1446, true), (10, false), (18, false)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c938, c939, c57] c1907 (by decide) p (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step57 p h) (sat_nil p))))
def c1908 : List Lit := [(1441, false), (1446, false), (1456, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c946, c962, c933, c958, c947, c1565, c936] c1908 (by decide) p (sat_cons (step946 p h) (sat_cons (step962 p h) (sat_cons (step933 p h) (sat_cons (step958 p h) (sat_cons (step947 p h) (sat_cons (step1565 p h) (sat_cons (step936 p h) (sat_nil p))))))))
end B112E040
