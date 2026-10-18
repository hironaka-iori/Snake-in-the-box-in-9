import B112E047Part0004
namespace B112E047
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1863 : List Lit := [(1534, false), (1542, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c1611, c1165] c1863 (by decide) p (sat_cons (step1611 p h) (sat_cons (step1165 p h) (sat_nil p)))
def c1864 : List Lit := [(1535, false), (1543, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c1611, c1166] c1864 (by decide) p (sat_cons (step1611 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c1865 : List Lit := [(1536, false), (1544, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c1611, c1167] c1865 (by decide) p (sat_cons (step1611 p h) (sat_cons (step1167 p h) (sat_nil p)))
def c1866 : List Lit := [(1513, false), (1541, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c1609, c1168] c1866 (by decide) p (sat_cons (step1609 p h) (sat_cons (step1168 p h) (sat_nil p)))
def c1867 : List Lit := [(1514, false), (1542, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c1609, c1174] c1867 (by decide) p (sat_cons (step1609 p h) (sat_cons (step1174 p h) (sat_nil p)))
def c1868 : List Lit := [(1515, false), (1543, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c1609, c1179] c1868 (by decide) p (sat_cons (step1609 p h) (sat_cons (step1179 p h) (sat_nil p)))
def c1869 : List Lit := [(1555, true), (1485, false)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1184] c1869 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1184 p h) (sat_nil p)))
def c1870 : List Lit := [(1556, true), (1486, false)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1190] c1870 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1190 p h) (sat_nil p)))
def c1871 : List Lit := [(1556, true), (1487, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c1610, c1196] c1871 (by decide) p (sat_cons (step1610 p h) (sat_cons (step1196 p h) (sat_nil p)))
def c1872 : List Lit := [(1557, true), (1487, false)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1197] c1872 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1197 p h) (sat_nil p)))
def c1873 : List Lit := [(1557, true), (1488, false)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c1610, c1204] c1873 (by decide) p (sat_cons (step1610 p h) (sat_cons (step1204 p h) (sat_nil p)))
def c1874 : List Lit := [(1558, true), (1488, false)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1205] c1874 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1205 p h) (sat_nil p)))
def c1875 : List Lit := [(1558, true), (1489, false)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c1610, c1211] c1875 (by decide) p (sat_cons (step1610 p h) (sat_cons (step1211 p h) (sat_nil p)))
def c1876 : List Lit := [(1559, true), (1489, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1212] c1876 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1212 p h) (sat_nil p)))
def c1877 : List Lit := [(1559, true), (1490, false)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1610, c1217] c1877 (by decide) p (sat_cons (step1610 p h) (sat_cons (step1217 p h) (sat_nil p)))
def c1878 : List Lit := [(1560, true), (1490, false)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1218] c1878 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1218 p h) (sat_nil p)))
def c1879 : List Lit := [(1561, true), (1491, false)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1222] c1879 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1222 p h) (sat_nil p)))
def c1880 : List Lit := [(1603, false), (1611, true)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1311] c1880 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1311 p h) (sat_nil p)))
def c1881 : List Lit := [(1604, false), (1612, true)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1312] c1881 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1312 p h) (sat_nil p)))
def c1882 : List Lit := [(1605, false), (1613, true)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1313] c1882 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1313 p h) (sat_nil p)))
def c1883 : List Lit := [(1606, false), (1614, true)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1314] c1883 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1314 p h) (sat_nil p)))
def c1884 : List Lit := [(1607, false), (1615, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1315] c1884 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1315 p h) (sat_nil p)))
def c1885 : List Lit := [(1583, false), (1611, true)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1316] c1885 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1316 p h) (sat_nil p)))
def c1886 : List Lit := [(1584, false), (1612, true)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1323] c1886 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1323 p h) (sat_nil p)))
def c1887 : List Lit := [(1585, false), (1613, true)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1329] c1887 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1329 p h) (sat_nil p)))
def c1888 : List Lit := [(1586, false), (1614, true)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1334] c1888 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1334 p h) (sat_nil p)))
def c1889 : List Lit := [(1587, false), (1615, true)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1338] c1889 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1338 p h) (sat_nil p)))
def c1890 : List Lit := [(1657, true), (1645, false)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c1634, c1404] c1890 (by decide) p (sat_cons (step1634 p h) (sat_cons (step1404 p h) (sat_nil p)))
def c1891 : List Lit := [(1646, false), (1658, true)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c1634, c1407] c1891 (by decide) p (sat_cons (step1634 p h) (sat_cons (step1407 p h) (sat_nil p)))
def c1892 : List Lit := [(1647, false), (1659, true)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c1634, c1410] c1892 (by decide) p (sat_cons (step1634 p h) (sat_cons (step1410 p h) (sat_nil p)))
def c1893 : List Lit := [(1664, true), (1636, false)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c1635, c1417] c1893 (by decide) p (sat_cons (step1635 p h) (sat_cons (step1417 p h) (sat_nil p)))
def c1894 : List Lit := [(1665, true), (1637, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c1635, c1422] c1894 (by decide) p (sat_cons (step1635 p h) (sat_cons (step1422 p h) (sat_nil p)))
def c1895 : List Lit := [(1638, false), (1666, true)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c1635, c1427] c1895 (by decide) p (sat_cons (step1635 p h) (sat_cons (step1427 p h) (sat_nil p)))
def c1896 : List Lit := [(1639, false), (1667, true)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c1635, c1431] c1896 (by decide) p (sat_cons (step1635 p h) (sat_cons (step1431 p h) (sat_nil p)))
def c1897 : List Lit := [(1640, false), (1668, true)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c1635, c1435] c1897 (by decide) p (sat_cons (step1635 p h) (sat_cons (step1435 p h) (sat_nil p)))
def c1898 : List Lit := [(1641, false), (1669, true)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c1635, c1439] c1898 (by decide) p (sat_cons (step1635 p h) (sat_cons (step1439 p h) (sat_nil p)))
def c1899 : List Lit := [(1667, false), (1682, true)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c1596, c1442] c1899 (by decide) p (sat_cons (step1596 p h) (sat_cons (step1442 p h) (sat_nil p)))
def c1900 : List Lit := [(1668, false), (1683, true)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c1596, c1443] c1900 (by decide) p (sat_cons (step1596 p h) (sat_cons (step1443 p h) (sat_nil p)))
def c1901 : List Lit := [(1669, false), (1684, true)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c1596, c1444] c1901 (by decide) p (sat_cons (step1596 p h) (sat_cons (step1444 p h) (sat_nil p)))
def c1902 : List Lit := [(1665, false), (1681, true)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c1598, c1445] c1902 (by decide) p (sat_cons (step1598 p h) (sat_cons (step1445 p h) (sat_nil p)))
def c1903 : List Lit := [(1666, false), (1682, true)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c1598, c1446] c1903 (by decide) p (sat_cons (step1598 p h) (sat_cons (step1446 p h) (sat_nil p)))
def c1904 : List Lit := [(1667, false), (1683, true)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c1598, c1447] c1904 (by decide) p (sat_cons (step1598 p h) (sat_cons (step1447 p h) (sat_nil p)))
def c1905 : List Lit := [(1668, false), (1684, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c1598, c1448] c1905 (by decide) p (sat_cons (step1598 p h) (sat_cons (step1448 p h) (sat_nil p)))
def c1906 : List Lit := [(1669, false), (1685, true)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c1598, c1449] c1906 (by decide) p (sat_cons (step1598 p h) (sat_cons (step1449 p h) (sat_nil p)))
def c1907 : List Lit := [(1670, false), (1686, true)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c1598, c1450] c1907 (by decide) p (sat_cons (step1598 p h) (sat_cons (step1450 p h) (sat_nil p)))
def c1908 : List Lit := [(1671, false), (1687, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c1598, c1451] c1908 (by decide) p (sat_cons (step1598 p h) (sat_cons (step1451 p h) (sat_nil p)))
def c1909 : List Lit := [(1680, true), (1611, false)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c1636, c1452] c1909 (by decide) p (sat_cons (step1636 p h) (sat_cons (step1452 p h) (sat_nil p)))
def c1910 : List Lit := [(1681, true), (1612, false)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c1636, c1459] c1910 (by decide) p (sat_cons (step1636 p h) (sat_cons (step1459 p h) (sat_nil p)))
def c1911 : List Lit := [(1613, false), (1682, true)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c1636, c1466] c1911 (by decide) p (sat_cons (step1636 p h) (sat_cons (step1466 p h) (sat_nil p)))
def c1912 : List Lit := [(1615, false), (1684, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c1636, c1480] c1912 (by decide) p (sat_cons (step1636 p h) (sat_cons (step1480 p h) (sat_nil p)))
def c1913 : List Lit := [(1616, false), (1685, true)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c1636, c1485] c1913 (by decide) p (sat_cons (step1636 p h) (sat_cons (step1485 p h) (sat_nil p)))
def c1914 : List Lit := [(1617, false), (1686, true)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c1636, c1490] c1914 (by decide) p (sat_cons (step1636 p h) (sat_cons (step1490 p h) (sat_nil p)))
def c1915 : List Lit := [(1555, false), (1689, false)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1492] c1915 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1492 p h) (sat_nil p)))
def c1916 : List Lit := [(1556, false), (1688, false)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1493] c1916 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1493 p h) (sat_nil p)))
def c1917 : List Lit := [(1557, false), (1687, false)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1494] c1917 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1494 p h) (sat_nil p)))
def c1918 : List Lit := [(1558, false), (1686, false)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1495] c1918 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1495 p h) (sat_nil p)))
def c1919 : List Lit := [(1559, false), (1685, false)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1496] c1919 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1496 p h) (sat_nil p)))
def c1920 : List Lit := [(1560, false), (1684, false)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1497] c1920 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1497 p h) (sat_nil p)))
def c1921 : List Lit := [(1561, false), (1683, false)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1498] c1921 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1498 p h) (sat_nil p)))
def c1922 : List Lit := [(1562, false), (1682, false)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1499] c1922 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1499 p h) (sat_nil p)))
def c1923 : List Lit := [(1563, false), (1681, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1500] c1923 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1500 p h) (sat_nil p)))
def c1924 : List Lit := [(1564, false), (1680, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1501] c1924 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1501 p h) (sat_nil p)))
def c1925 : List Lit := [(1666, true), (87, false), (1626, false), (21, false)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c1634, c1613] c1925 (by decide) p (sat_cons (step1634 p h) (sat_cons (step1613 p h) (sat_nil p)))
def c1926 : List Lit := [(6, true), (90, false), (221, true), (7, false), (1668, true), (1525, true), (125, true), (25, false)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c1634, c1623] c1926 (by decide) p (sat_cons (step1634 p h) (sat_cons (step1623 p h) (sat_nil p)))
end B112E047
