import B112E158Part0004
namespace B112E158
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1890 : List Lit := [(381, false), (383, false)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c1591, c839] c1890 (by decide) p (sat_cons (step1591 p h) (sat_cons (step839 p h) (sat_nil p)))
def c1891 : List Lit := [(379, false), (385, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c1585, c843] c1891 (by decide) p (sat_cons (step1585 p h) (sat_cons (step843 p h) (sat_nil p)))
def c1892 : List Lit := [(393, false), (399, false)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c1584, c854] c1892 (by decide) p (sat_cons (step1584 p h) (sat_cons (step854 p h) (sat_nil p)))
def c1893 : List Lit := [(387, false), (401, false)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c1579, c858] c1893 (by decide) p (sat_cons (step1579 p h) (sat_cons (step858 p h) (sat_nil p)))
def c1894 : List Lit := [(375, false), (403, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c1575, c863] c1894 (by decide) p (sat_cons (step1575 p h) (sat_cons (step863 p h) (sat_nil p)))
def c1895 : List Lit := [(409, false), (415, false)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c1583, c870] c1895 (by decide) p (sat_cons (step1583 p h) (sat_cons (step870 p h) (sat_nil p)))
def c1896 : List Lit := [(417, false), (431, false)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c1578, c879] c1896 (by decide) p (sat_cons (step1578 p h) (sat_cons (step879 p h) (sat_nil p)))
def c1897 : List Lit := [(405, false), (463, false)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c1572, c898] c1897 (by decide) p (sat_cons (step1572 p h) (sat_cons (step898 p h) (sat_nil p)))
def c1898 : List Lit := [(349, false), (465, false)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c903, c901] c1898 (by decide) p (sat_cons (step903 p h) (sat_cons (step901 p h) (sat_nil p)))
def c1899 : List Lit := [(923, false), (1059, false)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c996, c992] c1899 (by decide) p (sat_cons (step996 p h) (sat_cons (step992 p h) (sat_nil p)))
def c1900 : List Lit := [(924, false), (1058, false)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c996, c993] c1900 (by decide) p (sat_cons (step996 p h) (sat_cons (step993 p h) (sat_nil p)))
def c1901 : List Lit := [(925, false), (1057, false)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c996, c994] c1901 (by decide) p (sat_cons (step996 p h) (sat_cons (step994 p h) (sat_nil p)))
def c1902 : List Lit := [(926, false), (1056, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c996, c995] c1902 (by decide) p (sat_cons (step996 p h) (sat_cons (step995 p h) (sat_nil p)))
def c1903 : List Lit := [(1523, false), (1540, true)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1229] c1903 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1229 p h) (sat_nil p)))
def c1904 : List Lit := [(1524, false), (1541, true)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1230] c1904 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1230 p h) (sat_nil p)))
def c1905 : List Lit := [(1525, false), (1542, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1231] c1905 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1231 p h) (sat_nil p)))
def c1906 : List Lit := [(1526, false), (1543, true)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1232] c1906 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1232 p h) (sat_nil p)))
def c1907 : List Lit := [(1527, false), (1544, true)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1233] c1907 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1233 p h) (sat_nil p)))
def c1908 : List Lit := [(1528, false), (1545, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1234] c1908 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1234 p h) (sat_nil p)))
def c1909 : List Lit := [(1529, false), (1546, true)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1235] c1909 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1235 p h) (sat_nil p)))
def c1910 : List Lit := [(1590, false), (1599, true)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c1599, c1349] c1910 (by decide) p (sat_cons (step1599 p h) (sat_cons (step1349 p h) (sat_nil p)))
def c1911 : List Lit := [(1591, false), (1600, true)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c1599, c1350] c1911 (by decide) p (sat_cons (step1599 p h) (sat_cons (step1350 p h) (sat_nil p)))
def c1912 : List Lit := [(1592, false), (1601, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c1599, c1351] c1912 (by decide) p (sat_cons (step1599 p h) (sat_cons (step1351 p h) (sat_nil p)))
def c1913 : List Lit := [(1593, false), (1602, true)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c1599, c1352] c1913 (by decide) p (sat_cons (step1599 p h) (sat_cons (step1352 p h) (sat_nil p)))
def c1914 : List Lit := [(1567, false), (1599, true)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1353] c1914 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1353 p h) (sat_nil p)))
def c1915 : List Lit := [(1600, true), (1568, false)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1360] c1915 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1360 p h) (sat_nil p)))
def c1916 : List Lit := [(1569, false), (1601, true)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1366] c1916 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1366 p h) (sat_nil p)))
def c1917 : List Lit := [(1570, false), (1602, true)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1372] c1917 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1372 p h) (sat_nil p)))
def c1918 : List Lit := [(1571, false), (1603, true)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1377] c1918 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1377 p h) (sat_nil p)))
def c1919 : List Lit := [(1572, false), (1604, true)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1380] c1919 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1380 p h) (sat_nil p)))
def c1920 : List Lit := [(1649, false), (1658, true)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1457] c1920 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1457 p h) (sat_nil p)))
def c1921 : List Lit := [(1650, false), (1659, true)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1458] c1921 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1458 p h) (sat_nil p)))
def c1922 : List Lit := [(1651, false), (1660, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1459] c1922 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1459 p h) (sat_nil p)))
def c1923 : List Lit := [(1658, true), (1626, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c1622, c1460] c1923 (by decide) p (sat_cons (step1622 p h) (sat_cons (step1460 p h) (sat_nil p)))
def c1924 : List Lit := [(1659, true), (1627, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c1622, c1465] c1924 (by decide) p (sat_cons (step1622 p h) (sat_cons (step1465 p h) (sat_nil p)))
def c1925 : List Lit := [(1628, false), (1660, true)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c1622, c1470] c1925 (by decide) p (sat_cons (step1622 p h) (sat_cons (step1470 p h) (sat_nil p)))
def c1926 : List Lit := [(1661, false), (1677, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c1600, c1475] c1926 (by decide) p (sat_cons (step1600 p h) (sat_cons (step1475 p h) (sat_nil p)))
def c1927 : List Lit := [(1659, false), (1676, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1476] c1927 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1476 p h) (sat_nil p)))
def c1928 : List Lit := [(1660, false), (1677, true)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1477] c1928 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1477 p h) (sat_nil p)))
def c1929 : List Lit := [(1661, false), (1678, true)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1478] c1929 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1478 p h) (sat_nil p)))
def c1930 : List Lit := [(1662, false), (1679, true)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1479] c1930 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1479 p h) (sat_nil p)))
def c1931 : List Lit := [(1663, false), (1680, true)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1480] c1931 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1480 p h) (sat_nil p)))
def c1932 : List Lit := [(1675, true), (1599, false)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c1623, c1481] c1932 (by decide) p (sat_cons (step1623 p h) (sat_cons (step1481 p h) (sat_nil p)))
def c1933 : List Lit := [(1676, true), (1600, false)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c1623, c1487] c1933 (by decide) p (sat_cons (step1623 p h) (sat_cons (step1487 p h) (sat_nil p)))
def c1934 : List Lit := [(1677, true), (1601, false)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c1623, c1493] c1934 (by decide) p (sat_cons (step1623 p h) (sat_cons (step1493 p h) (sat_nil p)))
def c1935 : List Lit := [(1678, true), (1602, false)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c1623, c1499] c1935 (by decide) p (sat_cons (step1623 p h) (sat_cons (step1499 p h) (sat_nil p)))
def c1936 : List Lit := [(1603, false), (1679, true)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c1623, c1504] c1936 (by decide) p (sat_cons (step1623 p h) (sat_cons (step1504 p h) (sat_nil p)))
def c1937 : List Lit := [(1604, false), (1680, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c1623, c1509] c1937 (by decide) p (sat_cons (step1623 p h) (sat_cons (step1509 p h) (sat_nil p)))
def c1938 : List Lit := [(1605, false), (1681, true)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c1623, c1513] c1938 (by decide) p (sat_cons (step1623 p h) (sat_cons (step1513 p h) (sat_nil p)))
def c1939 : List Lit := [(1606, false), (1682, true)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c1623, c1516] c1939 (by decide) p (sat_cons (step1623 p h) (sat_cons (step1516 p h) (sat_nil p)))
def c1940 : List Lit := [(1539, false), (1683, false)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1518] c1940 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1518 p h) (sat_nil p)))
def c1941 : List Lit := [(1540, false), (1682, false)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1519] c1941 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1519 p h) (sat_nil p)))
def c1942 : List Lit := [(1541, false), (1681, false)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1520] c1942 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1520 p h) (sat_nil p)))
def c1943 : List Lit := [(1542, false), (1680, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1521] c1943 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1521 p h) (sat_nil p)))
def c1944 : List Lit := [(1543, false), (1679, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1522] c1944 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1522 p h) (sat_nil p)))
def c1945 : List Lit := [(1544, false), (1678, false)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1523] c1945 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1523 p h) (sat_nil p)))
def c1946 : List Lit := [(1545, false), (1677, false)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1524] c1946 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1524 p h) (sat_nil p)))
def c1947 : List Lit := [(1546, false), (1676, false)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1525] c1947 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1525 p h) (sat_nil p)))
def c1948 : List Lit := [(1547, false), (1675, false)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1526] c1948 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1526 p h) (sat_nil p)))
def c1949 : List Lit := [(1569, false), (1612, false), (1679, true), (1649, false)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c1920, c1500, c1916, c1367, c1495, c1726, c1461, c1618, c1409, c1387] c1949 (by decide) p (sat_cons (step1920 p h) (sat_cons (step1500 p h) (sat_cons (step1916 p h) (sat_cons (step1367 p h) (sat_cons (step1495 p h) (sat_cons (step1726 p h) (sat_cons (step1461 p h) (sat_cons (step1618 p h) (sat_cons (step1409 p h) (sat_cons (step1387 p h) (sat_nil p)))))))))))
def c1950 : List Lit := [(1457, false), (32, true), (1524, false), (45, false), (34, true), (1564, false), (7, false), (1513, false), (37, true), (24, true), (1544, true), (39, false), (54, false)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c1102, c1107, c1256, c1748, c1734, c1077, c1084, c1249, c1248, c1019, c1023, c1218, c1944, c1013, c1002, c1134, c1137, c1005, c1006, c1116, c1108, c21, c1759, c1103, c9, c1742, c1382, c1949, c1300, c1274, c1276, c1272, c403, c214, c1793, c158, c1112, c1114, c1118, c233, c1109, c1805, c255] c1950 (by decide) p (sat_cons (step1102 p h) (sat_cons (step1107 p h) (sat_cons (step1256 p h) (sat_cons (step1748 p h) (sat_cons (step1734 p h) (sat_cons (step1077 p h) (sat_cons (step1084 p h) (sat_cons (step1249 p h) (sat_cons (step1248 p h) (sat_cons (step1019 p h) (sat_cons (step1023 p h) (sat_cons (step1218 p h) (sat_cons (step1944 p h) (sat_cons (step1013 p h) (sat_cons (step1002 p h) (sat_cons (step1134 p h) (sat_cons (step1137 p h) (sat_cons (step1005 p h) (sat_cons (step1006 p h) (sat_cons (step1116 p h) (sat_cons (step1108 p h) (sat_cons (step21 p h) (sat_cons (step1759 p h) (sat_cons (step1103 p h) (sat_cons (step9 p h) (sat_cons (step1742 p h) (sat_cons (step1382 p h) (sat_cons (step1949 p h) (sat_cons (step1300 p h) (sat_cons (step1274 p h) (sat_cons (step1276 p h) (sat_cons (step1272 p h) (sat_cons (step403 p h) (sat_cons (step214 p h) (sat_cons (step1793 p h) (sat_cons (step158 p h) (sat_cons (step1112 p h) (sat_cons (step1114 p h) (sat_cons (step1118 p h) (sat_cons (step233 p h) (sat_cons (step1109 p h) (sat_cons (step1805 p h) (sat_cons (step255 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c1951 : List Lit := [(30, false), (1476, true), (52, true), (39, false), (54, false)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c153, c1731] c1951 (by decide) p (sat_cons (step153 p h) (sat_cons (step1731 p h) (sat_nil p)))
def c1952 : List Lit := [(1564, true), (73, true), (69, false), (28, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c1704, c1289, c1610, c1284, c510] c1952 (by decide) p (sat_cons (step1704 p h) (sat_cons (step1289 p h) (sat_cons (step1610 p h) (sat_cons (step1284 p h) (sat_cons (step510 p h) (sat_nil p))))))
def c1953 : List Lit := [(1484, true), (1569, true), (39, false), (54, false)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c1115, c1117, c1112, c1113, c1109, c158, c242, c1799, c1803, c228, c479, c480, c481, c1273, c1280, c1283, c1275, c1288, c1304] c1953 (by decide) p (sat_cons (step1115 p h) (sat_cons (step1117 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step1109 p h) (sat_cons (step158 p h) (sat_cons (step242 p h) (sat_cons (step1799 p h) (sat_cons (step1803 p h) (sat_cons (step228 p h) (sat_cons (step479 p h) (sat_cons (step480 p h) (sat_cons (step481 p h) (sat_cons (step1273 p h) (sat_cons (step1280 p h) (sat_cons (step1283 p h) (sat_cons (step1275 p h) (sat_cons (step1288 p h) (sat_cons (step1304 p h) (sat_nil p))))))))))))))))))))
end B112E158
