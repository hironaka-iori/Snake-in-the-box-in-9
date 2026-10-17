import B112E034Part0001
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1907 : List Lit := [(1789, true), (95, true), (87, true), (86, false), (89, false), (107, true)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c889, c1522, c1524, c1843, c1542, c1523, c1515, c1906, c1506, c471, c488, c481] c1907 (by decide) p (sat_cons (step889 p h) (sat_cons (step1522 p h) (sat_cons (step1524 p h) (sat_cons (step1843 p h) (sat_cons (step1542 p h) (sat_cons (step1523 p h) (sat_cons (step1515 p h) (sat_cons (step1906 p h) (sat_cons (step1506 p h) (sat_cons (step471 p h) (sat_cons (step488 p h) (sat_cons (step481 p h) (sat_nil p)))))))))))))
def c1908 : List Lit := [(1727, true), (84, false)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c883, c368, c1420, c1421, c365] c1908 (by decide) p (sat_cons (step883 p h) (sat_cons (step368 p h) (sat_cons (step1420 p h) (sat_cons (step1421 p h) (sat_cons (step365 p h) (sat_nil p))))))
def c1909 : List Lit := [(1811, false), (1777, false), (112, true), (87, true), (92, false), (1831, true), (1781, false)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c886, c1524, c1547, c1637, c1555, c1562, c1595, c1601, c1644, c1565, c1563, c1548, c1556, c1558, c1527, c667, c1519, c450, c463] c1909 (by decide) p (sat_cons (step886 p h) (sat_cons (step1524 p h) (sat_cons (step1547 p h) (sat_cons (step1637 p h) (sat_cons (step1555 p h) (sat_cons (step1562 p h) (sat_cons (step1595 p h) (sat_cons (step1601 p h) (sat_cons (step1644 p h) (sat_cons (step1565 p h) (sat_cons (step1563 p h) (sat_cons (step1548 p h) (sat_cons (step1556 p h) (sat_cons (step1558 p h) (sat_cons (step1527 p h) (sat_cons (step667 p h) (sat_cons (step1519 p h) (sat_cons (step450 p h) (sat_cons (step463 p h) (sat_nil p))))))))))))))))))))
def c1910 : List Lit := [(1777, false), (1791, true), (1831, true), (87, true), (1781, false), (126, true), (112, true), (92, false)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c897, c1571, c1574, c1909, c1548, c1580, c1583, c1527, c1575, c1577, c1568, c1569, c1519, c1573, c762, c803, c839, c792] c1910 (by decide) p (sat_cons (step897 p h) (sat_cons (step1571 p h) (sat_cons (step1574 p h) (sat_cons (step1909 p h) (sat_cons (step1548 p h) (sat_cons (step1580 p h) (sat_cons (step1583 p h) (sat_cons (step1527 p h) (sat_cons (step1575 p h) (sat_cons (step1577 p h) (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step1519 p h) (sat_cons (step1573 p h) (sat_cons (step762 p h) (sat_cons (step803 p h) (sat_cons (step839 p h) (sat_cons (step792 p h) (sat_nil p)))))))))))))))))))
def c1911 : List Lit := [(1818, true), (1805, false), (116, true), (109, false), (117, true), (1800, false), (1795, false)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c896, c1574, c1579, c1601, c1606, c1580, c1564, c1577, c1559, c741, c624] c1911 (by decide) p (sat_cons (step896 p h) (sat_cons (step1574 p h) (sat_cons (step1579 p h) (sat_cons (step1601 p h) (sat_cons (step1606 p h) (sat_cons (step1580 p h) (sat_cons (step1564 p h) (sat_cons (step1577 p h) (sat_cons (step1559 p h) (sat_cons (step741 p h) (sat_cons (step624 p h) (sat_nil p))))))))))))
def c1912 : List Lit := [(1831, true), (94, false), (87, true), (1781, false), (1818, false), (1817, false), (126, true), (1773, false), (97, true), (112, true), (92, false)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c1504, c1513, c1644, c1637, c1910, c1543, c1516, c1527, c1506, c1519, c461] c1912 (by decide) p (sat_cons (step1504 p h) (sat_cons (step1513 p h) (sat_cons (step1644 p h) (sat_cons (step1637 p h) (sat_cons (step1910 p h) (sat_cons (step1543 p h) (sat_cons (step1516 p h) (sat_cons (step1527 p h) (sat_cons (step1506 p h) (sat_cons (step1519 p h) (sat_cons (step461 p h) (sat_nil p))))))))))))
def c1913 : List Lit := [(98, false), (97, false), (89, false), (86, false)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c890, c416, c471, c488, c487] c1913 (by decide) p (sat_cons (step890 p h) (sat_cons (step416 p h) (sat_cons (step471 p h) (sat_cons (step488 p h) (sat_cons (step487 p h) (sat_nil p))))))
def c1914 : List Lit := [(95, true), (1772, true), (89, false), (1777, true), (86, false), (109, false)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c891, c1505, c1506, c1514, c1913, c1509, c441, c472, c496] c1914 (by decide) p (sat_cons (step891 p h) (sat_cons (step1505 p h) (sat_cons (step1506 p h) (sat_cons (step1514 p h) (sat_cons (step1913 p h) (sat_cons (step1509 p h) (sat_cons (step441 p h) (sat_cons (step472 p h) (sat_cons (step496 p h) (sat_nil p))))))))))
def c1915 : List Lit := [(1779, true), (95, false), (92, false)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c888, c1518, c1519, c461, c531, c468] c1915 (by decide) p (sat_cons (step888 p h) (sat_cons (step1518 p h) (sat_cons (step1519 p h) (sat_cons (step461 p h) (sat_cons (step531 p h) (sat_cons (step468 p h) (sat_nil p)))))))
def c1916 : List Lit := [(100, false), (96, true), (109, false), (86, false)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c891, c441, c496] c1916 (by decide) p (sat_cons (step891 p h) (sat_cons (step441 p h) (sat_cons (step496 p h) (sat_nil p))))
def c1917 : List Lit := [(1706, true), (64, true), (68, true), (103, false)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c875, c1374, c1378, c1380, c1376, c1372, c284, c278] c1917 (by decide) p (sat_cons (step875 p h) (sat_cons (step1374 p h) (sat_cons (step1378 p h) (sat_cons (step1380 p h) (sat_cons (step1376 p h) (sat_cons (step1372 p h) (sat_cons (step284 p h) (sat_cons (step278 p h) (sat_nil p)))))))))
def c1918 : List Lit := [(65, false), (61, false), (103, false), (64, true)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c875, c284, c278] c1918 (by decide) p (sat_cons (step875 p h) (sat_cons (step284 p h) (sat_cons (step278 p h) (sat_nil p))))
def c1919 : List Lit := [(77, false), (73, false), (74, false), (72, false)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c878, c339, c337, c320] c1919 (by decide) p (sat_cons (step878 p h) (sat_cons (step339 p h) (sat_cons (step337 p h) (sat_cons (step320 p h) (sat_nil p)))))
def c1920 : List Lit := [(1604, true), (27, false), (9, false)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1192, c91] c1920 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1192 p h) (sat_cons (step91 p h) (sat_nil p))))
def c1921 : List Lit := [(1581, true)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c1860, c1888, c1118, c1132, c1896] c1921 (by decide) p (sat_cons (step1860 p h) (sat_cons (step1888 p h) (sat_cons (step1118 p h) (sat_cons (step1132 p h) (sat_cons (step1896 p h) (sat_nil p))))))
def c1922 : List Lit := [(1592, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c1921, c1855, c1167] c1922 (by decide) p (sat_cons (step1921 p h) (sat_cons (step1855 p h) (sat_cons (step1167 p h) (sat_nil p))))
def c1923 : List Lit := [(1640, true), (57, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c1258, c1260, c1255, c1256, c246] c1923 (by decide) p (sat_cons (step1258 p h) (sat_cons (step1260 p h) (sat_cons (step1255 p h) (sat_cons (step1256 p h) (sat_cons (step246 p h) (sat_nil p))))))
def c1924 : List Lit := [(1645, true), (58, true), (53, true), (62, false)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c874, c1256, c1258, c1252, c268, c1268, c1271, c1259, c1254, c1257, c230] c1924 (by decide) p (sat_cons (step874 p h) (sat_cons (step1256 p h) (sat_cons (step1258 p h) (sat_cons (step1252 p h) (sat_cons (step268 p h) (sat_cons (step1268 p h) (sat_cons (step1271 p h) (sat_cons (step1259 p h) (sat_cons (step1254 p h) (sat_cons (step1257 p h) (sat_cons (step230 p h) (sat_nil p))))))))))))
def c1925 : List Lit := [(1805, true), (82, false), (124, false)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c1571, c1572, c811] c1925 (by decide) p (sat_cons (step1571 p h) (sat_cons (step1572 p h) (sat_cons (step811 p h) (sat_nil p))))
def c1926 : List Lit := [(1820, true), (109, false), (1804, false), (117, true), (1806, false)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c896, c1575, c1588, c1558, c1560, c1598, c1603, c1589, c1561, c1563, c1578, c1559, c1554, c1555, c623, c712, c741] c1926 (by decide) p (sat_cons (step896 p h) (sat_cons (step1575 p h) (sat_cons (step1588 p h) (sat_cons (step1558 p h) (sat_cons (step1560 p h) (sat_cons (step1598 p h) (sat_cons (step1603 p h) (sat_cons (step1589 p h) (sat_cons (step1561 p h) (sat_cons (step1563 p h) (sat_cons (step1578 p h) (sat_cons (step1559 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step623 p h) (sat_cons (step712 p h) (sat_cons (step741 p h) (sat_nil p))))))))))))))))))
def c1927 : List Lit := [(1737, true), (1775, true)]
theorem step1927 (p : Nat → Bool) (h : Constraints p) : clause p c1927 = true :=
  Snake9.LocalRup.prove_clause [c890, c1510, c1508, c1512, c1504, c1507, c474, c1436, c1438, c1433, c421, c488, c487] c1927 (by decide) p (sat_cons (step890 p h) (sat_cons (step1510 p h) (sat_cons (step1508 p h) (sat_cons (step1512 p h) (sat_cons (step1504 p h) (sat_cons (step1507 p h) (sat_cons (step474 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1433 p h) (sat_cons (step421 p h) (sat_cons (step488 p h) (sat_cons (step487 p h) (sat_nil p))))))))))))))
def c1928 : List Lit := [(89, false), (1775, true), (107, false)]
theorem step1928 (p : Nat → Bool) (h : Constraints p) : clause p c1928 = true :=
  Snake9.LocalRup.prove_clause [c890, c1510, c1508, c1512, c1504, c1507, c474, c423, c488, c487] c1928 (by decide) p (sat_cons (step890 p h) (sat_cons (step1510 p h) (sat_cons (step1508 p h) (sat_cons (step1512 p h) (sat_cons (step1504 p h) (sat_cons (step1507 p h) (sat_cons (step474 p h) (sat_cons (step423 p h) (sat_cons (step488 p h) (sat_cons (step487 p h) (sat_nil p)))))))))))
def c1929 : List Lit := [(113, true), (93, false), (1801, true), (1796, true), (117, true), (107, false)]
theorem step1929 (p : Nat → Bool) (h : Constraints p) : clause p c1929 = true :=
  Snake9.LocalRup.prove_clause [c896, c1554, c1556, c1564, c1559, c619, c698, c742] c1929 (by decide) p (sat_cons (step896 p h) (sat_cons (step1554 p h) (sat_cons (step1556 p h) (sat_cons (step1564 p h) (sat_cons (step1559 p h) (sat_cons (step619 p h) (sat_cons (step698 p h) (sat_cons (step742 p h) (sat_nil p)))))))))
def c1930 : List Lit := [(1820, true), (109, false), (111, true), (112, false), (1800, false), (1806, false), (120, true), (117, true)]
theorem step1930 (p : Nat → Bool) (h : Constraints p) : clause p c1930 = true :=
  Snake9.LocalRup.prove_clause [c898, c1569, c1603, c1926, c1585, c1570, c1578, c802, c797] c1930 (by decide) p (sat_cons (step898 p h) (sat_cons (step1569 p h) (sat_cons (step1603 p h) (sat_cons (step1926 p h) (sat_cons (step1585 p h) (sat_cons (step1570 p h) (sat_cons (step1578 p h) (sat_cons (step802 p h) (sat_cons (step797 p h) (sat_nil p))))))))))
def c1931 : List Lit := [(122, false), (121, false), (111, true), (112, false)]
theorem step1931 (p : Nat → Bool) (h : Constraints p) : clause p c1931 = true :=
  Snake9.LocalRup.prove_clause [c898, c802, c797] c1931 (by decide) p (sat_cons (step898 p h) (sat_cons (step802 p h) (sat_cons (step797 p h) (sat_nil p))))
def c1932 : List Lit := [(103, false), (128, false), (1775, true)]
theorem step1932 (p : Nat → Bool) (h : Constraints p) : clause p c1932 = true :=
  Snake9.LocalRup.prove_clause [c891, c888, c1510, c1507, c1508, c1512, c1504, c474, c494, c1505, c522, c524, c468] c1932 (by decide) p (sat_cons (step891 p h) (sat_cons (step888 p h) (sat_cons (step1510 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step1512 p h) (sat_cons (step1504 p h) (sat_cons (step474 p h) (sat_cons (step494 p h) (sat_cons (step1505 p h) (sat_cons (step522 p h) (sat_cons (step524 p h) (sat_cons (step468 p h) (sat_nil p))))))))))))))
def c1933 : List Lit := [(1686, true), (18, true), (1623, false), (1644, false), (16, true)]
theorem step1933 (p : Nat → Bool) (h : Constraints p) : clause p c1933 = true :=
  Snake9.LocalRup.prove_clause [c1922, c1855, c867, c1118, c1122, c1127, c1275, c1312, c1324, c1337, c1314, c1169, c1873, c1285, c1154, c1241, c1245, c1863, c1247, c1243, c1238, c1239, c185, c197, c202] c1933 (by decide) p (sat_cons (step1922 p h) (sat_cons (step1855 p h) (sat_cons (step867 p h) (sat_cons (step1118 p h) (sat_cons (step1122 p h) (sat_cons (step1127 p h) (sat_cons (step1275 p h) (sat_cons (step1312 p h) (sat_cons (step1324 p h) (sat_cons (step1337 p h) (sat_cons (step1314 p h) (sat_cons (step1169 p h) (sat_cons (step1873 p h) (sat_cons (step1285 p h) (sat_cons (step1154 p h) (sat_cons (step1241 p h) (sat_cons (step1245 p h) (sat_cons (step1863 p h) (sat_cons (step1247 p h) (sat_cons (step1243 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step185 p h) (sat_cons (step197 p h) (sat_cons (step202 p h) (sat_nil p))))))))))))))))))))))))))
def c1934 : List Lit := [(1749, true), (1725, false), (1738, false), (86, true)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c1425, c1430, c1446, c1466, c1461, c1426, c1450, c1908, c1432] c1934 (by decide) p (sat_cons (step1425 p h) (sat_cons (step1430 p h) (sat_cons (step1446 p h) (sat_cons (step1466 p h) (sat_cons (step1461 p h) (sat_cons (step1426 p h) (sat_cons (step1450 p h) (sat_cons (step1908 p h) (sat_cons (step1432 p h) (sat_nil p))))))))))
def c1935 : List Lit := [(1623, true), (43, true), (1617, false), (42, true), (112, false), (1604, false), (107, false)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c1230, c1878, c1200, c567, c1195] c1935 (by decide) p (sat_cons (step1230 p h) (sat_cons (step1878 p h) (sat_cons (step1200 p h) (sat_cons (step567 p h) (sat_cons (step1195 p h) (sat_nil p))))))
def c1936 : List Lit := [(91, true), (103, false), (95, false)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c888, c470, c469, c1760] c1936 (by decide) p (sat_cons (step888 p h) (sat_cons (step470 p h) (sat_cons (step469 p h) (sat_cons (step1760 p h) (sat_nil p)))))
def c1937 : List Lit := [(91, true), (92, true), (104, true), (1775, true), (117, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c891, c888, c1786, c1510, c1507, c1508, c1512, c1504, c474, c494, c1505, c470, c1936, c466, c511, c1019, c1034, c1022, c1036, c1023, c1037, c1024, c1052, c1027, c1079, c1085] c1937 (by decide) p (sat_cons (step891 p h) (sat_cons (step888 p h) (sat_cons (step1786 p h) (sat_cons (step1510 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step1512 p h) (sat_cons (step1504 p h) (sat_cons (step474 p h) (sat_cons (step494 p h) (sat_cons (step1505 p h) (sat_cons (step470 p h) (sat_cons (step1936 p h) (sat_cons (step466 p h) (sat_cons (step511 p h) (sat_cons (step1019 p h) (sat_cons (step1034 p h) (sat_cons (step1022 p h) (sat_cons (step1036 p h) (sat_cons (step1023 p h) (sat_cons (step1037 p h) (sat_cons (step1024 p h) (sat_cons (step1052 p h) (sat_cons (step1027 p h) (sat_cons (step1079 p h) (sat_cons (step1085 p h) (sat_nil p)))))))))))))))))))))))))))
def c1938 : List Lit := [(1633, true), (25, false), (51, true)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c867, c1241, c1245, c1247, c1243, c1238, c1239, c197, c185, c202] c1938 (by decide) p (sat_cons (step867 p h) (sat_cons (step1241 p h) (sat_cons (step1245 p h) (sat_cons (step1247 p h) (sat_cons (step1243 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step197 p h) (sat_cons (step185 p h) (sat_cons (step202 p h) (sat_nil p)))))))))))
def c1939 : List Lit := [(103, false), (31, false), (102, false), (95, false)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c888, c517, c514, c468] c1939 (by decide) p (sat_cons (step888 p h) (sat_cons (step517 p h) (sat_cons (step514 p h) (sat_cons (step468 p h) (sat_nil p)))))
def c1940 : List Lit := [(104, false), (102, true), (103, false), (95, false)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c892, c531, c526] c1940 (by decide) p (sat_cons (step892 p h) (sat_cons (step531 p h) (sat_cons (step526 p h) (sat_nil p))))
def c1941 : List Lit := [(100, false), (86, false), (98, false), (102, true)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c891, c473, c494] c1941 (by decide) p (sat_cons (step891 p h) (sat_cons (step473 p h) (sat_cons (step494 p h) (sat_nil p))))
def c1942 : List Lit := [(1805, false), (45, true), (1811, true)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c898, c1580, c1574, c1577, c1583, c798, c1568, c1569, c803] c1942 (by decide) p (sat_cons (step898 p h) (sat_cons (step1580 p h) (sat_cons (step1574 p h) (sat_cons (step1577 p h) (sat_cons (step1583 p h) (sat_cons (step798 p h) (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step803 p h) (sat_nil p))))))))))
def c1943 : List Lit := [(1807, false), (1805, true), (1811, true), (1818, true), (1797, false), (128, true)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c897, c899, c1572, c1571, c1579, c1583, c1606, c1568, c1569, c1566, c762, c834, c792, c823, c821, c800, c1771, c1556] c1943 (by decide) p (sat_cons (step897 p h) (sat_cons (step899 p h) (sat_cons (step1572 p h) (sat_cons (step1571 p h) (sat_cons (step1579 p h) (sat_cons (step1583 p h) (sat_cons (step1606 p h) (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step1566 p h) (sat_cons (step762 p h) (sat_cons (step834 p h) (sat_cons (step792 p h) (sat_cons (step823 p h) (sat_cons (step821 p h) (sat_cons (step800 p h) (sat_cons (step1771 p h) (sat_cons (step1556 p h) (sat_nil p)))))))))))))))))))
def c1944 : List Lit := [(1801, true), (117, true), (112, true), (111, true), (126, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c896, c1558, c1555, c1566, c1564, c1556, c1559, c706, c742] c1944 (by decide) p (sat_cons (step896 p h) (sat_cons (step1558 p h) (sat_cons (step1555 p h) (sat_cons (step1566 p h) (sat_cons (step1564 p h) (sat_cons (step1556 p h) (sat_cons (step1559 p h) (sat_cons (step706 p h) (sat_cons (step742 p h) (sat_nil p))))))))))
def c1945 : List Lit := [(1803, true), (123, false), (122, false)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1569, c803] c1945 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step803 p h) (sat_nil p))))
def c1946 : List Lit := [(95, true), (1776, true), (102, true)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c891, c1515, c1505, c1506, c1513, c1507, c1508, c494, c474] c1946 (by decide) p (sat_cons (step891 p h) (sat_cons (step1515 p h) (sat_cons (step1505 p h) (sat_cons (step1506 p h) (sat_cons (step1513 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step494 p h) (sat_cons (step474 p h) (sat_nil p))))))))))
def c1947 : List Lit := [(112, false), (123, false), (1804, true), (122, false)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c802, c801, c1570] c1947 (by decide) p (sat_cons (step802 p h) (sat_cons (step801 p h) (sat_cons (step1570 p h) (sat_nil p))))
def c1948 : List Lit := [(3, false), (51, false)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c29, c1779, c5] c1948 (by decide) p (sat_cons (step29 p h) (sat_cons (step1779 p h) (sat_cons (step5 p h) (sat_nil p))))
def c1949 : List Lit := [(15, false), (51, false)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c29, c1779, c6] c1949 (by decide) p (sat_cons (step29 p h) (sat_cons (step1779 p h) (sat_cons (step6 p h) (sat_nil p))))
def c1950 : List Lit := [(2, false), (4, true)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c842, c7] c1950 (by decide) p (sat_cons (step842 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1951 : List Lit := [(5, false), (3, false), (54, false)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c1779, c8] c1951 (by decide) p (sat_cons (step1779 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1952 : List Lit := [(5, true), (54, true), (3, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c843, c9] c1952 (by decide) p (sat_cons (step843 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1953 : List Lit := [(12, true), (5, true), (6, false)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c844, c14] c1953 (by decide) p (sat_cons (step844 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1954 : List Lit := [(12, true), (4, true), (6, false)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c844, c15] c1954 (by decide) p (sat_cons (step844 p h) (sat_cons (step15 p h) (sat_nil p)))
def c1955 : List Lit := [(4, true), (5, true), (6, false)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c844, c16] c1955 (by decide) p (sat_cons (step844 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1956 : List Lit := [(27, true), (64, true), (9, false)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c847, c20] c1956 (by decide) p (sat_cons (step847 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1957 : List Lit := [(9, false), (10, true), (27, true)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c847, c21] c1957 (by decide) p (sat_cons (step847 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1958 : List Lit := [(10, false), (11, true), (138, true)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c1785, c22] c1958 (by decide) p (sat_cons (step1785 p h) (sat_cons (step22 p h) (sat_nil p)))
def c1959 : List Lit := [(10, false), (9, true), (138, true)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c1785, c23] c1959 (by decide) p (sat_cons (step1785 p h) (sat_cons (step23 p h) (sat_nil p)))
def c1960 : List Lit := [(11, false), (12, true)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c848, c24] c1960 (by decide) p (sat_cons (step848 p h) (sat_cons (step24 p h) (sat_nil p)))
def c1961 : List Lit := [(11, false), (10, true)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c848, c25] c1961 (by decide) p (sat_cons (step848 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1962 : List Lit := [(14, true), (20, true), (15, false), (87, true)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c849, c40] c1962 (by decide) p (sat_cons (step849 p h) (sat_cons (step40 p h) (sat_nil p)))
def c1963 : List Lit := [(34, true), (90, true), (16, false), (17, true), (22, true)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c850, c41] c1963 (by decide) p (sat_cons (step850 p h) (sat_cons (step41 p h) (sat_nil p)))
def c1964 : List Lit := [(22, true), (14, true), (16, false), (34, true), (90, true)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c850, c42] c1964 (by decide) p (sat_cons (step850 p h) (sat_cons (step42 p h) (sat_nil p)))
def c1965 : List Lit := [(22, true), (16, false), (14, true), (17, true), (90, true)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c850, c43] c1965 (by decide) p (sat_cons (step850 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1966 : List Lit := [(26, true), (18, false), (91, true)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c851, c50] c1966 (by decide) p (sat_cons (step851 p h) (sat_cons (step50 p h) (sat_nil p)))
def c1967 : List Lit := [(18, false), (91, true), (17, true)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c851, c51] c1967 (by decide) p (sat_cons (step851 p h) (sat_cons (step51 p h) (sat_nil p)))
def c1968 : List Lit := [(27, true), (20, true), (19, false), (22, true)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c852, c52] c1968 (by decide) p (sat_cons (step852 p h) (sat_cons (step52 p h) (sat_nil p)))
def c1969 : List Lit := [(20, true), (14, true), (19, false), (27, true)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c852, c53] c1969 (by decide) p (sat_cons (step852 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1970 : List Lit := [(38, true), (21, false), (20, true), (30, true)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c853, c72] c1970 (by decide) p (sat_cons (step853 p h) (sat_cons (step72 p h) (sat_nil p)))
end B112E034
