import B112E050Part0001
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1944 : List Lit := [(1817, true), (1797, false), (1807, false), (125, true), (1799, false)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c899, c1595, c1608, c1612, c1599, c1579, c1584, c1585, c1571, c796, c793] c1944 (by decide) p (sat_cons (step899 p h) (sat_cons (step1595 p h) (sat_cons (step1608 p h) (sat_cons (step1612 p h) (sat_cons (step1599 p h) (sat_cons (step1579 p h) (sat_cons (step1584 p h) (sat_cons (step1585 p h) (sat_cons (step1571 p h) (sat_cons (step796 p h) (sat_cons (step793 p h) (sat_nil p))))))))))))
def c1945 : List Lit := [(1735, true), (80, true)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c883, c1425, c1427, c1423, c1419, c1420, c366, c364] c1945 (by decide) p (sat_cons (step883 p h) (sat_cons (step1425 p h) (sat_cons (step1427 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step366 p h) (sat_cons (step364 p h) (sat_nil p)))))))))
def c1946 : List Lit := [(1660, true), (56, true), (1644, false), (61, false), (62, false)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c1247, c1254, c1238, c1266, c1270, c1257, c1241, c1248, c1232, c221] c1946 (by decide) p (sat_cons (step1247 p h) (sat_cons (step1254 p h) (sat_cons (step1238 p h) (sat_cons (step1266 p h) (sat_cons (step1270 p h) (sat_cons (step1257 p h) (sat_cons (step1241 p h) (sat_cons (step1248 p h) (sat_cons (step1232 p h) (sat_cons (step221 p h) (sat_nil p)))))))))))
def c1947 : List Lit := [(1773, true), (102, false), (62, false)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1522, c582] c1947 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step582 p h) (sat_nil p))))
def c1948 : List Lit := [(1724, true), (1707, false)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c1377, c1406, c1402, c1378, c1389, c1903] c1948 (by decide) p (sat_cons (step1377 p h) (sat_cons (step1406 p h) (sat_cons (step1402 p h) (sat_cons (step1378 p h) (sat_cons (step1389 p h) (sat_cons (step1903 p h) (sat_nil p)))))))
def c1949 : List Lit := [(7, false), (1718, true), (80, false), (62, false)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c308, c307, c1388] c1949 (by decide) p (sat_cons (step308 p h) (sat_cons (step307 p h) (sat_cons (step1388 p h) (sat_nil p))))
def c1950 : List Lit := [(1620, false), (1635, true)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c1222, c1192, c1195, c1219, c1186, c1206, c1208, c1942, c1204, c1201, c101] c1950 (by decide) p (sat_cons (step1222 p h) (sat_cons (step1192 p h) (sat_cons (step1195 p h) (sat_cons (step1219 p h) (sat_cons (step1186 p h) (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step1942 p h) (sat_cons (step1204 p h) (sat_cons (step1201 p h) (sat_cons (step101 p h) (sat_nil p))))))))))))
def c1951 : List Lit := [(43, false), (33, false), (35, false)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c1825, c1822, c1823, c864, c860, c100, c108, c134, c140, c151, c1820, c129, c913, c965, c916, c968, c917, c972, c919, c974, c956, c1002, c1008] c1951 (by decide) p (sat_cons (step1825 p h) (sat_cons (step1822 p h) (sat_cons (step1823 p h) (sat_cons (step864 p h) (sat_cons (step860 p h) (sat_cons (step100 p h) (sat_cons (step108 p h) (sat_cons (step134 p h) (sat_cons (step140 p h) (sat_cons (step151 p h) (sat_cons (step1820 p h) (sat_cons (step129 p h) (sat_cons (step913 p h) (sat_cons (step965 p h) (sat_cons (step916 p h) (sat_cons (step968 p h) (sat_cons (step917 p h) (sat_cons (step972 p h) (sat_cons (step919 p h) (sat_cons (step974 p h) (sat_cons (step956 p h) (sat_cons (step1002 p h) (sat_cons (step1008 p h) (sat_nil p))))))))))))))))))))))))
def c1952 : List Lit := [(102, false), (1790, true), (62, false), (109, true), (27, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c566, c564, c565, c1537, c1523, c1539, c1525, c1557] c1952 (by decide) p (sat_cons (step566 p h) (sat_cons (step564 p h) (sat_cons (step565 p h) (sat_cons (step1537 p h) (sat_cons (step1523 p h) (sat_cons (step1539 p h) (sat_cons (step1525 p h) (sat_cons (step1557 p h) (sat_nil p)))))))))
def c1953 : List Lit := [(5, false), (68, false), (6, true), (33, false)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c847, c10, c3] c1953 (by decide) p (sat_cons (step847 p h) (sat_cons (step10 p h) (sat_cons (step3 p h) (sat_nil p))))
def c1954 : List Lit := [(1748, true), (85, true)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c1423, c1425, c1456, c1452, c1426, c1894, c1424] c1954 (by decide) p (sat_cons (step1423 p h) (sat_cons (step1425 p h) (sat_cons (step1456 p h) (sat_cons (step1452 p h) (sat_cons (step1426 p h) (sat_cons (step1894 p h) (sat_cons (step1424 p h) (sat_nil p))))))))
def c1955 : List Lit := [(1731, true), (73, false), (68, false)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c878, c1419, c1420, c288, c353, c286] c1955 (by decide) p (sat_cons (step878 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step288 p h) (sat_cons (step353 p h) (sat_cons (step286 p h) (sat_nil p)))))))
def c1956 : List Lit := [(1811, true), (123, true), (81, true)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c1584, c1602, c1599, c1586, c1590, c1592, c1938, c1587, c833] c1956 (by decide) p (sat_cons (step1584 p h) (sat_cons (step1602 p h) (sat_cons (step1599 p h) (sat_cons (step1586 p h) (sat_cons (step1590 p h) (sat_cons (step1592 p h) (sat_cons (step1938 p h) (sat_cons (step1587 p h) (sat_cons (step833 p h) (sat_nil p))))))))))
def c1957 : List Lit := [(86, true), (1741, true)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c886, c1437, c1436, c448, c447, c1798] c1957 (by decide) p (sat_cons (step886 p h) (sat_cons (step1437 p h) (sat_cons (step1436 p h) (sat_cons (step448 p h) (sat_cons (step447 p h) (sat_cons (step1798 p h) (sat_nil p)))))))
def c1958 : List Lit := [(94, false), (1789, true), (1743, true)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1434, c1439, c1437, c1957, c372, c1535, c1436, c491, c492, c1518, c1532, c1526, c1541, c1552] c1958 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1434 p h) (sat_cons (step1439 p h) (sat_cons (step1437 p h) (sat_cons (step1957 p h) (sat_cons (step372 p h) (sat_cons (step1535 p h) (sat_cons (step1436 p h) (sat_cons (step491 p h) (sat_cons (step492 p h) (sat_cons (step1518 p h) (sat_cons (step1532 p h) (sat_cons (step1526 p h) (sat_cons (step1541 p h) (sat_cons (step1552 p h) (sat_nil p))))))))))))))))
def c1959 : List Lit := [(1789, true), (1743, true)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c886, c1441, c1434, c1439, c1437, c1957, c372, c1535, c1436, c1958, c446, c475, c474, c1533, c1519, c1541, c1526, c1552] c1959 (by decide) p (sat_cons (step886 p h) (sat_cons (step1441 p h) (sat_cons (step1434 p h) (sat_cons (step1439 p h) (sat_cons (step1437 p h) (sat_cons (step1957 p h) (sat_cons (step372 p h) (sat_cons (step1535 p h) (sat_cons (step1436 p h) (sat_cons (step1958 p h) (sat_cons (step446 p h) (sat_cons (step475 p h) (sat_cons (step474 p h) (sat_cons (step1533 p h) (sat_cons (step1519 p h) (sat_cons (step1541 p h) (sat_cons (step1526 p h) (sat_cons (step1552 p h) (sat_nil p)))))))))))))))))))
def c1960 : List Lit := [(1799, true)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1578, c1922] c1960 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1578 p h) (sat_cons (step1922 p h) (sat_nil p))))
def c1961 : List Lit := [(36, false), (39, false), (109, false), (33, false)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c861, c92, c111, c112] c1961 (by decide) p (sat_cons (step861 p h) (sat_cons (step92 p h) (sat_cons (step111 p h) (sat_cons (step112 p h) (sat_nil p)))))
def c1962 : List Lit := [(102, true), (90, true), (91, false), (96, false), (1774, true), (227, true)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c885, c890, c445, c416, c422, c547, c1523, c562] c1962 (by decide) p (sat_cons (step885 p h) (sat_cons (step890 p h) (sat_cons (step445 p h) (sat_cons (step416 p h) (sat_cons (step422 p h) (sat_cons (step547 p h) (sat_cons (step1523 p h) (sat_cons (step562 p h) (sat_nil p)))))))))
def c1963 : List Lit := [(1635, true), (1622, false)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c1950, c1219, c1190, c1206, c1208, c1942, c1204, c1201, c102] c1963 (by decide) p (sat_cons (step1950 p h) (sat_cons (step1219 p h) (sat_cons (step1190 p h) (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step1942 p h) (sat_cons (step1204 p h) (sat_cons (step1201 p h) (sat_cons (step102 p h) (sat_nil p))))))))))
def c1964 : List Lit := [(43, false), (42, false), (39, false), (35, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c860, c102, c151, c108] c1964 (by decide) p (sat_cons (step860 p h) (sat_cons (step102 p h) (sat_cons (step151 p h) (sat_cons (step108 p h) (sat_nil p)))))
def c1965 : List Lit := [(1788, true), (1781, false), (87, false), (97, false), (62, false)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c890, c1538, c1547, c1551, c1541, c1524, c1532, c1521, c1947, c666, c431, c560] c1965 (by decide) p (sat_cons (step890 p h) (sat_cons (step1538 p h) (sat_cons (step1547 p h) (sat_cons (step1551 p h) (sat_cons (step1541 p h) (sat_cons (step1524 p h) (sat_cons (step1532 p h) (sat_cons (step1521 p h) (sat_cons (step1947 p h) (sat_cons (step666 p h) (sat_cons (step431 p h) (sat_cons (step560 p h) (sat_nil p)))))))))))))
def c1966 : List Lit := [(1773, true), (66, false), (87, false), (97, false), (62, false)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c890, c1521, c1947, c431, c560, c656] c1966 (by decide) p (sat_cons (step890 p h) (sat_cons (step1521 p h) (sat_cons (step1947 p h) (sat_cons (step431 p h) (sat_cons (step560 p h) (sat_cons (step656 p h) (sat_nil p)))))))
def c1967 : List Lit := [(101, false), (90, true), (102, true), (66, false), (97, false)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c890, c560, c656] c1967 (by decide) p (sat_cons (step890 p h) (sat_cons (step560 p h) (sat_cons (step656 p h) (sat_nil p))))
def c1968 : List Lit := [(106, true), (67, true), (65, false), (66, false), (1661, true), (96, false), (1650, false)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c874, c241, c242, c238, c208, c205, c1249, c1237, c1255, c1239, c1271] c1968 (by decide) p (sat_cons (step874 p h) (sat_cons (step241 p h) (sat_cons (step242 p h) (sat_cons (step238 p h) (sat_cons (step208 p h) (sat_cons (step205 p h) (sat_cons (step1249 p h) (sat_cons (step1237 p h) (sat_cons (step1255 p h) (sat_cons (step1239 p h) (sat_cons (step1271 p h) (sat_nil p))))))))))))
def c1969 : List Lit := [(100, true), (102, true), (1789, true), (1774, true), (87, false), (97, false)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c890, c1522, c1523, c1524, c431, c560, c1552, c666, c667, c1532, c1536, c1541] c1969 (by decide) p (sat_cons (step890 p h) (sat_cons (step1522 p h) (sat_cons (step1523 p h) (sat_cons (step1524 p h) (sat_cons (step431 p h) (sat_cons (step560 p h) (sat_cons (step1552 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step1532 p h) (sat_cons (step1536 p h) (sat_cons (step1541 p h) (sat_nil p)))))))))))))
def c1970 : List Lit := [(1815, true)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1606] c1970 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1606 p h) (sat_nil p)))
def c1971 : List Lit := [(1715, false), (1725, true), (1707, false)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c1377, c1403, c1391, c1392, c1407, c1903, c1378] c1971 (by decide) p (sat_cons (step1377 p h) (sat_cons (step1403 p h) (sat_cons (step1391 p h) (sat_cons (step1392 p h) (sat_cons (step1407 p h) (sat_cons (step1903 p h) (sat_cons (step1378 p h) (sat_nil p))))))))
def c1972 : List Lit := [(1717, true), (72, false), (1710, true), (62, false)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c880, c1386, c1387, c322, c303, c304, c298, c276, c1374] c1972 (by decide) p (sat_cons (step880 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step322 p h) (sat_cons (step303 p h) (sat_cons (step304 p h) (sat_cons (step298 p h) (sat_cons (step276 p h) (sat_cons (step1374 p h) (sat_nil p))))))))))
def c1973 : List Lit := [(80, true), (71, true), (69, false), (72, false), (1718, true)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c880, c877, c304, c284, c1388, c270] c1973 (by decide) p (sat_cons (step880 p h) (sat_cons (step877 p h) (sat_cons (step304 p h) (sat_cons (step284 p h) (sat_cons (step1388 p h) (sat_cons (step270 p h) (sat_nil p)))))))
def c1974 : List Lit := [(1725, true), (1707, false), (62, false)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c1377, c1411, c1403, c1379, c1390, c1971, c1384, c1972, c1389, c1407, c1378, c1372, c1373, c274, c1973, c321, c322, c1388] c1974 (by decide) p (sat_cons (step1377 p h) (sat_cons (step1411 p h) (sat_cons (step1403 p h) (sat_cons (step1379 p h) (sat_cons (step1390 p h) (sat_cons (step1971 p h) (sat_cons (step1384 p h) (sat_cons (step1972 p h) (sat_cons (step1389 p h) (sat_cons (step1407 p h) (sat_cons (step1378 p h) (sat_cons (step1372 p h) (sat_cons (step1373 p h) (sat_cons (step274 p h) (sat_cons (step1973 p h) (sat_cons (step321 p h) (sat_cons (step322 p h) (sat_cons (step1388 p h) (sat_nil p)))))))))))))))))))
def c1975 : List Lit := [(1812, true), (109, false), (1805, false), (104, false), (123, true)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c899, c1590, c1584, c1600, c1603, c1593, c1586, c830, c790, c794] c1975 (by decide) p (sat_cons (step899 p h) (sat_cons (step1590 p h) (sat_cons (step1584 p h) (sat_cons (step1600 p h) (sat_cons (step1603 p h) (sat_cons (step1593 p h) (sat_cons (step1586 p h) (sat_cons (step830 p h) (sat_cons (step790 p h) (sat_cons (step794 p h) (sat_nil p)))))))))))
def c1976 : List Lit := [(121, false), (124, false), (125, true), (109, false)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c899, c790, c794] c1976 (by decide) p (sat_cons (step899 p h) (sat_cons (step790 p h) (sat_cons (step794 p h) (sat_nil p))))
def c1977 : List Lit := [(63, true), (1655, true), (68, false), (187, true), (87, false)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c871, c1249, c216, c1255, c1246, c173, c220] c1977 (by decide) p (sat_cons (step871 p h) (sat_cons (step1249 p h) (sat_cons (step216 p h) (sat_cons (step1255 p h) (sat_cons (step1246 p h) (sat_cons (step173 p h) (sat_cons (step220 p h) (sat_nil p))))))))
def c1978 : List Lit := [(1580, true), (100, false), (96, false)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c854, c1125, c1126, c56, c403, c40] c1978 (by decide) p (sat_cons (step854 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step56 p h) (sat_cons (step403 p h) (sat_cons (step40 p h) (sat_nil p)))))))
def c1979 : List Lit := [(1580, true), (1745, true), (96, false)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c854, c855, c1125, c1126, c56, c40, c44, c46, c400, c1753, c455, c1433, c1438, c1443] c1979 (by decide) p (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step56 p h) (sat_cons (step40 p h) (sat_cons (step44 p h) (sat_cons (step46 p h) (sat_cons (step400 p h) (sat_cons (step1753 p h) (sat_cons (step455 p h) (sat_cons (step1433 p h) (sat_cons (step1438 p h) (sat_cons (step1443 p h) (sat_nil p)))))))))))))))
def c1980 : List Lit := [(1788, true), (62, false), (87, false), (1783, false), (97, false)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c890, c1551, c1965, c1524, c1536, c1521, c1947, c667, c431, c560] c1980 (by decide) p (sat_cons (step890 p h) (sat_cons (step1551 p h) (sat_cons (step1965 p h) (sat_cons (step1524 p h) (sat_cons (step1536 p h) (sat_cons (step1521 p h) (sat_cons (step1947 p h) (sat_cons (step667 p h) (sat_cons (step431 p h) (sat_cons (step560 p h) (sat_nil p)))))))))))
def c1981 : List Lit := [(1660, true), (46, true), (115, false), (53, true), (96, false)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c869, c871, c1236, c1233, c1241, c1274, c1270, c1244, c1242, c1252, c1254, c1234, c1237, c1250, c1246, c1247, c221, c207, c472, c187, c188, c219, c174] c1981 (by decide) p (sat_cons (step869 p h) (sat_cons (step871 p h) (sat_cons (step1236 p h) (sat_cons (step1233 p h) (sat_cons (step1241 p h) (sat_cons (step1274 p h) (sat_cons (step1270 p h) (sat_cons (step1244 p h) (sat_cons (step1242 p h) (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step1234 p h) (sat_cons (step1237 p h) (sat_cons (step1250 p h) (sat_cons (step1246 p h) (sat_cons (step1247 p h) (sat_cons (step221 p h) (sat_cons (step207 p h) (sat_cons (step472 p h) (sat_cons (step187 p h) (sat_cons (step188 p h) (sat_cons (step219 p h) (sat_cons (step174 p h) (sat_nil p))))))))))))))))))))))))
def c1982 : List Lit := [(1660, false), (1670, true), (1691, true)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c1881, c1883, c1286, c1292, c1340, c1963, c1170, c1194, c1915] c1982 (by decide) p (sat_cons (step1881 p h) (sat_cons (step1883 p h) (sat_cons (step1286 p h) (sat_cons (step1292 p h) (sat_cons (step1340 p h) (sat_cons (step1963 p h) (sat_cons (step1170 p h) (sat_cons (step1194 p h) (sat_cons (step1915 p h) (sat_nil p))))))))))
def c1983 : List Lit := [(1635, true), (37, false), (46, false)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c1950, c1963, c1189, c1194, c113, c1186] c1983 (by decide) p (sat_cons (step1950 p h) (sat_cons (step1963 p h) (sat_cons (step1189 p h) (sat_cons (step1194 p h) (sat_cons (step113 p h) (sat_cons (step1186 p h) (sat_nil p)))))))
def c1984 : List Lit := [(1659, true), (115, false), (53, true), (96, false)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c869, c1236, c1238, c1269, c1265, c1239, c1241, c1254, c1237, c1232, c1247, c207, c472, c187, c188, c1763] c1984 (by decide) p (sat_cons (step869 p h) (sat_cons (step1236 p h) (sat_cons (step1238 p h) (sat_cons (step1269 p h) (sat_cons (step1265 p h) (sat_cons (step1239 p h) (sat_cons (step1241 p h) (sat_cons (step1254 p h) (sat_cons (step1237 p h) (sat_cons (step1232 p h) (sat_cons (step1247 p h) (sat_cons (step207 p h) (sat_cons (step472 p h) (sat_cons (step187 p h) (sat_cons (step188 p h) (sat_cons (step1763 p h) (sat_nil p)))))))))))))))))
def c1985 : List Lit := [(57, true), (51, false), (54, false), (93, true)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c869, c187, c188, c1763] c1985 (by decide) p (sat_cons (step869 p h) (sat_cons (step187 p h) (sat_cons (step188 p h) (sat_cons (step1763 p h) (sat_nil p)))))
def c1986 : List Lit := [(1691, true), (1660, false), (1606, false)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1982] c1986 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1982 p h) (sat_nil p)))
def c1987 : List Lit := [(1783, true), (106, true), (93, true)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c891, c1538, c1540, c1536, c1532, c1533, c618, c607] c1987 (by decide) p (sat_cons (step891 p h) (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step1536 p h) (sat_cons (step1532 p h) (sat_cons (step1533 p h) (sat_cons (step618 p h) (sat_cons (step607 p h) (sat_nil p)))))))))
def c1988 : List Lit := [(1731, true), (81, false), (124, false)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c1419, c1420, c356] c1988 (by decide) p (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step356 p h) (sat_nil p))))
def c1989 : List Lit := [(1635, true), (109, false)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c1215, c1950, c1963, c1189, c1190, c1194, c1186, c1951, c1961, c1204, c1201, c1209] c1989 (by decide) p (sat_cons (step1215 p h) (sat_cons (step1950 p h) (sat_cons (step1963 p h) (sat_cons (step1189 p h) (sat_cons (step1190 p h) (sat_cons (step1194 p h) (sat_cons (step1186 p h) (sat_cons (step1951 p h) (sat_cons (step1961 p h) (sat_cons (step1204 p h) (sat_cons (step1201 p h) (sat_cons (step1209 p h) (sat_nil p)))))))))))))
def c1990 : List Lit := [(1708, false), (1726, true), (1715, false)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1412, c1380, c1381, c1408, c1903, c1392] c1990 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1412 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step1408 p h) (sat_cons (step1903 p h) (sat_cons (step1392 p h) (sat_nil p))))))))
def c1991 : List Lit := [(1644, true), (57, false), (65, false)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1236, c201] c1991 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step201 p h) (sat_nil p))))
def c1992 : List Lit := [(1659, true), (46, true), (93, true), (53, false)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c1233, c1240, c1269, c1265, c1243, c1241, c1254, c1234, c1235, c1247, c1985, c200] c1992 (by decide) p (sat_cons (step1233 p h) (sat_cons (step1240 p h) (sat_cons (step1269 p h) (sat_cons (step1265 p h) (sat_cons (step1243 p h) (sat_cons (step1241 p h) (sat_cons (step1254 p h) (sat_cons (step1234 p h) (sat_cons (step1235 p h) (sat_cons (step1247 p h) (sat_cons (step1985 p h) (sat_cons (step200 p h) (sat_nil p)))))))))))))
def c1993 : List Lit := [(1707, true), (67, false), (62, false)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c1369, c1370, c251] c1993 (by decide) p (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step251 p h) (sat_nil p))))
def c1994 : List Lit := [(78, true), (1715, false), (1727, true), (1707, false), (80, true), (68, true)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c880, c1373, c1378, c1409, c1393, c1387, c1388, c1392, c304, c303, c1413, c1781, c1379, c1374] c1994 (by decide) p (sat_cons (step880 p h) (sat_cons (step1373 p h) (sat_cons (step1378 p h) (sat_cons (step1409 p h) (sat_cons (step1393 p h) (sat_cons (step1387 p h) (sat_cons (step1388 p h) (sat_cons (step1392 p h) (sat_cons (step304 p h) (sat_cons (step303 p h) (sat_cons (step1413 p h) (sat_cons (step1781 p h) (sat_cons (step1379 p h) (sat_cons (step1374 p h) (sat_nil p)))))))))))))))
def c1995 : List Lit := [(79, false), (69, false), (78, false), (80, true)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c880, c303, c298] c1995 (by decide) p (sat_cons (step880 p h) (sat_cons (step303 p h) (sat_cons (step298 p h) (sat_nil p))))
def c1996 : List Lit := [(117, false), (96, false), (127, false), (1798, true)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c773, c774, c1575] c1996 (by decide) p (sat_cons (step773 p h) (sat_cons (step774 p h) (sat_cons (step1575 p h) (sat_nil p))))
def c1997 : List Lit := [(93, true), (57, true), (117, true), (106, true), (96, false), (1597, true), (1588, false)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c887, c1141, c1160, c1865, c521, c523, c1752, c1126, c1127, c1864, c58, c1156, c1136, c1144] c1997 (by decide) p (sat_cons (step887 p h) (sat_cons (step1141 p h) (sat_cons (step1160 p h) (sat_cons (step1865 p h) (sat_cons (step521 p h) (sat_cons (step523 p h) (sat_cons (step1752 p h) (sat_cons (step1126 p h) (sat_cons (step1127 p h) (sat_cons (step1864 p h) (sat_cons (step58 p h) (sat_cons (step1156 p h) (sat_cons (step1136 p h) (sat_cons (step1144 p h) (sat_nil p)))))))))))))))
def c1998 : List Lit := [(57, false), (96, false), (1645, true), (65, false)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c205, c208, c1237] c1998 (by decide) p (sat_cons (step205 p h) (sat_cons (step208 p h) (sat_cons (step1237 p h) (sat_nil p))))
def c1999 : List Lit := [(113, true), (93, true), (1800, true), (117, true)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c897, c1581, c1570, c1572, c1579, c1573, c1574, c760, c766] c1999 (by decide) p (sat_cons (step897 p h) (sat_cons (step1581 p h) (sat_cons (step1570 p h) (sat_cons (step1572 p h) (sat_cons (step1579 p h) (sat_cons (step1573 p h) (sat_cons (step1574 p h) (sat_cons (step760 p h) (sat_cons (step766 p h) (sat_nil p))))))))))
def c2000 : List Lit := [(1817, true), (1797, false), (1805, false), (104, false)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1590, c1944, c1608, c1596, c1599, c1593, c1585, c830] c2000 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1590 p h) (sat_cons (step1944 p h) (sat_cons (step1608 p h) (sat_cons (step1596 p h) (sat_cons (step1599 p h) (sat_cons (step1593 p h) (sat_cons (step1585 p h) (sat_cons (step830 p h) (sat_nil p))))))))))
def c2001 : List Lit := [(1811, true), (109, false), (1805, false), (104, false)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c1590, c1596, c1599, c1593, c1585, c830, c1976] c2001 (by decide) p (sat_cons (step1590 p h) (sat_cons (step1596 p h) (sat_cons (step1599 p h) (sat_cons (step1593 p h) (sat_cons (step1585 p h) (sat_cons (step830 p h) (sat_cons (step1976 p h) (sat_nil p))))))))
def c2002 : List Lit := [(108, false), (125, true), (1776, true), (1779, true)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c892, c1533, c1532, c618, c611, c672, c669, c1521, c1518, c1527] c2002 (by decide) p (sat_cons (step892 p h) (sat_cons (step1533 p h) (sat_cons (step1532 p h) (sat_cons (step618 p h) (sat_cons (step611 p h) (sat_cons (step672 p h) (sat_cons (step669 p h) (sat_cons (step1521 p h) (sat_cons (step1518 p h) (sat_cons (step1527 p h) (sat_nil p)))))))))))
def c2003 : List Lit := [(114, false), (119, false), (1796, true), (123, false)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c756, c755, c1572] c2003 (by decide) p (sat_cons (step756 p h) (sat_cons (step755 p h) (sat_cons (step1572 p h) (sat_nil p))))
def c2004 : List Lit := [(35, false), (1607, true), (1796, true), (123, false)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c1919, c141, c147, c1099, c1139, c1896, c1141, c1175, c1867] c2004 (by decide) p (sat_cons (step1919 p h) (sat_cons (step141 p h) (sat_cons (step147 p h) (sat_cons (step1099 p h) (sat_cons (step1139 p h) (sat_cons (step1896 p h) (sat_cons (step1141 p h) (sat_cons (step1175 p h) (sat_cons (step1867 p h) (sat_nil p))))))))))
def c2005 : List Lit := [(1595, false), (1623, false), (1607, true), (1692, true), (1659, false), (44, false), (123, false)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c1883, c1169, c1175, c1332, c1896, c1305, c1099, c1224, c144, c143, c1204, c1200, c1209] c2005 (by decide) p (sat_cons (step1883 p h) (sat_cons (step1169 p h) (sat_cons (step1175 p h) (sat_cons (step1332 p h) (sat_cons (step1896 p h) (sat_cons (step1305 p h) (sat_cons (step1099 p h) (sat_cons (step1224 p h) (sat_cons (step144 p h) (sat_cons (step143 p h) (sat_cons (step1204 p h) (sat_cons (step1200 p h) (sat_cons (step1209 p h) (sat_nil p))))))))))))))
def c2006 : List Lit := [(1623, false), (1607, true), (123, false), (1692, true), (1659, false), (44, false)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c2005, c1867, c1141, c1139, c138, c149, c150, c1099, c1200, c1204, c1896, c1209, c1875, c1224, c1332, c1305] c2006 (by decide) p (sat_cons (step2005 p h) (sat_cons (step1867 p h) (sat_cons (step1141 p h) (sat_cons (step1139 p h) (sat_cons (step138 p h) (sat_cons (step149 p h) (sat_cons (step150 p h) (sat_cons (step1099 p h) (sat_cons (step1200 p h) (sat_cons (step1204 p h) (sat_cons (step1896 p h) (sat_cons (step1209 p h) (sat_cons (step1875 p h) (sat_cons (step1224 p h) (sat_cons (step1332 p h) (sat_cons (step1305 p h) (sat_nil p)))))))))))))))))
def c2007 : List Lit := [(1607, true), (1692, true), (1659, false), (44, false), (1796, true), (123, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c1883, c1170, c2004, c1915, c1190, c1195, c2006] c2007 (by decide) p (sat_cons (step1883 p h) (sat_cons (step1170 p h) (sat_cons (step2004 p h) (sat_cons (step1915 p h) (sat_cons (step1190 p h) (sat_cons (step1195 p h) (sat_cons (step2006 p h) (sat_nil p))))))))
end B112E050
