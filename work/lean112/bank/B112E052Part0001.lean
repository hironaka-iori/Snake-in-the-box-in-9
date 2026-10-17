import B112E052Part0000
namespace B112E052
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2054 : List Lit := [(79, false), (77, false), (67, false), (78, false), (1698, true)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c1006, c392, c1956, c1537, c366, c328] c2054 (by decide) p (sat_cons (step1006 p h) (sat_cons (step392 p h) (sat_cons (step1956 p h) (sat_cons (step1537 p h) (sat_cons (step366 p h) (sat_cons (step328 p h) (sat_nil p)))))))
def c2055 : List Lit := [(77, false), (1698, true), (67, false), (78, false)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c1006, c2054, c364, c365, c354, c329, c1537] c2055 (by decide) p (sat_cons (step1006 p h) (sat_cons (step2054 p h) (sat_cons (step364 p h) (sat_cons (step365 p h) (sat_cons (step354 p h) (sat_cons (step329 p h) (sat_cons (step1537 p h) (sat_nil p))))))))
def c2056 : List Lit := [(1719, false), (1736, true)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c1013, c1619, c1590, c1591, c1615, c1586, c1602, c1604, c1599, c1600, c1596, c562, c573, c534] c2056 (by decide) p (sat_cons (step1013 p h) (sat_cons (step1619 p h) (sat_cons (step1590 p h) (sat_cons (step1591 p h) (sat_cons (step1615 p h) (sat_cons (step1586 p h) (sat_cons (step1602 p h) (sat_cons (step1604 p h) (sat_cons (step1599 p h) (sat_cons (step1600 p h) (sat_cons (step1596 p h) (sat_cons (step562 p h) (sat_cons (step573 p h) (sat_cons (step534 p h) (sat_nil p)))))))))))))))
def c2057 : List Lit := [(77, false), (78, false), (1700, true), (84, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c1006, c1539, c2055, c398, c1532, c364, c1541, c354, c1536] c2057 (by decide) p (sat_cons (step1006 p h) (sat_cons (step1539 p h) (sat_cons (step2055 p h) (sat_cons (step398 p h) (sat_cons (step1532 p h) (sat_cons (step364 p h) (sat_cons (step1541 p h) (sat_cons (step354 p h) (sat_cons (step1536 p h) (sat_nil p))))))))))
def c2058 : List Lit := [(1697, true), (78, false), (84, false)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c1535, c1536, c2052, c330] c2058 (by decide) p (sat_cons (step1535 p h) (sat_cons (step1536 p h) (sat_cons (step2052 p h) (sat_cons (step330 p h) (sat_nil p)))))
def c2059 : List Lit := [(78, false), (1713, true), (1719, true)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c1007, c2051, c1570, c1583, c1582, c2057, c1546, c2058, c1538, c1566, c1557, c1555, c1548, c1549, c418, c431, c423] c2059 (by decide) p (sat_cons (step1007 p h) (sat_cons (step2051 p h) (sat_cons (step1570 p h) (sat_cons (step1583 p h) (sat_cons (step1582 p h) (sat_cons (step2057 p h) (sat_cons (step1546 p h) (sat_cons (step2058 p h) (sat_cons (step1538 p h) (sat_cons (step1566 p h) (sat_cons (step1557 p h) (sat_cons (step1555 p h) (sat_cons (step1548 p h) (sat_cons (step1549 p h) (sat_cons (step418 p h) (sat_cons (step431 p h) (sat_cons (step423 p h) (sat_nil p))))))))))))))))))
def c2060 : List Lit := [(1708, true), (78, true), (1719, true)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c1007, c1550, c1583, c1582, c1553, c1555, c1551, c1547, c431, c418, c423] c2060 (by decide) p (sat_cons (step1007 p h) (sat_cons (step1550 p h) (sat_cons (step1583 p h) (sat_cons (step1582 p h) (sat_cons (step1553 p h) (sat_cons (step1555 p h) (sat_cons (step1551 p h) (sat_cons (step1547 p h) (sat_cons (step431 p h) (sat_cons (step418 p h) (sat_cons (step423 p h) (sat_nil p))))))))))))
def c2061 : List Lit := [(77, false), (1699, true), (84, false)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c1003, c1538, c1535, c1540, c1532, c1536, c327, c393, c323, c339] c2061 (by decide) p (sat_cons (step1003 p h) (sat_cons (step1538 p h) (sat_cons (step1535 p h) (sat_cons (step1540 p h) (sat_cons (step1532 p h) (sat_cons (step1536 p h) (sat_cons (step327 p h) (sat_cons (step393 p h) (sat_cons (step323 p h) (sat_cons (step339 p h) (sat_nil p)))))))))))
def c2062 : List Lit := [(1713, true), (1719, true)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c1004, c1583, c1582, c1562, c2059, c1550, c1558, c2060, c1566, c1540, c1532, c2061, c1546, c1548, c1556, c344, c1551, c342, c418] c2062 (by decide) p (sat_cons (step1004 p h) (sat_cons (step1583 p h) (sat_cons (step1582 p h) (sat_cons (step1562 p h) (sat_cons (step2059 p h) (sat_cons (step1550 p h) (sat_cons (step1558 p h) (sat_cons (step2060 p h) (sat_cons (step1566 p h) (sat_cons (step1540 p h) (sat_cons (step1532 p h) (sat_cons (step2061 p h) (sat_cons (step1546 p h) (sat_cons (step1548 p h) (sat_cons (step1556 p h) (sat_cons (step344 p h) (sat_cons (step1551 p h) (sat_cons (step342 p h) (sat_cons (step418 p h) (sat_nil p))))))))))))))))))))
def c2063 : List Lit := [(1735, true)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c1013, c1610, c1614, c1602, c1604, c1588, c1599, c1600, c1596, c1586, c562, c573, c534] c2063 (by decide) p (sat_cons (step1013 p h) (sat_cons (step1610 p h) (sat_cons (step1614 p h) (sat_cons (step1602 p h) (sat_cons (step1604 p h) (sat_cons (step1588 p h) (sat_cons (step1599 p h) (sat_cons (step1600 p h) (sat_cons (step1596 p h) (sat_cons (step1586 p h) (sat_cons (step562 p h) (sat_cons (step573 p h) (sat_cons (step534 p h) (sat_nil p))))))))))))))
def c2064 : List Lit := [(81, false), (71, false), (1719, true), (1642, true)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c1007, c1009, c1583, c1582, c431, c423, c437, c415, c384, c1406] c2064 (by decide) p (sat_cons (step1007 p h) (sat_cons (step1009 p h) (sat_cons (step1583 p h) (sat_cons (step1582 p h) (sat_cons (step431 p h) (sat_cons (step423 p h) (sat_cons (step437 p h) (sat_cons (step415 p h) (sat_cons (step384 p h) (sat_cons (step1406 p h) (sat_nil p)))))))))))
def c2065 : List Lit := [(79, true), (1699, true), (84, false), (1648, true)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c1003, c1009, c1538, c1535, c1540, c1532, c1536, c327, c1533, c339, c439, c317, c293, c1391, c1405, c1393, c1407, c1419] c2065 (by decide) p (sat_cons (step1003 p h) (sat_cons (step1009 p h) (sat_cons (step1538 p h) (sat_cons (step1535 p h) (sat_cons (step1540 p h) (sat_cons (step1532 p h) (sat_cons (step1536 p h) (sat_cons (step327 p h) (sat_cons (step1533 p h) (sat_cons (step339 p h) (sat_cons (step439 p h) (sat_cons (step317 p h) (sat_cons (step293 p h) (sat_cons (step1391 p h) (sat_cons (step1405 p h) (sat_cons (step1393 p h) (sat_cons (step1407 p h) (sat_cons (step1419 p h) (sat_nil p)))))))))))))))))))
def c2066 : List Lit := [(1623, true)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c986, c1369, c1372, c1363, c1364, c1349, c1361, c1357, c1358, c1347, c192, c138, c146] c2066 (by decide) p (sat_cons (step986 p h) (sat_cons (step1369 p h) (sat_cons (step1372 p h) (sat_cons (step1363 p h) (sat_cons (step1364 p h) (sat_cons (step1349 p h) (sat_cons (step1361 p h) (sat_cons (step1357 p h) (sat_cons (step1358 p h) (sat_cons (step1347 p h) (sat_cons (step192 p h) (sat_cons (step138 p h) (sat_cons (step146 p h) (sat_nil p))))))))))))))
def c2067 : List Lit := [(1655, true)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c2066, c1436] c2067 (by decide) p (sat_cons (step2066 p h) (sat_cons (step1436 p h) (sat_nil p)))
def c2068 : List Lit := [(1579, true)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c984, c1291, c1293, c1288, c1285, c1286, c109, c85] c2068 (by decide) p (sat_cons (step984 p h) (sat_cons (step1291 p h) (sat_cons (step1293 p h) (sat_cons (step1288 p h) (sat_cons (step1285 p h) (sat_cons (step1286 p h) (sat_cons (step109 p h) (sat_cons (step85 p h) (sat_nil p)))))))))
def c2069 : List Lit := [(1583, true)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c2068, c1299] c2069 (by decide) p (sat_cons (step2068 p h) (sat_cons (step1299 p h) (sat_nil p)))
def c2070 : List Lit := [(1594, true)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c2069, c2043] c2070 (by decide) p (sat_cons (step2069 p h) (sat_cons (step2043 p h) (sat_nil p)))
def c2071 : List Lit := [(1675, true)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c2070, c2067, c1472] c2071 (by decide) p (sat_cons (step2070 p h) (sat_cons (step2067 p h) (sat_cons (step1472 p h) (sat_nil p))))
def c2072 : List Lit := [(1841, false)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c2071, c1919, c1906] c2072 (by decide) p (sat_cons (step2071 p h) (sat_cons (step1919 p h) (sat_cons (step1906 p h) (sat_nil p))))
def c2073 : List Lit := [(68, false), (1635, true), (56, false), (71, false)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c994, c1395, c1387, c1393, c1390, c1391, c211, c259, c229, c317, c239] c2073 (by decide) p (sat_cons (step994 p h) (sat_cons (step1395 p h) (sat_cons (step1387 p h) (sat_cons (step1393 p h) (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step211 p h) (sat_cons (step259 p h) (sat_cons (step229 p h) (sat_cons (step317 p h) (sat_cons (step239 p h) (sat_nil p))))))))))))
def c2074 : List Lit := [(122, false), (1789, true), (120, true), (113, false), (71, false)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c846, c847, c1737, c1741, c1746] c2074 (by decide) p (sat_cons (step846 p h) (sat_cons (step847 p h) (sat_cons (step1737 p h) (sat_cons (step1741 p h) (sat_cons (step1746 p h) (sat_nil p))))))
def c2075 : List Lit := [(1648, true), (55, true), (1633, false), (49, true)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c993, c1393, c1423, c1419, c1396, c1407, c1409, c1387, c1405, c1401, c226, c273] c2075 (by decide) p (sat_cons (step993 p h) (sat_cons (step1393 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step1396 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1387 p h) (sat_cons (step1405 p h) (sat_cons (step1401 p h) (sat_cons (step226 p h) (sat_cons (step273 p h) (sat_nil p)))))))))))))
def c2076 : List Lit := [(1624, true), (7, false), (1609, false)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c990, c1349, c1376, c1373, c1352, c1363, c1364, c1343, c1361, c1357, c1358, c137, c183, c174] c2076 (by decide) p (sat_cons (step990 p h) (sat_cons (step1349 p h) (sat_cons (step1376 p h) (sat_cons (step1373 p h) (sat_cons (step1352 p h) (sat_cons (step1363 p h) (sat_cons (step1364 p h) (sat_cons (step1343 p h) (sat_cons (step1361 p h) (sat_cons (step1357 p h) (sat_cons (step1358 p h) (sat_cons (step137 p h) (sat_cons (step183 p h) (sat_cons (step174 p h) (sat_nil p)))))))))))))))
def c2077 : List Lit := [(1721, true), (90, false), (113, true), (112, false)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c1012, c1585, c1586, c502, c514, c532] c2077 (by decide) p (sat_cons (step1012 p h) (sat_cons (step1585 p h) (sat_cons (step1586 p h) (sat_cons (step502 p h) (sat_cons (step514 p h) (sat_cons (step532 p h) (sat_nil p)))))))
def c2078 : List Lit := [(1712, true), (1697, false)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1569, c1565, c1539, c1541, c1552, c1554, c1532, c1550, c1546, c2055] c2078 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1569 p h) (sat_cons (step1565 p h) (sat_cons (step1539 p h) (sat_cons (step1541 p h) (sat_cons (step1552 p h) (sat_cons (step1554 p h) (sat_cons (step1532 p h) (sat_cons (step1550 p h) (sat_cons (step1546 p h) (sat_cons (step2055 p h) (sat_nil p))))))))))))
def c2079 : List Lit := [(18, false), (1730, true), (92, false), (114, false)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c548, c550, c1601] c2079 (by decide) p (sat_cons (step548 p h) (sat_cons (step550 p h) (sat_cons (step1601 p h) (sat_nil p))))
def c2080 : List Lit := [(102, false), (1730, true), (92, false), (114, false)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c571, c570, c1601] c2080 (by decide) p (sat_cons (step571 p h) (sat_cons (step570 p h) (sat_cons (step1601 p h) (sat_nil p))))
def c2081 : List Lit := [(1729, true), (92, false), (114, false)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c1599, c1600, c569] c2081 (by decide) p (sat_cons (step1599 p h) (sat_cons (step1600 p h) (sat_cons (step569 p h) (sat_nil p))))
def c2082 : List Lit := [(1572, true), (18, true), (90, false), (112, false)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c978, c1275, c1278, c1280, c1276, c1271, c486, c51, c50, c1921] c2082 (by decide) p (sat_cons (step978 p h) (sat_cons (step1275 p h) (sat_cons (step1278 p h) (sat_cons (step1280 p h) (sat_cons (step1276 p h) (sat_cons (step1271 p h) (sat_cons (step486 p h) (sat_cons (step51 p h) (sat_cons (step50 p h) (sat_cons (step1921 p h) (sat_nil p)))))))))))
def c2083 : List Lit := [(1764, true), (102, true), (90, false), (112, false)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c1012, c1688, c1692, c1694, c1690, c1685, c1686, c508, c684, c523, c533] c2083 (by decide) p (sat_cons (step1012 p h) (sat_cons (step1688 p h) (sat_cons (step1692 p h) (sat_cons (step1694 p h) (sat_cons (step1690 p h) (sat_cons (step1685 p h) (sat_cons (step1686 p h) (sat_cons (step508 p h) (sat_cons (step684 p h) (sat_cons (step523 p h) (sat_cons (step533 p h) (sat_nil p))))))))))))
def c2084 : List Lit := [(17, false), (87, true), (88, true), (95, true), (18, true)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c978, c2003, c51, c50, c1921, c75, c48, c1063, c1046, c1066, c1047, c1067, c1051, c1079, c1055, c1084] c2084 (by decide) p (sat_cons (step978 p h) (sat_cons (step2003 p h) (sat_cons (step51 p h) (sat_cons (step50 p h) (sat_cons (step1921 p h) (sat_cons (step75 p h) (sat_cons (step48 p h) (sat_cons (step1063 p h) (sat_cons (step1046 p h) (sat_cons (step1066 p h) (sat_cons (step1047 p h) (sat_cons (step1067 p h) (sat_cons (step1051 p h) (sat_cons (step1079 p h) (sat_cons (step1055 p h) (sat_cons (step1084 p h) (sat_nil p)))))))))))))))))
def c2085 : List Lit := [(46, true), (66, true), (1649, true), (101, true), (1633, false)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c998, c1428, c1399, c1388, c1389, c1396, c1424, c1407, c1409, c1405, c1401, c273, c280] c2085 (by decide) p (sat_cons (step998 p h) (sat_cons (step1428 p h) (sat_cons (step1399 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1396 p h) (sat_cons (step1424 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1405 p h) (sat_cons (step1401 p h) (sat_cons (step273 p h) (sat_cons (step280 p h) (sat_nil p))))))))))))))
def c2086 : List Lit := [(46, false), (126, true), (1804, true), (124, false), (103, false), (122, true), (118, true)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c937, c938, c939, c1741, c1752, c1755, c1743, c1763, c1777] c2086 (by decide) p (sat_cons (step937 p h) (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step1741 p h) (sat_cons (step1752 p h) (sat_cons (step1755 p h) (sat_cons (step1743 p h) (sat_cons (step1763 p h) (sat_cons (step1777 p h) (sat_nil p))))))))))
def c2087 : List Lit := [(1648, false), (1680, true), (1609, false), (1585, false)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c2066, c2045, c1492, c1438, c1445, c1499, c2076, c1325, c1248, c2037, c1251] c2087 (by decide) p (sat_cons (step2066 p h) (sat_cons (step2045 p h) (sat_cons (step1492 p h) (sat_cons (step1438 p h) (sat_cons (step1445 p h) (sat_cons (step1499 p h) (sat_cons (step2076 p h) (sat_cons (step1325 p h) (sat_cons (step1248 p h) (sat_cons (step2037 p h) (sat_cons (step1251 p h) (sat_nil p))))))))))))
def c2088 : List Lit := [(1721, true), (89, false), (90, false)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1586, c514] c2088 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1586 p h) (sat_cons (step514 p h) (sat_nil p))))
def c2089 : List Lit := [(1731, false), (1737, true), (1747, true), (1721, false)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c1588, c1620, c1615, c1591, c1650, c2062] c2089 (by decide) p (sat_cons (step1588 p h) (sat_cons (step1620 p h) (sat_cons (step1615 p h) (sat_cons (step1591 p h) (sat_cons (step1650 p h) (sat_cons (step2062 p h) (sat_nil p)))))))
def c2090 : List Lit := [(1731, true), (93, true)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c1013, c1602, c1604, c1599, c1600, c1596, c534, c562] c2090 (by decide) p (sat_cons (step1013 p h) (sat_cons (step1602 p h) (sat_cons (step1604 p h) (sat_cons (step1599 p h) (sat_cons (step1600 p h) (sat_cons (step1596 p h) (sat_cons (step534 p h) (sat_cons (step562 p h) (sat_nil p)))))))))
def c2091 : List Lit := [(1783, true), (1779, true), (108, true), (1731, true)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c1024, c1018, c1602, c1600, c1604, c1596, c2090, c579, c1686, c1693, c1721, c580, c1700, c1967, c1597, c1599, c1736, c1737, c872, c861, c864, c600, c1704, c1709, c1712, c1725, c1701, c2083, c700, c722] c2091 (by decide) p (sat_cons (step1024 p h) (sat_cons (step1018 p h) (sat_cons (step1602 p h) (sat_cons (step1600 p h) (sat_cons (step1604 p h) (sat_cons (step1596 p h) (sat_cons (step2090 p h) (sat_cons (step579 p h) (sat_cons (step1686 p h) (sat_cons (step1693 p h) (sat_cons (step1721 p h) (sat_cons (step580 p h) (sat_cons (step1700 p h) (sat_cons (step1967 p h) (sat_cons (step1597 p h) (sat_cons (step1599 p h) (sat_cons (step1736 p h) (sat_cons (step1737 p h) (sat_cons (step872 p h) (sat_cons (step861 p h) (sat_cons (step864 p h) (sat_cons (step600 p h) (sat_cons (step1704 p h) (sat_cons (step1709 p h) (sat_cons (step1712 p h) (sat_cons (step1725 p h) (sat_cons (step1701 p h) (sat_cons (step2083 p h) (sat_cons (step700 p h) (sat_cons (step722 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2092 : List Lit := [(1778, true), (1769, false), (1731, true)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c1018, c2090, c1604, c1596, c1602, c1600, c580, c1700, c1708, c579, c1686, c1693, c1967, c1720, c1724, c1711, c1696, c1694, c1701, c1687, c1688, c725, c712, c700] c2092 (by decide) p (sat_cons (step1018 p h) (sat_cons (step2090 p h) (sat_cons (step1604 p h) (sat_cons (step1596 p h) (sat_cons (step1602 p h) (sat_cons (step1600 p h) (sat_cons (step580 p h) (sat_cons (step1700 p h) (sat_cons (step1708 p h) (sat_cons (step579 p h) (sat_cons (step1686 p h) (sat_cons (step1693 p h) (sat_cons (step1967 p h) (sat_cons (step1720 p h) (sat_cons (step1724 p h) (sat_cons (step1711 p h) (sat_cons (step1696 p h) (sat_cons (step1694 p h) (sat_cons (step1701 p h) (sat_cons (step1687 p h) (sat_cons (step1688 p h) (sat_cons (step725 p h) (sat_cons (step712 p h) (sat_cons (step700 p h) (sat_nil p)))))))))))))))))))))))))
def c2093 : List Lit := [(122, true), (1796, true), (116, true), (105, true)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c1029, c1761, c1751, c1752, c1759, c1753, c1754, c959, c953] c2093 (by decide) p (sat_cons (step1029 p h) (sat_cons (step1761 p h) (sat_cons (step1751 p h) (sat_cons (step1752 p h) (sat_cons (step1759 p h) (sat_cons (step1753 p h) (sat_cons (step1754 p h) (sat_cons (step959 p h) (sat_cons (step953 p h) (sat_nil p))))))))))
def c2094 : List Lit := [(1795, true), (116, true), (105, true)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c1029, c1756, c1758, c1753, c1754, c1750, c959, c953] c2094 (by decide) p (sat_cons (step1029 p h) (sat_cons (step1756 p h) (sat_cons (step1758 p h) (sat_cons (step1753 p h) (sat_cons (step1754 p h) (sat_cons (step1750 p h) (sat_cons (step959 p h) (sat_cons (step953 p h) (sat_nil p)))))))))
def c2095 : List Lit := [(127, false), (120, false), (103, false), (100, false), (104, true)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c1019, c763, c950, c707] c2095 (by decide) p (sat_cons (step1019 p h) (sat_cons (step763 p h) (sat_cons (step950 p h) (sat_cons (step707 p h) (sat_nil p)))))
def c2096 : List Lit := [(1747, true), (1731, false), (1721, false), (1712, false)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c1643, c2089] c2096 (by decide) p (sat_cons (step1643 p h) (sat_cons (step2089 p h) (sat_nil p)))
def c2097 : List Lit := [(1759, true), (95, false), (90, false), (100, false)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c1012, c1685, c1686, c506, c684, c523, c533] c2097 (by decide) p (sat_cons (step1012 p h) (sat_cons (step1685 p h) (sat_cons (step1686 p h) (sat_cons (step506 p h) (sat_cons (step684 p h) (sat_cons (step523 p h) (sat_cons (step533 p h) (sat_nil p))))))))
def c2098 : List Lit := [(18, true), (1572, true), (21, false), (95, false)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c1278, c1275, c1276, c1280, c72, c1271] c2098 (by decide) p (sat_cons (step1278 p h) (sat_cons (step1275 p h) (sat_cons (step1276 p h) (sat_cons (step1280 p h) (sat_cons (step72 p h) (sat_cons (step1271 p h) (sat_nil p)))))))
def c2099 : List Lit := [(1572, true), (21, false), (95, false)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c2098, c71, c73, c1271, c1274, c1280] c2099 (by decide) p (sat_cons (step2098 p h) (sat_cons (step71 p h) (sat_cons (step73 p h) (sat_cons (step1271 p h) (sat_cons (step1274 p h) (sat_cons (step1280 p h) (sat_nil p)))))))
def c2100 : List Lit := [(1648, true), (57, false), (1631, false)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c1395, c1423, c1419, c1396, c1409, c1390, c1391, c1402, c259] c2100 (by decide) p (sat_cons (step1395 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step1396 p h) (sat_cons (step1409 p h) (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step1402 p h) (sat_cons (step259 p h) (sat_nil p))))))))))
def c2101 : List Lit := [(1731, true), (93, false), (103, false)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c1602, c1604, c1600, c1596, c580] c2101 (by decide) p (sat_cons (step1602 p h) (sat_cons (step1604 p h) (sat_cons (step1600 p h) (sat_cons (step1596 p h) (sat_cons (step580 p h) (sat_nil p))))))
def c2102 : List Lit := [(1721, true), (85, false), (91, false)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1586, c440] c2102 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1586 p h) (sat_cons (step440 p h) (sat_nil p))))
def c2103 : List Lit := [(122, false), (90, false), (1697, true), (84, false)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c1003, c1536, c1535, c841, c397, c337, c336, c1948] c2103 (by decide) p (sat_cons (step1003 p h) (sat_cons (step1536 p h) (sat_cons (step1535 p h) (sat_cons (step841 p h) (sat_cons (step397 p h) (sat_cons (step337 p h) (sat_cons (step336 p h) (sat_cons (step1948 p h) (sat_nil p)))))))))
def c2104 : List Lit := [(79, true), (113, true), (1697, true)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c1003, c1536, c1535, c337, c336, c1948] c2104 (by decide) p (sat_cons (step1003 p h) (sat_cons (step1536 p h) (sat_cons (step1535 p h) (sat_cons (step337 p h) (sat_cons (step336 p h) (sat_cons (step1948 p h) (sat_nil p)))))))
def c2105 : List Lit := [(1648, false), (1679, true), (1584, false), (1609, false)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c2066, c2044, c1484, c1438, c1445, c1491, c2076, c1324, c1248, c2037, c1251] c2105 (by decide) p (sat_cons (step2066 p h) (sat_cons (step2044 p h) (sat_cons (step1484 p h) (sat_cons (step1438 p h) (sat_cons (step1445 p h) (sat_cons (step1491 p h) (sat_cons (step2076 p h) (sat_cons (step1324 p h) (sat_cons (step1248 p h) (sat_cons (step2037 p h) (sat_cons (step1251 p h) (sat_nil p))))))))))))
def c2106 : List Lit := [(88, true), (105, true), (99, false), (100, false), (106, false), (90, false)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c1012, c1016, c684, c533, c646, c652] c2106 (by decide) p (sat_cons (step1012 p h) (sat_cons (step1016 p h) (sat_cons (step684 p h) (sat_cons (step533 p h) (sat_cons (step646 p h) (sat_cons (step652 p h) (sat_nil p)))))))
def c2107 : List Lit := [(1767, true), (106, false), (127, false)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c1699, c1700, c765] c2107 (by decide) p (sat_cons (step1699 p h) (sat_cons (step1700 p h) (sat_cons (step765 p h) (sat_nil p))))
def c2108 : List Lit := [(1796, true), (122, true), (125, false), (127, false)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1761, c1759, c1752, c1754, c953] c2108 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1761 p h) (sat_cons (step1759 p h) (sat_cons (step1752 p h) (sat_cons (step1754 p h) (sat_cons (step953 p h) (sat_nil p)))))))
def c2109 : List Lit := [(1714, true), (1719, true), (79, true), (71, true), (65, true)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c1006, c2051, c1533, c1535, c1541, c1574, c1571, c1544, c1542, c2060, c1534, c1537, c328, c365] c2109 (by decide) p (sat_cons (step1006 p h) (sat_cons (step2051 p h) (sat_cons (step1533 p h) (sat_cons (step1535 p h) (sat_cons (step1541 p h) (sat_cons (step1574 p h) (sat_cons (step1571 p h) (sat_cons (step1544 p h) (sat_cons (step1542 p h) (sat_cons (step2060 p h) (sat_cons (step1534 p h) (sat_cons (step1537 p h) (sat_cons (step328 p h) (sat_cons (step365 p h) (sat_nil p)))))))))))))))
def c2110 : List Lit := [(1648, true), (1633, false), (79, true), (101, true)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c998, c1393, c1423, c1419, c1396, c1407, c1409, c1387, c1405, c1401, c279, c273] c2110 (by decide) p (sat_cons (step998 p h) (sat_cons (step1393 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step1396 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1387 p h) (sat_cons (step1405 p h) (sat_cons (step1401 p h) (sat_cons (step279 p h) (sat_cons (step273 p h) (sat_nil p)))))))))))))
def c2111 : List Lit := [(1633, false), (79, true), (46, true), (1649, true), (101, true)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c998, c1388, c1428, c1399, c1396, c1389, c1424, c1407, c1409, c1405, c1401, c279, c273] c2111 (by decide) p (sat_cons (step998 p h) (sat_cons (step1388 p h) (sat_cons (step1428 p h) (sat_cons (step1399 p h) (sat_cons (step1396 p h) (sat_cons (step1389 p h) (sat_cons (step1424 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1405 p h) (sat_cons (step1401 p h) (sat_cons (step279 p h) (sat_cons (step273 p h) (sat_nil p))))))))))))))
def c2112 : List Lit := [(1801, true), (127, false), (108, false), (1783, false), (118, true)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c1026, c1740, c1745, c1778, c1774, c1746, c1758, c1741, c1750, c952, c902, c897] c2112 (by decide) p (sat_cons (step1026 p h) (sat_cons (step1740 p h) (sat_cons (step1745 p h) (sat_cons (step1778 p h) (sat_cons (step1774 p h) (sat_cons (step1746 p h) (sat_cons (step1758 p h) (sat_cons (step1741 p h) (sat_cons (step1750 p h) (sat_cons (step952 p h) (sat_cons (step902 p h) (sat_cons (step897 p h) (sat_nil p)))))))))))))
def c2113 : List Lit := [(92, true), (85, true), (1733, true), (15, false), (18, false), (1572, true)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c1013, c979, c536, c55, c54, c1596, c59, c2099, c1606, c1601] c2113 (by decide) p (sat_cons (step1013 p h) (sat_cons (step979 p h) (sat_cons (step536 p h) (sat_cons (step55 p h) (sat_cons (step54 p h) (sat_cons (step1596 p h) (sat_cons (step59 p h) (sat_cons (step2099 p h) (sat_cons (step1606 p h) (sat_cons (step1601 p h) (sat_nil p)))))))))))
def c2114 : List Lit := [(92, false), (1733, true), (54, false), (18, false)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c538, c539, c537, c1601, c1596, c1606] c2114 (by decide) p (sat_cons (step538 p h) (sat_cons (step539 p h) (sat_cons (step537 p h) (sat_cons (step1601 p h) (sat_cons (step1596 p h) (sat_cons (step1606 p h) (sat_nil p)))))))
def c2115 : List Lit := [(1737, true), (15, false), (54, false), (18, false), (1572, true)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c979, c1612, c2114, c55, c54, c2113, c59, c2099, c1601, c1603, c1606, c1616, c1596, c1588, c2102] c2115 (by decide) p (sat_cons (step979 p h) (sat_cons (step1612 p h) (sat_cons (step2114 p h) (sat_cons (step55 p h) (sat_cons (step54 p h) (sat_cons (step2113 p h) (sat_cons (step59 p h) (sat_cons (step2099 p h) (sat_cons (step1601 p h) (sat_cons (step1603 p h) (sat_cons (step1606 p h) (sat_cons (step1616 p h) (sat_cons (step1596 p h) (sat_cons (step1588 p h) (sat_cons (step2102 p h) (sat_nil p))))))))))))))))
def c2116 : List Lit := [(122, false), (1712, true), (90, false)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c2078, c1535, c1561, c841, c2104, c396, c394, c1550, c1546, c1555] c2116 (by decide) p (sat_cons (step2078 p h) (sat_cons (step1535 p h) (sat_cons (step1561 p h) (sat_cons (step841 p h) (sat_cons (step2104 p h) (sat_cons (step396 p h) (sat_cons (step394 p h) (sat_cons (step1550 p h) (sat_cons (step1546 p h) (sat_cons (step1555 p h) (sat_nil p)))))))))))
def c2117 : List Lit := [(113, true), (69, true), (1712, true)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c1003, c2078, c1536, c1535, c2104, c338, c1953, c327, c1550, c1532, c1552, c1540, c1565] c2117 (by decide) p (sat_cons (step1003 p h) (sat_cons (step2078 p h) (sat_cons (step1536 p h) (sat_cons (step1535 p h) (sat_cons (step2104 p h) (sat_cons (step338 p h) (sat_cons (step1953 p h) (sat_cons (step327 p h) (sat_cons (step1550 p h) (sat_cons (step1532 p h) (sat_cons (step1552 p h) (sat_cons (step1540 p h) (sat_cons (step1565 p h) (sat_nil p))))))))))))))
end B112E052
