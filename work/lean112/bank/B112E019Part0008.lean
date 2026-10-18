import B112E019Part0007
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2318 : List Lit := [(173, true), (49, true), (48, true), (52, false), (50, true)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c245, c242, c2015, c1764] c2318 (by decide) p (sat_cons (step245 p h) (sat_cons (step242 p h) (sat_cons (step2015 p h) (sat_cons (step1764 p h) (sat_nil p)))))
def c2319 : List Lit := [(54, false), (57, true), (46, false), (175, true), (118, false)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c263, c253] c2319 (by decide) p (sat_cons (step263 p h) (sat_cons (step253 p h) (sat_nil p)))
def c2320 : List Lit := [(1681, true), (99, true), (212, true), (1673, false)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c1562, c1571, c1578, c1582, c1574, c2276, c1564] c2320 (by decide) p (sat_cons (step1562 p h) (sat_cons (step1571 p h) (sat_cons (step1578 p h) (sat_cons (step1582 p h) (sat_cons (step1574 p h) (sat_cons (step2276 p h) (sat_cons (step1564 p h) (sat_nil p))))))))
def c2321 : List Lit := [(1639, true), (1686, true), (92, false)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1482, c1484, c1479, c1480, c1476, c1477, c2301, c463, c472, c434, c477] c2321 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step2301 p h) (sat_cons (step463 p h) (sat_cons (step472 p h) (sat_cons (step434 p h) (sat_cons (step477 p h) (sat_nil p)))))))))))))
def c2322 : List Lit := [(1622, true), (116, false), (107, false), (99, true), (63, true), (109, true), (387, true)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c1070, c1045, c1043, c1040, c1068, c1065, c1054, c1052, c1051, c1881, c1891, c651, c305, c304, c2035, c1773] c2322 (by decide) p (sat_cons (step1070 p h) (sat_cons (step1045 p h) (sat_cons (step1043 p h) (sat_cons (step1040 p h) (sat_cons (step1068 p h) (sat_cons (step1065 p h) (sat_cons (step1054 p h) (sat_cons (step1052 p h) (sat_cons (step1051 p h) (sat_cons (step1881 p h) (sat_cons (step1891 p h) (sat_cons (step651 p h) (sat_cons (step305 p h) (sat_cons (step304 p h) (sat_cons (step2035 p h) (sat_cons (step1773 p h) (sat_nil p)))))))))))))))))
def c2323 : List Lit := [(1607, true), (74, true), (187, true), (116, false), (107, false)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c1422, c1423, c651, c317, c304] c2323 (by decide) p (sat_cons (step1422 p h) (sat_cons (step1423 p h) (sat_cons (step651 p h) (sat_cons (step317 p h) (sat_cons (step304 p h) (sat_nil p))))))
def c2324 : List Lit := [(212, true), (91, false), (95, true), (83, true)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c497, c498, c2065, c1789] c2324 (by decide) p (sat_cons (step497 p h) (sat_cons (step498 p h) (sat_cons (step2065 p h) (sat_cons (step1789 p h) (sat_nil p)))))
def c2325 : List Lit := [(79, false), (85, false), (80, false), (1644, true)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c386, c388, c1465, c1477, c1468, c1484, c1495] c2325 (by decide) p (sat_cons (step386 p h) (sat_cons (step388 p h) (sat_cons (step1465 p h) (sat_cons (step1477 p h) (sat_cons (step1468 p h) (sat_cons (step1484 p h) (sat_cons (step1495 p h) (sat_nil p))))))))
def c2326 : List Lit := [(1637, true), (79, true), (85, false), (105, true), (1686, true)]
theorem step2326 (p : Nat → Bool) (h : Constraints p) : clause p c2326 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1479, c1480, c2301, c472, c1906, c463] c2326 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step2301 p h) (sat_cons (step472 p h) (sat_cons (step1906 p h) (sat_cons (step463 p h) (sat_nil p))))))))
def c2327 : List Lit := [(85, false), (1644, true), (83, true), (105, true), (1686, true)]
theorem step2327 (p : Nat → Bool) (h : Constraints p) : clause p c2327 = true :=
  Snake9.LocalRup.prove_clause [c1491, c1483, c1595, c1594, c1880, c2325, c404, c1074, c1078, c2130, c1081, c1076, c2134, c1095, c1086, c1083, c2326, c1482, c1485, c1495, c1477, c1468, c470, c1465, c417, c442, c431, c460, c1481] c2327 (by decide) p (sat_cons (step1491 p h) (sat_cons (step1483 p h) (sat_cons (step1595 p h) (sat_cons (step1594 p h) (sat_cons (step1880 p h) (sat_cons (step2325 p h) (sat_cons (step404 p h) (sat_cons (step1074 p h) (sat_cons (step1078 p h) (sat_cons (step2130 p h) (sat_cons (step1081 p h) (sat_cons (step1076 p h) (sat_cons (step2134 p h) (sat_cons (step1095 p h) (sat_cons (step1086 p h) (sat_cons (step1083 p h) (sat_cons (step2326 p h) (sat_cons (step1482 p h) (sat_cons (step1485 p h) (sat_cons (step1495 p h) (sat_cons (step1477 p h) (sat_cons (step1468 p h) (sat_cons (step470 p h) (sat_cons (step1465 p h) (sat_cons (step417 p h) (sat_cons (step442 p h) (sat_cons (step431 p h) (sat_cons (step460 p h) (sat_cons (step1481 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2328 : List Lit := [(1644, true), (83, true), (105, true), (1686, true)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1491, c1487, c2327, c1476, c1478, c1484, c1485, c1495, c1479, c1480, c1468, c2301, c471, c1465, c431, c462, c477] c2328 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1491 p h) (sat_cons (step1487 p h) (sat_cons (step2327 p h) (sat_cons (step1476 p h) (sat_cons (step1478 p h) (sat_cons (step1484 p h) (sat_cons (step1485 p h) (sat_cons (step1495 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step1468 p h) (sat_cons (step2301 p h) (sat_cons (step471 p h) (sat_cons (step1465 p h) (sat_cons (step431 p h) (sat_cons (step462 p h) (sat_cons (step477 p h) (sat_nil p)))))))))))))))))))
def c2329 : List Lit := [(41, true), (36, false), (94, false), (1544, true), (327, true)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c988, c971, c964, c963, c1874, c1308, c1299, c986, c983, c976, c973, c1288, c1290, c1296, c156, c1311, c2184, c149, c1286, c142] c2329 (by decide) p (sat_cons (step988 p h) (sat_cons (step971 p h) (sat_cons (step964 p h) (sat_cons (step963 p h) (sat_cons (step1874 p h) (sat_cons (step1308 p h) (sat_cons (step1299 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step976 p h) (sat_cons (step973 p h) (sat_cons (step1288 p h) (sat_cons (step1290 p h) (sat_cons (step1296 p h) (sat_cons (step156 p h) (sat_cons (step1311 p h) (sat_cons (step2184 p h) (sat_cons (step149 p h) (sat_cons (step1286 p h) (sat_cons (step142 p h) (sat_nil p)))))))))))))))))))))
def c2330 : List Lit := [(48, true), (1566, true), (105, true), (40, true), (44, false)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c1346, c1327, c1316, c1318, c1324, c1343, c1335, c1331, c2203, c195, c255, c190, c1005, c979, c1008, c980, c1017, c982, c1020, c986, c2119] c2330 (by decide) p (sat_cons (step1346 p h) (sat_cons (step1327 p h) (sat_cons (step1316 p h) (sat_cons (step1318 p h) (sat_cons (step1324 p h) (sat_cons (step1343 p h) (sat_cons (step1335 p h) (sat_cons (step1331 p h) (sat_cons (step2203 p h) (sat_cons (step195 p h) (sat_cons (step255 p h) (sat_cons (step190 p h) (sat_cons (step1005 p h) (sat_cons (step979 p h) (sat_cons (step1008 p h) (sat_cons (step980 p h) (sat_cons (step1017 p h) (sat_cons (step982 p h) (sat_cons (step1020 p h) (sat_cons (step986 p h) (sat_cons (step2119 p h) (sat_nil p))))))))))))))))))))))
def c2331 : List Lit := [(48, false), (105, true), (40, true), (1686, true), (44, false)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1594, c703, c212, c220, c189, c991, c979, c992, c980, c1002, c982, c1022, c986, c2119] c2331 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1594 p h) (sat_cons (step703 p h) (sat_cons (step212 p h) (sat_cons (step220 p h) (sat_cons (step189 p h) (sat_cons (step991 p h) (sat_cons (step979 p h) (sat_cons (step992 p h) (sat_cons (step980 p h) (sat_cons (step1002 p h) (sat_cons (step982 p h) (sat_cons (step1022 p h) (sat_cons (step986 p h) (sat_cons (step2119 p h) (sat_nil p))))))))))))))))
def c2332 : List Lit := [(1551, true), (57, true), (172, true), (43, false)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c1320, c2187, c237] c2332 (by decide) p (sat_cons (step1320 p h) (sat_cons (step2187 p h) (sat_cons (step237 p h) (sat_nil p))))
def c2333 : List Lit := [(1673, true), (100, false), (80, false)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1566, c590] c2333 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1566 p h) (sat_cons (step590 p h) (sat_nil p))))
def c2334 : List Lit := [(103, false), (224, true), (83, true), (1686, true), (43, false)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1594, c693, c631, c626] c2334 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1594 p h) (sat_cons (step693 p h) (sat_cons (step631 p h) (sat_cons (step626 p h) (sat_nil p))))))
def c2335 : List Lit := [(1704, true), (236, true), (116, false), (1696, false), (112, true), (107, false)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1598, c1600, c1632, c1628, c1601, c1942, c1617, c1599, c1609, c742, c775] c2335 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1598 p h) (sat_cons (step1600 p h) (sat_cons (step1632 p h) (sat_cons (step1628 p h) (sat_cons (step1601 p h) (sat_cons (step1942 p h) (sat_cons (step1617 p h) (sat_cons (step1599 p h) (sat_cons (step1609 p h) (sat_cons (step742 p h) (sat_cons (step775 p h) (sat_nil p)))))))))))))
def c2336 : List Lit := [(387, true), (67, true), (74, true), (1623, true), (116, false), (63, true), (1686, true)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1438, c1459, c1429, c1595, c1594, c1068, c1070, c1065, c1045, c1056, c1043, c1050, c1040, c2323, c1428, c1455, c1441, c1432, c709, c328, c318, c319, c1424] c2336 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1438 p h) (sat_cons (step1459 p h) (sat_cons (step1429 p h) (sat_cons (step1595 p h) (sat_cons (step1594 p h) (sat_cons (step1068 p h) (sat_cons (step1070 p h) (sat_cons (step1065 p h) (sat_cons (step1045 p h) (sat_cons (step1056 p h) (sat_cons (step1043 p h) (sat_cons (step1050 p h) (sat_cons (step1040 p h) (sat_cons (step2323 p h) (sat_cons (step1428 p h) (sat_cons (step1455 p h) (sat_cons (step1441 p h) (sat_cons (step1432 p h) (sat_cons (step709 p h) (sat_cons (step328 p h) (sat_cons (step318 p h) (sat_cons (step319 p h) (sat_cons (step1424 p h) (sat_nil p)))))))))))))))))))))))))
def c2337 : List Lit := [(66, true), (109, true), (67, true), (1623, true), (63, true), (107, false)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1438, c1459, c1429, c1422, c1424, c1428, c1455, c1441, c1439, c1432, c1433, c1964] c2337 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1438 p h) (sat_cons (step1459 p h) (sat_cons (step1429 p h) (sat_cons (step1422 p h) (sat_cons (step1424 p h) (sat_cons (step1428 p h) (sat_cons (step1455 p h) (sat_cons (step1441 p h) (sat_cons (step1439 p h) (sat_cons (step1432 p h) (sat_cons (step1433 p h) (sat_cons (step1964 p h) (sat_nil p))))))))))))))
def c2338 : List Lit := [(69, false), (63, true), (1622, true), (110, false), (74, true), (107, false), (116, false)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c709, c1881, c651, c319, c304, c328, c1040, c1050, c1043, c1056, c1045, c1065, c2128] c2338 (by decide) p (sat_cons (step709 p h) (sat_cons (step1881 p h) (sat_cons (step651 p h) (sat_cons (step319 p h) (sat_cons (step304 p h) (sat_cons (step328 p h) (sat_cons (step1040 p h) (sat_cons (step1050 p h) (sat_cons (step1043 p h) (sat_cons (step1056 p h) (sat_cons (step1045 p h) (sat_cons (step1065 p h) (sat_cons (step2128 p h) (sat_nil p))))))))))))))
def c2339 : List Lit := [(1576, true), (1561, false), (41, true), (107, false), (116, false)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c1339, c2290, c1369, c1364, c2309, c1343, c1291, c1292, c1324, c645, c1317, c1892] c2339 (by decide) p (sat_cons (step1339 p h) (sat_cons (step2290 p h) (sat_cons (step1369 p h) (sat_cons (step1364 p h) (sat_cons (step2309 p h) (sat_cons (step1343 p h) (sat_cons (step1291 p h) (sat_cons (step1292 p h) (sat_cons (step1324 p h) (sat_cons (step645 p h) (sat_cons (step1317 p h) (sat_cons (step1892 p h) (sat_nil p)))))))))))))
def c2340 : List Lit := [(353, true), (46, false), (1562, true), (76, false), (116, false)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c1015, c1017, c1012, c1007, c1011, c1006, c1808, c2031, c1333, c1336, c1330, c1876, c796] c2340 (by decide) p (sat_cons (step1015 p h) (sat_cons (step1017 p h) (sat_cons (step1012 p h) (sat_cons (step1007 p h) (sat_cons (step1011 p h) (sat_cons (step1006 p h) (sat_cons (step1808 p h) (sat_cons (step2031 p h) (sat_cons (step1333 p h) (sat_cons (step1336 p h) (sat_cons (step1330 p h) (sat_cons (step1876 p h) (sat_cons (step796 p h) (sat_nil p))))))))))))))
def c2341 : List Lit := [(1622, true), (109, true), (1609, false), (107, false), (72, false), (67, true), (190, true)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1438, c1454, c1450, c1426, c1441, c1432, c328, c1964, c319, c1424] c2341 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1438 p h) (sat_cons (step1454 p h) (sat_cons (step1450 p h) (sat_cons (step1426 p h) (sat_cons (step1441 p h) (sat_cons (step1432 p h) (sat_cons (step328 p h) (sat_cons (step1964 p h) (sat_cons (step319 p h) (sat_cons (step1424 p h) (sat_nil p))))))))))))
def c2342 : List Lit := [(109, true), (1655, true), (1631, false), (1609, false), (107, false), (72, false), (67, true), (190, true), (210, true)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c2341, c1534, c1495, c1482, c1484, c1479, c1480, c1476, c472, c484, c463] c2342 (by decide) p (sat_cons (step2341 p h) (sat_cons (step1534 p h) (sat_cons (step1495 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step1476 p h) (sat_cons (step472 p h) (sat_cons (step484 p h) (sat_cons (step463 p h) (sat_nil p))))))))))))
def c2343 : List Lit := [(1655, true), (1631, false), (1609, false), (107, false), (72, false), (67, true), (190, true), (210, true), (48, false)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c2342, c697, c700, c1432, c1479, c1441, c1482, c1450, c1495, c1534] c2343 (by decide) p (sat_cons (step2342 p h) (sat_cons (step697 p h) (sat_cons (step700 p h) (sat_cons (step1432 p h) (sat_cons (step1479 p h) (sat_cons (step1441 p h) (sat_cons (step1482 p h) (sat_cons (step1450 p h) (sat_cons (step1495 p h) (sat_cons (step1534 p h) (sat_nil p)))))))))))
def c2344 : List Lit := [(44, false), (40, true), (107, false), (165, true), (48, false), (116, false)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c645, c212, c189] c2344 (by decide) p (sat_cons (step645 p h) (sat_cons (step212 p h) (sat_cons (step189 p h) (sat_nil p))))
def c2345 : List Lit := [(109, false), (1705, true), (1688, false), (107, false), (118, true), (48, false)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c703, c704, c1594, c1613, c1603, c1615, c1633] c2345 (by decide) p (sat_cons (step703 p h) (sat_cons (step704 p h) (sat_cons (step1594 p h) (sat_cons (step1613 p h) (sat_cons (step1603 p h) (sat_cons (step1615 p h) (sat_cons (step1633 p h) (sat_nil p))))))))
def c2346 : List Lit := [(110, true), (109, true), (1705, true), (112, true), (118, true), (241, true), (116, false)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1614, c1637, c1598, c1594, c1603, c1604, c1633, c1599, c1615, c1890, c1613] c2346 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1614 p h) (sat_cons (step1637 p h) (sat_cons (step1598 p h) (sat_cons (step1594 p h) (sat_cons (step1603 p h) (sat_cons (step1604 p h) (sat_cons (step1633 p h) (sat_cons (step1599 p h) (sat_cons (step1615 p h) (sat_cons (step1890 p h) (sat_cons (step1613 p h) (sat_nil p)))))))))))))
def c2347 : List Lit := [(120, false), (119, true), (109, true), (241, true), (76, false), (116, false)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c809, c842] c2347 (by decide) p (sat_cons (step809 p h) (sat_cons (step842 p h) (sat_nil p)))
def c2348 : List Lit := [(119, true), (1700, true), (112, false), (109, true), (118, true), (236, true), (241, true), (76, false), (116, false)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c2347, c1613, c1618, c1609, c741, c775] c2348 (by decide) p (sat_cons (step2347 p h) (sat_cons (step1613 p h) (sat_cons (step1618 p h) (sat_cons (step1609 p h) (sat_cons (step741 p h) (sat_cons (step775 p h) (sat_nil p)))))))
def c2349 : List Lit := [(1643, true), (110, false), (48, false)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c1490, c2175, c1482, c1480] c2349 (by decide) p (sat_cons (step1490 p h) (sat_cons (step2175 p h) (sat_cons (step1482 p h) (sat_cons (step1480 p h) (sat_nil p)))))
def c2350 : List Lit := [(1639, true), (88, true), (109, true), (210, true)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c1482, c1484, c1479, c1480, c1476, c484, c463] c2350 (by decide) p (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step1476 p h) (sat_cons (step484 p h) (sat_cons (step463 p h) (sat_nil p))))))))
def c2351 : List Lit := [(89, false), (87, false), (81, false), (88, true), (109, true), (210, true)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c484, c462] c2351 (by decide) p (sat_cons (step484 p h) (sat_cons (step462 p h) (sat_nil p)))
def c2352 : List Lit := [(87, false), (1640, true), (81, false), (105, true), (88, true), (109, true), (413, true)]
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c1095, c1086, c1083, c1093, c1091, c1088, c2351, c1479, c1485, c1476, c1477, c460, c391, c442] c2352 (by decide) p (sat_cons (step1095 p h) (sat_cons (step1086 p h) (sat_cons (step1083 p h) (sat_cons (step1093 p h) (sat_cons (step1091 p h) (sat_cons (step1088 p h) (sat_cons (step2351 p h) (sat_cons (step1479 p h) (sat_cons (step1485 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step460 p h) (sat_cons (step391 p h) (sat_cons (step442 p h) (sat_nil p)))))))))))))))
def c2353 : List Lit := [(85, false), (1637, true), (109, true), (107, false), (210, true)]
theorem step2353 (p : Nat → Bool) (h : Constraints p) : clause p c2353 = true :=
  Snake9.LocalRup.prove_clause [c1480, c1479, c472, c463, c484] c2353 (by decide) p (sat_cons (step1480 p h) (sat_cons (step1479 p h) (sat_cons (step472 p h) (sat_cons (step463 p h) (sat_cons (step484 p h) (sat_nil p))))))
def c2354 : List Lit := [(120, false), (109, true), (107, false), (241, true), (76, false), (116, false)]
theorem step2354 (p : Nat → Bool) (h : Constraints p) : clause p c2354 = true :=
  Snake9.LocalRup.prove_clause [c809, c830, c842] c2354 (by decide) p (sat_cons (step809 p h) (sat_cons (step830 p h) (sat_cons (step842 p h) (sat_nil p))))
def c2355 : List Lit := [(1705, true), (112, true), (119, true), (1699, false), (109, true), (118, true), (236, true), (241, true), (116, false)]
theorem step2355 (p : Nat → Bool) (h : Constraints p) : clause p c2355 = true :=
  Snake9.LocalRup.prove_clause [c1633, c1601, c1901, c1599, c775, c742] c2355 (by decide) p (sat_cons (step1633 p h) (sat_cons (step1601 p h) (sat_cons (step1901 p h) (sat_cons (step1599 p h) (sat_cons (step775 p h) (sat_cons (step742 p h) (sat_nil p)))))))
def c2356 : List Lit := [(1543, true), (47, true), (107, false), (327, true), (46, false), (116, false)]
theorem step2356 (p : Nat → Bool) (h : Constraints p) : clause p c2356 = true :=
  Snake9.LocalRup.prove_clause [c988, c971, c964, c963, c1874, c986, c982, c980, c979, c1307, c2290, c1294, c1291, c192, c645, c188] c2356 (by decide) p (sat_cons (step988 p h) (sat_cons (step971 p h) (sat_cons (step964 p h) (sat_cons (step963 p h) (sat_cons (step1874 p h) (sat_cons (step986 p h) (sat_cons (step982 p h) (sat_cons (step980 p h) (sat_cons (step979 p h) (sat_cons (step1307 p h) (sat_cons (step2290 p h) (sat_cons (step1294 p h) (sat_cons (step1291 p h) (sat_cons (step192 p h) (sat_cons (step645 p h) (sat_cons (step188 p h) (sat_nil p)))))))))))))))))
def c2357 : List Lit := [(1644, true), (89, true), (105, true), (109, true), (107, false), (413, true)]
theorem step2357 (p : Nat → Bool) (h : Constraints p) : clause p c2357 = true :=
  Snake9.LocalRup.prove_clause [c1479, c1482, c1491, c1495, c1483, c1485, c1468, c1481, c1476, c1477, c1465, c470, c2352] c2357 (by decide) p (sat_cons (step1479 p h) (sat_cons (step1482 p h) (sat_cons (step1491 p h) (sat_cons (step1495 p h) (sat_cons (step1483 p h) (sat_cons (step1485 p h) (sat_cons (step1468 p h) (sat_cons (step1481 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step1465 p h) (sat_cons (step470 p h) (sat_cons (step2352 p h) (sat_nil p))))))))))))))
def c2358 : List Lit := [(88, true), (89, false), (1644, true), (109, true), (210, true)]
theorem step2358 (p : Nat → Bool) (h : Constraints p) : clause p c2358 = true :=
  Snake9.LocalRup.prove_clause [c2350, c485, c484, c1495, c1782, c1468, c1465] c2358 (by decide) p (sat_cons (step2350 p h) (sat_cons (step485 p h) (sat_cons (step484 p h) (sat_cons (step1495 p h) (sat_cons (step1782 p h) (sat_cons (step1468 p h) (sat_cons (step1465 p h) (sat_nil p))))))))
def c2359 : List Lit := [(109, true), (112, false), (1700, true), (107, false), (118, true), (236, true), (241, true), (76, false), (116, false)]
theorem step2359 (p : Nat → Bool) (h : Constraints p) : clause p c2359 = true :=
  Snake9.LocalRup.prove_clause [c2354, c2348, c1613, c828, c1618, c1609] c2359 (by decide) p (sat_cons (step2354 p h) (sat_cons (step2348 p h) (sat_cons (step1613 p h) (sat_cons (step828 p h) (sat_cons (step1618 p h) (sat_cons (step1609 p h) (sat_nil p)))))))
def c2360 : List Lit := [(115, false), (99, false), (107, false), (236, true), (116, false)]
theorem step2360 (p : Nat → Bool) (h : Constraints p) : clause p c2360 = true :=
  Snake9.LocalRup.prove_clause [c828, c738, c775] c2360 (by decide) p (sat_cons (step828 p h) (sat_cons (step738 p h) (sat_cons (step775 p h) (sat_nil p))))
def c2361 : List Lit := [(1680, true), (1673, false), (212, true)]
theorem step2361 (p : Nat → Bool) (h : Constraints p) : clause p c2361 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1577, c1581, c1571, c2276, c1563] c2361 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1577 p h) (sat_cons (step1581 p h) (sat_cons (step1571 p h) (sat_cons (step2276 p h) (sat_cons (step1563 p h) (sat_nil p)))))))
def c2362 : List Lit := [(120, false), (107, false), (241, true), (76, false), (48, false), (116, false)]
theorem step2362 (p : Nat → Bool) (h : Constraints p) : clause p c2362 = true :=
  Snake9.LocalRup.prove_clause [c809, c704, c830, c842] c2362 (by decide) p (sat_cons (step809 p h) (sat_cons (step704 p h) (sat_cons (step830 p h) (sat_cons (step842 p h) (sat_nil p)))))
def c2363 : List Lit := [(1644, true), (109, true), (105, true), (107, false), (413, true)]
theorem step2363 (p : Nat → Bool) (h : Constraints p) : clause p c2363 = true :=
  Snake9.LocalRup.prove_clause [c1093, c1091, c1088, c1491, c2357, c1487, c2358, c471, c472, c1478] c2363 (by decide) p (sat_cons (step1093 p h) (sat_cons (step1091 p h) (sat_cons (step1088 p h) (sat_cons (step1491 p h) (sat_cons (step2357 p h) (sat_cons (step1487 p h) (sat_cons (step2358 p h) (sat_cons (step471 p h) (sat_cons (step472 p h) (sat_cons (step1478 p h) (sat_nil p)))))))))))
def c2364 : List Lit := [(1680, true), (99, true), (1675, false), (212, true)]
theorem step2364 (p : Nat → Bool) (h : Constraints p) : clause p c2364 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1581, c1573, c2276, c1564] c2364 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1581 p h) (sat_cons (step1573 p h) (sat_cons (step2276 p h) (sat_cons (step1564 p h) (sat_nil p))))))
def c2365 : List Lit := [(1705, false), (1656, false), (1536, false), (1680, false), (1716, true), (99, true), (100, false), (212, true), (1566, false)]
theorem step2365 (p : Nat → Bool) (h : Constraints p) : clause p c2365 = true :=
  Snake9.LocalRup.prove_clause [c1664, c1657, c2320, c1721, c2259, c2166, c2309, c2150, c1370] c2365 (by decide) p (sat_cons (step1664 p h) (sat_cons (step1657 p h) (sat_cons (step2320 p h) (sat_cons (step1721 p h) (sat_cons (step2259 p h) (sat_cons (step2166 p h) (sat_cons (step2309 p h) (sat_cons (step2150 p h) (sat_cons (step1370 p h) (sat_nil p))))))))))
def c2366 : List Lit := [(1644, true), (103, false), (1637, false), (201, true)]
theorem step2366 (p : Nat → Bool) (h : Constraints p) : clause p c2366 = true :=
  Snake9.LocalRup.prove_clause [c1482, c1491, c1495, c1485, c1468, c1476, c1477, c1466, c2325, c404, c428] c2366 (by decide) p (sat_cons (step1482 p h) (sat_cons (step1491 p h) (sat_cons (step1495 p h) (sat_cons (step1485 p h) (sat_cons (step1468 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step1466 p h) (sat_cons (step2325 p h) (sat_cons (step404 p h) (sat_cons (step428 p h) (sat_nil p))))))))))))
def c2367 : List Lit := [(80, false), (1636, true), (1681, true), (99, true), (100, true), (477, true), (116, false)]
theorem step2367 (p : Nat → Bool) (h : Constraints p) : clause p c2367 = true :=
  Snake9.LocalRup.prove_clause [c1169, c1103, c1098, c1093, c1090, c1089, c2320, c1565, c1562, c1570, c1586, c1100, c1081, c1078, c1074, c1167, c1164, c1131, c1114, c1112, c1109, c402, c429, c428, c1559, c1560, c1478, c1582, c1554, c1573, c510, c1564, c1919] c2367 (by decide) p (sat_cons (step1169 p h) (sat_cons (step1103 p h) (sat_cons (step1098 p h) (sat_cons (step1093 p h) (sat_cons (step1090 p h) (sat_cons (step1089 p h) (sat_cons (step2320 p h) (sat_cons (step1565 p h) (sat_cons (step1562 p h) (sat_cons (step1570 p h) (sat_cons (step1586 p h) (sat_cons (step1100 p h) (sat_cons (step1081 p h) (sat_cons (step1078 p h) (sat_cons (step1074 p h) (sat_cons (step1167 p h) (sat_cons (step1164 p h) (sat_cons (step1131 p h) (sat_cons (step1114 p h) (sat_cons (step1112 p h) (sat_cons (step1109 p h) (sat_cons (step402 p h) (sat_cons (step429 p h) (sat_cons (step428 p h) (sat_cons (step1559 p h) (sat_cons (step1560 p h) (sat_cons (step1478 p h) (sat_cons (step1582 p h) (sat_cons (step1554 p h) (sat_cons (step1573 p h) (sat_cons (step510 p h) (sat_cons (step1564 p h) (sat_cons (step1919 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c2368 : List Lit := [(1705, true), (1688, false), (107, false), (118, true), (236, true), (241, true), (76, false), (48, false), (116, false)]
theorem step2368 (p : Nat → Bool) (h : Constraints p) : clause p c2368 = true :=
  Snake9.LocalRup.prove_clause [c1600, c2362, c1613, c1615, c2345, c1629, c1618, c2359, c1609, c2355, c828] c2368 (by decide) p (sat_cons (step1600 p h) (sat_cons (step2362 p h) (sat_cons (step1613 p h) (sat_cons (step1615 p h) (sat_cons (step2345 p h) (sat_cons (step1629 p h) (sat_cons (step1618 p h) (sat_cons (step2359 p h) (sat_cons (step1609 p h) (sat_cons (step2355 p h) (sat_cons (step828 p h) (sat_nil p))))))))))))
def c2369 : List Lit := [(1645, true), (89, true), (105, true), (99, false), (100, true), (107, false), (415, true)]
theorem step2369 (p : Nat → Bool) (h : Constraints p) : clause p c2369 = true :=
  Snake9.LocalRup.prove_clause [c1479, c1482, c1100, c1081, c1078, c1074, c1935, c1468, c1098, c1095, c1086, c1083, c1500, c1496, c1469, c1483, c1485, c1481, c1476, c1477, c394, c470, c403, c442, c1467, c460] c2369 (by decide) p (sat_cons (step1479 p h) (sat_cons (step1482 p h) (sat_cons (step1100 p h) (sat_cons (step1081 p h) (sat_cons (step1078 p h) (sat_cons (step1074 p h) (sat_cons (step1935 p h) (sat_cons (step1468 p h) (sat_cons (step1098 p h) (sat_cons (step1095 p h) (sat_cons (step1086 p h) (sat_cons (step1083 p h) (sat_cons (step1500 p h) (sat_cons (step1496 p h) (sat_cons (step1469 p h) (sat_cons (step1483 p h) (sat_cons (step1485 p h) (sat_cons (step1481 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step394 p h) (sat_cons (step470 p h) (sat_cons (step403 p h) (sat_cons (step442 p h) (sat_cons (step1467 p h) (sat_cons (step460 p h) (sat_nil p)))))))))))))))))))))))))))
def c2370 : List Lit := [(1679, true), (212, true)]
theorem step2370 (p : Nat → Bool) (h : Constraints p) : clause p c2370 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1580, c1570, c2276, c1563] c2370 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1580 p h) (sat_cons (step1570 p h) (sat_cons (step2276 p h) (sat_cons (step1563 p h) (sat_nil p))))))
def c2371 : List Lit := [(1715, true), (1700, false), (1705, false), (1688, false), (100, true), (107, false), (477, true)]
theorem step2371 (p : Nat → Bool) (h : Constraints p) : clause p c2371 = true :=
  Snake9.LocalRup.prove_clause [c1169, c1103, c1098, c1093, c1090, c1089, c2370, c1167, c1164, c1129, c1125, c1124, c1123, c1651, c1657, c1634, c2361, c1603, c1565, c1566, c1594, c693, c632, c625] c2371 (by decide) p (sat_cons (step1169 p h) (sat_cons (step1103 p h) (sat_cons (step1098 p h) (sat_cons (step1093 p h) (sat_cons (step1090 p h) (sat_cons (step1089 p h) (sat_cons (step2370 p h) (sat_cons (step1167 p h) (sat_cons (step1164 p h) (sat_cons (step1129 p h) (sat_cons (step1125 p h) (sat_cons (step1124 p h) (sat_cons (step1123 p h) (sat_cons (step1651 p h) (sat_cons (step1657 p h) (sat_cons (step1634 p h) (sat_cons (step2361 p h) (sat_cons (step1603 p h) (sat_cons (step1565 p h) (sat_cons (step1566 p h) (sat_cons (step1594 p h) (sat_cons (step693 p h) (sat_cons (step632 p h) (sat_cons (step625 p h) (sat_nil p)))))))))))))))))))))))))
def c2372 : List Lit := [(110, false), (102, false), (103, false), (100, true), (107, false), (224, true)]
theorem step2372 (p : Nat → Bool) (h : Constraints p) : clause p c2372 = true :=
  Snake9.LocalRup.prove_clause [c693, c632, c625] c2372 (by decide) p (sat_cons (step693 p h) (sat_cons (step632 p h) (sat_cons (step625 p h) (sat_nil p))))
def c2373 : List Lit := [(80, true), (87, false), (89, false), (1644, true), (210, true)]
theorem step2373 (p : Nat → Bool) (h : Constraints p) : clause p c2373 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1469, c1466, c1467, c1468, c462, c1495, c1484, c1476, c1477, c1947, c431] c2373 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1469 p h) (sat_cons (step1466 p h) (sat_cons (step1467 p h) (sat_cons (step1468 p h) (sat_cons (step462 p h) (sat_cons (step1495 p h) (sat_cons (step1484 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step1947 p h) (sat_cons (step431 p h) (sat_nil p)))))))))))))
def c2374 : List Lit := [(1644, true), (83, false), (103, false), (100, true), (415, true)]
theorem step2374 (p : Nat → Bool) (h : Constraints p) : clause p c2374 = true :=
  Snake9.LocalRup.prove_clause [c1100, c1081, c1078, c1074, c1098, c1093, c1091, c1088, c1491, c2366, c1487, c1479, c1480, c2373, c403, c428, c2325, c1478] c2374 (by decide) p (sat_cons (step1100 p h) (sat_cons (step1081 p h) (sat_cons (step1078 p h) (sat_cons (step1074 p h) (sat_cons (step1098 p h) (sat_cons (step1093 p h) (sat_cons (step1091 p h) (sat_cons (step1088 p h) (sat_cons (step1491 p h) (sat_cons (step2366 p h) (sat_cons (step1487 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step2373 p h) (sat_cons (step403 p h) (sat_cons (step428 p h) (sat_cons (step2325 p h) (sat_cons (step1478 p h) (sat_nil p)))))))))))))))))))
def c2375 : List Lit := [(1544, true), (43, true), (100, true), (327, true)]
theorem step2375 (p : Nat → Bool) (h : Constraints p) : clause p c2375 = true :=
  Snake9.LocalRup.prove_clause [c1292, c988, c971, c964, c963, c1874, c986, c983, c975, c974, c1308, c2309, c1295, c2263, c1293] c2375 (by decide) p (sat_cons (step1292 p h) (sat_cons (step988 p h) (sat_cons (step971 p h) (sat_cons (step964 p h) (sat_cons (step963 p h) (sat_cons (step1874 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step975 p h) (sat_cons (step974 p h) (sat_cons (step1308 p h) (sat_cons (step2309 p h) (sat_cons (step1295 p h) (sat_cons (step2263 p h) (sat_cons (step1293 p h) (sat_nil p))))))))))))))))
def c2376 : List Lit := [(58, false), (1517, true), (76, false)]
theorem step2376 (p : Nat → Bool) (h : Constraints p) : clause p c2376 = true :=
  Snake9.LocalRup.prove_clause [c2031, c2174, c1808, c1011, c2116, c1010, c276, c1752, c2180, c1226, c2181, c1228] c2376 (by decide) p (sat_cons (step2031 p h) (sat_cons (step2174 p h) (sat_cons (step1808 p h) (sat_cons (step1011 p h) (sat_cons (step2116 p h) (sat_cons (step1010 p h) (sat_cons (step276 p h) (sat_cons (step1752 p h) (sat_cons (step2180 p h) (sat_cons (step1226 p h) (sat_cons (step2181 p h) (sat_cons (step1228 p h) (sat_nil p)))))))))))))
def c2377 : List Lit := [(1706, true), (1692, false), (1687, false), (118, true), (236, true), (116, false)]
theorem step2377 (p : Nat → Bool) (h : Constraints p) : clause p c2377 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1614, c1642, c1638, c1607, c1916, c1617, c1609, c775, c742, c741, c1599] c2377 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1614 p h) (sat_cons (step1642 p h) (sat_cons (step1638 p h) (sat_cons (step1607 p h) (sat_cons (step1916 p h) (sat_cons (step1617 p h) (sat_cons (step1609 p h) (sat_cons (step775 p h) (sat_cons (step742 p h) (sat_cons (step741 p h) (sat_cons (step1599 p h) (sat_nil p)))))))))))))
def c2378 : List Lit := [(1543, true), (100, true), (327, true)]
theorem step2378 (p : Nat → Bool) (h : Constraints p) : clause p c2378 = true :=
  Snake9.LocalRup.prove_clause [c988, c971, c964, c963, c1874, c986, c983, c975, c974, c1307, c2290, c1294, c2263, c1291] c2378 (by decide) p (sat_cons (step988 p h) (sat_cons (step971 p h) (sat_cons (step964 p h) (sat_cons (step963 p h) (sat_cons (step1874 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step975 p h) (sat_cons (step974 p h) (sat_cons (step1307 p h) (sat_cons (step2290 p h) (sat_cons (step1294 p h) (sat_cons (step2263 p h) (sat_cons (step1291 p h) (sat_nil p)))))))))))))))
def c2379 : List Lit := [(1594, true), (1576, false), (1562, true), (76, false), (46, false), (1566, false), (116, false)]
theorem step2379 (p : Nat → Bool) (h : Constraints p) : clause p c2379 = true :=
  Snake9.LocalRup.prove_clause [c2150, c1390, c1370, c2376, c1333, c1336, c1330, c1331, c2203, c796, c259, c1006, c2115, c1005, c255, c194, c195, c2309, c1291] c2379 (by decide) p (sat_cons (step2150 p h) (sat_cons (step1390 p h) (sat_cons (step1370 p h) (sat_cons (step2376 p h) (sat_cons (step1333 p h) (sat_cons (step1336 p h) (sat_cons (step1330 p h) (sat_cons (step1331 p h) (sat_cons (step2203 p h) (sat_cons (step796 p h) (sat_cons (step259 p h) (sat_cons (step1006 p h) (sat_cons (step2115 p h) (sat_cons (step1005 p h) (sat_cons (step255 p h) (sat_cons (step194 p h) (sat_cons (step195 p h) (sat_cons (step2309 p h) (sat_cons (step1291 p h) (sat_nil p))))))))))))))))))))
def c2380 : List Lit := [(103, false), (43, false), (1706, false), (108, true), (1736, true), (1622, false), (100, true), (477, true)]
theorem step2380 (p : Nat → Bool) (h : Constraints p) : clause p c2380 = true :=
  Snake9.LocalRup.prove_clause [c1169, c1103, c1098, c1093, c1090, c1089, c1167, c1164, c1129, c1125, c1124, c1123, c627, c625, c2374, c629, c1534, c1566, c1714, c2361, c1658] c2380 (by decide) p (sat_cons (step1169 p h) (sat_cons (step1103 p h) (sat_cons (step1098 p h) (sat_cons (step1093 p h) (sat_cons (step1090 p h) (sat_cons (step1089 p h) (sat_cons (step1167 p h) (sat_cons (step1164 p h) (sat_cons (step1129 p h) (sat_cons (step1125 p h) (sat_cons (step1124 p h) (sat_cons (step1123 p h) (sat_cons (step627 p h) (sat_cons (step625 p h) (sat_cons (step2374 p h) (sat_cons (step629 p h) (sat_cons (step1534 p h) (sat_cons (step1566 p h) (sat_cons (step1714 p h) (sat_cons (step2361 p h) (sat_cons (step1658 p h) (sat_nil p))))))))))))))))))))))
def c2381 : List Lit := [(99, false), (1644, true), (100, true), (415, true)]
theorem step2381 (p : Nat → Bool) (h : Constraints p) : clause p c2381 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1469, c1100, c1081, c1078, c1074, c1098, c1093, c1091, c1088, c1935, c1468, c1495, c1482, c1484, c1479, c1480, c1476, c2373, c1921, c403] c2381 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1469 p h) (sat_cons (step1100 p h) (sat_cons (step1081 p h) (sat_cons (step1078 p h) (sat_cons (step1074 p h) (sat_cons (step1098 p h) (sat_cons (step1093 p h) (sat_cons (step1091 p h) (sat_cons (step1088 p h) (sat_cons (step1935 p h) (sat_cons (step1468 p h) (sat_cons (step1495 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step1476 p h) (sat_cons (step2373 p h) (sat_cons (step1921 p h) (sat_cons (step403 p h) (sat_nil p))))))))))))))))))))))
end B112E019
