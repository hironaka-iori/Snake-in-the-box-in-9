import B112E004Part0010
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2438 : List Lit := [(1644, true), (91, true), (84, false), (99, true), (51, false), (54, false), (100, true)]
theorem step2438 (p : Nat → Bool) (h : Constraints p) : clause p c2438 = true :=
  Snake9.LocalRup.prove_clause [c1497, c1508, c1499, c1506, c1500, c592, c2012, c2022, c370] c2438 (by decide) p (sat_cons (step1497 p h) (sat_cons (step1508 p h) (sat_cons (step1499 p h) (sat_cons (step1506 p h) (sat_cons (step1500 p h) (sat_cons (step592 p h) (sat_cons (step2012 p h) (sat_cons (step2022 p h) (sat_cons (step370 p h) (sat_nil p))))))))))
def c2439 : List Lit := [(1602, true), (1509, false), (1540, false), (1572, true), (15, true), (71, false), (1500, false)]
theorem step2439 (p : Nat → Bool) (h : Constraints p) : clause p c2439 = true :=
  Snake9.LocalRup.prove_clause [c1417, c1874, c2001, c1365, c131, c1310, c1205, c1231] c2439 (by decide) p (sat_cons (step1417 p h) (sat_cons (step1874 p h) (sat_cons (step2001 p h) (sat_cons (step1365 p h) (sat_cons (step131 p h) (sat_cons (step1310 p h) (sat_cons (step1205 p h) (sat_cons (step1231 p h) (sat_nil p)))))))))
def c2440 : List Lit := [(13, false), (9, true), (29, true), (21, false), (1456, true), (50, true), (1448, false)]
theorem step2440 (p : Nat → Bool) (h : Constraints p) : clause p c2440 = true :=
  Snake9.LocalRup.prove_clause [c1915, c9, c10, c1098, c1107, c1101, c1115, c1126] c2440 (by decide) p (sat_cons (step1915 p h) (sat_cons (step9 p h) (sat_cons (step10 p h) (sat_cons (step1098 p h) (sat_cons (step1107 p h) (sat_cons (step1101 p h) (sat_cons (step1115 p h) (sat_cons (step1126 p h) (sat_nil p)))))))))
def c2441 : List Lit := [(109, true), (1691, true), (1652, true), (99, true), (54, true), (1643, false), (50, true), (51, false)]
theorem step2441 (p : Nat → Bool) (h : Constraints p) : clause p c2441 = true :=
  Snake9.LocalRup.prove_clause [c1518, c1550, c2291, c1547, c1821, c1514, c1516, c1520, c2276, c1512, c1599, c2407] c2441 (by decide) p (sat_cons (step1518 p h) (sat_cons (step1550 p h) (sat_cons (step2291 p h) (sat_cons (step1547 p h) (sat_cons (step1821 p h) (sat_cons (step1514 p h) (sat_cons (step1516 p h) (sat_cons (step1520 p h) (sat_cons (step2276 p h) (sat_cons (step1512 p h) (sat_cons (step1599 p h) (sat_cons (step2407 p h) (sat_nil p)))))))))))))
def c2442 : List Lit := [(1612, true), (1657, true), (99, true), (39, true)]
theorem step2442 (p : Nat → Bool) (h : Constraints p) : clause p c2442 = true :=
  Snake9.LocalRup.prove_clause [c1539, c1431, c1433, c1861, c1868, c1428, c1429, c1425, c1725, c1501, c1844, c2008, c1509, c1515, c620, c1497, c1499, c1507, c2012, c1502, c592] c2442 (by decide) p (sat_cons (step1539 p h) (sat_cons (step1431 p h) (sat_cons (step1433 p h) (sat_cons (step1861 p h) (sat_cons (step1868 p h) (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step1425 p h) (sat_cons (step1725 p h) (sat_cons (step1501 p h) (sat_cons (step1844 p h) (sat_cons (step2008 p h) (sat_cons (step1509 p h) (sat_cons (step1515 p h) (sat_cons (step620 p h) (sat_cons (step1497 p h) (sat_cons (step1499 p h) (sat_cons (step1507 p h) (sat_cons (step2012 p h) (sat_cons (step1502 p h) (sat_cons (step592 p h) (sat_nil p))))))))))))))))))))))
def c2443 : List Lit := [(91, true), (84, false), (1644, true), (99, true), (39, true)]
theorem step2443 (p : Nat → Bool) (h : Constraints p) : clause p c2443 = true :=
  Snake9.LocalRup.prove_clause [c1508, c1497, c1499, c1506, c2012, c1500, c592] c2443 (by decide) p (sat_cons (step1508 p h) (sat_cons (step1497 p h) (sat_cons (step1499 p h) (sat_cons (step1506 p h) (sat_cons (step2012 p h) (sat_cons (step1500 p h) (sat_cons (step592 p h) (sat_nil p))))))))
def c2444 : List Lit := [(1567, true), (1515, false), (1530, false), (39, true), (51, false)]
theorem step2444 (p : Nat → Bool) (h : Constraints p) : clause p c2444 = true :=
  Snake9.LocalRup.prove_clause [c2325, c1307, c2113, c1345, c1308, c2094, c2312] c2444 (by decide) p (sat_cons (step2325 p h) (sat_cons (step1307 p h) (sat_cons (step2113 p h) (sat_cons (step1345 p h) (sat_cons (step1308 p h) (sat_cons (step2094 p h) (sat_cons (step2312 p h) (sat_nil p))))))))
def c2445 : List Lit := [(55, false), (1539, true), (103, false), (1530, false)]
theorem step2445 (p : Nat → Bool) (h : Constraints p) : clause p c2445 = true :=
  Snake9.LocalRup.prove_clause [c2393, c2364] c2445 (by decide) p (sat_cons (step2393 p h) (sat_cons (step2364 p h) (sat_nil p)))
def c2446 : List Lit := [(39, true), (51, false), (56, false), (1522, false), (1568, true), (55, true), (1515, false), (1530, false)]
theorem step2446 (p : Nat → Bool) (h : Constraints p) : clause p c2446 = true :=
  Snake9.LocalRup.prove_clause [c1245, c2325, c1259, c2262, c2340, c1202, c2094, c1346, c1308, c1314, c1277, c1273, c1228, c1248, c1262, c1239, c1240, c1254, c319, c2216, c1954, c1210, c2193, c271, c1219, c1232, c2263, c1203, c1201] c2446 (by decide) p (sat_cons (step1245 p h) (sat_cons (step2325 p h) (sat_cons (step1259 p h) (sat_cons (step2262 p h) (sat_cons (step2340 p h) (sat_cons (step1202 p h) (sat_cons (step2094 p h) (sat_cons (step1346 p h) (sat_cons (step1308 p h) (sat_cons (step1314 p h) (sat_cons (step1277 p h) (sat_cons (step1273 p h) (sat_cons (step1228 p h) (sat_cons (step1248 p h) (sat_cons (step1262 p h) (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step1254 p h) (sat_cons (step319 p h) (sat_cons (step2216 p h) (sat_cons (step1954 p h) (sat_cons (step1210 p h) (sat_cons (step2193 p h) (sat_cons (step271 p h) (sat_cons (step1219 p h) (sat_cons (step1232 p h) (sat_cons (step2263 p h) (sat_cons (step1203 p h) (sat_cons (step1201 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2447 : List Lit := [(1549, true), (51, false), (56, false), (1522, false), (55, true), (1515, false), (1530, false)]
theorem step2447 (p : Nat → Bool) (h : Constraints p) : clause p c2447 = true :=
  Snake9.LocalRup.prove_clause [c1245, c2325, c1259, c1308, c1314, c1277, c1273, c1248, c1262, c1239, c1240, c1254, c319, c2216, c1954, c1953, c2193, c271, c1232, c1199, c1203, c1202, c1201, c1228, c1810, c2304, c174] c2447 (by decide) p (sat_cons (step1245 p h) (sat_cons (step2325 p h) (sat_cons (step1259 p h) (sat_cons (step1308 p h) (sat_cons (step1314 p h) (sat_cons (step1277 p h) (sat_cons (step1273 p h) (sat_cons (step1248 p h) (sat_cons (step1262 p h) (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step1254 p h) (sat_cons (step319 p h) (sat_cons (step2216 p h) (sat_cons (step1954 p h) (sat_cons (step1953 p h) (sat_cons (step2193 p h) (sat_cons (step271 p h) (sat_cons (step1232 p h) (sat_cons (step1199 p h) (sat_cons (step1203 p h) (sat_cons (step1202 p h) (sat_cons (step1201 p h) (sat_cons (step1228 p h) (sat_cons (step1810 p h) (sat_cons (step2304 p h) (sat_cons (step174 p h) (sat_nil p))))))))))))))))))))))))))))
def c2448 : List Lit := [(36, true), (1501, true), (44, true), (1516, true), (1505, false), (39, false), (51, false)]
theorem step2448 (p : Nat → Bool) (h : Constraints p) : clause p c2448 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1201, c1202, c206, c1228, c1212, c1217] c2448 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1201 p h) (sat_cons (step1202 p h) (sat_cons (step206 p h) (sat_cons (step1228 p h) (sat_cons (step1212 p h) (sat_cons (step1217 p h) (sat_nil p))))))))
def c2449 : List Lit := [(5, true), (1455, true)]
theorem step2449 (p : Nat → Bool) (h : Constraints p) : clause p c2449 = true :=
  Snake9.LocalRup.prove_clause [c1098, c2187, c1101, c1109, c1125, c1112] c2449 (by decide) p (sat_cons (step1098 p h) (sat_cons (step2187 p h) (sat_cons (step1101 p h) (sat_cons (step1109 p h) (sat_cons (step1125 p h) (sat_cons (step1112 p h) (sat_nil p)))))))
def c2450 : List Lit := [(15, false), (12, false), (56, false), (55, true)]
theorem step2450 (p : Nat → Bool) (h : Constraints p) : clause p c2450 = true :=
  Snake9.LocalRup.prove_clause [c56, c1918] c2450 (by decide) p (sat_cons (step56 p h) (sat_cons (step1918 p h) (sat_nil p)))
def c2451 : List Lit := [(1516, true), (4, true), (13, false), (1500, false), (14, true), (42, true), (21, false), (1505, false), (51, false)]
theorem step2451 (p : Nat → Bool) (h : Constraints p) : clause p c2451 = true :=
  Snake9.LocalRup.prove_clause [c1211, c1216, c1202, c1228, c1217, c1212, c1232, c1205, c329, c107, c1914] c2451 (by decide) p (sat_cons (step1211 p h) (sat_cons (step1216 p h) (sat_cons (step1202 p h) (sat_cons (step1228 p h) (sat_cons (step1217 p h) (sat_cons (step1212 p h) (sat_cons (step1232 p h) (sat_cons (step1205 p h) (sat_cons (step329 p h) (sat_cons (step107 p h) (sat_cons (step1914 p h) (sat_nil p))))))))))))
def c2452 : List Lit := [(56, true), (55, false), (1537, true)]
theorem step2452 (p : Nat → Bool) (h : Constraints p) : clause p c2452 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1264, c1253, c1255, c1261, c2258, c1272] c2452 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1264 p h) (sat_cons (step1253 p h) (sat_cons (step1255 p h) (sat_cons (step1261 p h) (sat_cons (step2258 p h) (sat_cons (step1272 p h) (sat_nil p))))))))
def c2453 : List Lit := [(53, false), (1525, true), (56, false), (55, false)]
theorem step2453 (p : Nat → Bool) (h : Constraints p) : clause p c2453 = true :=
  Snake9.LocalRup.prove_clause [c430, c436, c1239, c1242, c1248] c2453 (by decide) p (sat_cons (step430 p h) (sat_cons (step436 p h) (sat_cons (step1239 p h) (sat_cons (step1242 p h) (sat_cons (step1248 p h) (sat_nil p))))))
def c2454 : List Lit := [(1524, true), (56, false)]
theorem step2454 (p : Nat → Bool) (h : Constraints p) : clause p c2454 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1247, c1242, c2309] c2454 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1247 p h) (sat_cons (step1242 p h) (sat_cons (step2309 p h) (sat_nil p)))))
def c2455 : List Lit := [(1537, true), (56, false), (55, false)]
theorem step2455 (p : Nat → Bool) (h : Constraints p) : clause p c2455 = true :=
  Snake9.LocalRup.prove_clause [c2454, c1276, c1272, c2453, c1261, c1254] c2455 (by decide) p (sat_cons (step2454 p h) (sat_cons (step1276 p h) (sat_cons (step1272 p h) (sat_cons (step2453 p h) (sat_cons (step1261 p h) (sat_cons (step1254 p h) (sat_nil p)))))))
def c2456 : List Lit := [(1657, false), (1712, true), (38, false), (1595, false), (1594, false)]
theorem step2456 (p : Nat → Bool) (h : Constraints p) : clause p c2456 = true :=
  Snake9.LocalRup.prove_clause [c2167, c2268, c2153, c1645, c1604] c2456 (by decide) p (sat_cons (step2167 p h) (sat_cons (step2268 p h) (sat_cons (step2153 p h) (sat_cons (step1645 p h) (sat_cons (step1604 p h) (sat_nil p))))))
def c2457 : List Lit := [(40, false), (49, true), (38, false), (36, false), (56, false)]
theorem step2457 (p : Nat → Bool) (h : Constraints p) : clause p c2457 = true :=
  Snake9.LocalRup.prove_clause [c176, c247, c1945] c2457 (by decide) p (sat_cons (step176 p h) (sat_cons (step247 p h) (sat_cons (step1945 p h) (sat_nil p))))
def c2458 : List Lit := [(1647, false), (1644, false), (108, true), (1693, true), (103, true), (1649, false)]
theorem step2458 (p : Nat → Bool) (h : Constraints p) : clause p c2458 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1554, c2120, c1614, c1537, c1520, c1521, c1536, c1516, c1610, c2189, c2121, c1548, c1557] c2458 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1554 p h) (sat_cons (step2120 p h) (sat_cons (step1614 p h) (sat_cons (step1537 p h) (sat_cons (step1520 p h) (sat_cons (step1521 p h) (sat_cons (step1536 p h) (sat_cons (step1516 p h) (sat_cons (step1610 p h) (sat_cons (step2189 p h) (sat_cons (step2121 p h) (sat_cons (step1548 p h) (sat_cons (step1557 p h) (sat_nil p)))))))))))))))
def c2459 : List Lit := [(1612, true), (50, true), (90, true), (1693, true), (103, true), (54, true), (1649, false), (51, false)]
theorem step2459 (p : Nat → Bool) (h : Constraints p) : clause p c2459 = true :=
  Snake9.LocalRup.prove_clause [c1498, c1517, c1433, c1868, c2290, c1425, c1501, c1546, c1506, c2458, c1511, c1512, c2284, c2030, c2192, c1610, c1540, c1509, c1507, c1499, c1502, c594, c668, c2022] c2459 (by decide) p (sat_cons (step1498 p h) (sat_cons (step1517 p h) (sat_cons (step1433 p h) (sat_cons (step1868 p h) (sat_cons (step2290 p h) (sat_cons (step1425 p h) (sat_cons (step1501 p h) (sat_cons (step1546 p h) (sat_cons (step1506 p h) (sat_cons (step2458 p h) (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step2284 p h) (sat_cons (step2030 p h) (sat_cons (step2192 p h) (sat_cons (step1610 p h) (sat_cons (step1540 p h) (sat_cons (step1509 p h) (sat_cons (step1507 p h) (sat_cons (step1499 p h) (sat_cons (step1502 p h) (sat_cons (step594 p h) (sat_cons (step668 p h) (sat_cons (step2022 p h) (sat_nil p)))))))))))))))))))))))))
def c2460 : List Lit := [(1647, false), (1691, true), (103, true), (1653, true), (102, false), (1649, false)]
theorem step2460 (p : Nat → Bool) (h : Constraints p) : clause p c2460 = true :=
  Snake9.LocalRup.prove_clause [c1520, c1521, c1526, c1516, c1599, c1821, c2121, c1554, c1555, c2192, c1578, c1549, c1550, c2046, c1892, c736] c2460 (by decide) p (sat_cons (step1520 p h) (sat_cons (step1521 p h) (sat_cons (step1526 p h) (sat_cons (step1516 p h) (sat_cons (step1599 p h) (sat_cons (step1821 p h) (sat_cons (step2121 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step2192 p h) (sat_cons (step1578 p h) (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step2046 p h) (sat_cons (step1892 p h) (sat_cons (step736 p h) (sat_nil p)))))))))))))))))
def c2461 : List Lit := [(1691, true), (103, true), (1657, true), (102, false), (91, false), (90, false), (1649, false)]
theorem step2461 (p : Nat → Bool) (h : Constraints p) : clause p c2461 = true :=
  Snake9.LocalRup.prove_clause [c1517, c1535, c1527, c2460, c1512, c2434, c616, c2010, c598, c597, c1550, c1500, c1503, c1530, c1531, c1599, c1518, c2121, c1516, c1555, c1821] c2461 (by decide) p (sat_cons (step1517 p h) (sat_cons (step1535 p h) (sat_cons (step1527 p h) (sat_cons (step2460 p h) (sat_cons (step1512 p h) (sat_cons (step2434 p h) (sat_cons (step616 p h) (sat_cons (step2010 p h) (sat_cons (step598 p h) (sat_cons (step597 p h) (sat_cons (step1550 p h) (sat_cons (step1500 p h) (sat_cons (step1503 p h) (sat_cons (step1530 p h) (sat_cons (step1531 p h) (sat_cons (step1599 p h) (sat_cons (step1518 p h) (sat_cons (step2121 p h) (sat_cons (step1516 p h) (sat_cons (step1555 p h) (sat_cons (step1821 p h) (sat_nil p))))))))))))))))))))))
def c2462 : List Lit := [(5, false), (1516, true), (38, true), (39, false), (90, false)]
theorem step2462 (p : Nat → Bool) (h : Constraints p) : clause p c2462 = true :=
  Snake9.LocalRup.prove_clause [c196, c192, c199, c1209, c1200, c1211, c1202, c1219, c1228] c2462 (by decide) p (sat_cons (step196 p h) (sat_cons (step192 p h) (sat_cons (step199 p h) (sat_cons (step1209 p h) (sat_cons (step1200 p h) (sat_cons (step1211 p h) (sat_cons (step1202 p h) (sat_cons (step1219 p h) (sat_cons (step1228 p h) (sat_nil p))))))))))
def c2463 : List Lit := [(1610, true), (93, true)]
theorem step2463 (p : Nat → Bool) (h : Constraints p) : clause p c2463 = true :=
  Snake9.LocalRup.prove_clause [c1428, c1429, c2008, c2007, c1725] c2463 (by decide) p (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step2008 p h) (sat_cons (step2007 p h) (sat_cons (step1725 p h) (sat_nil p))))))
def c2464 : List Lit := [(1589, true), (55, true), (56, false)]
theorem step2464 (p : Nat → Bool) (h : Constraints p) : clause p c2464 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1393, c1388, c1385, c1995, c530] c2464 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step1388 p h) (sat_cons (step1385 p h) (sat_cons (step1995 p h) (sat_cons (step530 p h) (sat_nil p)))))))
def c2465 : List Lit := [(39, false), (90, false), (1515, true), (51, false)]
theorem step2465 (p : Nat → Bool) (h : Constraints p) : clause p c2465 = true :=
  Snake9.LocalRup.prove_clause [c219, c210, c216, c1211, c1200, c1207, c1216, c1202, c1227] c2465 (by decide) p (sat_cons (step219 p h) (sat_cons (step210 p h) (sat_cons (step216 p h) (sat_cons (step1211 p h) (sat_cons (step1200 p h) (sat_cons (step1207 p h) (sat_cons (step1216 p h) (sat_cons (step1202 p h) (sat_cons (step1227 p h) (sat_nil p))))))))))
def c2466 : List Lit := [(1663, false), (102, false), (109, false), (111, false), (1681, true)]
theorem step2466 (p : Nat → Bool) (h : Constraints p) : clause p c2466 = true :=
  Snake9.LocalRup.prove_clause [c1554, c2192, c1578, c2046, c1892, c736] c2466 (by decide) p (sat_cons (step1554 p h) (sat_cons (step2192 p h) (sat_cons (step1578 p h) (sat_cons (step2046 p h) (sat_cons (step1892 p h) (sat_cons (step736 p h) (sat_nil p)))))))
def c2467 : List Lit := [(102, false), (1681, true), (117, true)]
theorem step2467 (p : Nat → Bool) (h : Constraints p) : clause p c2467 = true :=
  Snake9.LocalRup.prove_clause [c1564, c2335, c1550, c1549, c1576, c2466, c1547, c2409, c1570, c1565, c736, c774, c2055] c2467 (by decide) p (sat_cons (step1564 p h) (sat_cons (step2335 p h) (sat_cons (step1550 p h) (sat_cons (step1549 p h) (sat_cons (step1576 p h) (sat_cons (step2466 p h) (sat_cons (step1547 p h) (sat_cons (step2409 p h) (sat_cons (step1570 p h) (sat_cons (step1565 p h) (sat_cons (step736 p h) (sat_cons (step774 p h) (sat_cons (step2055 p h) (sat_nil p))))))))))))))
def c2468 : List Lit := [(119, true), (1681, true), (117, true)]
theorem step2468 (p : Nat → Bool) (h : Constraints p) : clause p c2468 = true :=
  Snake9.LocalRup.prove_clause [c1576, c1892, c1565, c1578, c1570, c1554, c2409, c1547] c2468 (by decide) p (sat_cons (step1576 p h) (sat_cons (step1892 p h) (sat_cons (step1565 p h) (sat_cons (step1578 p h) (sat_cons (step1570 p h) (sat_cons (step1554 p h) (sat_cons (step2409 p h) (sat_cons (step1547 p h) (sat_nil p)))))))))
def c2469 : List Lit := [(1663, true), (1648, false), (1644, false), (1673, false), (1693, true)]
theorem step2469 (p : Nat → Bool) (h : Constraints p) : clause p c2469 = true :=
  Snake9.LocalRup.prove_clause [c1547, c1821, c2409, c1514, c1569, c1523, c1575, c1537, c1614] c2469 (by decide) p (sat_cons (step1547 p h) (sat_cons (step1821 p h) (sat_cons (step2409 p h) (sat_cons (step1514 p h) (sat_cons (step1569 p h) (sat_cons (step1523 p h) (sat_cons (step1575 p h) (sat_cons (step1537 p h) (sat_cons (step1614 p h) (sat_nil p))))))))))
def c2470 : List Lit := [(108, false), (105, false), (114, false)]
theorem step2470 (p : Nat → Bool) (h : Constraints p) : clause p c2470 = true :=
  Snake9.LocalRup.prove_clause [c719, c2036] c2470 (by decide) p (sat_cons (step719 p h) (sat_cons (step2036 p h) (sat_nil p)))
def c2471 : List Lit := [(1681, true), (1644, false), (117, true), (101, true), (1693, true)]
theorem step2471 (p : Nat → Bool) (h : Constraints p) : clause p c2471 = true :=
  Snake9.LocalRup.prove_clause [c1564, c2121, c1557, c2467, c1513, c2469, c1554, c2120, c1578, c1614, c1569, c1537, c1561, c2409, c1523, c1548, c1514, c2470] c2471 (by decide) p (sat_cons (step1564 p h) (sat_cons (step2121 p h) (sat_cons (step1557 p h) (sat_cons (step2467 p h) (sat_cons (step1513 p h) (sat_cons (step2469 p h) (sat_cons (step1554 p h) (sat_cons (step2120 p h) (sat_cons (step1578 p h) (sat_cons (step1614 p h) (sat_cons (step1569 p h) (sat_cons (step1537 p h) (sat_cons (step1561 p h) (sat_cons (step2409 p h) (sat_cons (step1523 p h) (sat_cons (step1548 p h) (sat_cons (step1514 p h) (sat_cons (step2470 p h) (sat_nil p)))))))))))))))))))
def c2472 : List Lit := [(1590, true), (1549, true), (73, true), (55, false), (103, false), (50, true), (51, false)]
theorem step2472 (p : Nat → Bool) (h : Constraints p) : clause p c2472 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1394, c1879, c2146, c1210, c1257, c2147, c2445, c1301] c2472 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1394 p h) (sat_cons (step1879 p h) (sat_cons (step2146 p h) (sat_cons (step1210 p h) (sat_cons (step1257 p h) (sat_cons (step2147 p h) (sat_cons (step2445 p h) (sat_cons (step1301 p h) (sat_nil p))))))))))
def c2473 : List Lit := [(1514, true), (53, false), (51, false)]
theorem step2473 (p : Nat → Bool) (h : Constraints p) : clause p c2473 = true :=
  Snake9.LocalRup.prove_clause [c2437, c1804, c2147, c2262, c1211, c1202, c395, c1947, c1226, c246, c1215, c1207] c2473 (by decide) p (sat_cons (step2437 p h) (sat_cons (step1804 p h) (sat_cons (step2147 p h) (sat_cons (step2262 p h) (sat_cons (step1211 p h) (sat_cons (step1202 p h) (sat_cons (step395 p h) (sat_cons (step1947 p h) (sat_cons (step1226 p h) (sat_cons (step246 p h) (sat_cons (step1215 p h) (sat_cons (step1207 p h) (sat_nil p)))))))))))))
def c2474 : List Lit := [(1590, true), (1569, true), (73, true), (15, true), (55, false), (1455, false), (103, false), (50, true), (51, false)]
theorem step2474 (p : Nat → Bool) (h : Constraints p) : clause p c2474 = true :=
  Snake9.LocalRup.prove_clause [c2094, c1347, c1388, c1392, c1394, c1879, c2472, c1390, c1386, c2146, c1210, c1355, c1257, c1189, c2445, c1799, c1309, c1136, c2223, c1852, c1111, c1204, c2198, c1227, c1207, c1216] c2474 (by decide) p (sat_cons (step2094 p h) (sat_cons (step1347 p h) (sat_cons (step1388 p h) (sat_cons (step1392 p h) (sat_cons (step1394 p h) (sat_cons (step1879 p h) (sat_cons (step2472 p h) (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step2146 p h) (sat_cons (step1210 p h) (sat_cons (step1355 p h) (sat_cons (step1257 p h) (sat_cons (step1189 p h) (sat_cons (step2445 p h) (sat_cons (step1799 p h) (sat_cons (step1309 p h) (sat_cons (step1136 p h) (sat_cons (step2223 p h) (sat_cons (step1852 p h) (sat_cons (step1111 p h) (sat_cons (step1204 p h) (sat_cons (step2198 p h) (sat_cons (step1227 p h) (sat_cons (step1207 p h) (sat_cons (step1216 p h) (sat_nil p)))))))))))))))))))))))))))
def c2475 : List Lit := [(1665, false), (1692, true), (1668, true), (102, true)]
theorem step2475 (p : Nat → Bool) (h : Constraints p) : clause p c2475 = true :=
  Snake9.LocalRup.prove_clause [c1555, c1821, c2404, c1514] c2475 (by decide) p (sat_cons (step1555 p h) (sat_cons (step1821 p h) (sat_cons (step2404 p h) (sat_cons (step1514 p h) (sat_nil p)))))
def c2476 : List Lit := [(1649, false), (1658, true), (102, true), (55, true), (103, false)]
theorem step2476 (p : Nat → Bool) (h : Constraints p) : clause p c2476 = true :=
  Snake9.LocalRup.prove_clause [c2035, c2034, c1729, c1497, c1505, c1532, c1511, c1523, c1520, c1513, c1536, c674, c1506, c1500] c2476 (by decide) p (sat_cons (step2035 p h) (sat_cons (step2034 p h) (sat_cons (step1729 p h) (sat_cons (step1497 p h) (sat_cons (step1505 p h) (sat_cons (step1532 p h) (sat_cons (step1511 p h) (sat_cons (step1523 p h) (sat_cons (step1520 p h) (sat_cons (step1513 p h) (sat_cons (step1536 p h) (sat_cons (step674 p h) (sat_cons (step1506 p h) (sat_cons (step1500 p h) (sat_nil p)))))))))))))))
def c2477 : List Lit := [(1691, true), (1681, true), (102, true), (55, true), (103, false)]
theorem step2477 (p : Nat → Bool) (h : Constraints p) : clause p c2477 = true :=
  Snake9.LocalRup.prove_clause [c2121, c1557, c2035, c2034, c1729, c1497, c1505, c2126, c2476, c1514, c1821, c2189, c1554, c1548, c2120, c1578, c2470, c1604, c1561, c1531, c1569, c1522, c1564, c1513, c677] c2477 (by decide) p (sat_cons (step2121 p h) (sat_cons (step1557 p h) (sat_cons (step2035 p h) (sat_cons (step2034 p h) (sat_cons (step1729 p h) (sat_cons (step1497 p h) (sat_cons (step1505 p h) (sat_cons (step2126 p h) (sat_cons (step2476 p h) (sat_cons (step1514 p h) (sat_cons (step1821 p h) (sat_cons (step2189 p h) (sat_cons (step1554 p h) (sat_cons (step1548 p h) (sat_cons (step2120 p h) (sat_cons (step1578 p h) (sat_cons (step2470 p h) (sat_cons (step1604 p h) (sat_cons (step1561 p h) (sat_cons (step1531 p h) (sat_cons (step1569 p h) (sat_cons (step1522 p h) (sat_cons (step1564 p h) (sat_cons (step1513 p h) (sat_cons (step677 p h) (sat_nil p))))))))))))))))))))))))))
def c2478 : List Lit := [(105, false), (1618, true), (1668, true), (21, false)]
theorem step2478 (p : Nat → Bool) (h : Constraints p) : clause p c2478 = true :=
  Snake9.LocalRup.prove_clause [c1557, c1821, c2189, c1555, c1548, c1550, c2290, c1827, c1449, c1421] c2478 (by decide) p (sat_cons (step1557 p h) (sat_cons (step1821 p h) (sat_cons (step2189 p h) (sat_cons (step1555 p h) (sat_cons (step1548 p h) (sat_cons (step1550 p h) (sat_cons (step2290 p h) (sat_cons (step1827 p h) (sat_cons (step1449 p h) (sat_cons (step1421 p h) (sat_nil p)))))))))))
def c2479 : List Lit := [(1657, true), (102, true), (55, true), (103, false)]
theorem step2479 (p : Nat → Bool) (h : Constraints p) : clause p c2479 = true :=
  Snake9.LocalRup.prove_clause [c1511, c1519, c2035, c2034, c1729, c1497, c1505, c1531, c1535, c1522, c1506, c1513, c1500, c674] c2479 (by decide) p (sat_cons (step1511 p h) (sat_cons (step1519 p h) (sat_cons (step2035 p h) (sat_cons (step2034 p h) (sat_cons (step1729 p h) (sat_cons (step1497 p h) (sat_cons (step1505 p h) (sat_cons (step1531 p h) (sat_cons (step1535 p h) (sat_cons (step1522 p h) (sat_cons (step1506 p h) (sat_cons (step1513 p h) (sat_cons (step1500 p h) (sat_cons (step674 p h) (sat_nil p)))))))))))))))
def c2480 : List Lit := [(97, true), (1658, true), (102, true), (55, true), (103, false)]
theorem step2480 (p : Nat → Bool) (h : Constraints p) : clause p c2480 = true :=
  Snake9.LocalRup.prove_clause [c2035, c2034, c1729, c1497, c1511, c1519, c1540, c1507, c1501, c1502, c1506, c674, c1536, c1513, c1522] c2480 (by decide) p (sat_cons (step2035 p h) (sat_cons (step2034 p h) (sat_cons (step1729 p h) (sat_cons (step1497 p h) (sat_cons (step1511 p h) (sat_cons (step1519 p h) (sat_cons (step1540 p h) (sat_cons (step1507 p h) (sat_cons (step1501 p h) (sat_cons (step1502 p h) (sat_cons (step1506 p h) (sat_cons (step674 p h) (sat_cons (step1536 p h) (sat_cons (step1513 p h) (sat_cons (step1522 p h) (sat_nil p))))))))))))))))
def c2481 : List Lit := [(101, false), (97, false), (1645, true), (1525, true), (1548, true), (1532, false), (1507, false), (55, true), (103, false), (51, false)]
theorem step2481 (p : Nat → Bool) (h : Constraints p) : clause p c2481 = true :=
  Snake9.LocalRup.prove_clause [c2035, c2034, c1729, c665, c674, c1242, c1500, c1245, c1248, c1509, c1272, c1239, c1240, c1499, c1307, c321, c2465, c1954, c2296, c271] c2481 (by decide) p (sat_cons (step2035 p h) (sat_cons (step2034 p h) (sat_cons (step1729 p h) (sat_cons (step665 p h) (sat_cons (step674 p h) (sat_cons (step1242 p h) (sat_cons (step1500 p h) (sat_cons (step1245 p h) (sat_cons (step1248 p h) (sat_cons (step1509 p h) (sat_cons (step1272 p h) (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step1499 p h) (sat_cons (step1307 p h) (sat_cons (step321 p h) (sat_cons (step2465 p h) (sat_cons (step1954 p h) (sat_cons (step2296 p h) (sat_cons (step271 p h) (sat_nil p)))))))))))))))))))))
def c2482 : List Lit := [(1658, true), (1525, true), (1548, true), (1532, false), (1507, false), (102, true), (55, true), (103, false), (51, false)]
theorem step2482 (p : Nat → Bool) (h : Constraints p) : clause p c2482 = true :=
  Snake9.LocalRup.prove_clause [c1511, c1519, c2035, c2034, c1729, c1497, c1540, c2480, c2481, c1513, c1522, c1536, c1508, c1506, c1499, c1500, c663, c1242, c1245, c1248, c1272, c1239, c1240, c1307, c321, c2465, c1954, c2296, c271] c2482 (by decide) p (sat_cons (step1511 p h) (sat_cons (step1519 p h) (sat_cons (step2035 p h) (sat_cons (step2034 p h) (sat_cons (step1729 p h) (sat_cons (step1497 p h) (sat_cons (step1540 p h) (sat_cons (step2480 p h) (sat_cons (step2481 p h) (sat_cons (step1513 p h) (sat_cons (step1522 p h) (sat_cons (step1536 p h) (sat_cons (step1508 p h) (sat_cons (step1506 p h) (sat_cons (step1499 p h) (sat_cons (step1500 p h) (sat_cons (step663 p h) (sat_cons (step1242 p h) (sat_cons (step1245 p h) (sat_cons (step1248 p h) (sat_cons (step1272 p h) (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step1307 p h) (sat_cons (step321 p h) (sat_cons (step2465 p h) (sat_cons (step1954 p h) (sat_cons (step2296 p h) (sat_cons (step271 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2483 : List Lit := [(1524, true), (55, true), (50, true)]
theorem step2483 (p : Nat → Bool) (h : Constraints p) : clause p c2483 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1247, c1242, c2149, c1964] c2483 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1247 p h) (sat_cons (step1242 p h) (sat_cons (step2149 p h) (sat_cons (step1964 p h) (sat_nil p))))))
def c2484 : List Lit := [(1505, false), (45, false), (52, false), (1515, true), (42, true)]
theorem step2484 (p : Nat → Bool) (h : Constraints p) : clause p c2484 = true :=
  Snake9.LocalRup.prove_clause [c1223, c1211, c1216, c1217, c1227, c1212, c1202, c270, c1199] c2484 (by decide) p (sat_cons (step1223 p h) (sat_cons (step1211 p h) (sat_cons (step1216 p h) (sat_cons (step1217 p h) (sat_cons (step1227 p h) (sat_cons (step1212 p h) (sat_cons (step1202 p h) (sat_cons (step270 p h) (sat_cons (step1199 p h) (sat_nil p))))))))))
def c2485 : List Lit := [(52, false), (1515, true), (1549, true), (56, true), (42, true), (55, true), (50, true), (51, false)]
theorem step2485 (p : Nat → Bool) (h : Constraints p) : clause p c2485 = true :=
  Snake9.LocalRup.prove_clause [c1964, c2484, c1207, c1208, c2249] c2485 (by decide) p (sat_cons (step1964 p h) (sat_cons (step2484 p h) (sat_cons (step1207 p h) (sat_cons (step1208 p h) (sat_cons (step2249 p h) (sat_nil p))))))
def c2486 : List Lit := [(45, false), (46, false), (48, false), (1515, true), (42, true)]
theorem step2486 (p : Nat → Bool) (h : Constraints p) : clause p c2486 = true :=
  Snake9.LocalRup.prove_clause [c274, c271, c1212, c1199, c1214, c1202, c1227] c2486 (by decide) p (sat_cons (step274 p h) (sat_cons (step271 p h) (sat_cons (step1212 p h) (sat_cons (step1199 p h) (sat_cons (step1214 p h) (sat_cons (step1202 p h) (sat_cons (step1227 p h) (sat_nil p))))))))
def c2487 : List Lit := [(1520, true), (42, true), (1511, true), (45, true), (47, false), (55, true), (53, false)]
theorem step2487 (p : Nat → Bool) (h : Constraints p) : clause p c2487 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1240, c287, c1954, c1212, c309, c1217, c1208] c2487 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step287 p h) (sat_cons (step1954 p h) (sat_cons (step1212 p h) (sat_cons (step309 p h) (sat_cons (step1217 p h) (sat_cons (step1208 p h) (sat_nil p)))))))))
def c2488 : List Lit := [(48, false), (12, false), (56, false), (45, true), (55, true)]
theorem step2488 (p : Nat → Bool) (h : Constraints p) : clause p c2488 = true :=
  Snake9.LocalRup.prove_clause [c1954, c303] c2488 (by decide) p (sat_cons (step1954 p h) (sat_cons (step303 p h) (sat_nil p)))
def c2489 : List Lit := [(38, true), (1507, false), (1515, true), (51, false)]
theorem step2489 (p : Nat → Bool) (h : Constraints p) : clause p c2489 = true :=
  Snake9.LocalRup.prove_clause [c1223, c1219, c1208, c1209, c1216, c1227, c1202, c1200, c2262, c204] c2489 (by decide) p (sat_cons (step1223 p h) (sat_cons (step1219 p h) (sat_cons (step1208 p h) (sat_cons (step1209 p h) (sat_cons (step1216 p h) (sat_cons (step1227 p h) (sat_cons (step1202 p h) (sat_cons (step1200 p h) (sat_cons (step2262 p h) (sat_cons (step204 p h) (sat_nil p)))))))))))
def c2490 : List Lit := [(1500, true), (42, false), (51, false)]
theorem step2490 (p : Nat → Bool) (h : Constraints p) : clause p c2490 = true :=
  Snake9.LocalRup.prove_clause [c1200, c2262, c206] c2490 (by decide) p (sat_cons (step1200 p h) (sat_cons (step2262 p h) (sat_cons (step206 p h) (sat_nil p))))
def c2491 : List Lit := [(1505, false), (38, false), (42, false), (1515, true), (1538, true), (1522, false), (47, false), (53, false), (51, false)]
theorem step2491 (p : Nat → Bool) (h : Constraints p) : clause p c2491 = true :=
  Snake9.LocalRup.prove_clause [c2490, c1202, c1227, c1281, c1251, c1215, c1231, c1203, c1216, c1210, c287, c1239, c1241, c1248, c1277, c1261, c1253, c2145, c248, c310, c206, c1945, c1201, c177] c2491 (by decide) p (sat_cons (step2490 p h) (sat_cons (step1202 p h) (sat_cons (step1227 p h) (sat_cons (step1281 p h) (sat_cons (step1251 p h) (sat_cons (step1215 p h) (sat_cons (step1231 p h) (sat_cons (step1203 p h) (sat_cons (step1216 p h) (sat_cons (step1210 p h) (sat_cons (step287 p h) (sat_cons (step1239 p h) (sat_cons (step1241 p h) (sat_cons (step1248 p h) (sat_cons (step1277 p h) (sat_cons (step1261 p h) (sat_cons (step1253 p h) (sat_cons (step2145 p h) (sat_cons (step248 p h) (sat_cons (step310 p h) (sat_cons (step206 p h) (sat_cons (step1945 p h) (sat_cons (step1201 p h) (sat_cons (step177 p h) (sat_nil p)))))))))))))))))))))))))
def c2492 : List Lit := [(38, false), (42, false), (1515, true), (1538, true), (1522, false), (47, false), (54, true), (53, false), (51, false)]
theorem step2492 (p : Nat → Bool) (h : Constraints p) : clause p c2492 = true :=
  Snake9.LocalRup.prove_clause [c2491, c1207, c212, c246, c1947] c2492 (by decide) p (sat_cons (step2491 p h) (sat_cons (step1207 p h) (sat_cons (step212 p h) (sat_cons (step246 p h) (sat_cons (step1947 p h) (sat_nil p))))))
def c2493 : List Lit := [(1538, true), (42, false), (1515, true), (1522, false), (47, false), (54, true), (53, false), (51, false)]
theorem step2493 (p : Nat → Bool) (h : Constraints p) : clause p c2493 = true :=
  Snake9.LocalRup.prove_clause [c2490, c1202, c1227, c1218, c2492, c1209, c2489, c212, c1210, c1947, c287, c249, c1239, c1253, c1248, c1261, c1277] c2493 (by decide) p (sat_cons (step2490 p h) (sat_cons (step1202 p h) (sat_cons (step1227 p h) (sat_cons (step1218 p h) (sat_cons (step2492 p h) (sat_cons (step1209 p h) (sat_cons (step2489 p h) (sat_cons (step212 p h) (sat_cons (step1210 p h) (sat_cons (step1947 p h) (sat_cons (step287 p h) (sat_cons (step249 p h) (sat_cons (step1239 p h) (sat_cons (step1253 p h) (sat_cons (step1248 p h) (sat_cons (step1261 p h) (sat_cons (step1277 p h) (sat_nil p))))))))))))))))))
def c2494 : List Lit := [(38, true), (43, false), (39, true), (1500, false), (1515, true), (45, true), (15, true), (47, false), (33, false), (1475, true), (1489, true), (21, false), (50, true), (51, false)]
theorem step2494 (p : Nat → Bool) (h : Constraints p) : clause p c2494 = true :=
  Snake9.LocalRup.prove_clause [c1202, c1227, c1218, c1109, c2095, c1208, c1209, c2489, c1215, c2212, c2198, c1210, c1231, c1098, c1111, c1203, c1205, c1101, c1857, c2440, c1126, c254, c1115, c1936, c1107, c1201, c10, c1941, c1911, c223] c2494 (by decide) p (sat_cons (step1202 p h) (sat_cons (step1227 p h) (sat_cons (step1218 p h) (sat_cons (step1109 p h) (sat_cons (step2095 p h) (sat_cons (step1208 p h) (sat_cons (step1209 p h) (sat_cons (step2489 p h) (sat_cons (step1215 p h) (sat_cons (step2212 p h) (sat_cons (step2198 p h) (sat_cons (step1210 p h) (sat_cons (step1231 p h) (sat_cons (step1098 p h) (sat_cons (step1111 p h) (sat_cons (step1203 p h) (sat_cons (step1205 p h) (sat_cons (step1101 p h) (sat_cons (step1857 p h) (sat_cons (step2440 p h) (sat_cons (step1126 p h) (sat_cons (step254 p h) (sat_cons (step1115 p h) (sat_cons (step1936 p h) (sat_cons (step1107 p h) (sat_cons (step1201 p h) (sat_cons (step10 p h) (sat_cons (step1941 p h) (sat_cons (step1911 p h) (sat_cons (step223 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2495 : List Lit := [(13, false), (9, true), (32, false), (1448, false), (33, false), (1475, true), (1456, true), (21, false), (50, true)]
theorem step2495 (p : Nat → Bool) (h : Constraints p) : clause p c2495 = true :=
  Snake9.LocalRup.prove_clause [c1857, c2440] c2495 (by decide) p (sat_cons (step1857 p h) (sat_cons (step2440 p h) (sat_nil p)))
def c2496 : List Lit := [(1691, true), (102, false), (55, true), (103, false)]
theorem step2496 (p : Nat → Bool) (h : Constraints p) : clause p c2496 = true :=
  Snake9.LocalRup.prove_clause [c2285, c2035, c2034, c1729, c1497, c1505, c2331, c1599, c1604, c2467, c677, c676, c1512, c1500, c1519, c1506, c1535] c2496 (by decide) p (sat_cons (step2285 p h) (sat_cons (step2035 p h) (sat_cons (step2034 p h) (sat_cons (step1729 p h) (sat_cons (step1497 p h) (sat_cons (step1505 p h) (sat_cons (step2331 p h) (sat_cons (step1599 p h) (sat_cons (step1604 p h) (sat_cons (step2467 p h) (sat_cons (step677 p h) (sat_cons (step676 p h) (sat_cons (step1512 p h) (sat_cons (step1500 p h) (sat_cons (step1519 p h) (sat_cons (step1506 p h) (sat_cons (step1535 p h) (sat_nil p))))))))))))))))))
def c2497 : List Lit := [(38, true), (42, false), (1515, true), (45, true), (15, true), (47, false), (54, true), (33, false), (1475, true), (1489, true), (21, false), (50, true), (51, false)]
theorem step2497 (p : Nat → Bool) (h : Constraints p) : clause p c2497 = true :=
  Snake9.LocalRup.prove_clause [c2490, c1202, c1227, c1218, c1209, c212, c1947, c2494] c2497 (by decide) p (sat_cons (step2490 p h) (sat_cons (step1202 p h) (sat_cons (step1227 p h) (sat_cons (step1218 p h) (sat_cons (step1209 p h) (sat_cons (step212 p h) (sat_cons (step1947 p h) (sat_cons (step2494 p h) (sat_nil p)))))))))
def c2498 : List Lit := [(1515, true), (38, true), (45, true), (15, true), (47, false), (54, true), (33, false), (1475, true), (1489, true), (21, false), (50, true), (51, false)]
theorem step2498 (p : Nat → Bool) (h : Constraints p) : clause p c2498 = true :=
  Snake9.LocalRup.prove_clause [c2489, c2497, c1211] c2498 (by decide) p (sat_cons (step2489 p h) (sat_cons (step2497 p h) (sat_cons (step1211 p h) (sat_nil p))))
def c2499 : List Lit := [(109, true), (120, false), (1681, true), (102, false)]
theorem step2499 (p : Nat → Bool) (h : Constraints p) : clause p c2499 = true :=
  Snake9.LocalRup.prove_clause [c1550, c2282, c1552] c2499 (by decide) p (sat_cons (step1550 p h) (sat_cons (step2282 p h) (sat_cons (step1552 p h) (sat_nil p))))
def c2500 : List Lit := [(38, true), (1515, true), (1538, true), (55, true), (54, true), (50, true), (53, false), (51, false)]
theorem step2500 (p : Nat → Bool) (h : Constraints p) : clause p c2500 = true :=
  Snake9.LocalRup.prove_clause [c1965, c1208, c2489, c1215, c1210, c1211, c1876, c1231, c2493, c1202, c1203, c1242, c1227, c1964, c1218, c270, c263, c1209, c1201, c212, c1936] c2500 (by decide) p (sat_cons (step1965 p h) (sat_cons (step1208 p h) (sat_cons (step2489 p h) (sat_cons (step1215 p h) (sat_cons (step1210 p h) (sat_cons (step1211 p h) (sat_cons (step1876 p h) (sat_cons (step1231 p h) (sat_cons (step2493 p h) (sat_cons (step1202 p h) (sat_cons (step1203 p h) (sat_cons (step1242 p h) (sat_cons (step1227 p h) (sat_cons (step1964 p h) (sat_cons (step1218 p h) (sat_cons (step270 p h) (sat_cons (step263 p h) (sat_cons (step1209 p h) (sat_cons (step1201 p h) (sat_cons (step212 p h) (sat_cons (step1936 p h) (sat_nil p))))))))))))))))))))))
def c2501 : List Lit := [(38, false), (1618, true), (1681, true), (21, false)]
theorem step2501 (p : Nat → Bool) (h : Constraints p) : clause p c2501 = true :=
  Snake9.LocalRup.prove_clause [c1845, c1420, c1445, c1432, c1773, c2166, c1449, c1550, c1421, c1827] c2501 (by decide) p (sat_cons (step1845 p h) (sat_cons (step1420 p h) (sat_cons (step1445 p h) (sat_cons (step1432 p h) (sat_cons (step1773 p h) (sat_cons (step2166 p h) (sat_cons (step1449 p h) (sat_cons (step1550 p h) (sat_cons (step1421 p h) (sat_cons (step1827 p h) (sat_nil p)))))))))))
end B112E004
