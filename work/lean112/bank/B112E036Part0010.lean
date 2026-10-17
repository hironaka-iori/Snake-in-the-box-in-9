import B112E036Part0009
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2285 : List Lit := [(1779, false), (1773, false), (1789, true), (108, false), (106, false)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1392, c1420, c1408, c1409, c1424, c1403, c1395, c661, c1387] c2285 (by decide) p (sat_cons (step1392 p h) (sat_cons (step1420 p h) (sat_cons (step1408 p h) (sat_cons (step1409 p h) (sat_cons (step1424 p h) (sat_cons (step1403 p h) (sat_cons (step1395 p h) (sat_cons (step661 p h) (sat_cons (step1387 p h) (sat_nil p))))))))))
def c2286 : List Lit := [(109, false), (103, false), (1749, true), (1772, true), (108, false), (106, false), (95, true)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c658, c661, c1326, c1388, c1328, c1921, c459, c458, c1347, c1336, c1338] c2286 (by decide) p (sat_cons (step658 p h) (sat_cons (step661 p h) (sat_cons (step1326 p h) (sat_cons (step1388 p h) (sat_cons (step1328 p h) (sat_cons (step1921 p h) (sat_cons (step459 p h) (sat_cons (step458 p h) (sat_cons (step1347 p h) (sat_cons (step1336 p h) (sat_cons (step1338 p h) (sat_nil p))))))))))))
def c2287 : List Lit := [(109, true), (1779, false), (1744, true), (1789, true)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1403, c2129, c1409, c1334, c1336, c1420, c1340, c1394, c1333, c2280] c2287 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1403 p h) (sat_cons (step2129 p h) (sat_cons (step1409 p h) (sat_cons (step1334 p h) (sat_cons (step1336 p h) (sat_cons (step1420 p h) (sat_cons (step1340 p h) (sat_cons (step1394 p h) (sat_cons (step1333 p h) (sat_cons (step2280 p h) (sat_nil p))))))))))))
def c2288 : List Lit := [(1771, false), (101, true), (109, false), (72, false), (1777, true), (1807, false), (105, false), (1829, true), (1800, false)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c2279, c1396, c1499, c1391, c1483, c489, c678, c1467, c1928, c1452, c627] c2288 (by decide) p (sat_cons (step2279 p h) (sat_cons (step1396 p h) (sat_cons (step1499 p h) (sat_cons (step1391 p h) (sat_cons (step1483 p h) (sat_cons (step489 p h) (sat_cons (step678 p h) (sat_cons (step1467 p h) (sat_cons (step1928 p h) (sat_cons (step1452 p h) (sat_cons (step627 p h) (sat_nil p))))))))))))
def c2289 : List Lit := [(1771, true), (1745, true), (103, false), (95, true)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c1386, c2060, c1921, c459, c458, c1333, c1336, c1341] c2289 (by decide) p (sat_cons (step1386 p h) (sat_cons (step2060 p h) (sat_cons (step1921 p h) (sat_cons (step459 p h) (sat_cons (step458 p h) (sat_cons (step1333 p h) (sat_cons (step1336 p h) (sat_cons (step1341 p h) (sat_nil p)))))))))
def c2290 : List Lit := [(1817, true), (1773, false), (1790, true), (1800, false), (95, true)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c2267, c1482, c1736, c1466, c1452] c2290 (by decide) p (sat_cons (step2267 p h) (sat_cons (step1482 p h) (sat_cons (step1736 p h) (sat_cons (step1466 p h) (sat_cons (step1452 p h) (sat_nil p))))))
def c2291 : List Lit := [(32, true), (36, false), (55, false), (1629, true), (1613, false)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c1145, c1116, c1105, c1106, c1113, c152, c1142, c1121, c1124] c2291 (by decide) p (sat_cons (step1145 p h) (sat_cons (step1116 p h) (sat_cons (step1105 p h) (sat_cons (step1106 p h) (sat_cons (step1113 p h) (sat_cons (step152 p h) (sat_cons (step1142 p h) (sat_cons (step1121 p h) (sat_cons (step1124 p h) (sat_nil p))))))))))
def c2292 : List Lit := [(1735, false), (1742, false), (1750, true), (1816, false), (95, false), (1849, true), (1724, false)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1347, c1348, c1362, c1341, c1553, c1333, c1497, c2279, c1386, c2278, c1623] c2292 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1347 p h) (sat_cons (step1348 p h) (sat_cons (step1362 p h) (sat_cons (step1341 p h) (sat_cons (step1553 p h) (sat_cons (step1333 p h) (sat_cons (step1497 p h) (sat_cons (step2279 p h) (sat_cons (step1386 p h) (sat_cons (step2278 p h) (sat_cons (step1623 p h) (sat_nil p)))))))))))))
def c2293 : List Lit := [(1742, false), (1750, true), (1816, false), (95, false), (1849, true), (1724, false)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1343, c1361, c1547, c1505, c2292, c1328, c1330, c1781, c1325, c1326, c1322, c1760, c1389, c404, c1392, c1906, c1902, c1420, c391, c1738, c1401, c1409] c2293 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1343 p h) (sat_cons (step1361 p h) (sat_cons (step1547 p h) (sat_cons (step1505 p h) (sat_cons (step2292 p h) (sat_cons (step1328 p h) (sat_cons (step1330 p h) (sat_cons (step1781 p h) (sat_cons (step1325 p h) (sat_cons (step1326 p h) (sat_cons (step1322 p h) (sat_cons (step1760 p h) (sat_cons (step1389 p h) (sat_cons (step404 p h) (sat_cons (step1392 p h) (sat_cons (step1906 p h) (sat_cons (step1902 p h) (sat_cons (step1420 p h) (sat_cons (step391 p h) (sat_cons (step1738 p h) (sat_cons (step1401 p h) (sat_cons (step1409 p h) (sat_nil p))))))))))))))))))))))))
def c2294 : List Lit := [(93, false), (1629, true), (46, false), (38, true), (64, false)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c1145, c1107, c2174, c1118, c209, c1109, c1111, c1114, c1142, c1104, c1124, c2183] c2294 (by decide) p (sat_cons (step1145 p h) (sat_cons (step1107 p h) (sat_cons (step2174 p h) (sat_cons (step1118 p h) (sat_cons (step209 p h) (sat_cons (step1109 p h) (sat_cons (step1111 p h) (sat_cons (step1114 p h) (sat_cons (step1142 p h) (sat_cons (step1104 p h) (sat_cons (step1124 p h) (sat_cons (step2183 p h) (sat_nil p)))))))))))))
def c2295 : List Lit := [(1810, true), (1790, true)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1466, c1724, c1452, c1389, c1736] c2295 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1466 p h) (sat_cons (step1724 p h) (sat_cons (step1452 p h) (sat_cons (step1389 p h) (sat_cons (step1736 p h) (sat_nil p)))))))
def c2296 : List Lit := [(1807, true), (1773, false), (1790, true), (66, true)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c1458, c1460, c2033, c1455, c1456, c1401, c767, c1705, c1961] c2296 (by decide) p (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step2033 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step1401 p h) (sat_cons (step767 p h) (sat_cons (step1705 p h) (sat_cons (step1961 p h) (sat_nil p))))))))))
def c2297 : List Lit := [(1771, false), (109, false), (101, true), (105, false), (1807, false), (1800, false), (1720, true), (1829, true)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1512, c2295, c1482, c1506, c1428, c1396, c2288, c1391, c1295, c2086, c1303, c557, c1298] c2297 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1512 p h) (sat_cons (step2295 p h) (sat_cons (step1482 p h) (sat_cons (step1506 p h) (sat_cons (step1428 p h) (sat_cons (step1396 p h) (sat_cons (step2288 p h) (sat_cons (step1391 p h) (sat_cons (step1295 p h) (sat_cons (step2086 p h) (sat_cons (step1303 p h) (sat_cons (step557 p h) (sat_cons (step1298 p h) (sat_nil p)))))))))))))))
def c2298 : List Lit := [(1771, true), (1744, true), (103, false)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c1771, c2060, c1340, c1333] c2298 (by decide) p (sat_cons (step1771 p h) (sat_cons (step2060 p h) (sat_cons (step1340 p h) (sat_cons (step1333 p h) (sat_nil p)))))
def c2299 : List Lit := [(1771, true), (115, false), (95, false)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1387, c534] c2299 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step534 p h) (sat_nil p))))
def c2300 : List Lit := [(73, true), (1725, true), (1707, false)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c1288, c1311, c1305, c1294, c1296, c2275, c1303, c1297, c1298, c1896, c376] c2300 (by decide) p (sat_cons (step1288 p h) (sat_cons (step1311 p h) (sat_cons (step1305 p h) (sat_cons (step1294 p h) (sat_cons (step1296 p h) (sat_cons (step2275 p h) (sat_cons (step1303 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step1896 p h) (sat_cons (step376 p h) (sat_nil p))))))))))))
def c2301 : List Lit := [(100, true), (1783, false), (1772, false), (1829, true), (1799, false)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1517, c1434, c1399, c1390, c1391, c1398, c1724, c1429, c1477, c1512] c2301 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1517 p h) (sat_cons (step1434 p h) (sat_cons (step1399 p h) (sat_cons (step1390 p h) (sat_cons (step1391 p h) (sat_cons (step1398 p h) (sat_cons (step1724 p h) (sat_cons (step1429 p h) (sat_cons (step1477 p h) (sat_cons (step1512 p h) (sat_nil p))))))))))))
def c2302 : List Lit := [(1773, true), (1771, false), (1725, false), (1849, true), (117, true)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c2279, c1394, c1441, c1444, c1389, c1390, c1732, c1724, c1781, c1477, c1345, c1497, c1366, c1553, c1547, c1367, c1505, c1498, c1346, c1420, c1424, c1482, c1339, c2030, c1397, c2044, c1333, c2069] c2302 (by decide) p (sat_cons (step2279 p h) (sat_cons (step1394 p h) (sat_cons (step1441 p h) (sat_cons (step1444 p h) (sat_cons (step1389 p h) (sat_cons (step1390 p h) (sat_cons (step1732 p h) (sat_cons (step1724 p h) (sat_cons (step1781 p h) (sat_cons (step1477 p h) (sat_cons (step1345 p h) (sat_cons (step1497 p h) (sat_cons (step1366 p h) (sat_cons (step1553 p h) (sat_cons (step1547 p h) (sat_cons (step1367 p h) (sat_cons (step1505 p h) (sat_cons (step1498 p h) (sat_cons (step1346 p h) (sat_cons (step1420 p h) (sat_cons (step1424 p h) (sat_cons (step1482 p h) (sat_cons (step1339 p h) (sat_cons (step2030 p h) (sat_cons (step1397 p h) (sat_cons (step2044 p h) (sat_cons (step1333 p h) (sat_cons (step2069 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2303 : List Lit := [(101, false), (1783, true), (1748, true)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1401, c1400, c1406, c1403, c1781, c636, c624, c1346, c1929, c1337, c1334, c1335, c493] c2303 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1401 p h) (sat_cons (step1400 p h) (sat_cons (step1406 p h) (sat_cons (step1403 p h) (sat_cons (step1781 p h) (sat_cons (step636 p h) (sat_cons (step624 p h) (sat_cons (step1346 p h) (sat_cons (step1929 p h) (sat_cons (step1337 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step493 p h) (sat_nil p)))))))))))))))
def c2304 : List Lit := [(1810, true), (66, true)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1466, c1458, c1460, c1452, c1455, c1456, c738, c767, c1960] c2304 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1466 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1452 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step738 p h) (sat_cons (step767 p h) (sat_cons (step1960 p h) (sat_nil p)))))))))))
def c2305 : List Lit := [(1817, true), (1771, true), (1807, false)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c2267, c2032, c2299] c2305 (by decide) p (sat_cons (step2267 p h) (sat_cons (step2032 p h) (sat_cons (step2299 p h) (sat_nil p))))
def c2306 : List Lit := [(1849, true), (1773, true), (1725, false), (100, false), (1826, false), (117, true)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c1389, c1781, c1560, c2302, c1368, c1771, c2076, c1347, c1333, c1340] c2306 (by decide) p (sat_cons (step1389 p h) (sat_cons (step1781 p h) (sat_cons (step1560 p h) (sat_cons (step2302 p h) (sat_cons (step1368 p h) (sat_cons (step1771 p h) (sat_cons (step2076 p h) (sat_cons (step1347 p h) (sat_cons (step1333 p h) (sat_cons (step1340 p h) (sat_nil p)))))))))))
def c2307 : List Lit := [(101, false), (32, false), (1624, true), (35, true), (46, false), (34, true), (70, false)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c427, c1825, c1822, c181, c189, c1118, c1122, c1127] c2307 (by decide) p (sat_cons (step427 p h) (sat_cons (step1825 p h) (sat_cons (step1822 p h) (sat_cons (step181 p h) (sat_cons (step189 p h) (sat_cons (step1118 p h) (sat_cons (step1122 p h) (sat_cons (step1127 p h) (sat_nil p)))))))))
def c2308 : List Lit := [(41, false), (1629, true), (46, false), (38, true), (64, false)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c1145, c209, c1109, c1111, c1114, c1142, c1104, c1105, c2107, c100] c2308 (by decide) p (sat_cons (step1145 p h) (sat_cons (step209 p h) (sat_cons (step1109 p h) (sat_cons (step1111 p h) (sat_cons (step1114 p h) (sat_cons (step1142 p h) (sat_cons (step1104 p h) (sat_cons (step1105 p h) (sat_cons (step2107 p h) (sat_cons (step100 p h) (sat_nil p)))))))))))
def c2309 : List Lit := [(1783, false), (1789, true), (1828, true), (1807, false), (1773, false)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c1392, c1419, c1498, c1424, c2305, c1395] c2309 (by decide) p (sat_cons (step1392 p h) (sat_cons (step1419 p h) (sat_cons (step1498 p h) (sat_cons (step1424 p h) (sat_cons (step2305 p h) (sat_cons (step1395 p h) (sat_nil p)))))))
def c2310 : List Lit := [(1671, false), (1693, true)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c2088, c1245] c2310 (by decide) p (sat_cons (step2088 p h) (sat_cons (step1245 p h) (sat_nil p)))
def c2311 : List Lit := [(1849, true), (1829, false)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c2262, c1542] c2311 (by decide) p (sat_cons (step2262 p h) (sat_cons (step1542 p h) (sat_nil p)))
def c2312 : List Lit := [(1850, true), (1830, false)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c2262, c1543] c2312 (by decide) p (sat_cons (step2262 p h) (sat_cons (step1543 p h) (sat_nil p)))
def c2313 : List Lit := [(1851, true), (1831, false)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c2262, c1544] c2313 (by decide) p (sat_cons (step2262 p h) (sat_cons (step1544 p h) (sat_nil p)))
def c2314 : List Lit := [(1832, false), (1852, true)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c2262, c1545] c2314 (by decide) p (sat_cons (step2262 p h) (sat_cons (step1545 p h) (sat_nil p)))
def c2315 : List Lit := [(1833, false), (1853, true)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c2262, c1546] c2315 (by decide) p (sat_cons (step2262 p h) (sat_cons (step1546 p h) (sat_nil p)))
def c2316 : List Lit := [(1771, true), (73, false), (100, false)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1387, c571, c521, c1919] c2316 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step571 p h) (sat_cons (step521 p h) (sat_cons (step1919 p h) (sat_nil p))))))
def c2317 : List Lit := [(1800, true), (73, false), (1742, true), (95, false), (100, false), (1829, true), (1807, false), (117, true)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1444, c1445, c1447, c1443, c1438, c525, c523, c526, c1730, c1388, c1404, c728, c1397, c1406, c1453, c1424, c1467, c1506, c1478] c2317 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1444 p h) (sat_cons (step1445 p h) (sat_cons (step1447 p h) (sat_cons (step1443 p h) (sat_cons (step1438 p h) (sat_cons (step525 p h) (sat_cons (step523 p h) (sat_cons (step526 p h) (sat_cons (step1730 p h) (sat_cons (step1388 p h) (sat_cons (step1404 p h) (sat_cons (step728 p h) (sat_cons (step1397 p h) (sat_cons (step1406 p h) (sat_cons (step1453 p h) (sat_cons (step1424 p h) (sat_cons (step1467 p h) (sat_cons (step1506 p h) (sat_cons (step1478 p h) (sat_nil p)))))))))))))))))))))
def c2318 : List Lit := [(1789, true), (1748, true), (1771, false), (100, true)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c1390, c1395, c1428, c1424, c1396, c2303, c1391] c2318 (by decide) p (sat_cons (step1390 p h) (sat_cons (step1395 p h) (sat_cons (step1428 p h) (sat_cons (step1424 p h) (sat_cons (step1396 p h) (sat_cons (step2303 p h) (sat_cons (step1391 p h) (sat_nil p))))))))
def c2319 : List Lit := [(115, false), (73, false), (95, false), (100, true), (1829, true), (1799, false)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c526, c525, c523, c1404, c1388, c1406, c2301] c2319 (by decide) p (sat_cons (step526 p h) (sat_cons (step525 p h) (sat_cons (step523 p h) (sat_cons (step1404 p h) (sat_cons (step1388 p h) (sat_cons (step1406 p h) (sat_cons (step2301 p h) (sat_nil p))))))))
def c2320 : List Lit := [(1810, true), (67, false), (64, false)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c1463, c2304, c1458, c327, c1456] c2320 (by decide) p (sat_cons (step1463 p h) (sat_cons (step2304 p h) (sat_cons (step1458 p h) (sat_cons (step327 p h) (sat_cons (step1456 p h) (sat_nil p))))))
def c2321 : List Lit := [(1807, true), (1773, false), (1829, true), (73, false), (95, false), (67, false), (64, false)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c2320, c1473, c1517, c1458, c1460, c2033, c1455, c1456, c1401, c767, c327, c1961, c2296, c1708, c1512, c525, c1477, c1442, c1444] c2321 (by decide) p (sat_cons (step2320 p h) (sat_cons (step1473 p h) (sat_cons (step1517 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step2033 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step1401 p h) (sat_cons (step767 p h) (sat_cons (step327 p h) (sat_cons (step1961 p h) (sat_cons (step2296 p h) (sat_cons (step1708 p h) (sat_cons (step1512 p h) (sat_cons (step525 p h) (sat_cons (step1477 p h) (sat_cons (step1442 p h) (sat_cons (step1444 p h) (sat_nil p))))))))))))))))))))
def c2322 : List Lit := [(1817, false), (1771, false), (100, true), (1849, true), (1724, false)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c2279, c2311, c1506, c1498, c2318, c1547, c1361] c2322 (by decide) p (sat_cons (step2279 p h) (sat_cons (step2311 p h) (sat_cons (step1506 p h) (sat_cons (step1498 p h) (sat_cons (step2318 p h) (sat_cons (step1547 p h) (sat_cons (step1361 p h) (sat_nil p))))))))
def c2323 : List Lit := [(115, false), (98, true), (1829, true), (100, true), (1807, false), (73, false), (95, false), (1810, false)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c1473, c1517, c1390, c526, c523, c2319, c1404, c1388, c1444, c1446, c1406, c1398, c1441, c1438, c1439, c1434, c1429, c710, c1399, c1512, c1391, c1474, c2244, c1784, c1953] c2323 (by decide) p (sat_cons (step1473 p h) (sat_cons (step1517 p h) (sat_cons (step1390 p h) (sat_cons (step526 p h) (sat_cons (step523 p h) (sat_cons (step2319 p h) (sat_cons (step1404 p h) (sat_cons (step1388 p h) (sat_cons (step1444 p h) (sat_cons (step1446 p h) (sat_cons (step1406 p h) (sat_cons (step1398 p h) (sat_cons (step1441 p h) (sat_cons (step1438 p h) (sat_cons (step1439 p h) (sat_cons (step1434 p h) (sat_cons (step1429 p h) (sat_cons (step710 p h) (sat_cons (step1399 p h) (sat_cons (step1512 p h) (sat_cons (step1391 p h) (sat_cons (step1474 p h) (sat_cons (step2244 p h) (sat_cons (step1784 p h) (sat_cons (step1953 p h) (sat_nil p))))))))))))))))))))))))))
def c2324 : List Lit := [(98, true), (1829, true), (100, true), (1807, false), (73, false), (95, false), (1810, false)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c1390, c1386, c1395, c2323, c2032, c1506, c1428, c1424, c1398, c1406, c1388, c1404, c522] c2324 (by decide) p (sat_cons (step1390 p h) (sat_cons (step1386 p h) (sat_cons (step1395 p h) (sat_cons (step2323 p h) (sat_cons (step2032 p h) (sat_cons (step1506 p h) (sat_cons (step1428 p h) (sat_cons (step1424 p h) (sat_cons (step1398 p h) (sat_cons (step1406 p h) (sat_cons (step1388 p h) (sat_cons (step1404 p h) (sat_cons (step522 p h) (sat_nil p))))))))))))))
def c2325 : List Lit := [(1829, true), (100, true), (1807, false), (73, false), (95, false), (1810, false)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c1390, c2324, c525, c524, c521, c2032, c1404, c1387, c1506, c1406, c1395, c1424] c2325 (by decide) p (sat_cons (step1390 p h) (sat_cons (step2324 p h) (sat_cons (step525 p h) (sat_cons (step524 p h) (sat_cons (step521 p h) (sat_cons (step2032 p h) (sat_cons (step1404 p h) (sat_cons (step1387 p h) (sat_cons (step1506 p h) (sat_cons (step1406 p h) (sat_cons (step1395 p h) (sat_cons (step1424 p h) (sat_nil p)))))))))))))
def c2326 : List Lit := [(114, false), (94, false), (105, false), (1742, true)]
theorem step2326 (p : Nat → Bool) (h : Constraints p) : clause p c2326 = true :=
  Snake9.LocalRup.prove_clause [c500, c497, c1336] c2326 (by decide) p (sat_cons (step500 p h) (sat_cons (step497 p h) (sat_cons (step1336 p h) (sat_nil p))))
def c2327 : List Lit := [(1818, true), (105, false), (1798, false), (101, false), (1807, false), (1810, false)]
theorem step2327 (p : Nat → Bool) (h : Constraints p) : clause p c2327 = true :=
  Snake9.LocalRup.prove_clause [c1445, c1487, c1483, c1448, c1467, c1439, c1452, c1698] c2327 (by decide) p (sat_cons (step1445 p h) (sat_cons (step1487 p h) (sat_cons (step1483 p h) (sat_cons (step1448 p h) (sat_cons (step1467 p h) (sat_cons (step1439 p h) (sat_cons (step1452 p h) (sat_cons (step1698 p h) (sat_nil p)))))))))
def c2328 : List Lit := [(1735, true), (109, false), (105, false)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1702, c1323, c621] c2328 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1702 p h) (sat_cons (step1323 p h) (sat_cons (step621 p h) (sat_nil p)))))
def c2329 : List Lit := [(1707, true), (58, false), (67, false)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c1280, c1281, c1872, c329, c328, c1874] c2329 (by decide) p (sat_cons (step1280 p h) (sat_cons (step1281 p h) (sat_cons (step1872 p h) (sat_cons (step329 p h) (sat_cons (step328 p h) (sat_cons (step1874 p h) (sat_nil p)))))))
def c2330 : List Lit := [(68, false), (64, false), (58, false), (67, false)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c329, c328, c1874] c2330 (by decide) p (sat_cons (step329 p h) (sat_cons (step328 p h) (sat_cons (step1874 p h) (sat_nil p))))
def c2331 : List Lit := [(46, true), (47, false), (50, false)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c1851, c1850, c1605] c2331 (by decide) p (sat_cons (step1851 p h) (sat_cons (step1850 p h) (sat_cons (step1605 p h) (sat_nil p))))
def c2332 : List Lit := [(1631, true), (46, false), (38, true), (47, false), (1611, false), (1621, false), (39, true)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c1107, c1113, c1119, c1127, c1147, c1114, c1109, c208, c1120, c1144, c1130] c2332 (by decide) p (sat_cons (step1107 p h) (sat_cons (step1113 p h) (sat_cons (step1119 p h) (sat_cons (step1127 p h) (sat_cons (step1147 p h) (sat_cons (step1114 p h) (sat_cons (step1109 p h) (sat_cons (step208 p h) (sat_cons (step1120 p h) (sat_cons (step1144 p h) (sat_cons (step1130 p h) (sat_nil p))))))))))))
def c2333 : List Lit := [(57, true), (1649, true), (188, true), (61, true)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c1743, c1176, c1171] c2333 (by decide) p (sat_cons (step1743 p h) (sat_cons (step1176 p h) (sat_cons (step1171 p h) (sat_nil p))))
def c2334 : List Lit := [(1552, true), (15, false), (16, false), (1592, true), (4, true), (17, true)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c996, c1007, c1005, c998, c999, c1806, c1807, c51, c1045, c1047, c1058, c1054, c1673, c1070] c2334 (by decide) p (sat_cons (step996 p h) (sat_cons (step1007 p h) (sat_cons (step1005 p h) (sat_cons (step998 p h) (sat_cons (step999 p h) (sat_cons (step1806 p h) (sat_cons (step1807 p h) (sat_cons (step51 p h) (sat_cons (step1045 p h) (sat_cons (step1047 p h) (sat_cons (step1058 p h) (sat_cons (step1054 p h) (sat_cons (step1673 p h) (sat_cons (step1070 p h) (sat_nil p)))))))))))))))
def c2335 : List Lit := [(1601, true), (4, true), (17, true), (50, false)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c996, c1004, c1028, c1694, c1989, c2037, c1079, c1037, c1016, c1013, c1014, c64, c1802, c2334, c1033, c1083, c1716, c1067, c998, c1673, c1008, c1058, c999, c51] c2335 (by decide) p (sat_cons (step996 p h) (sat_cons (step1004 p h) (sat_cons (step1028 p h) (sat_cons (step1694 p h) (sat_cons (step1989 p h) (sat_cons (step2037 p h) (sat_cons (step1079 p h) (sat_cons (step1037 p h) (sat_cons (step1016 p h) (sat_cons (step1013 p h) (sat_cons (step1014 p h) (sat_cons (step64 p h) (sat_cons (step1802 p h) (sat_cons (step2334 p h) (sat_cons (step1033 p h) (sat_cons (step1083 p h) (sat_cons (step1716 p h) (sat_cons (step1067 p h) (sat_cons (step998 p h) (sat_cons (step1673 p h) (sat_cons (step1008 p h) (sat_cons (step1058 p h) (sat_cons (step999 p h) (sat_cons (step51 p h) (sat_nil p)))))))))))))))))))))))))
def c2336 : List Lit := [(73, false), (1829, true), (100, true), (1807, false), (74, true), (6, true)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1890, c2325] c2336 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1890 p h) (sat_cons (step2325 p h) (sat_nil p))))
def c2337 : List Lit := [(1631, true), (1625, false), (34, false), (38, false), (1620, false), (32, true), (47, false), (50, false)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c1105, c1112, c1140, c1144, c1131, c1115, c1106, c138, c1123, c227, c1847, c1846, c1598] c2337 (by decide) p (sat_cons (step1105 p h) (sat_cons (step1112 p h) (sat_cons (step1140 p h) (sat_cons (step1144 p h) (sat_cons (step1131 p h) (sat_cons (step1115 p h) (sat_cons (step1106 p h) (sat_cons (step138 p h) (sat_cons (step1123 p h) (sat_cons (step227 p h) (sat_cons (step1847 p h) (sat_cons (step1846 p h) (sat_cons (step1598 p h) (sat_nil p))))))))))))))
def c2338 : List Lit := [(45, false), (47, false), (33, false), (50, false)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c227, c1847, c1846, c1598] c2338 (by decide) p (sat_cons (step227 p h) (sat_cons (step1847 p h) (sat_cons (step1846 p h) (sat_cons (step1598 p h) (sat_nil p)))))
def c2339 : List Lit := [(1771, true), (95, false), (37, false)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1387, c511] c2339 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step511 p h) (sat_nil p))))
def c2340 : List Lit := [(1773, true), (1735, false), (1817, false), (1851, true), (1739, false), (1724, false), (106, true), (98, false), (1775, false)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c1389, c1390, c2030, c1420, c1506, c1555, c1362, c1347, c1340, c1334, c1335, c456, c570, c1920] c2340 (by decide) p (sat_cons (step1389 p h) (sat_cons (step1390 p h) (sat_cons (step2030 p h) (sat_cons (step1420 p h) (sat_cons (step1506 p h) (sat_cons (step1555 p h) (sat_cons (step1362 p h) (sat_cons (step1347 p h) (sat_cons (step1340 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step456 p h) (sat_cons (step570 p h) (sat_cons (step1920 p h) (sat_nil p)))))))))))))))
def c2341 : List Lit := [(1735, false), (1817, false), (1851, true), (1739, false), (1724, false), (106, true), (98, false), (1771, false)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c1339, c1404, c1406, c1394, c1346, c1361, c1549, c1513, c2340, c1395, c1424, c1425, c1506, c1407, c1409, c1555, c1405, c1400, c1401, c1362, c1347, c1340, c1334, c1335, c493, c635, c1929, c1927, c1640] c2341 (by decide) p (sat_cons (step1339 p h) (sat_cons (step1404 p h) (sat_cons (step1406 p h) (sat_cons (step1394 p h) (sat_cons (step1346 p h) (sat_cons (step1361 p h) (sat_cons (step1549 p h) (sat_cons (step1513 p h) (sat_cons (step2340 p h) (sat_cons (step1395 p h) (sat_cons (step1424 p h) (sat_cons (step1425 p h) (sat_cons (step1506 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_cons (step1555 p h) (sat_cons (step1405 p h) (sat_cons (step1400 p h) (sat_cons (step1401 p h) (sat_cons (step1362 p h) (sat_cons (step1347 p h) (sat_cons (step1340 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step493 p h) (sat_cons (step635 p h) (sat_cons (step1929 p h) (sat_cons (step1927 p h) (sat_cons (step1640 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2342 : List Lit := [(1817, false), (1851, true), (1739, false), (1724, false), (106, true), (98, false), (1771, false)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c2313, c1404, c1519, c2341, c1328, c1330, c1781, c1325, c1326, c1322, c1389, c404, c1395, c1906, c1426, c391, c1412, c1401, c1402, c1410, c2328, c1405] c2342 (by decide) p (sat_cons (step2313 p h) (sat_cons (step1404 p h) (sat_cons (step1519 p h) (sat_cons (step2341 p h) (sat_cons (step1328 p h) (sat_cons (step1330 p h) (sat_cons (step1781 p h) (sat_cons (step1325 p h) (sat_cons (step1326 p h) (sat_cons (step1322 p h) (sat_cons (step1389 p h) (sat_cons (step404 p h) (sat_cons (step1395 p h) (sat_cons (step1906 p h) (sat_cons (step1426 p h) (sat_cons (step391 p h) (sat_cons (step1412 p h) (sat_cons (step1401 p h) (sat_cons (step1402 p h) (sat_cons (step1410 p h) (sat_cons (step2328 p h) (sat_cons (step1405 p h) (sat_nil p)))))))))))))))))))))))
def c2343 : List Lit := [(105, false), (1742, true), (80, false), (102, false), (1817, true), (115, true)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c1442, c1444, c1478, c1470, c622, c1452, c1454, c1466, c1482, c1445, c1447, c1443, c1438, c730, c2326, c1943] c2343 (by decide) p (sat_cons (step1442 p h) (sat_cons (step1444 p h) (sat_cons (step1478 p h) (sat_cons (step1470 p h) (sat_cons (step622 p h) (sat_cons (step1452 p h) (sat_cons (step1454 p h) (sat_cons (step1466 p h) (sat_cons (step1482 p h) (sat_cons (step1445 p h) (sat_cons (step1447 p h) (sat_cons (step1443 p h) (sat_cons (step1438 p h) (sat_cons (step730 p h) (sat_cons (step2326 p h) (sat_cons (step1943 p h) (sat_nil p)))))))))))))))))
def c2344 : List Lit := [(1735, true), (1773, false), (1851, true), (98, false), (95, false), (37, false)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c2339, c1395, c515, c514, c504, c2130, c508, c1333, c2342, c2032, c2033, c1401, c1458, c1456, c1442, c1444, c1478, c1476, c2313, c1528, c1328, c1330, c1702, c1781, c1325, c1326, c1322, c1323, c1760, c404, c1902, c660, c1405, c2222, c1426, c1517, c1555, c1362, c1344, c1341, c2343, c1402, c2114, c1413, c1523, c1432, c1481, c1396, c1445, c1447, c1391, c1443, c1438, c1735] c2344 (by decide) p (sat_cons (step2339 p h) (sat_cons (step1395 p h) (sat_cons (step515 p h) (sat_cons (step514 p h) (sat_cons (step504 p h) (sat_cons (step2130 p h) (sat_cons (step508 p h) (sat_cons (step1333 p h) (sat_cons (step2342 p h) (sat_cons (step2032 p h) (sat_cons (step2033 p h) (sat_cons (step1401 p h) (sat_cons (step1458 p h) (sat_cons (step1456 p h) (sat_cons (step1442 p h) (sat_cons (step1444 p h) (sat_cons (step1478 p h) (sat_cons (step1476 p h) (sat_cons (step2313 p h) (sat_cons (step1528 p h) (sat_cons (step1328 p h) (sat_cons (step1330 p h) (sat_cons (step1702 p h) (sat_cons (step1781 p h) (sat_cons (step1325 p h) (sat_cons (step1326 p h) (sat_cons (step1322 p h) (sat_cons (step1323 p h) (sat_cons (step1760 p h) (sat_cons (step404 p h) (sat_cons (step1902 p h) (sat_cons (step660 p h) (sat_cons (step1405 p h) (sat_cons (step2222 p h) (sat_cons (step1426 p h) (sat_cons (step1517 p h) (sat_cons (step1555 p h) (sat_cons (step1362 p h) (sat_cons (step1344 p h) (sat_cons (step1341 p h) (sat_cons (step2343 p h) (sat_cons (step1402 p h) (sat_cons (step2114 p h) (sat_cons (step1413 p h) (sat_cons (step1523 p h) (sat_cons (step1432 p h) (sat_cons (step1481 p h) (sat_cons (step1396 p h) (sat_cons (step1445 p h) (sat_cons (step1447 p h) (sat_cons (step1391 p h) (sat_cons (step1443 p h) (sat_cons (step1438 p h) (sat_cons (step1735 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2345 : List Lit := [(1785, false), (1830, true), (1742, true), (1776, false), (115, true), (1771, false)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c1442, c1444, c1476, c1522, c1426, c1431, c1518, c1396, c1481, c1477, c1445, c1447, c1724, c1443, c1438, c1391, c1735] c2345 (by decide) p (sat_cons (step1442 p h) (sat_cons (step1444 p h) (sat_cons (step1476 p h) (sat_cons (step1522 p h) (sat_cons (step1426 p h) (sat_cons (step1431 p h) (sat_cons (step1518 p h) (sat_cons (step1396 p h) (sat_cons (step1481 p h) (sat_cons (step1477 p h) (sat_cons (step1445 p h) (sat_cons (step1447 p h) (sat_cons (step1724 p h) (sat_cons (step1443 p h) (sat_cons (step1438 p h) (sat_cons (step1391 p h) (sat_cons (step1735 p h) (sat_nil p))))))))))))))))))
def c2346 : List Lit := [(1742, true), (114, false), (117, false), (1851, true), (98, false), (95, false), (37, false)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c515, c2339, c514, c504, c2130, c508, c1333, c2342, c2032, c1458, c1455, c1456, c1460, c767, c1964, c2033, c1401, c1442, c1444, c1478, c1470, c1339, c1404, c1735, c1390, c1395, c2344, c1346, c1361, c1549, c2345, c1412, c1410, c1402, c1405, c2326, c1944, c1943, c749, c730, c1454, c627, c1955] c2346 (by decide) p (sat_cons (step515 p h) (sat_cons (step2339 p h) (sat_cons (step514 p h) (sat_cons (step504 p h) (sat_cons (step2130 p h) (sat_cons (step508 p h) (sat_cons (step1333 p h) (sat_cons (step2342 p h) (sat_cons (step2032 p h) (sat_cons (step1458 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step1460 p h) (sat_cons (step767 p h) (sat_cons (step1964 p h) (sat_cons (step2033 p h) (sat_cons (step1401 p h) (sat_cons (step1442 p h) (sat_cons (step1444 p h) (sat_cons (step1478 p h) (sat_cons (step1470 p h) (sat_cons (step1339 p h) (sat_cons (step1404 p h) (sat_cons (step1735 p h) (sat_cons (step1390 p h) (sat_cons (step1395 p h) (sat_cons (step2344 p h) (sat_cons (step1346 p h) (sat_cons (step1361 p h) (sat_cons (step1549 p h) (sat_cons (step2345 p h) (sat_cons (step1412 p h) (sat_cons (step1410 p h) (sat_cons (step1402 p h) (sat_cons (step1405 p h) (sat_cons (step2326 p h) (sat_cons (step1944 p h) (sat_cons (step1943 p h) (sat_cons (step749 p h) (sat_cons (step730 p h) (sat_cons (step1454 p h) (sat_cons (step627 p h) (sat_cons (step1955 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c2347 : List Lit := [(1773, false), (1745, false), (1851, true), (98, false), (95, false), (37, false)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c514, c1404, c515, c2339, c504, c2130, c508, c1333, c2342, c2032, c2033, c1401, c1409, c1442, c1444, c1476, c1395, c2344, c1425, c1348, c1511, c1363, c1562] c2347 (by decide) p (sat_cons (step514 p h) (sat_cons (step1404 p h) (sat_cons (step515 p h) (sat_cons (step2339 p h) (sat_cons (step504 p h) (sat_cons (step2130 p h) (sat_cons (step508 p h) (sat_cons (step1333 p h) (sat_cons (step2342 p h) (sat_cons (step2032 p h) (sat_cons (step2033 p h) (sat_cons (step1401 p h) (sat_cons (step1409 p h) (sat_cons (step1442 p h) (sat_cons (step1444 p h) (sat_cons (step1476 p h) (sat_cons (step1395 p h) (sat_cons (step2344 p h) (sat_cons (step1425 p h) (sat_cons (step1348 p h) (sat_cons (step1511 p h) (sat_cons (step1363 p h) (sat_cons (step1562 p h) (sat_nil p))))))))))))))))))))))))
def c2348 : List Lit := [(1745, false), (1851, true), (98, false), (95, false), (37, false)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c2339, c1394, c514, c1404, c515, c504, c2130, c508, c1333, c2342, c2032, c2033, c1401, c1409, c1420, c1442, c1444, c2347, c1389, c1724, c1781, c1477, c1348, c1505, c1363, c1562] c2348 (by decide) p (sat_cons (step2339 p h) (sat_cons (step1394 p h) (sat_cons (step514 p h) (sat_cons (step1404 p h) (sat_cons (step515 p h) (sat_cons (step504 p h) (sat_cons (step2130 p h) (sat_cons (step508 p h) (sat_cons (step1333 p h) (sat_cons (step2342 p h) (sat_cons (step2032 p h) (sat_cons (step2033 p h) (sat_cons (step1401 p h) (sat_cons (step1409 p h) (sat_cons (step1420 p h) (sat_cons (step1442 p h) (sat_cons (step1444 p h) (sat_cons (step2347 p h) (sat_cons (step1389 p h) (sat_cons (step1724 p h) (sat_cons (step1781 p h) (sat_cons (step1477 p h) (sat_cons (step1348 p h) (sat_cons (step1505 p h) (sat_cons (step1363 p h) (sat_cons (step1562 p h) (sat_nil p)))))))))))))))))))))))))))
end B112E036
