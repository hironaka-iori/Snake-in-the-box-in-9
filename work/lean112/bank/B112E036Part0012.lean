import B112E036Part0011
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2413 : List Lit := [(1614, false), (39, true), (1631, true), (33, true), (34, true)]
theorem step2413 (p : Nat → Bool) (h : Constraints p) : clause p c2413 = true :=
  Snake9.LocalRup.prove_clause [c1104, c1114, c2383] c2413 (by decide) p (sat_cons (step1104 p h) (sat_cons (step1114 p h) (sat_cons (step2383 p h) (sat_nil p))))
def c2414 : List Lit := [(1659, true), (1636, false), (63, false), (52, true)]
theorem step2414 (p : Nat → Bool) (h : Constraints p) : clause p c2414 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1164, c1873, c1996, c1201, c1165, c2027, c1157, c302] c2414 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1164 p h) (sat_cons (step1873 p h) (sat_cons (step1996 p h) (sat_cons (step1201 p h) (sat_cons (step1165 p h) (sat_cons (step2027 p h) (sat_cons (step1157 p h) (sat_cons (step302 p h) (sat_nil p))))))))))
def c2415 : List Lit := [(1827, true), (73, false)]
theorem step2415 (p : Nat → Bool) (h : Constraints p) : clause p c2415 = true :=
  Snake9.LocalRup.prove_clause [c1510, c2401, c2295, c1389, c1390, c1732, c1473, c2316, c1504, c1394, c2279, c1420, c1424, c2404, c2030, c1397, c1783, c524, c522, c1388] c2415 (by decide) p (sat_cons (step1510 p h) (sat_cons (step2401 p h) (sat_cons (step2295 p h) (sat_cons (step1389 p h) (sat_cons (step1390 p h) (sat_cons (step1732 p h) (sat_cons (step1473 p h) (sat_cons (step2316 p h) (sat_cons (step1504 p h) (sat_cons (step1394 p h) (sat_cons (step2279 p h) (sat_cons (step1420 p h) (sat_cons (step1424 p h) (sat_cons (step2404 p h) (sat_cons (step2030 p h) (sat_cons (step1397 p h) (sat_cons (step1783 p h) (sat_cons (step524 p h) (sat_cons (step522 p h) (sat_cons (step1388 p h) (sat_nil p)))))))))))))))))))))
def c2416 : List Lit := [(1658, true), (67, false), (1708, true), (58, true), (1635, false), (52, true)]
theorem step2416 (p : Nat → Bool) (h : Constraints p) : clause p c2416 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1161, c2150, c1197, c1282, c2019, c2120, c312, c324, c1880] c2416 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1161 p h) (sat_cons (step2150 p h) (sat_cons (step1197 p h) (sat_cons (step1282 p h) (sat_cons (step2019 p h) (sat_cons (step2120 p h) (sat_cons (step312 p h) (sat_cons (step324 p h) (sat_cons (step1880 p h) (sat_nil p)))))))))))
def c2417 : List Lit := [(56, false), (67, false), (64, false), (23, false), (7, false), (58, true)]
theorem step2417 (p : Nat → Bool) (h : Constraints p) : clause p c2417 = true :=
  Snake9.LocalRup.prove_clause [c77, c2353] c2417 (by decide) p (sat_cons (step77 p h) (sat_cons (step2353 p h) (sat_nil p)))
def c2418 : List Lit := [(1748, true), (1828, true), (117, false), (1830, true), (1735, false)]
theorem step2418 (p : Nat → Bool) (h : Constraints p) : clause p c2418 = true :=
  Snake9.LocalRup.prove_clause [c1346, c1337, c1339, c1740, c1334, c1335, c1333, c2403, c2406] c2418 (by decide) p (sat_cons (step1346 p h) (sat_cons (step1337 p h) (sat_cons (step1339 p h) (sat_cons (step1740 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step1333 p h) (sat_cons (step2403 p h) (sat_cons (step2406 p h) (sat_nil p))))))))))
def c2419 : List Lit := [(1827, false), (1849, true), (1725, false), (1830, true), (1735, false)]
theorem step2419 (p : Nat → Bool) (h : Constraints p) : clause p c2419 = true :=
  Snake9.LocalRup.prove_clause [c1345, c1366, c1547, c1553, c1367, c1346, c2418, c1740, c1441, c2279, c2402] c2419 (by decide) p (sat_cons (step1345 p h) (sat_cons (step1366 p h) (sat_cons (step1547 p h) (sat_cons (step1553 p h) (sat_cons (step1367 p h) (sat_cons (step1346 p h) (sat_cons (step2418 p h) (sat_cons (step1740 p h) (sat_cons (step1441 p h) (sat_cons (step2279 p h) (sat_cons (step2402 p h) (sat_nil p))))))))))))
def c2420 : List Lit := [(1658, true), (1712, true), (58, true), (1635, false), (52, true)]
theorem step2420 (p : Nat → Bool) (h : Constraints p) : clause p c2420 = true :=
  Snake9.LocalRup.prove_clause [c1291, c2150, c2416, c1281, c1284, c1289] c2420 (by decide) p (sat_cons (step1291 p h) (sat_cons (step2150 p h) (sat_cons (step2416 p h) (sat_cons (step1281 p h) (sat_cons (step1284 p h) (sat_cons (step1289 p h) (sat_nil p)))))))
def c2421 : List Lit := [(1799, true), (37, false), (73, false)]
theorem step2421 (p : Nat → Bool) (h : Constraints p) : clause p c2421 = true :=
  Snake9.LocalRup.prove_clause [c1444, c1783, c1442, c506] c2421 (by decide) p (sat_cons (step1444 p h) (sat_cons (step1783 p h) (sat_cons (step1442 p h) (sat_cons (step506 p h) (sat_nil p)))))
def c2422 : List Lit := [(18, true), (1558, true), (15, true), (4, false)]
theorem step2422 (p : Nat → Bool) (h : Constraints p) : clause p c2422 = true :=
  Snake9.LocalRup.prove_clause [c2115, c1802, c1015] c2422 (by decide) p (sat_cons (step2115 p h) (sat_cons (step1802 p h) (sat_cons (step1015 p h) (sat_nil p))))
def c2423 : List Lit := [(1849, true), (1725, false), (1735, false), (1830, true)]
theorem step2423 (p : Nat → Bool) (h : Constraints p) : clause p c2423 = true :=
  Snake9.LocalRup.prove_clause [c2419, c1510, c2410, c2401, c2295, c1482, c1389, c1390, c1732, c1757, c1560, c2306, c1368, c1347, c1338, c1735, c1438, c1446, c1447, c1478, c1728, c1784] c2423 (by decide) p (sat_cons (step2419 p h) (sat_cons (step1510 p h) (sat_cons (step2410 p h) (sat_cons (step2401 p h) (sat_cons (step2295 p h) (sat_cons (step1482 p h) (sat_cons (step1389 p h) (sat_cons (step1390 p h) (sat_cons (step1732 p h) (sat_cons (step1757 p h) (sat_cons (step1560 p h) (sat_cons (step2306 p h) (sat_cons (step1368 p h) (sat_cons (step1347 p h) (sat_cons (step1338 p h) (sat_cons (step1735 p h) (sat_cons (step1438 p h) (sat_cons (step1446 p h) (sat_cons (step1447 p h) (sat_cons (step1478 p h) (sat_cons (step1728 p h) (sat_cons (step1784 p h) (sat_nil p)))))))))))))))))))))))
def c2424 : List Lit := [(13, false), (5, true), (11, false), (4, false)]
theorem step2424 (p : Nat → Bool) (h : Constraints p) : clause p c2424 = true :=
  Snake9.LocalRup.prove_clause [c1801, c42] c2424 (by decide) p (sat_cons (step1801 p h) (sat_cons (step42 p h) (sat_nil p)))
def c2425 : List Lit := [(1636, false), (1624, false), (1670, true), (4, false), (35, false), (52, true)]
theorem step2425 (p : Nat → Bool) (h : Constraints p) : clause p c2425 = true :=
  Snake9.LocalRup.prove_clause [c1133, c1218, c1996, c1156, c1164, c1165, c1995, c1157, c1223, c143, c1138, c1105, c1112] c2425 (by decide) p (sat_cons (step1133 p h) (sat_cons (step1218 p h) (sat_cons (step1996 p h) (sat_cons (step1156 p h) (sat_cons (step1164 p h) (sat_cons (step1165 p h) (sat_cons (step1995 p h) (sat_cons (step1157 p h) (sat_cons (step1223 p h) (sat_cons (step143 p h) (sat_cons (step1138 p h) (sat_cons (step1105 p h) (sat_cons (step1112 p h) (sat_nil p))))))))))))))
def c2426 : List Lit := [(1623, false), (1670, true), (1641, false), (1611, false), (58, false)]
theorem step2426 (p : Nat → Bool) (h : Constraints p) : clause p c2426 = true :=
  Snake9.LocalRup.prove_clause [c1995, c1223, c1112, c1137, c1142, c1218, c1113, c1201, c1107, c2373] c2426 (by decide) p (sat_cons (step1995 p h) (sat_cons (step1223 p h) (sat_cons (step1112 p h) (sat_cons (step1137 p h) (sat_cons (step1142 p h) (sat_cons (step1218 p h) (sat_cons (step1113 p h) (sat_cons (step1201 p h) (sat_cons (step1107 p h) (sat_cons (step2373 p h) (sat_nil p)))))))))))
def c2427 : List Lit := [(1670, true), (37, true), (1641, false), (1611, false), (58, false)]
theorem step2427 (p : Nat → Bool) (h : Constraints p) : clause p c2427 = true :=
  Snake9.LocalRup.prove_clause [c1108, c1113, c1141, c1995, c1223, c1218, c1145, c1201, c1114, c2373, c1109] c2427 (by decide) p (sat_cons (step1108 p h) (sat_cons (step1113 p h) (sat_cons (step1141 p h) (sat_cons (step1995 p h) (sat_cons (step1223 p h) (sat_cons (step1218 p h) (sat_cons (step1145 p h) (sat_cons (step1201 p h) (sat_cons (step1114 p h) (sat_cons (step2373 p h) (sat_cons (step1109 p h) (sat_nil p))))))))))))
def c2428 : List Lit := [(1623, false), (1671, true), (37, true), (1641, false), (1611, false), (58, false)]
theorem step2428 (p : Nat → Bool) (h : Constraints p) : clause p c2428 = true :=
  Snake9.LocalRup.prove_clause [c1995, c1230, c1108, c1113, c1146, c1142, c1114, c1224, c1109, c1201, c2373] c2428 (by decide) p (sat_cons (step1995 p h) (sat_cons (step1230 p h) (sat_cons (step1108 p h) (sat_cons (step1113 p h) (sat_cons (step1146 p h) (sat_cons (step1142 p h) (sat_cons (step1114 p h) (sat_cons (step1224 p h) (sat_cons (step1109 p h) (sat_cons (step1201 p h) (sat_cons (step2373 p h) (sat_nil p))))))))))))
def c2429 : List Lit := [(1624, false), (1651, false), (1670, true), (1635, false), (4, false), (35, false), (52, true)]
theorem step2429 (p : Nat → Bool) (h : Constraints p) : clause p c2429 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1161, c1197, c1223, c1133, c1138, c1218, c1112, c1201, c1105, c1162, c143, c1157] c2429 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1161 p h) (sat_cons (step1197 p h) (sat_cons (step1223 p h) (sat_cons (step1133 p h) (sat_cons (step1138 p h) (sat_cons (step1218 p h) (sat_cons (step1112 p h) (sat_cons (step1201 p h) (sat_cons (step1105 p h) (sat_cons (step1162 p h) (sat_cons (step143 p h) (sat_cons (step1157 p h) (sat_nil p))))))))))))))
def c2430 : List Lit := [(1621, true), (33, false), (49, true)]
theorem step2430 (p : Nat → Bool) (h : Constraints p) : clause p c2430 = true :=
  Snake9.LocalRup.prove_clause [c1121, c1122, c1846, c196] c2430 (by decide) p (sat_cons (step1121 p h) (sat_cons (step1122 p h) (sat_cons (step1846 p h) (sat_cons (step196 p h) (sat_nil p)))))
def c2431 : List Lit := [(47, false), (64, false), (48, true), (37, false)]
theorem step2431 (p : Nat → Bool) (h : Constraints p) : clause p c2431 = true :=
  Snake9.LocalRup.prove_clause [c1851, c211] c2431 (by decide) p (sat_cons (step1851 p h) (sat_cons (step211 p h) (sat_nil p)))
def c2432 : List Lit := [(88, false), (33, false), (6, true), (73, false), (37, false)]
theorem step2432 (p : Nat → Bool) (h : Constraints p) : clause p c2432 = true :=
  Snake9.LocalRup.prove_clause [c502, c106, c1829] c2432 (by decide) p (sat_cons (step502 p h) (sat_cons (step106 p h) (sat_cons (step1829 p h) (sat_nil p))))
def c2433 : List Lit := [(101, true), (1776, true), (73, false)]
theorem step2433 (p : Nat → Bool) (h : Constraints p) : clause p c2433 = true :=
  Snake9.LocalRup.prove_clause [c1393, c1389, c1391, c1395, c2316] c2433 (by decide) p (sat_cons (step1393 p h) (sat_cons (step1389 p h) (sat_cons (step1391 p h) (sat_cons (step1395 p h) (sat_cons (step2316 p h) (sat_nil p))))))
def c2434 : List Lit := [(1621, true), (101, false), (33, false), (34, true)]
theorem step2434 (p : Nat → Bool) (h : Constraints p) : clause p c2434 = true :=
  Snake9.LocalRup.prove_clause [c1121, c1122, c2109, c196, c1604, c1843] c2434 (by decide) p (sat_cons (step1121 p h) (sat_cons (step1122 p h) (sat_cons (step2109 p h) (sat_cons (step196 p h) (sat_cons (step1604 p h) (sat_cons (step1843 p h) (sat_nil p)))))))
def c2435 : List Lit := [(1660, true), (1642, false), (1636, false), (63, false), (64, false), (67, false), (1641, false), (52, true)]
theorem step2435 (p : Nat → Bool) (h : Constraints p) : clause p c2435 = true :=
  Snake9.LocalRup.prove_clause [c2368, c1204, c312, c2120, c1874, c324] c2435 (by decide) p (sat_cons (step2368 p h) (sat_cons (step1204 p h) (sat_cons (step312 p h) (sat_cons (step2120 p h) (sat_cons (step1874 p h) (sat_cons (step324 p h) (sat_nil p)))))))
def c2436 : List Lit := [(1789, false), (88, false), (1828, true)]
theorem step2436 (p : Nat → Bool) (h : Constraints p) : clause p c2436 = true :=
  Snake9.LocalRup.prove_clause [c2386, c2406, c1444, c1441] c2436 (by decide) p (sat_cons (step2386 p h) (sat_cons (step2406 p h) (sat_cons (step1444 p h) (sat_cons (step1441 p h) (sat_nil p)))))
def c2437 : List Lit := [(67, true), (73, true), (1725, true)]
theorem step2437 (p : Nat → Bool) (h : Constraints p) : clause p c2437 = true :=
  Snake9.LocalRup.prove_clause [c1294, c2004, c1287, c1284, c1285, c1286, c1311, c1305, c1303, c1296, c1297, c1298, c376, c369, c1895] c2437 (by decide) p (sat_cons (step1294 p h) (sat_cons (step2004 p h) (sat_cons (step1287 p h) (sat_cons (step1284 p h) (sat_cons (step1285 p h) (sat_cons (step1286 p h) (sat_cons (step1311 p h) (sat_cons (step1305 p h) (sat_cons (step1303 p h) (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step376 p h) (sat_cons (step369 p h) (sat_cons (step1895 p h) (sat_nil p))))))))))))))))
def c2438 : List Lit := [(1629, true), (33, false), (49, true), (39, true), (34, true)]
theorem step2438 (p : Nat → Bool) (h : Constraints p) : clause p c2438 = true :=
  Snake9.LocalRup.prove_clause [c2430, c1746, c1119, c1134, c1138, c1130, c1128, c1112, c1120, c1105, c2053, c1123, c194, c187, c1845] c2438 (by decide) p (sat_cons (step2430 p h) (sat_cons (step1746 p h) (sat_cons (step1119 p h) (sat_cons (step1134 p h) (sat_cons (step1138 p h) (sat_cons (step1130 p h) (sat_cons (step1128 p h) (sat_cons (step1112 p h) (sat_cons (step1120 p h) (sat_cons (step1105 p h) (sat_cons (step2053 p h) (sat_cons (step1123 p h) (sat_cons (step194 p h) (sat_cons (step187 p h) (sat_cons (step1845 p h) (sat_nil p))))))))))))))))
def c2439 : List Lit := [(33, true), (1630, true), (1613, false), (39, true), (34, true)]
theorem step2439 (p : Nat → Bool) (h : Constraints p) : clause p c2439 = true :=
  Snake9.LocalRup.prove_clause [c1104, c2377, c1113] c2439 (by decide) p (sat_cons (step1104 p h) (sat_cons (step2377 p h) (sat_cons (step1113 p h) (sat_nil p))))
def c2440 : List Lit := [(1629, true), (49, true), (39, true), (34, true)]
theorem step2440 (p : Nat → Bool) (h : Constraints p) : clause p c2440 = true :=
  Snake9.LocalRup.prove_clause [c1746, c1138, c2438, c1112, c1104] c2440 (by decide) p (sat_cons (step1746 p h) (sat_cons (step1138 p h) (sat_cons (step2438 p h) (sat_cons (step1112 p h) (sat_cons (step1104 p h) (sat_nil p))))))
def c2441 : List Lit := [(1807, false), (1817, true), (1829, true), (100, true), (73, false)]
theorem step2441 (p : Nat → Bool) (h : Constraints p) : clause p c2441 = true :=
  Snake9.LocalRup.prove_clause [c1463, c2325, c2267] c2441 (by decide) p (sat_cons (step1463 p h) (sat_cons (step2325 p h) (sat_cons (step2267 p h) (sat_nil p))))
def c2442 : List Lit := [(46, true), (31, true), (37, false), (73, false)]
theorem step2442 (p : Nat → Bool) (h : Constraints p) : clause p c2442 = true :=
  Snake9.LocalRup.prove_clause [c1830, c1827, c1590] c2442 (by decide) p (sat_cons (step1830 p h) (sat_cons (step1827 p h) (sat_cons (step1590 p h) (sat_nil p))))
def c2443 : List Lit := [(1630, true), (1614, false), (39, true), (34, true)]
theorem step2443 (p : Nat → Bool) (h : Constraints p) : clause p c2443 = true :=
  Snake9.LocalRup.prove_clause [c1111, c1119, c1126, c1146, c1143, c1114, c2363, c1105] c2443 (by decide) p (sat_cons (step1111 p h) (sat_cons (step1119 p h) (sat_cons (step1126 p h) (sat_cons (step1146 p h) (sat_cons (step1143 p h) (sat_cons (step1114 p h) (sat_cons (step2363 p h) (sat_cons (step1105 p h) (sat_nil p)))))))))
def c2444 : List Lit := [(1559, true), (4, false), (2, false)]
theorem step2444 (p : Nat → Bool) (h : Constraints p) : clause p c2444 = true :=
  Snake9.LocalRup.prove_clause [c1016, c1018, c1014, c1010, c12, c2424] c2444 (by decide) p (sat_cons (step1016 p h) (sat_cons (step1018 p h) (sat_cons (step1014 p h) (sat_cons (step1010 p h) (sat_cons (step12 p h) (sat_cons (step2424 p h) (sat_nil p)))))))
def c2445 : List Lit := [(1735, true), (15, true)]
theorem step2445 (p : Nat → Bool) (h : Constraints p) : clause p c2445 = true :=
  Snake9.LocalRup.prove_clause [c1328, c1330, c1721, c1325, c1326, c1322, c404] c2445 (by decide) p (sat_cons (step1328 p h) (sat_cons (step1330 p h) (sat_cons (step1721 p h) (sat_cons (step1325 p h) (sat_cons (step1326 p h) (sat_cons (step1322 p h) (sat_cons (step404 p h) (sat_nil p))))))))
def c2446 : List Lit := [(1725, true), (41, false), (73, true), (58, true), (37, false)]
theorem step2446 (p : Nat → Bool) (h : Constraints p) : clause p c2446 = true :=
  Snake9.LocalRup.prove_clause [c2300, c2437, c1280, c209, c2284, c2160] c2446 (by decide) p (sat_cons (step2300 p h) (sat_cons (step2437 p h) (sat_cons (step1280 p h) (sat_cons (step209 p h) (sat_cons (step2284 p h) (sat_cons (step2160 p h) (sat_nil p)))))))
def c2447 : List Lit := [(47, false), (41, false), (48, true), (37, false)]
theorem step2447 (p : Nat → Bool) (h : Constraints p) : clause p c2447 = true :=
  Snake9.LocalRup.prove_clause [c208, c1851] c2447 (by decide) p (sat_cons (step208 p h) (sat_cons (step1851 p h) (sat_nil p)))
def c2448 : List Lit := [(1712, true), (196, true), (66, false), (27, false), (23, false), (7, false), (1652, true), (64, true), (58, true), (50, true)]
theorem step2448 (p : Nat → Bool) (h : Constraints p) : clause p c2448 = true :=
  Snake9.LocalRup.prove_clause [c1291, c2375, c2351, c1282, c2382, c1872, c77, c330, c1863] c2448 (by decide) p (sat_cons (step1291 p h) (sat_cons (step2375 p h) (sat_cons (step2351 p h) (sat_cons (step1282 p h) (sat_cons (step2382 p h) (sat_cons (step1872 p h) (sat_cons (step77 p h) (sat_cons (step330 p h) (sat_cons (step1863 p h) (sat_nil p))))))))))
def c2449 : List Lit := [(1851, true), (1789, false), (1742, false), (1725, false), (1827, false), (1735, false)]
theorem step2449 (p : Nat → Bool) (h : Constraints p) : clause p c2449 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1347, c1368, c1567, c1562, c1369, c2436, c1348, c1333, c1341] c2449 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1347 p h) (sat_cons (step1368 p h) (sat_cons (step1567 p h) (sat_cons (step1562 p h) (sat_cons (step1369 p h) (sat_cons (step2436 p h) (sat_cons (step1348 p h) (sat_cons (step1333 p h) (sat_cons (step1341 p h) (sat_nil p)))))))))))
def c2450 : List Lit := [(1789, true), (227, true), (106, true), (93, true), (97, false), (38, false), (37, false)]
theorem step2450 (p : Nat → Bool) (h : Constraints p) : clause p c2450 = true :=
  Snake9.LocalRup.prove_clause [c1687, c1420, c2041, c1407, c1405] c2450 (by decide) p (sat_cons (step1687 p h) (sat_cons (step1420 p h) (sat_cons (step2041 p h) (sat_cons (step1407 p h) (sat_cons (step1405 p h) (sat_nil p))))))
def c2451 : List Lit := [(43, false), (41, false), (1622, true), (33, false)]
theorem step2451 (p : Nat → Bool) (h : Constraints p) : clause p c2451 = true :=
  Snake9.LocalRup.prove_clause [c195, c194, c1123] c2451 (by decide) p (sat_cons (step195 p h) (sat_cons (step194 p h) (sat_cons (step1123 p h) (sat_nil p))))
def c2452 : List Lit := [(27, false), (57, false), (1712, true), (15, true)]
theorem step2452 (p : Nat → Bool) (h : Constraints p) : clause p c2452 = true :=
  Snake9.LocalRup.prove_clause [c1816, c2375] c2452 (by decide) p (sat_cons (step1816 p h) (sat_cons (step2375 p h) (sat_nil p)))
def c2453 : List Lit := [(41, true), (170, true), (1624, true), (33, false), (32, true), (34, true)]
theorem step2453 (p : Nat → Bool) (h : Constraints p) : clause p c2453 = true :=
  Snake9.LocalRup.prove_clause [c1118, c1127, c2109, c2434, c193] c2453 (by decide) p (sat_cons (step1118 p h) (sat_cons (step1127 p h) (sat_cons (step2109 p h) (sat_cons (step2434 p h) (sat_cons (step193 p h) (sat_nil p))))))
def c2454 : List Lit := [(1725, true), (27, false), (73, true), (15, true)]
theorem step2454 (p : Nat → Bool) (h : Constraints p) : clause p c2454 = true :=
  Snake9.LocalRup.prove_clause [c2300, c2437, c1280, c2365] c2454 (by decide) p (sat_cons (step2300 p h) (sat_cons (step2437 p h) (sat_cons (step1280 p h) (sat_cons (step2365 p h) (sat_nil p)))))
def c2455 : List Lit := [(1629, true), (33, true), (39, true), (34, true)]
theorem step2455 (p : Nat → Bool) (h : Constraints p) : clause p c2455 = true :=
  Snake9.LocalRup.prove_clause [c1104, c1112, c1119, c1126, c1138, c1142, c2363, c1115, c1106] c2455 (by decide) p (sat_cons (step1104 p h) (sat_cons (step1112 p h) (sat_cons (step1119 p h) (sat_cons (step1126 p h) (sat_cons (step1138 p h) (sat_cons (step1142 p h) (sat_cons (step2363 p h) (sat_cons (step1115 p h) (sat_cons (step1106 p h) (sat_nil p))))))))))
def c2456 : List Lit := [(70, false), (88, false), (1550, true), (73, false), (37, false)]
theorem step2456 (p : Nat → Bool) (h : Constraints p) : clause p c2456 = true :=
  Snake9.LocalRup.prove_clause [c502, c342, c1689, c1891, c361, c25, c1001] c2456 (by decide) p (sat_cons (step502 p h) (sat_cons (step342 p h) (sat_cons (step1689 p h) (sat_cons (step1891 p h) (sat_cons (step361 p h) (sat_cons (step25 p h) (sat_cons (step1001 p h) (sat_nil p))))))))
def c2457 : List Lit := [(1772, false), (1789, true)]
theorem step2457 (p : Nat → Bool) (h : Constraints p) : clause p c2457 = true :=
  Snake9.LocalRup.prove_clause [c1428, c1397, c1398, c1424, c1732] c2457 (by decide) p (sat_cons (step1428 p h) (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step1424 p h) (sat_cons (step1732 p h) (sat_nil p))))))
def c2458 : List Lit := [(7, false), (1772, true), (1720, true), (73, false), (37, false)]
theorem step2458 (p : Nat → Bool) (h : Constraints p) : clause p c2458 = true :=
  Snake9.LocalRup.prove_clause [c22, c1753] c2458 (by decide) p (sat_cons (step22 p h) (sat_cons (step1753 p h) (sat_nil p)))
def c2459 : List Lit := [(1625, true), (47, false), (1621, false), (33, false), (39, true), (37, false)]
theorem step2459 (p : Nat → Bool) (h : Constraints p) : clause p c2459 = true :=
  Snake9.LocalRup.prove_clause [c1119, c1128, c1130, c1120, c105, c2451, c208, c1839] c2459 (by decide) p (sat_cons (step1119 p h) (sat_cons (step1128 p h) (sat_cons (step1130 p h) (sat_cons (step1120 p h) (sat_cons (step105 p h) (sat_cons (step2451 p h) (sat_cons (step208 p h) (sat_cons (step1839 p h) (sat_nil p)))))))))
def c2460 : List Lit := [(1741, false), (1707, false), (67, true), (1550, true), (1744, true), (1760, true), (73, false), (37, false), (1735, false)]
theorem step2460 (p : Nat → Bool) (h : Constraints p) : clause p c2460 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1340, c1346, c1333, c1373, c2456, c2005, c1285, c1290] c2460 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1340 p h) (sat_cons (step1346 p h) (sat_cons (step1333 p h) (sat_cons (step1373 p h) (sat_cons (step2456 p h) (sat_cons (step2005 p h) (sat_cons (step1285 p h) (sat_cons (step1290 p h) (sat_nil p))))))))))
def c2461 : List Lit := [(1564, true), (1559, false), (4, false), (35, false)]
theorem step2461 (p : Nat → Bool) (h : Constraints p) : clause p c2461 = true :=
  Snake9.LocalRup.prove_clause [c1025, c1029, c2036, c1002, c1004, c999, c1000, c1697, c17] c2461 (by decide) p (sat_cons (step1025 p h) (sat_cons (step1029 p h) (sat_cons (step2036 p h) (sat_cons (step1002 p h) (sat_cons (step1004 p h) (sat_cons (step999 p h) (sat_cons (step1000 p h) (sat_cons (step1697 p h) (sat_cons (step17 p h) (sat_nil p))))))))))
def c2462 : List Lit := [(7, false), (1712, true), (56, false), (46, false), (23, false), (66, false), (27, false), (1652, true), (58, true), (50, true)]
theorem step2462 (p : Nat → Bool) (h : Constraints p) : clause p c2462 = true :=
  Snake9.LocalRup.prove_clause [c1291, c77, c1863, c308, c1280, c2448, c1282, c1289, c339, c1284] c2462 (by decide) p (sat_cons (step1291 p h) (sat_cons (step77 p h) (sat_cons (step1863 p h) (sat_cons (step308 p h) (sat_cons (step1280 p h) (sat_cons (step2448 p h) (sat_cons (step1282 p h) (sat_cons (step1289 p h) (sat_cons (step339 p h) (sat_cons (step1284 p h) (sat_nil p)))))))))))
def c2463 : List Lit := [(1726, false), (1789, false), (1761, true), (1851, true), (1741, false), (1735, false)]
theorem step2463 (p : Nat → Bool) (h : Constraints p) : clause p c2463 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1346, c1373, c1374, c1562, c1347, c2436, c1340, c1333] c2463 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1346 p h) (sat_cons (step1373 p h) (sat_cons (step1374 p h) (sat_cons (step1562 p h) (sat_cons (step1347 p h) (sat_cons (step2436 p h) (sat_cons (step1340 p h) (sat_cons (step1333 p h) (sat_nil p))))))))))
def c2464 : List Lit := [(7, false), (1726, true), (46, false), (27, false), (23, false), (1652, true), (73, true), (58, true), (15, true), (50, true)]
theorem step2464 (p : Nat → Bool) (h : Constraints p) : clause p c2464 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1719, c1315, c2452, c2462, c2382] c2464 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1719 p h) (sat_cons (step1315 p h) (sat_cons (step2452 p h) (sat_cons (step2462 p h) (sat_cons (step2382 p h) (sat_nil p)))))))
def c2465 : List Lit := [(95, false), (1772, true), (88, false), (73, false)]
theorem step2465 (p : Nat → Bool) (h : Constraints p) : clause p c2465 = true :=
  Snake9.LocalRup.prove_clause [c518, c517, c1388] c2465 (by decide) p (sat_cons (step518 p h) (sat_cons (step517 p h) (sat_cons (step1388 p h) (sat_nil p))))
def c2466 : List Lit := [(1771, true), (88, false), (93, false)]
theorem step2466 (p : Nat → Bool) (h : Constraints p) : clause p c2466 = true :=
  Snake9.LocalRup.prove_clause [c1386, c2278, c453] c2466 (by decide) p (sat_cons (step1386 p h) (sat_cons (step2278 p h) (sat_cons (step453 p h) (sat_nil p))))
def c2467 : List Lit := [(125, false), (27, false), (1712, true), (15, true)]
theorem step2467 (p : Nat → Bool) (h : Constraints p) : clause p c2467 = true :=
  Snake9.LocalRup.prove_clause [c1816, c2397, c323, c1280, c1284, c1289] c2467 (by decide) p (sat_cons (step1816 p h) (sat_cons (step2397 p h) (sat_cons (step323 p h) (sat_cons (step1280 p h) (sat_cons (step1284 p h) (sat_cons (step1289 p h) (sat_nil p)))))))
def c2468 : List Lit := [(1849, true), (1788, false), (1807, false), (1724, false), (1741, false), (73, false), (1735, false)]
theorem step2468 (p : Nat → Bool) (h : Constraints p) : clause p c2468 = true :=
  Snake9.LocalRup.prove_clause [c1337, c1346, c1361, c2415, c1553, c1547, c1362, c1498, c1347, c2267, c2032, c1340, c520, c1333] c2468 (by decide) p (sat_cons (step1337 p h) (sat_cons (step1346 p h) (sat_cons (step1361 p h) (sat_cons (step2415 p h) (sat_cons (step1553 p h) (sat_cons (step1547 p h) (sat_cons (step1362 p h) (sat_cons (step1498 p h) (sat_cons (step1347 p h) (sat_cons (step2267 p h) (sat_cons (step2032 p h) (sat_cons (step1340 p h) (sat_cons (step520 p h) (sat_cons (step1333 p h) (sat_nil p)))))))))))))))
def c2469 : List Lit := [(100, true), (1849, true), (1807, false), (1724, false), (73, false), (1735, false)]
theorem step2469 (p : Nat → Bool) (h : Constraints p) : clause p c2469 = true :=
  Snake9.LocalRup.prove_clause [c2415, c1553, c1362, c1347, c2311, c1390, c2441, c1392, c2322, c2395, c1771, c2468] c2469 (by decide) p (sat_cons (step2415 p h) (sat_cons (step1553 p h) (sat_cons (step1362 p h) (sat_cons (step1347 p h) (sat_cons (step2311 p h) (sat_cons (step1390 p h) (sat_cons (step2441 p h) (sat_cons (step1392 p h) (sat_cons (step2322 p h) (sat_cons (step2395 p h) (sat_cons (step1771 p h) (sat_cons (step2468 p h) (sat_nil p)))))))))))))
def c2470 : List Lit := [(1829, true), (1789, false), (100, true), (1807, false), (73, false)]
theorem step2470 (p : Nat → Bool) (h : Constraints p) : clause p c2470 = true :=
  Snake9.LocalRup.prove_clause [c2441, c1506] c2470 (by decide) p (sat_cons (step2441 p h) (sat_cons (step1506 p h) (sat_nil p)))
def c2471 : List Lit := [(1726, true), (1707, false), (1712, false), (67, true), (73, true)]
theorem step2471 (p : Nat → Bool) (h : Constraints p) : clause p c2471 = true :=
  Snake9.LocalRup.prove_clause [c1294, c2005, c1315, c1290, c1305, c1303, c1285, c1296, c1297, c1298, c376, c369, c1895] c2471 (by decide) p (sat_cons (step1294 p h) (sat_cons (step2005 p h) (sat_cons (step1315 p h) (sat_cons (step1290 p h) (sat_cons (step1305 p h) (sat_cons (step1303 p h) (sat_cons (step1285 p h) (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step376 p h) (sat_cons (step369 p h) (sat_cons (step1895 p h) (sat_nil p))))))))))))))
def c2472 : List Lit := [(1807, true), (66, false), (27, false), (1652, true)]
theorem step2472 (p : Nat → Bool) (h : Constraints p) : clause p c2472 = true :=
  Snake9.LocalRup.prove_clause [c1179, c1458, c2385, c1456, c1169, c320, c1176, c1175, c1171, c1182, c1742, c1167] c2472 (by decide) p (sat_cons (step1179 p h) (sat_cons (step1458 p h) (sat_cons (step2385 p h) (sat_cons (step1456 p h) (sat_cons (step1169 p h) (sat_cons (step320 p h) (sat_cons (step1176 p h) (sat_cons (step1175 p h) (sat_cons (step1171 p h) (sat_cons (step1182 p h) (sat_cons (step1742 p h) (sat_cons (step1167 p h) (sat_nil p)))))))))))))
def c2473 : List Lit := [(57, false), (1713, true), (196, true), (66, false), (27, false), (50, true)]
theorem step2473 (p : Nat → Bool) (h : Constraints p) : clause p c2473 = true :=
  Snake9.LocalRup.prove_clause [c319, c2391, c340, c1872] c2473 (by decide) p (sat_cons (step319 p h) (sat_cons (step2391 p h) (sat_cons (step340 p h) (sat_cons (step1872 p h) (sat_nil p)))))
def c2474 : List Lit := [(1725, true), (1659, true), (73, true), (1635, false), (35, false), (52, true)]
theorem step2474 (p : Nat → Bool) (h : Constraints p) : clause p c2474 = true :=
  Snake9.LocalRup.prove_clause [c2300, c2437, c2407] c2474 (by decide) p (sat_cons (step2300 p h) (sat_cons (step2437 p h) (sat_cons (step2407 p h) (sat_nil p))))
def c2475 : List Lit := [(1629, true), (39, true), (1613, false), (34, true)]
theorem step2475 (p : Nat → Bool) (h : Constraints p) : clause p c2475 = true :=
  Snake9.LocalRup.prove_clause [c1119, c1126, c1110, c1142, c1138, c1113, c2363, c1105] c2475 (by decide) p (sat_cons (step1119 p h) (sat_cons (step1126 p h) (sat_cons (step1110 p h) (sat_cons (step1142 p h) (sat_cons (step1138 p h) (sat_cons (step1113 p h) (sat_cons (step2363 p h) (sat_cons (step1105 p h) (sat_nil p)))))))))
def c2476 : List Lit := [(315, false), (61, true), (1712, true), (54, true), (58, true), (50, true)]
theorem step2476 (p : Nat → Bool) (h : Constraints p) : clause p c2476 = true :=
  Snake9.LocalRup.prove_clause [c1291, c898, c1972, c1985, c892, c989, c888, c932, c887, c918, c885, c908, c884, c906, c305, c904, c1873, c2351, c2361] c2476 (by decide) p (sat_cons (step1291 p h) (sat_cons (step898 p h) (sat_cons (step1972 p h) (sat_cons (step1985 p h) (sat_cons (step892 p h) (sat_cons (step989 p h) (sat_cons (step888 p h) (sat_cons (step932 p h) (sat_cons (step887 p h) (sat_cons (step918 p h) (sat_cons (step885 p h) (sat_cons (step908 p h) (sat_cons (step884 p h) (sat_cons (step906 p h) (sat_cons (step305 p h) (sat_cons (step904 p h) (sat_cons (step1873 p h) (sat_cons (step2351 p h) (sat_cons (step2361 p h) (sat_nil p))))))))))))))))))))
end B112E036
