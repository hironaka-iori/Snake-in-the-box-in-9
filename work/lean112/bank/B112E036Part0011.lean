import B112E036Part0010
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2349 : List Lit := [(117, false), (1851, true), (98, false), (95, false), (37, false)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c508, c1333, c2348, c1341, c514, c1404, c515, c2339, c504, c2130, c2342, c2032, c2033, c1401, c1409, c1442, c1486, c1450, c1339, c2346, c1438, c1440, c1447, c1481, c1482, c1466, c1724, c1453, c1389, c712, c2344, c1953, c1346, c729, c1361, c1391, c1549, c1396, c1518, c1430] c2349 (by decide) p (sat_cons (step508 p h) (sat_cons (step1333 p h) (sat_cons (step2348 p h) (sat_cons (step1341 p h) (sat_cons (step514 p h) (sat_cons (step1404 p h) (sat_cons (step515 p h) (sat_cons (step2339 p h) (sat_cons (step504 p h) (sat_cons (step2130 p h) (sat_cons (step2342 p h) (sat_cons (step2032 p h) (sat_cons (step2033 p h) (sat_cons (step1401 p h) (sat_cons (step1409 p h) (sat_cons (step1442 p h) (sat_cons (step1486 p h) (sat_cons (step1450 p h) (sat_cons (step1339 p h) (sat_cons (step2346 p h) (sat_cons (step1438 p h) (sat_cons (step1440 p h) (sat_cons (step1447 p h) (sat_cons (step1481 p h) (sat_cons (step1482 p h) (sat_cons (step1466 p h) (sat_cons (step1724 p h) (sat_cons (step1453 p h) (sat_cons (step1389 p h) (sat_cons (step712 p h) (sat_cons (step2344 p h) (sat_cons (step1953 p h) (sat_cons (step1346 p h) (sat_cons (step729 p h) (sat_cons (step1361 p h) (sat_cons (step1391 p h) (sat_cons (step1549 p h) (sat_cons (step1396 p h) (sat_cons (step1518 p h) (sat_cons (step1430 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c2350 : List Lit := [(1851, true), (98, false), (95, false), (37, false)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c508, c1333, c504, c2130, c515, c514, c2339, c2342, c1486, c2032, c1458, c1460, c1455, c1456, c2349, c1443, c1445, c1448, c1481, c1482, c1438, c1466, c1724, c2295, c1452, c1389, c1512, c738, c2344, c1555, c2148, c1362, c693, c1347, c1334, c1340] c2350 (by decide) p (sat_cons (step508 p h) (sat_cons (step1333 p h) (sat_cons (step504 p h) (sat_cons (step2130 p h) (sat_cons (step515 p h) (sat_cons (step514 p h) (sat_cons (step2339 p h) (sat_cons (step2342 p h) (sat_cons (step1486 p h) (sat_cons (step2032 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step2349 p h) (sat_cons (step1443 p h) (sat_cons (step1445 p h) (sat_cons (step1448 p h) (sat_cons (step1481 p h) (sat_cons (step1482 p h) (sat_cons (step1438 p h) (sat_cons (step1466 p h) (sat_cons (step1724 p h) (sat_cons (step2295 p h) (sat_cons (step1452 p h) (sat_cons (step1389 p h) (sat_cons (step1512 p h) (sat_cons (step738 p h) (sat_cons (step2344 p h) (sat_cons (step1555 p h) (sat_cons (step2148 p h) (sat_cons (step1362 p h) (sat_cons (step693 p h) (sat_cons (step1347 p h) (sat_cons (step1334 p h) (sat_cons (step1340 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c2351 : List Lit := [(67, true), (1712, true), (196, true), (50, true)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c1284, c340, c1289, c1872, c1281] c2351 (by decide) p (sat_cons (step1284 p h) (sat_cons (step340 p h) (sat_cons (step1289 p h) (sat_cons (step1872 p h) (sat_cons (step1281 p h) (sat_nil p))))))
def c2352 : List Lit := [(1621, true), (41, false), (49, true)]
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c1121, c1122, c1846, c197] c2352 (by decide) p (sat_cons (step1121 p h) (sat_cons (step1122 p h) (sat_cons (step1846 p h) (sat_cons (step197 p h) (sat_nil p)))))
def c2353 : List Lit := [(56, false), (58, true), (64, false), (67, false), (22, true)]
theorem step2353 (p : Nat → Bool) (h : Constraints p) : clause p c2353 = true :=
  Snake9.LocalRup.prove_clause [c1863, c312] c2353 (by decide) p (sat_cons (step1863 p h) (sat_cons (step312 p h) (sat_nil p)))
def c2354 : List Lit := [(57, false), (58, true), (64, false), (67, false), (179, true), (33, true), (52, true)]
theorem step2354 (p : Nat → Bool) (h : Constraints p) : clause p c2354 = true :=
  Snake9.LocalRup.prove_clause [c324, c1865, c1864, c249, c1606] c2354 (by decide) p (sat_cons (step324 p h) (sat_cons (step1865 p h) (sat_cons (step1864 p h) (sat_cons (step249 p h) (sat_cons (step1606 p h) (sat_nil p))))))
def c2355 : List Lit := [(1623, true), (49, true)]
theorem step2355 (p : Nat → Bool) (h : Constraints p) : clause p c2355 = true :=
  Snake9.LocalRup.prove_clause [c1124, c1126, c2352, c1118] c2355 (by decide) p (sat_cons (step1124 p h) (sat_cons (step1126 p h) (sat_cons (step2352 p h) (sat_cons (step1118 p h) (sat_nil p)))))
def c2356 : List Lit := [(1651, true), (58, false), (67, false)]
theorem step2356 (p : Nat → Bool) (h : Constraints p) : clause p c2356 = true :=
  Snake9.LocalRup.prove_clause [c2019, c2120, c289] c2356 (by decide) p (sat_cons (step2019 p h) (sat_cons (step2120 p h) (sat_cons (step289 p h) (sat_nil p))))
def c2357 : List Lit := [(1826, true), (1807, false), (1815, false)]
theorem step2357 (p : Nat → Bool) (h : Constraints p) : clause p c2357 = true :=
  Snake9.LocalRup.prove_clause [c1492, c1496, c2305, c2279] c2357 (by decide) p (sat_cons (step1492 p h) (sat_cons (step1496 p h) (sat_cons (step2305 p h) (sat_cons (step2279 p h) (sat_nil p)))))
def c2358 : List Lit := [(309, true), (27, true), (30, false), (23, true)]
theorem step2358 (p : Nat → Bool) (h : Constraints p) : clause p c2358 = true :=
  Snake9.LocalRup.prove_clause [c852, c853, c851, c849, c1819, c93, c1818] c2358 (by decide) p (sat_cons (step852 p h) (sat_cons (step853 p h) (sat_cons (step851 p h) (sat_cons (step849 p h) (sat_cons (step1819 p h) (sat_cons (step93 p h) (sat_cons (step1818 p h) (sat_nil p))))))))
def c2359 : List Lit := [(1826, true), (1815, false)]
theorem step2359 (p : Nat → Bool) (h : Constraints p) : clause p c2359 = true :=
  Snake9.LocalRup.prove_clause [c1757, c2357, c1408, c2033, c1401] c2359 (by decide) p (sat_cons (step1757 p h) (sat_cons (step2357 p h) (sat_cons (step1408 p h) (sat_cons (step2033 p h) (sat_cons (step1401 p h) (sat_nil p))))))
def c2360 : List Lit := [(27, false), (58, false), (67, false), (1708, true), (15, true)]
theorem step2360 (p : Nat → Bool) (h : Constraints p) : clause p c2360 = true :=
  Snake9.LocalRup.prove_clause [c1816, c329, c321, c1872, c1282] c2360 (by decide) p (sat_cons (step1816 p h) (sat_cons (step329 p h) (sat_cons (step321 p h) (sat_cons (step1872 p h) (sat_cons (step1282 p h) (sat_nil p))))))
def c2361 : List Lit := [(63, true), (58, true), (196, true), (67, false), (1708, true), (50, true)]
theorem step2361 (p : Nat → Bool) (h : Constraints p) : clause p c2361 = true :=
  Snake9.LocalRup.prove_clause [c1282, c341, c2284] c2361 (by decide) p (sat_cons (step1282 p h) (sat_cons (step341 p h) (sat_cons (step2284 p h) (sat_nil p))))
def c2362 : List Lit := [(54, false), (1646, true), (63, false), (35, false)]
theorem step2362 (p : Nat → Bool) (h : Constraints p) : clause p c2362 = true :=
  Snake9.LocalRup.prove_clause [c1873, c257, c302, c1868, c1171] c2362 (by decide) p (sat_cons (step1873 p h) (sat_cons (step257 p h) (sat_cons (step302 p h) (sat_cons (step1868 p h) (sat_cons (step1171 p h) (sat_nil p))))))
def c2363 : List Lit := [(1624, true), (39, true), (32, false), (34, true)]
theorem step2363 (p : Nat → Bool) (h : Constraints p) : clause p c2363 = true :=
  Snake9.LocalRup.prove_clause [c1119, c1129, c1127, c1120, c1122, c2124, c187] c2363 (by decide) p (sat_cons (step1119 p h) (sat_cons (step1129 p h) (sat_cons (step1127 p h) (sat_cons (step1120 p h) (sat_cons (step1122 p h) (sat_cons (step2124 p h) (sat_cons (step187 p h) (sat_nil p))))))))
def c2364 : List Lit := [(1629, true), (35, false), (1616, false), (1613, false), (33, true), (4, false)]
theorem step2364 (p : Nat → Bool) (h : Constraints p) : clause p c2364 = true :=
  Snake9.LocalRup.prove_clause [c1145, c1142, c1116, c1126, c1106, c1119, c142] c2364 (by decide) p (sat_cons (step1145 p h) (sat_cons (step1142 p h) (sat_cons (step1116 p h) (sat_cons (step1126 p h) (sat_cons (step1106 p h) (sat_cons (step1119 p h) (sat_cons (step142 p h) (sat_nil p))))))))
def c2365 : List Lit := [(27, false), (67, false), (64, false), (15, true)]
theorem step2365 (p : Nat → Bool) (h : Constraints p) : clause p c2365 = true :=
  Snake9.LocalRup.prove_clause [c1816, c321] c2365 (by decide) p (sat_cons (step1816 p h) (sat_cons (step321 p h) (sat_nil p)))
def c2366 : List Lit := [(1787, true)]
theorem step2366 (p : Nat → Bool) (h : Constraints p) : clause p c2366 = true :=
  Snake9.LocalRup.prove_clause [c1414, c1418, c1732, c1392] c2366 (by decide) p (sat_cons (step1414 p h) (sat_cons (step1418 p h) (sat_cons (step1732 p h) (sat_cons (step1392 p h) (sat_nil p)))))
def c2367 : List Lit := [(1659, true), (56, true), (63, false), (1635, false), (52, true)]
theorem step2367 (p : Nat → Bool) (h : Constraints p) : clause p c2367 = true :=
  Snake9.LocalRup.prove_clause [c2019, c1873, c1156, c1161, c1198, c1201, c2271, c1162, c302, c1157] c2367 (by decide) p (sat_cons (step2019 p h) (sat_cons (step1873 p h) (sat_cons (step1156 p h) (sat_cons (step1161 p h) (sat_cons (step1198 p h) (sat_cons (step1201 p h) (sat_cons (step2271 p h) (sat_cons (step1162 p h) (sat_cons (step302 p h) (sat_cons (step1157 p h) (sat_nil p)))))))))))
def c2368 : List Lit := [(1660, true), (1636, false), (1641, false), (56, true), (63, false), (52, true)]
theorem step2368 (p : Nat → Bool) (h : Constraints p) : clause p c2368 = true :=
  Snake9.LocalRup.prove_clause [c2019, c1873, c1204, c1202, c1165, c2271, c1157, c302] c2368 (by decide) p (sat_cons (step2019 p h) (sat_cons (step1873 p h) (sat_cons (step1204 p h) (sat_cons (step1202 p h) (sat_cons (step1165 p h) (sat_cons (step2271 p h) (sat_cons (step1157 p h) (sat_cons (step302 p h) (sat_nil p)))))))))
def c2369 : List Lit := [(1659, true), (57, true), (63, false), (1635, false), (35, false), (52, true)]
theorem step2369 (p : Nat → Bool) (h : Constraints p) : clause p c2369 = true :=
  Snake9.LocalRup.prove_clause [c2120, c1156, c1161, c1198, c1201, c1179, c1162, c1176, c1157, c2362] c2369 (by decide) p (sat_cons (step2120 p h) (sat_cons (step1156 p h) (sat_cons (step1161 p h) (sat_cons (step1198 p h) (sat_cons (step1201 p h) (sat_cons (step1179 p h) (sat_cons (step1162 p h) (sat_cons (step1176 p h) (sat_cons (step1157 p h) (sat_cons (step2362 p h) (sat_nil p)))))))))))
def c2370 : List Lit := [(1800, true), (116, false), (56, false), (95, true)]
theorem step2370 (p : Nat → Bool) (h : Constraints p) : clause p c2370 = true :=
  Snake9.LocalRup.prove_clause [c2044, c707, c705, c1442, c1439, c1447] c2370 (by decide) p (sat_cons (step2044 p h) (sat_cons (step707 p h) (sat_cons (step705 p h) (sat_cons (step1442 p h) (sat_cons (step1439 p h) (sat_cons (step1447 p h) (sat_nil p)))))))
def c2371 : List Lit := [(38, false), (117, false), (1790, true), (106, true), (58, true), (34, true)]
theorem step2371 (p : Nat → Bool) (h : Constraints p) : clause p c2371 = true :=
  Snake9.LocalRup.prove_clause [c1832, c553, c550, c552, c1405, c1387, c1390, c1407, c1395, c1425] c2371 (by decide) p (sat_cons (step1832 p h) (sat_cons (step553 p h) (sat_cons (step550 p h) (sat_cons (step552 p h) (sat_cons (step1405 p h) (sat_cons (step1387 p h) (sat_cons (step1390 p h) (sat_cons (step1407 p h) (sat_cons (step1395 p h) (sat_cons (step1425 p h) (sat_nil p)))))))))))
def c2372 : List Lit := [(66, true), (57, false), (179, true), (58, true), (33, true), (52, true)]
theorem step2372 (p : Nat → Bool) (h : Constraints p) : clause p c2372 = true :=
  Snake9.LocalRup.prove_clause [c1864, c1865, c249, c1606] c2372 (by decide) p (sat_cons (step1864 p h) (sat_cons (step1865 p h) (sat_cons (step249 p h) (sat_cons (step1606 p h) (sat_nil p)))))
def c2373 : List Lit := [(1651, true), (38, false), (58, false)]
theorem step2373 (p : Nat → Bool) (h : Constraints p) : clause p c2373 = true :=
  Snake9.LocalRup.prove_clause [c2019, c2120, c277] c2373 (by decide) p (sat_cons (step2019 p h) (sat_cons (step2120 p h) (sat_cons (step277 p h) (sat_nil p))))
def c2374 : List Lit := [(1743, true), (1624, true), (1671, true), (37, false), (50, true), (35, false), (4, false), (34, true), (52, true)]
theorem step2374 (p : Nat → Bool) (h : Constraints p) : clause p c2374 = true :=
  Snake9.LocalRup.prove_clause [c1129, c1337, c1339, c1334, c1335, c1333, c146, c147, c144, c1119, c1120, c1157, c1127, c2180, c2124, c108, c1122, c1224, c1603, c1996, c1839, c1165, c208, c1154] c2374 (by decide) p (sat_cons (step1129 p h) (sat_cons (step1337 p h) (sat_cons (step1339 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step1333 p h) (sat_cons (step146 p h) (sat_cons (step147 p h) (sat_cons (step144 p h) (sat_cons (step1119 p h) (sat_cons (step1120 p h) (sat_cons (step1157 p h) (sat_cons (step1127 p h) (sat_cons (step2180 p h) (sat_cons (step2124 p h) (sat_cons (step108 p h) (sat_cons (step1122 p h) (sat_cons (step1224 p h) (sat_cons (step1603 p h) (sat_cons (step1996 p h) (sat_cons (step1839 p h) (sat_cons (step1165 p h) (sat_cons (step208 p h) (sat_cons (step1154 p h) (sat_nil p)))))))))))))))))))))))))
def c2375 : List Lit := [(57, false), (66, false), (27, false), (1712, true)]
theorem step2375 (p : Nat → Bool) (h : Constraints p) : clause p c2375 = true :=
  Snake9.LocalRup.prove_clause [c318, c319, c1280, c1284, c1289] c2375 (by decide) p (sat_cons (step318 p h) (sat_cons (step319 p h) (sat_cons (step1280 p h) (sat_cons (step1284 p h) (sat_cons (step1289 p h) (sat_nil p))))))
def c2376 : List Lit := [(1670, true), (1641, false), (1616, false), (58, false), (33, true), (35, false), (4, false)]
theorem step2376 (p : Nat → Bool) (h : Constraints p) : clause p c2376 = true :=
  Snake9.LocalRup.prove_clause [c1995, c1141, c1223, c1218, c2364, c1201, c1107, c2373] c2376 (by decide) p (sat_cons (step1995 p h) (sat_cons (step1141 p h) (sat_cons (step1223 p h) (sat_cons (step1218 p h) (sat_cons (step2364 p h) (sat_cons (step1201 p h) (sat_cons (step1107 p h) (sat_cons (step2373 p h) (sat_nil p)))))))))
def c2377 : List Lit := [(1630, true), (1613, false), (39, true), (1616, false), (33, true), (34, true)]
theorem step2377 (p : Nat → Bool) (h : Constraints p) : clause p c2377 = true :=
  Snake9.LocalRup.prove_clause [c1119, c1126, c1143, c1146, c2363, c1116, c1106] c2377 (by decide) p (sat_cons (step1119 p h) (sat_cons (step1126 p h) (sat_cons (step1143 p h) (sat_cons (step1146 p h) (sat_cons (step2363 p h) (sat_cons (step1116 p h) (sat_cons (step1106 p h) (sat_nil p))))))))
def c2378 : List Lit := [(117, true), (88, false), (1800, true), (37, false)]
theorem step2378 (p : Nat → Bool) (h : Constraints p) : clause p c2378 = true :=
  Snake9.LocalRup.prove_clause [c1445, c2044, c1443, c510] c2378 (by decide) p (sat_cons (step1445 p h) (sat_cons (step2044 p h) (sat_cons (step1443 p h) (sat_cons (step510 p h) (sat_nil p)))))
def c2379 : List Lit := [(1651, true), (117, false), (58, false)]
theorem step2379 (p : Nat → Bool) (h : Constraints p) : clause p c2379 = true :=
  Snake9.LocalRup.prove_clause [c2019, c2120, c290] c2379 (by decide) p (sat_cons (step2019 p h) (sat_cons (step2120 p h) (sat_cons (step290 p h) (sat_nil p))))
def c2380 : List Lit := [(1651, true), (66, false), (27, false), (23, false), (7, false), (58, true), (21, true)]
theorem step2380 (p : Nat → Bool) (h : Constraints p) : clause p c2380 = true :=
  Snake9.LocalRup.prove_clause [c2019, c2120, c77, c318, c319, c1815, c1863, c85, c315, c847, c901, c848, c902, c855, c910, c857, c918, c861, c932, c898, c989, c1985] c2380 (by decide) p (sat_cons (step2019 p h) (sat_cons (step2120 p h) (sat_cons (step77 p h) (sat_cons (step318 p h) (sat_cons (step319 p h) (sat_cons (step1815 p h) (sat_cons (step1863 p h) (sat_cons (step85 p h) (sat_cons (step315 p h) (sat_cons (step847 p h) (sat_cons (step901 p h) (sat_cons (step848 p h) (sat_cons (step902 p h) (sat_cons (step855 p h) (sat_cons (step910 p h) (sat_cons (step857 p h) (sat_cons (step918 p h) (sat_cons (step861 p h) (sat_cons (step932 p h) (sat_cons (step898 p h) (sat_cons (step989 p h) (sat_cons (step1985 p h) (sat_nil p)))))))))))))))))))))))
def c2381 : List Lit := [(1712, true), (1707, false), (27, false), (58, false), (15, true)]
theorem step2381 (p : Nat → Bool) (h : Constraints p) : clause p c2381 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1289, c2360, c1284] c2381 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1289 p h) (sat_cons (step2360 p h) (sat_cons (step1284 p h) (sat_nil p)))))
def c2382 : List Lit := [(56, true), (57, true), (1652, true)]
theorem step2382 (p : Nat → Bool) (h : Constraints p) : clause p c2382 = true :=
  Snake9.LocalRup.prove_clause [c1174, c1185, c1166, c1168, c1182, c1742, c1175, c1170] c2382 (by decide) p (sat_cons (step1174 p h) (sat_cons (step1185 p h) (sat_cons (step1166 p h) (sat_cons (step1168 p h) (sat_cons (step1182 p h) (sat_cons (step1742 p h) (sat_cons (step1175 p h) (sat_cons (step1170 p h) (sat_nil p)))))))))
def c2383 : List Lit := [(1631, true), (39, true), (1617, false), (1614, false), (33, true), (34, true)]
theorem step2383 (p : Nat → Bool) (h : Constraints p) : clause p c2383 = true :=
  Snake9.LocalRup.prove_clause [c1119, c1126, c1147, c1150, c2363, c1117, c1106] c2383 (by decide) p (sat_cons (step1119 p h) (sat_cons (step1126 p h) (sat_cons (step1147 p h) (sat_cons (step1150 p h) (sat_cons (step2363 p h) (sat_cons (step1117 p h) (sat_cons (step1106 p h) (sat_nil p))))))))
def c2384 : List Lit := [(38, false), (39, false), (58, true), (50, false), (34, true)]
theorem step2384 (p : Nat → Bool) (h : Constraints p) : clause p c2384 = true :=
  Snake9.LocalRup.prove_clause [c174, c1834] c2384 (by decide) p (sat_cons (step174 p h) (sat_cons (step1834 p h) (sat_nil p)))
def c2385 : List Lit := [(1807, true), (61, false)]
theorem step2385 (p : Nat → Bool) (h : Constraints p) : clause p c2385 = true :=
  Snake9.LocalRup.prove_clause [c1458, c1460, c1455, c1456, c767, c746, c1964] c2385 (by decide) p (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step767 p h) (sat_cons (step746 p h) (sat_cons (step1964 p h) (sat_nil p))))))))
def c2386 : List Lit := [(1828, true), (1789, false), (1799, false)]
theorem step2386 (p : Nat → Bool) (h : Constraints p) : clause p c2386 = true :=
  Snake9.LocalRup.prove_clause [c1476, c1511, c1505, c2295, c1477] c2386 (by decide) p (sat_cons (step1476 p h) (sat_cons (step1511 p h) (sat_cons (step1505 p h) (sat_cons (step2295 p h) (sat_cons (step1477 p h) (sat_nil p))))))
def c2387 : List Lit := [(1725, true), (50, false), (73, true)]
theorem step2387 (p : Nat → Bool) (h : Constraints p) : clause p c2387 = true :=
  Snake9.LocalRup.prove_clause [c1294, c2004, c2300, c1287, c1281, c1872, c337, c1284, c1285, c1286, c1311, c1305, c1303, c1296, c1297, c1298, c376, c369, c1895] c2387 (by decide) p (sat_cons (step1294 p h) (sat_cons (step2004 p h) (sat_cons (step2300 p h) (sat_cons (step1287 p h) (sat_cons (step1281 p h) (sat_cons (step1872 p h) (sat_cons (step337 p h) (sat_cons (step1284 p h) (sat_cons (step1285 p h) (sat_cons (step1286 p h) (sat_cons (step1311 p h) (sat_cons (step1305 p h) (sat_cons (step1303 p h) (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step376 p h) (sat_cons (step369 p h) (sat_cons (step1895 p h) (sat_nil p))))))))))))))))))))
def c2388 : List Lit := [(1670, true), (1624, false), (1630, false), (1613, false), (33, true), (35, false), (4, false), (52, true)]
theorem step2388 (p : Nat → Bool) (h : Constraints p) : clause p c2388 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1158, c1993, c1234, c1229, c1147, c1994, c1116, c1159, c1106, c1157, c143] c2388 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1993 p h) (sat_cons (step1234 p h) (sat_cons (step1229 p h) (sat_cons (step1147 p h) (sat_cons (step1994 p h) (sat_cons (step1116 p h) (sat_cons (step1159 p h) (sat_cons (step1106 p h) (sat_cons (step1157 p h) (sat_cons (step143 p h) (sat_nil p)))))))))))))
def c2389 : List Lit := [(67, false), (1652, true), (38, false), (58, false)]
theorem step2389 (p : Nat → Bool) (h : Constraints p) : clause p c2389 = true :=
  Snake9.LocalRup.prove_clause [c278, c280, c2382] c2389 (by decide) p (sat_cons (step278 p h) (sat_cons (step280 p h) (sat_cons (step2382 p h) (sat_nil p))))
def c2390 : List Lit := [(1817, false), (1851, true), (1783, false), (1774, false), (1725, false), (1735, false)]
theorem step2390 (p : Nat → Bool) (h : Constraints p) : clause p c2390 = true :=
  Snake9.LocalRup.prove_clause [c1345, c1366, c1549, c1393, c1424, c1513, c1506, c1429, c1555, c1396, c1367, c1740, c1346] c2390 (by decide) p (sat_cons (step1345 p h) (sat_cons (step1366 p h) (sat_cons (step1549 p h) (sat_cons (step1393 p h) (sat_cons (step1424 p h) (sat_cons (step1513 p h) (sat_cons (step1506 p h) (sat_cons (step1429 p h) (sat_cons (step1555 p h) (sat_cons (step1396 p h) (sat_cons (step1367 p h) (sat_cons (step1740 p h) (sat_cons (step1346 p h) (sat_nil p))))))))))))))
def c2391 : List Lit := [(57, false), (1713, true), (66, false), (27, false), (63, true)]
theorem step2391 (p : Nat → Bool) (h : Constraints p) : clause p c2391 = true :=
  Snake9.LocalRup.prove_clause [c319, c318, c1284, c1282, c1292] c2391 (by decide) p (sat_cons (step319 p h) (sat_cons (step318 p h) (sat_cons (step1284 p h) (sat_cons (step1282 p h) (sat_cons (step1292 p h) (sat_nil p))))))
def c2392 : List Lit := [(1712, true), (68, true), (58, true), (50, false)]
theorem step2392 (p : Nat → Bool) (h : Constraints p) : clause p c2392 = true :=
  Snake9.LocalRup.prove_clause [c1872, c1281, c1750, c1289, c2284, c1284] c2392 (by decide) p (sat_cons (step1872 p h) (sat_cons (step1281 p h) (sat_cons (step1750 p h) (sat_cons (step1289 p h) (sat_cons (step2284 p h) (sat_cons (step1284 p h) (sat_nil p)))))))
def c2393 : List Lit := [(68, false), (47, false), (40, false), (50, false)]
theorem step2393 (p : Nat → Bool) (h : Constraints p) : clause p c2393 = true :=
  Snake9.LocalRup.prove_clause [c236, c237, c1849] c2393 (by decide) p (sat_cons (step236 p h) (sat_cons (step237 p h) (sat_cons (step1849 p h) (sat_nil p))))
def c2394 : List Lit := [(1592, true), (1651, true), (7, false), (58, true), (1572, false), (15, true), (21, true)]
theorem step2394 (p : Nat → Bool) (h : Constraints p) : clause p c2394 = true :=
  Snake9.LocalRup.prove_clause [c1047, c1054, c1678, c1070, c1055, c1673, c1048, c1058, c2380, c1816] c2394 (by decide) p (sat_cons (step1047 p h) (sat_cons (step1054 p h) (sat_cons (step1678 p h) (sat_cons (step1070 p h) (sat_cons (step1055 p h) (sat_cons (step1673 p h) (sat_cons (step1048 p h) (sat_cons (step1058 p h) (sat_cons (step2380 p h) (sat_cons (step1816 p h) (sat_nil p)))))))))))
def c2395 : List Lit := [(1788, true), (1744, true), (1775, false)]
theorem step2395 (p : Nat → Bool) (h : Constraints p) : clause p c2395 = true :=
  Snake9.LocalRup.prove_clause [c2279, c1419, c2298, c1408, c1401] c2395 (by decide) p (sat_cons (step2279 p h) (sat_cons (step1419 p h) (sat_cons (step2298 p h) (sat_cons (step1408 p h) (sat_cons (step1401 p h) (sat_nil p))))))
def c2396 : List Lit := [(1720, true), (1741, true), (73, true), (5, true)]
theorem step2396 (p : Nat → Bool) (h : Constraints p) : clause p c2396 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1334, c1294, c1305, c1303, c1296, c1297, c1298, c482, c376, c1886] c2396 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1334 p h) (sat_cons (step1294 p h) (sat_cons (step1305 p h) (sat_cons (step1303 p h) (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step482 p h) (sat_cons (step376 p h) (sat_cons (step1886 p h) (sat_nil p))))))))))))
def c2397 : List Lit := [(27, false), (64, false), (125, false), (15, true)]
theorem step2397 (p : Nat → Bool) (h : Constraints p) : clause p c2397 = true :=
  Snake9.LocalRup.prove_clause [c1816, c322] c2397 (by decide) p (sat_cons (step1816 p h) (sat_cons (step322 p h) (sat_nil p)))
def c2398 : List Lit := [(68, false), (47, false), (18, false), (50, false)]
theorem step2398 (p : Nat → Bool) (h : Constraints p) : clause p c2398 = true :=
  Snake9.LocalRup.prove_clause [c234, c235, c1849] c2398 (by decide) p (sat_cons (step234 p h) (sat_cons (step235 p h) (sat_cons (step1849 p h) (sat_nil p))))
def c2399 : List Lit := [(1807, false), (1827, true)]
theorem step2399 (p : Nat → Bool) (h : Constraints p) : clause p c2399 = true :=
  Snake9.LocalRup.prove_clause [c2366, c1510, c2295, c1473, c1504, c1428, c1494, c2305, c2267, c2032, c1741, c1406, c1732, c1404, c1398, c535, c536, c1388] c2399 (by decide) p (sat_cons (step2366 p h) (sat_cons (step1510 p h) (sat_cons (step2295 p h) (sat_cons (step1473 p h) (sat_cons (step1504 p h) (sat_cons (step1428 p h) (sat_cons (step1494 p h) (sat_cons (step2305 p h) (sat_cons (step2267 p h) (sat_cons (step2032 p h) (sat_cons (step1741 p h) (sat_cons (step1406 p h) (sat_cons (step1732 p h) (sat_cons (step1404 p h) (sat_cons (step1398 p h) (sat_cons (step535 p h) (sat_cons (step536 p h) (sat_cons (step1388 p h) (sat_nil p)))))))))))))))))))
def c2400 : List Lit := [(1807, false), (1817, true), (88, false), (37, false)]
theorem step2400 (p : Nat → Bool) (h : Constraints p) : clause p c2400 = true :=
  Snake9.LocalRup.prove_clause [c2267, c2032, c510] c2400 (by decide) p (sat_cons (step2267 p h) (sat_cons (step2032 p h) (sat_cons (step510 p h) (sat_nil p))))
def c2401 : List Lit := [(1827, true), (1773, false)]
theorem step2401 (p : Nat → Bool) (h : Constraints p) : clause p c2401 = true :=
  Snake9.LocalRup.prove_clause [c1392, c1510, c2399, c2295, c2033, c1473, c1401, c1504, c1408, c1420, c1419, c1424, c1409, c1497, c1395, c1404, c1477, c1386, c1387, c1783, c533] c2401 (by decide) p (sat_cons (step1392 p h) (sat_cons (step1510 p h) (sat_cons (step2399 p h) (sat_cons (step2295 p h) (sat_cons (step2033 p h) (sat_cons (step1473 p h) (sat_cons (step1401 p h) (sat_cons (step1504 p h) (sat_cons (step1408 p h) (sat_cons (step1420 p h) (sat_cons (step1419 p h) (sat_cons (step1424 p h) (sat_cons (step1409 p h) (sat_cons (step1497 p h) (sat_cons (step1395 p h) (sat_cons (step1404 p h) (sat_cons (step1477 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step1783 p h) (sat_cons (step533 p h) (sat_nil p))))))))))))))))))))))
def c2402 : List Lit := [(1849, true), (1827, false), (1797, false), (1788, false), (1725, false), (1735, false)]
theorem step2402 (p : Nat → Bool) (h : Constraints p) : clause p c2402 = true :=
  Snake9.LocalRup.prove_clause [c1444, c1476, c1345, c1366, c1547, c1553, c1511, c2386, c1498, c1367, c2295, c1482, c1346, c1447, c1337, c1339, c1439, c1334, c1335, c1333, c442, c2277] c2402 (by decide) p (sat_cons (step1444 p h) (sat_cons (step1476 p h) (sat_cons (step1345 p h) (sat_cons (step1366 p h) (sat_cons (step1547 p h) (sat_cons (step1553 p h) (sat_cons (step1511 p h) (sat_cons (step2386 p h) (sat_cons (step1498 p h) (sat_cons (step1367 p h) (sat_cons (step2295 p h) (sat_cons (step1482 p h) (sat_cons (step1346 p h) (sat_cons (step1447 p h) (sat_cons (step1337 p h) (sat_cons (step1339 p h) (sat_cons (step1439 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step1333 p h) (sat_cons (step442 p h) (sat_cons (step2277 p h) (sat_nil p)))))))))))))))))))))))
def c2403 : List Lit := [(1789, true), (88, false), (92, false), (93, false), (1771, false), (1748, true), (1830, true)]
theorem step2403 (p : Nat → Bool) (h : Constraints p) : clause p c2403 = true :=
  Snake9.LocalRup.prove_clause [c450, c2318, c2277, c2276, c441, c442, c2083] c2403 (by decide) p (sat_cons (step450 p h) (sat_cons (step2318 p h) (sat_cons (step2277 p h) (sat_cons (step2276 p h) (sat_cons (step441 p h) (sat_cons (step442 p h) (sat_cons (step2083 p h) (sat_nil p))))))))
def c2404 : List Lit := [(1827, true), (1799, false), (1788, false)]
theorem step2404 (p : Nat → Bool) (h : Constraints p) : clause p c2404 = true :=
  Snake9.LocalRup.prove_clause [c1510, c1497, c2295, c1477] c2404 (by decide) p (sat_cons (step1510 p h) (sat_cons (step1497 p h) (sat_cons (step2295 p h) (sat_cons (step1477 p h) (sat_nil p)))))
def c2405 : List Lit := [(39, false), (1641, true), (40, true), (35, false), (4, false), (52, true)]
theorem step2405 (p : Nat → Bool) (h : Constraints p) : clause p c2405 = true :=
  Snake9.LocalRup.prove_clause [c145, c1835, c1157, c2104, c1162] c2405 (by decide) p (sat_cons (step145 p h) (sat_cons (step1835 p h) (sat_cons (step1157 p h) (sat_cons (step2104 p h) (sat_cons (step1162 p h) (sat_nil p))))))
def c2406 : List Lit := [(1828, true), (117, false), (1789, false), (88, false)]
theorem step2406 (p : Nat → Bool) (h : Constraints p) : clause p c2406 = true :=
  Snake9.LocalRup.prove_clause [c2386, c1505, c1444, c1783, c2061, c1442, c710, c1624, c1945] c2406 (by decide) p (sat_cons (step2386 p h) (sat_cons (step1505 p h) (sat_cons (step1444 p h) (sat_cons (step1783 p h) (sat_cons (step2061 p h) (sat_cons (step1442 p h) (sat_cons (step710 p h) (sat_cons (step1624 p h) (sat_cons (step1945 p h) (sat_nil p))))))))))
def c2407 : List Lit := [(1659, true), (67, false), (1707, true), (1635, false), (35, false), (52, true)]
theorem step2407 (p : Nat → Bool) (h : Constraints p) : clause p c2407 = true :=
  Snake9.LocalRup.prove_clause [c1281, c1280, c2369, c2367, c324, c312, c1874] c2407 (by decide) p (sat_cons (step1281 p h) (sat_cons (step1280 p h) (sat_cons (step2369 p h) (sat_cons (step2367 p h) (sat_cons (step324 p h) (sat_cons (step312 p h) (sat_cons (step1874 p h) (sat_nil p))))))))
def c2408 : List Lit := [(1725, true), (58, false), (73, true)]
theorem step2408 (p : Nat → Bool) (h : Constraints p) : clause p c2408 = true :=
  Snake9.LocalRup.prove_clause [c2231, c1294, c2004, c2300, c1311, c1287, c2329, c1305, c1303, c1285, c1296, c1297, c1298, c369, c376, c1896] c2408 (by decide) p (sat_cons (step2231 p h) (sat_cons (step1294 p h) (sat_cons (step2004 p h) (sat_cons (step2300 p h) (sat_cons (step1311 p h) (sat_cons (step1287 p h) (sat_cons (step2329 p h) (sat_cons (step1305 p h) (sat_cons (step1303 p h) (sat_cons (step1285 p h) (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step369 p h) (sat_cons (step376 p h) (sat_cons (step1896 p h) (sat_nil p)))))))))))))))))
def c2409 : List Lit := [(38, false), (39, true), (58, true), (168, true), (50, true), (34, true)]
theorem step2409 (p : Nat → Bool) (h : Constraints p) : clause p c2409 = true :=
  Snake9.LocalRup.prove_clause [c1832, c1834, c1600, c179] c2409 (by decide) p (sat_cons (step1832 p h) (sat_cons (step1834 p h) (sat_cons (step1600 p h) (sat_cons (step179 p h) (sat_nil p)))))
def c2410 : List Lit := [(1817, false), (1827, true)]
theorem step2410 (p : Nat → Bool) (h : Constraints p) : clause p c2410 = true :=
  Snake9.LocalRup.prove_clause [c2366, c1494] c2410 (by decide) p (sat_cons (step2366 p h) (sat_cons (step1494 p h) (sat_nil p)))
def c2411 : List Lit := [(1818, false), (1828, true)]
theorem step2411 (p : Nat → Bool) (h : Constraints p) : clause p c2411 = true :=
  Snake9.LocalRup.prove_clause [c2366, c1495] c2411 (by decide) p (sat_cons (step2366 p h) (sat_cons (step1495 p h) (sat_nil p)))
def c2412 : List Lit := [(1555, true), (6, false), (8, false), (4, false)]
theorem step2412 (p : Nat → Bool) (h : Constraints p) : clause p c2412 = true :=
  Snake9.LocalRup.prove_clause [c1011, c2055, c1589, c1795] c2412 (by decide) p (sat_cons (step1011 p h) (sat_cons (step2055 p h) (sat_cons (step1589 p h) (sat_cons (step1795 p h) (sat_nil p)))))
end B112E036
