import B112E105Part0007
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2441 : List Lit := [(22, true), (1561, true), (24, true), (16, true), (275, true)]
theorem step2441 (p : Nat → Bool) (h : Constraints p) : clause p c2441 = true :=
  Snake9.LocalRup.prove_clause [c1027, c1012, c1010, c1008, c18, c1273, c1025, c1021, c1019, c1016, c1299, c2069, c2001, c34, c1356, c1276, c1284, c1281] c2441 (by decide) p (sat_cons (step1027 p h) (sat_cons (step1012 p h) (sat_cons (step1010 p h) (sat_cons (step1008 p h) (sat_cons (step18 p h) (sat_cons (step1273 p h) (sat_cons (step1025 p h) (sat_cons (step1021 p h) (sat_cons (step1019 p h) (sat_cons (step1016 p h) (sat_cons (step1299 p h) (sat_cons (step2069 p h) (sat_cons (step2001 p h) (sat_cons (step34 p h) (sat_cons (step1356 p h) (sat_cons (step1276 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_nil p)))))))))))))))))))
def c2442 : List Lit := [(1586, true), (329, true)]
theorem step2442 (p : Nat → Bool) (h : Constraints p) : clause p c2442 = true :=
  Snake9.LocalRup.prove_clause [c1076, c1073, c1075, c1074, c1389, c2338, c2388, c2341] c2442 (by decide) p (sat_cons (step1076 p h) (sat_cons (step1073 p h) (sat_cons (step1075 p h) (sat_cons (step1074 p h) (sat_cons (step1389 p h) (sat_cons (step2338 p h) (sat_cons (step2388 p h) (sat_cons (step2341 p h) (sat_nil p)))))))))
def c2443 : List Lit := [(60, true), (365, true), (1605, true), (1598, true), (1596, false), (1620, true), (1582, false), (35, false), (37, false)]
theorem step2443 (p : Nat → Bool) (h : Constraints p) : clause p c2443 = true :=
  Snake9.LocalRup.prove_clause [c1118, c1082, c1067, c1065, c1064, c1116, c1113, c1094, c1087, c1084, c1423, c1420, c1421, c1422, c1425, c1435, c1417, c1467, c1394, c1371, c161, c160, c158, c1874, c2342] c2443 (by decide) p (sat_cons (step1118 p h) (sat_cons (step1082 p h) (sat_cons (step1067 p h) (sat_cons (step1065 p h) (sat_cons (step1064 p h) (sat_cons (step1116 p h) (sat_cons (step1113 p h) (sat_cons (step1094 p h) (sat_cons (step1087 p h) (sat_cons (step1084 p h) (sat_cons (step1423 p h) (sat_cons (step1420 p h) (sat_cons (step1421 p h) (sat_cons (step1422 p h) (sat_cons (step1425 p h) (sat_cons (step1435 p h) (sat_cons (step1417 p h) (sat_cons (step1467 p h) (sat_cons (step1394 p h) (sat_cons (step1371 p h) (sat_cons (step161 p h) (sat_cons (step160 p h) (sat_cons (step158 p h) (sat_cons (step1874 p h) (sat_cons (step2342 p h) (sat_nil p))))))))))))))))))))))))))
def c2444 : List Lit := [(1596, true), (188, true), (176, true), (59, false), (60, false)]
theorem step2444 (p : Nat → Bool) (h : Constraints p) : clause p c2444 = true :=
  Snake9.LocalRup.prove_clause [c1408, c2021, c1405, c2040] c2444 (by decide) p (sat_cons (step1408 p h) (sat_cons (step2021 p h) (sat_cons (step1405 p h) (sat_cons (step2040 p h) (sat_nil p)))))
def c2445 : List Lit := [(1594, true), (161, true), (176, true), (106, true), (50, false), (56, false), (1572, true)]
theorem step2445 (p : Nat → Bool) (h : Constraints p) : clause p c2445 = true :=
  Snake9.LocalRup.prove_clause [c1367, c1366, c1405, c1406, c289, c258, c158, c159, c254, c161, c217, c2103] c2445 (by decide) p (sat_cons (step1367 p h) (sat_cons (step1366 p h) (sat_cons (step1405 p h) (sat_cons (step1406 p h) (sat_cons (step289 p h) (sat_cons (step258 p h) (sat_cons (step158 p h) (sat_cons (step159 p h) (sat_cons (step254 p h) (sat_cons (step161 p h) (sat_cons (step217 p h) (sat_cons (step2103 p h) (sat_nil p)))))))))))))
def c2446 : List Lit := [(2, true), (1523, false), (13, false), (130, true), (137, true), (155, true), (24, true), (1561, true), (35, false)]
theorem step2446 (p : Nat → Bool) (h : Constraints p) : clause p c2446 = true :=
  Snake9.LocalRup.prove_clause [c2249, c1291, c33, c1270, c1271, c1287, c1265, c1266, c1356, c15, c16, c44, c2009, c1295, c2008, c1303, c1312, c1328, c1315] c2446 (by decide) p (sat_cons (step2249 p h) (sat_cons (step1291 p h) (sat_cons (step33 p h) (sat_cons (step1270 p h) (sat_cons (step1271 p h) (sat_cons (step1287 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step1356 p h) (sat_cons (step15 p h) (sat_cons (step16 p h) (sat_cons (step44 p h) (sat_cons (step2009 p h) (sat_cons (step1295 p h) (sat_cons (step2008 p h) (sat_cons (step1303 p h) (sat_cons (step1312 p h) (sat_cons (step1328 p h) (sat_cons (step1315 p h) (sat_nil p))))))))))))))))))))
def c2447 : List Lit := [(1513, true), (2, false), (13, false), (151, true), (155, true), (275, true), (24, true), (1551, true), (35, false)]
theorem step2447 (p : Nat → Bool) (h : Constraints p) : clause p c2447 = true :=
  Snake9.LocalRup.prove_clause [c1025, c1021, c1019, c1016, c33, c1027, c1013, c1006, c1005, c1012, c1010, c1009, c1265, c1266, c15, c16, c2311, c44, c2009, c2061, c1295, c2008, c1303, c1312, c2310, c1329, c1318, c36, c1310] c2447 (by decide) p (sat_cons (step1025 p h) (sat_cons (step1021 p h) (sat_cons (step1019 p h) (sat_cons (step1016 p h) (sat_cons (step33 p h) (sat_cons (step1027 p h) (sat_cons (step1013 p h) (sat_cons (step1006 p h) (sat_cons (step1005 p h) (sat_cons (step1012 p h) (sat_cons (step1010 p h) (sat_cons (step1009 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step15 p h) (sat_cons (step16 p h) (sat_cons (step2311 p h) (sat_cons (step44 p h) (sat_cons (step2009 p h) (sat_cons (step2061 p h) (sat_cons (step1295 p h) (sat_cons (step2008 p h) (sat_cons (step1303 p h) (sat_cons (step1312 p h) (sat_cons (step2310 p h) (sat_cons (step1329 p h) (sat_cons (step1318 p h) (sat_cons (step36 p h) (sat_cons (step1310 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2448 : List Lit := [(305, true), (58, true), (24, true), (1561, true), (16, true), (35, false)]
theorem step2448 (p : Nat → Bool) (h : Constraints p) : clause p c2448 = true :=
  Snake9.LocalRup.prove_clause [c1274, c2000, c1351, c2249, c1056, c1058, c1051, c1053, c1025, c1027, c2441, c1048, c1049, c1037, c1021, c1012, c1046, c1042, c1034, c1019, c1010, c1045, c1041, c1032, c1016, c1008, c1009, c81, c80, c18, c2071, c1273, c33, c1280, c1291, c1269, c2446, c2447, c1268, c1287, c1356, c2001, c1298, c76, c2369, c1310, c44, c1317, c1295, c1328, c1303] c2448 (by decide) p (sat_cons (step1274 p h) (sat_cons (step2000 p h) (sat_cons (step1351 p h) (sat_cons (step2249 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1051 p h) (sat_cons (step1053 p h) (sat_cons (step1025 p h) (sat_cons (step1027 p h) (sat_cons (step2441 p h) (sat_cons (step1048 p h) (sat_cons (step1049 p h) (sat_cons (step1037 p h) (sat_cons (step1021 p h) (sat_cons (step1012 p h) (sat_cons (step1046 p h) (sat_cons (step1042 p h) (sat_cons (step1034 p h) (sat_cons (step1019 p h) (sat_cons (step1010 p h) (sat_cons (step1045 p h) (sat_cons (step1041 p h) (sat_cons (step1032 p h) (sat_cons (step1016 p h) (sat_cons (step1008 p h) (sat_cons (step1009 p h) (sat_cons (step81 p h) (sat_cons (step80 p h) (sat_cons (step18 p h) (sat_cons (step2071 p h) (sat_cons (step1273 p h) (sat_cons (step33 p h) (sat_cons (step1280 p h) (sat_cons (step1291 p h) (sat_cons (step1269 p h) (sat_cons (step2446 p h) (sat_cons (step2447 p h) (sat_cons (step1268 p h) (sat_cons (step1287 p h) (sat_cons (step1356 p h) (sat_cons (step2001 p h) (sat_cons (step1298 p h) (sat_cons (step76 p h) (sat_cons (step2369 p h) (sat_cons (step1310 p h) (sat_cons (step44 p h) (sat_cons (step1317 p h) (sat_cons (step1295 p h) (sat_cons (step1328 p h) (sat_cons (step1303 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2449 : List Lit := [(1550, true), (22, false), (58, true), (24, true)]
theorem step2449 (p : Nat → Bool) (h : Constraints p) : clause p c2449 = true :=
  Snake9.LocalRup.prove_clause [c1324, c2001, c1320, c1298, c2361, c76, c1310, c1311, c1317, c1318, c1328, c1313, c1303, c1295, c1296, c121, c57, c114] c2449 (by decide) p (sat_cons (step1324 p h) (sat_cons (step2001 p h) (sat_cons (step1320 p h) (sat_cons (step1298 p h) (sat_cons (step2361 p h) (sat_cons (step76 p h) (sat_cons (step1310 p h) (sat_cons (step1311 p h) (sat_cons (step1317 p h) (sat_cons (step1318 p h) (sat_cons (step1328 p h) (sat_cons (step1313 p h) (sat_cons (step1303 p h) (sat_cons (step1295 p h) (sat_cons (step1296 p h) (sat_cons (step121 p h) (sat_cons (step57 p h) (sat_cons (step114 p h) (sat_nil p)))))))))))))))))))
def c2450 : List Lit := [(1698, true), (108, false), (1654, false), (71, true), (205, true)]
theorem step2450 (p : Nat → Bool) (h : Constraints p) : clause p c2450 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1534, c1545, c1626, c1620, c1546, c1587, c1537, c2372, c1528] c2450 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1534 p h) (sat_cons (step1545 p h) (sat_cons (step1626 p h) (sat_cons (step1620 p h) (sat_cons (step1546 p h) (sat_cons (step1587 p h) (sat_cons (step1537 p h) (sat_cons (step2372 p h) (sat_cons (step1528 p h) (sat_nil p)))))))))))
def c2451 : List Lit := [(1748, true), (66, false), (121, false)]
theorem step2451 (p : Nat → Bool) (h : Constraints p) : clause p c2451 = true :=
  Snake9.LocalRup.prove_clause [c2346, c887, c889, c1705, c1708, c1714] c2451 (by decide) p (sat_cons (step2346 p h) (sat_cons (step887 p h) (sat_cons (step889 p h) (sat_cons (step1705 p h) (sat_cons (step1708 p h) (sat_cons (step1714 p h) (sat_nil p)))))))
def c2452 : List Lit := [(123, true), (1748, true), (118, false), (60, false)]
theorem step2452 (p : Nat → Bool) (h : Constraints p) : clause p c2452 = true :=
  Snake9.LocalRup.prove_clause [c1712, c1708, c1710, c1714, c836, c1705] c2452 (by decide) p (sat_cons (step1712 p h) (sat_cons (step1708 p h) (sat_cons (step1710 p h) (sat_cons (step1714 p h) (sat_cons (step836 p h) (sat_cons (step1705 p h) (sat_nil p)))))))
def c2453 : List Lit := [(1698, true), (1740, true), (1654, false), (71, true), (205, true)]
theorem step2453 (p : Nat → Bool) (h : Constraints p) : clause p c2453 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1534, c1545, c1626, c1620, c2450, c1546, c1692, c1535, c1700, c1530, c1695, c1990] c2453 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1534 p h) (sat_cons (step1545 p h) (sat_cons (step1626 p h) (sat_cons (step1620 p h) (sat_cons (step2450 p h) (sat_cons (step1546 p h) (sat_cons (step1692 p h) (sat_cons (step1535 p h) (sat_cons (step1700 p h) (sat_cons (step1530 p h) (sat_cons (step1695 p h) (sat_cons (step1990 p h) (sat_nil p))))))))))))))
def c2454 : List Lit := [(78, false), (1730, true), (115, false), (118, false), (453, true)]
theorem step2454 (p : Nat → Bool) (h : Constraints p) : clause p c2454 = true :=
  Snake9.LocalRup.prove_clause [c1214, c1202, c1201, c1212, c1209, c1204, c844, c838, c841, c1993, c1659, c1680, c1664, c1662, c2295, c2399, c1660] c2454 (by decide) p (sat_cons (step1214 p h) (sat_cons (step1202 p h) (sat_cons (step1201 p h) (sat_cons (step1212 p h) (sat_cons (step1209 p h) (sat_cons (step1204 p h) (sat_cons (step844 p h) (sat_cons (step838 p h) (sat_cons (step841 p h) (sat_cons (step1993 p h) (sat_cons (step1659 p h) (sat_cons (step1680 p h) (sat_cons (step1664 p h) (sat_cons (step1662 p h) (sat_cons (step2295 p h) (sat_cons (step2399 p h) (sat_cons (step1660 p h) (sat_nil p))))))))))))))))))
def c2455 : List Lit := [(41, false), (61, true), (39, true), (165, true)]
theorem step2455 (p : Nat → Bool) (h : Constraints p) : clause p c2455 = true :=
  Snake9.LocalRup.prove_clause [c175, c176, c1875, c2096] c2455 (by decide) p (sat_cons (step175 p h) (sat_cons (step176 p h) (sat_cons (step1875 p h) (sat_cons (step2096 p h) (sat_nil p)))))
def c2456 : List Lit := [(1520, true), (1535, true), (58, true), (24, true)]
theorem step2456 (p : Nat → Bool) (h : Constraints p) : clause p c2456 = true :=
  Snake9.LocalRup.prove_clause [c1299, c1274, c1275, c2313, c27, c1016, c81, c1019, c1032, c1021, c1034, c1025, c1037, c2208, c1053] c2456 (by decide) p (sat_cons (step1299 p h) (sat_cons (step1274 p h) (sat_cons (step1275 p h) (sat_cons (step2313 p h) (sat_cons (step27 p h) (sat_cons (step1016 p h) (sat_cons (step81 p h) (sat_cons (step1019 p h) (sat_cons (step1032 p h) (sat_cons (step1021 p h) (sat_cons (step1034 p h) (sat_cons (step1025 p h) (sat_cons (step1037 p h) (sat_cons (step2208 p h) (sat_cons (step1053 p h) (sat_nil p))))))))))))))))
def c2457 : List Lit := [(1586, true), (58, true), (55, true)]
theorem step2457 (p : Nat → Bool) (h : Constraints p) : clause p c2457 = true :=
  Snake9.LocalRup.prove_clause [c1396, c2442, c1370, c1077, c2210, c1067, c1065, c1064, c2340, c1369, c2338, c1372, c1393, c181, c2002, c1382, c158, c1375, c2358] c2457 (by decide) p (sat_cons (step1396 p h) (sat_cons (step2442 p h) (sat_cons (step1370 p h) (sat_cons (step1077 p h) (sat_cons (step2210 p h) (sat_cons (step1067 p h) (sat_cons (step1065 p h) (sat_cons (step1064 p h) (sat_cons (step2340 p h) (sat_cons (step1369 p h) (sat_cons (step2338 p h) (sat_cons (step1372 p h) (sat_cons (step1393 p h) (sat_cons (step181 p h) (sat_cons (step2002 p h) (sat_cons (step1382 p h) (sat_cons (step158 p h) (sat_cons (step1375 p h) (sat_cons (step2358 p h) (sat_nil p))))))))))))))))))))
def c2458 : List Lit := [(1684, true), (215, true), (56, false), (123, false)]
theorem step2458 (p : Nat → Bool) (h : Constraints p) : clause p c2458 = true :=
  Snake9.LocalRup.prove_clause [c1575, c2373, c1573, c724] c2458 (by decide) p (sat_cons (step1575 p h) (sat_cons (step2373 p h) (sat_cons (step1573 p h) (sat_cons (step724 p h) (sat_nil p)))))
def c2459 : List Lit := [(1560, true), (19, false), (74, false), (76, false), (305, true)]
theorem step2459 (p : Nat → Bool) (h : Constraints p) : clause p c2459 = true :=
  Snake9.LocalRup.prove_clause [c1056, c1053, c1037, c1034, c1031, c2271, c2305, c1298, c1989, c66, c85, c2082] c2459 (by decide) p (sat_cons (step1056 p h) (sat_cons (step1053 p h) (sat_cons (step1037 p h) (sat_cons (step1034 p h) (sat_cons (step1031 p h) (sat_cons (step2271 p h) (sat_cons (step2305 p h) (sat_cons (step1298 p h) (sat_cons (step1989 p h) (sat_cons (step66 p h) (sat_cons (step85 p h) (sat_cons (step2082 p h) (sat_nil p)))))))))))))
def c2460 : List Lit := [(40, true), (331, true), (1587, true)]
theorem step2460 (p : Nat → Bool) (h : Constraints p) : clause p c2460 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1071, c1070, c1077, c1076, c1073, c1390, c2279, c2029, c2341] c2460 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1071 p h) (sat_cons (step1070 p h) (sat_cons (step1077 p h) (sat_cons (step1076 p h) (sat_cons (step1073 p h) (sat_cons (step1390 p h) (sat_cons (step2279 p h) (sat_cons (step2029 p h) (sat_cons (step2341 p h) (sat_nil p)))))))))))
def c2461 : List Lit := [(365, true), (62, true), (59, false), (60, false), (1587, true), (106, false)]
theorem step2461 (p : Nat → Bool) (h : Constraints p) : clause p c2461 = true :=
  Snake9.LocalRup.prove_clause [c1116, c1118, c1111, c1080, c1107, c1104, c1099, c2460, c330, c356, c353, c1883] c2461 (by decide) p (sat_cons (step1116 p h) (sat_cons (step1118 p h) (sat_cons (step1111 p h) (sat_cons (step1080 p h) (sat_cons (step1107 p h) (sat_cons (step1104 p h) (sat_cons (step1099 p h) (sat_cons (step2460 p h) (sat_cons (step330 p h) (sat_cons (step356 p h) (sat_cons (step353 p h) (sat_cons (step1883 p h) (sat_nil p)))))))))))))
def c2462 : List Lit := [(51, false), (61, false), (56, false), (1593, true)]
theorem step2462 (p : Nat → Bool) (h : Constraints p) : clause p c2462 = true :=
  Snake9.LocalRup.prove_clause [c236, c239, c1404] c2462 (by decide) p (sat_cons (step236 p h) (sat_cons (step239 p h) (sat_cons (step1404 p h) (sat_nil p))))
def c2463 : List Lit := [(1574, true), (30, false), (40, false)]
theorem step2463 (p : Nat → Bool) (h : Constraints p) : clause p c2463 = true :=
  Snake9.LocalRup.prove_clause [c1369, c1371, c1367, c126] c2463 (by decide) p (sat_cons (step1369 p h) (sat_cons (step1371 p h) (sat_cons (step1367 p h) (sat_cons (step126 p h) (sat_nil p)))))
def c2464 : List Lit := [(1596, true), (56, false)]
theorem step2464 (p : Nat → Bool) (h : Constraints p) : clause p c2464 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1410, c1405, c1406, c1402, c1403, c2018, c233, c295, c191, c207, c1084, c1087, c2319, c2212, c1089, c1092] c2464 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1405 p h) (sat_cons (step1406 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step2018 p h) (sat_cons (step233 p h) (sat_cons (step295 p h) (sat_cons (step191 p h) (sat_cons (step207 p h) (sat_cons (step1084 p h) (sat_cons (step1087 p h) (sat_cons (step2319 p h) (sat_cons (step2212 p h) (sat_cons (step1089 p h) (sat_cons (step1092 p h) (sat_nil p))))))))))))))))))
def c2465 : List Lit := [(52, false), (55, true), (176, true), (48, false), (49, false), (56, false)]
theorem step2465 (p : Nat → Bool) (h : Constraints p) : clause p c2465 = true :=
  Snake9.LocalRup.prove_clause [c191, c256, c254] c2465 (by decide) p (sat_cons (step191 p h) (sat_cons (step256 p h) (sat_cons (step254 p h) (sat_nil p))))
def c2466 : List Lit := [(1719, true), (104, false), (48, false)]
theorem step2466 (p : Nat → Bool) (h : Constraints p) : clause p c2466 = true :=
  Snake9.LocalRup.prove_clause [c1655, c1656, c615] c2466 (by decide) p (sat_cons (step1655 p h) (sat_cons (step1656 p h) (sat_cons (step615 p h) (sat_nil p))))
def c2467 : List Lit := [(1715, true), (117, false), (119, false), (225, true)]
theorem step2467 (p : Nat → Bool) (h : Constraints p) : clause p c2467 = true :=
  Snake9.LocalRup.prove_clause [c1647, c1649, c2302, c1644, c1645, c1641, c813, c545, c572] c2467 (by decide) p (sat_cons (step1647 p h) (sat_cons (step1649 p h) (sat_cons (step2302 p h) (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step1641 p h) (sat_cons (step813 p h) (sat_cons (step545 p h) (sat_cons (step572 p h) (sat_nil p))))))))))
def c2468 : List Lit := [(78, false), (71, false), (76, false), (202, true), (77, true), (118, true)]
theorem step2468 (p : Nat → Bool) (h : Constraints p) : clause p c2468 = true :=
  Snake9.LocalRup.prove_clause [c453, c457] c2468 (by decide) p (sat_cons (step453 p h) (sat_cons (step457 p h) (sat_nil p)))
def c2469 : List Lit := [(1684, true), (97, false), (217, true), (101, false)]
theorem step2469 (p : Nat → Bool) (h : Constraints p) : clause p c2469 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1577, c1572, c1569, c524, c544, c543, c2157] c2469 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1577 p h) (sat_cons (step1572 p h) (sat_cons (step1569 p h) (sat_cons (step524 p h) (sat_cons (step544 p h) (sat_cons (step543 p h) (sat_cons (step2157 p h) (sat_nil p)))))))))
def c2470 : List Lit := [(1604, true), (40, false), (58, false)]
theorem step2470 (p : Nat → Bool) (h : Constraints p) : clause p c2470 = true :=
  Snake9.LocalRup.prove_clause [c1422, c1424, c1420, c1416, c330] c2470 (by decide) p (sat_cons (step1422 p h) (sat_cons (step1424 p h) (sat_cons (step1420 p h) (sat_cons (step1416 p h) (sat_cons (step330 p h) (sat_nil p))))))
def c2471 : List Lit := [(1684, true), (56, false), (489, true), (1730, true), (117, true), (1719, false)]
theorem step2471 (p : Nat → Bool) (h : Constraints p) : clause p c2471 = true :=
  Snake9.LocalRup.prove_clause [c1257, c1185, c1180, c1176, c1174, c1171, c1173, c1172, c1255, c1252, c1216, c1214, c1202, c1201, c1575, c2012, c2373, c1573, c1993, c721, c1680, c1658, c1664] c2471 (by decide) p (sat_cons (step1257 p h) (sat_cons (step1185 p h) (sat_cons (step1180 p h) (sat_cons (step1176 p h) (sat_cons (step1174 p h) (sat_cons (step1171 p h) (sat_cons (step1173 p h) (sat_cons (step1172 p h) (sat_cons (step1255 p h) (sat_cons (step1252 p h) (sat_cons (step1216 p h) (sat_cons (step1214 p h) (sat_cons (step1202 p h) (sat_cons (step1201 p h) (sat_cons (step1575 p h) (sat_cons (step2012 p h) (sat_cons (step2373 p h) (sat_cons (step1573 p h) (sat_cons (step1993 p h) (sat_cons (step721 p h) (sat_cons (step1680 p h) (sat_cons (step1658 p h) (sat_cons (step1664 p h) (sat_nil p))))))))))))))))))))))))
def c2472 : List Lit := [(1715, true), (100, false), (93, false)]
theorem step2472 (p : Nat → Bool) (h : Constraints p) : clause p c2472 = true :=
  Snake9.LocalRup.prove_clause [c1647, c1649, c1645, c1641, c562] c2472 (by decide) p (sat_cons (step1647 p h) (sat_cons (step1649 p h) (sat_cons (step1645 p h) (sat_cons (step1641 p h) (sat_cons (step562 p h) (sat_nil p))))))
def c2473 : List Lit := [(85, false), (1725, true), (104, false), (48, false)]
theorem step2473 (p : Nat → Bool) (h : Constraints p) : clause p c2473 = true :=
  Snake9.LocalRup.prove_clause [c611, c2046] c2473 (by decide) p (sat_cons (step611 p h) (sat_cons (step2046 p h) (sat_nil p)))
def c2474 : List Lit := [(55, false), (37, false), (172, true), (61, false), (1598, true), (56, false)]
theorem step2474 (p : Nat → Bool) (h : Constraints p) : clause p c2474 = true :=
  Snake9.LocalRup.prove_clause [c2342, c286] c2474 (by decide) p (sat_cons (step2342 p h) (sat_cons (step286 p h) (sat_nil p)))
def c2475 : List Lit := [(1586, true), (55, true), (37, false)]
theorem step2475 (p : Nat → Bool) (h : Constraints p) : clause p c2475 = true :=
  Snake9.LocalRup.prove_clause [c1396, c2442, c1077, c2210, c1067, c1065, c1064, c159, c2340, c158, c1372, c1873] c2475 (by decide) p (sat_cons (step1396 p h) (sat_cons (step2442 p h) (sat_cons (step1077 p h) (sat_cons (step2210 p h) (sat_cons (step1067 p h) (sat_cons (step1065 p h) (sat_cons (step1064 p h) (sat_cons (step159 p h) (sat_cons (step2340 p h) (sat_cons (step158 p h) (sat_cons (step1372 p h) (sat_cons (step1873 p h) (sat_nil p)))))))))))))
def c2476 : List Lit := [(1699, true), (1655, false), (1676, false), (112, false), (56, false)]
theorem step2476 (p : Nat → Bool) (h : Constraints p) : clause p c2476 = true :=
  Snake9.LocalRup.prove_clause [c1548, c1587, c1627, c1621, c1549, c1588, c1532, c1575, c1530, c1573, c716] c2476 (by decide) p (sat_cons (step1548 p h) (sat_cons (step1587 p h) (sat_cons (step1627 p h) (sat_cons (step1621 p h) (sat_cons (step1549 p h) (sat_cons (step1588 p h) (sat_cons (step1532 p h) (sat_cons (step1575 p h) (sat_cons (step1530 p h) (sat_cons (step1573 p h) (sat_cons (step716 p h) (sat_nil p))))))))))))
def c2477 : List Lit := [(1559, true)]
theorem step2477 (p : Nat → Bool) (h : Constraints p) : clause p c2477 = true :=
  Snake9.LocalRup.prove_clause [c2243, c2315, c2001, c1299] c2477 (by decide) p (sat_cons (step2243 p h) (sat_cons (step2315 p h) (sat_cons (step2001 p h) (sat_cons (step1299 p h) (sat_nil p)))))
def c2478 : List Lit := [(85, true), (71, false), (72, false), (76, false), (1561, true), (67, true), (1677, true)]
theorem step2478 (p : Nat → Bool) (h : Constraints p) : clause p c2478 = true :=
  Snake9.LocalRup.prove_clause [c1562, c1558, c1560, c1564, c1555, c1556, c460, c457, c417, c414, c1138, c419, c1139, c1274, c2222, c2000, c1143, c2385, c1142, c440] c2478 (by decide) p (sat_cons (step1562 p h) (sat_cons (step1558 p h) (sat_cons (step1560 p h) (sat_cons (step1564 p h) (sat_cons (step1555 p h) (sat_cons (step1556 p h) (sat_cons (step460 p h) (sat_cons (step457 p h) (sat_cons (step417 p h) (sat_cons (step414 p h) (sat_cons (step1138 p h) (sat_cons (step419 p h) (sat_cons (step1139 p h) (sat_cons (step1274 p h) (sat_cons (step2222 p h) (sat_cons (step2000 p h) (sat_cons (step1143 p h) (sat_cons (step2385 p h) (sat_cons (step1142 p h) (sat_cons (step440 p h) (sat_nil p)))))))))))))))))))))
def c2479 : List Lit := [(1536, false), (1551, true)]
theorem step2479 (p : Nat → Bool) (h : Constraints p) : clause p c2479 = true :=
  Snake9.LocalRup.prove_clause [c1302, c2386] c2479 (by decide) p (sat_cons (step1302 p h) (sat_cons (step2386 p h) (sat_nil p)))
def c2480 : List Lit := [(1717, false), (1767, true), (1724, false), (104, false), (48, false), (1740, false), (1745, false)]
theorem step2480 (p : Nat → Bool) (h : Constraints p) : clause p c2480 = true :=
  Snake9.LocalRup.prove_clause [c1711, c1729, c1785, c1686, c1685, c2044, c1777, c1706, c1730, c1714] c2480 (by decide) p (sat_cons (step1711 p h) (sat_cons (step1729 p h) (sat_cons (step1785 p h) (sat_cons (step1686 p h) (sat_cons (step1685 p h) (sat_cons (step2044 p h) (sat_cons (step1777 p h) (sat_cons (step1706 p h) (sat_cons (step1730 p h) (sat_cons (step1714 p h) (sat_nil p)))))))))))
def c2481 : List Lit := [(1748, true), (1658, true), (106, false), (85, true), (1677, true), (123, true)]
theorem step2481 (p : Nat → Bool) (h : Constraints p) : clause p c2481 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1564, c1556, c1555, c1562, c1560, c1708, c1712, c1714, c1710, c1705, c846, c897, c444, c2045, c471, c1159, c460, c1162, c1528, c2225, c401, c1158, c455, c1155] c2481 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1564 p h) (sat_cons (step1556 p h) (sat_cons (step1555 p h) (sat_cons (step1562 p h) (sat_cons (step1560 p h) (sat_cons (step1708 p h) (sat_cons (step1712 p h) (sat_cons (step1714 p h) (sat_cons (step1710 p h) (sat_cons (step1705 p h) (sat_cons (step846 p h) (sat_cons (step897 p h) (sat_cons (step444 p h) (sat_cons (step2045 p h) (sat_cons (step471 p h) (sat_cons (step1159 p h) (sat_cons (step460 p h) (sat_cons (step1162 p h) (sat_cons (step1528 p h) (sat_cons (step2225 p h) (sat_cons (step401 p h) (sat_cons (step1158 p h) (sat_cons (step455 p h) (sat_cons (step1155 p h) (sat_nil p))))))))))))))))))))))))))
def c2482 : List Lit := [(95, false), (1684, true), (118, true), (106, false)]
theorem step2482 (p : Nat → Bool) (h : Constraints p) : clause p c2482 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1570, c1575, c1572, c2012, c491, c539, c1172, c536, c1173, c1190, c1176, c1191, c1180, c1199, c1185, c1218, c2241, c1252] c2482 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1570 p h) (sat_cons (step1575 p h) (sat_cons (step1572 p h) (sat_cons (step2012 p h) (sat_cons (step491 p h) (sat_cons (step539 p h) (sat_cons (step1172 p h) (sat_cons (step536 p h) (sat_cons (step1173 p h) (sat_cons (step1190 p h) (sat_cons (step1176 p h) (sat_cons (step1191 p h) (sat_cons (step1180 p h) (sat_cons (step1199 p h) (sat_cons (step1185 p h) (sat_cons (step1218 p h) (sat_cons (step2241 p h) (sat_cons (step1252 p h) (sat_nil p))))))))))))))))))))
def c2483 : List Lit := [(1713, true), (225, true), (217, true), (95, true), (1684, true)]
theorem step2483 (p : Nat → Bool) (h : Constraints p) : clause p c2483 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1569, c1644, c1645, c2469, c2438, c572, c1910, c2151] c2483 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1569 p h) (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step2469 p h) (sat_cons (step2438 p h) (sat_cons (step572 p h) (sat_cons (step1910 p h) (sat_cons (step2151 p h) (sat_nil p))))))))))
def c2484 : List Lit := [(101, false), (94, true), (225, true), (217, true), (1684, true)]
theorem step2484 (p : Nat → Bool) (h : Constraints p) : clause p c2484 = true :=
  Snake9.LocalRup.prove_clause [c2469, c572] c2484 (by decide) p (sat_cons (step2469 p h) (sat_cons (step572 p h) (sat_nil p)))
def c2485 : List Lit := [(1596, true), (172, true), (47, true), (104, true)]
theorem step2485 (p : Nat → Bool) (h : Constraints p) : clause p c2485 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1410, c1405, c1403, c2018, c205] c2485 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1405 p h) (sat_cons (step1403 p h) (sat_cons (step2018 p h) (sat_cons (step205 p h) (sat_nil p)))))))
def c2486 : List Lit := [(1621, true), (331, true), (58, false), (115, false), (61, true), (1600, false), (1596, false)]
theorem step2486 (p : Nat → Bool) (h : Constraints p) : clause p c2486 = true :=
  Snake9.LocalRup.prove_clause [c1077, c2442, c1419, c1425, c1436, c1462, c1468, c1437, c2460, c1426, c334, c1421] c2486 (by decide) p (sat_cons (step1077 p h) (sat_cons (step2442 p h) (sat_cons (step1419 p h) (sat_cons (step1425 p h) (sat_cons (step1436 p h) (sat_cons (step1462 p h) (sat_cons (step1468 p h) (sat_cons (step1437 p h) (sat_cons (step2460 p h) (sat_cons (step1426 p h) (sat_cons (step334 p h) (sat_cons (step1421 p h) (sat_nil p)))))))))))))
def c2487 : List Lit := [(64, true), (72, true), (1667, true), (104, true), (67, true)]
theorem step2487 (p : Nat → Bool) (h : Constraints p) : clause p c2487 = true :=
  Snake9.LocalRup.prove_clause [c1526, c1534, c1549, c1523, c1524, c1546, c1518, c1537, c1535, c393, c1528, c1530, c403] c2487 (by decide) p (sat_cons (step1526 p h) (sat_cons (step1534 p h) (sat_cons (step1549 p h) (sat_cons (step1523 p h) (sat_cons (step1524 p h) (sat_cons (step1546 p h) (sat_cons (step1518 p h) (sat_cons (step1537 p h) (sat_cons (step1535 p h) (sat_cons (step393 p h) (sat_cons (step1528 p h) (sat_cons (step1530 p h) (sat_cons (step403 p h) (sat_nil p))))))))))))))
def c2488 : List Lit := [(72, false), (81, false), (83, false), (108, false), (67, true)]
theorem step2488 (p : Nat → Bool) (h : Constraints p) : clause p c2488 = true :=
  Snake9.LocalRup.prove_clause [c460, c422, c414] c2488 (by decide) p (sat_cons (step460 p h) (sat_cons (step422 p h) (sat_cons (step414 p h) (sat_nil p))))
def c2489 : List Lit := [(64, false), (1623, true), (61, true), (56, true), (331, true), (58, false), (115, false), (1596, false)]
theorem step2489 (p : Nat → Bool) (h : Constraints p) : clause p c2489 = true :=
  Snake9.LocalRup.prove_clause [c335, c339, c338, c2460, c1421, c1418, c1470, c1429, c1438] c2489 (by decide) p (sat_cons (step335 p h) (sat_cons (step339 p h) (sat_cons (step338 p h) (sat_cons (step2460 p h) (sat_cons (step1421 p h) (sat_cons (step1418 p h) (sat_cons (step1470 p h) (sat_cons (step1429 p h) (sat_cons (step1438 p h) (sat_nil p))))))))))
def c2490 : List Lit := [(1665, true), (67, true), (104, true)]
theorem step2490 (p : Nat → Bool) (h : Constraints p) : clause p c2490 = true :=
  Snake9.LocalRup.prove_clause [c1540, c1544, c1532, c1534, c1521, c1530, c1527, c1518, c403, c393] c2490 (by decide) p (sat_cons (step1540 p h) (sat_cons (step1544 p h) (sat_cons (step1532 p h) (sat_cons (step1534 p h) (sat_cons (step1521 p h) (sat_cons (step1530 p h) (sat_cons (step1527 p h) (sat_cons (step1518 p h) (sat_cons (step403 p h) (sat_cons (step393 p h) (sat_nil p)))))))))))
def c2491 : List Lit := [(121, false), (1754, true), (83, false), (66, false)]
theorem step2491 (p : Nat → Bool) (h : Constraints p) : clause p c2491 = true :=
  Snake9.LocalRup.prove_clause [c878, c876, c877, c879, c1710, c1691, c1705, c1699, c1715, c1726] c2491 (by decide) p (sat_cons (step878 p h) (sat_cons (step876 p h) (sat_cons (step877 p h) (sat_cons (step879 p h) (sat_cons (step1710 p h) (sat_cons (step1691 p h) (sat_cons (step1705 p h) (sat_cons (step1699 p h) (sat_cons (step1715 p h) (sat_cons (step1726 p h) (sat_nil p)))))))))))
def c2492 : List Lit := [(1743, false), (122, true), (1753, true), (121, true), (234, true)]
theorem step2492 (p : Nat → Bool) (h : Constraints p) : clause p c2492 = true :=
  Snake9.LocalRup.prove_clause [c1709, c1721, c1714, c1715, c1725, c1710, c1697, c1699, c1695, c1691, c1692, c750, c697, c707] c2492 (by decide) p (sat_cons (step1709 p h) (sat_cons (step1721 p h) (sat_cons (step1714 p h) (sat_cons (step1715 p h) (sat_cons (step1725 p h) (sat_cons (step1710 p h) (sat_cons (step1697 p h) (sat_cons (step1699 p h) (sat_cons (step1695 p h) (sat_cons (step1691 p h) (sat_cons (step1692 p h) (sat_cons (step750 p h) (sat_cons (step697 p h) (sat_cons (step707 p h) (sat_nil p)))))))))))))))
def c2493 : List Lit := [(1719, true), (109, true), (229, true)]
theorem step2493 (p : Nat → Bool) (h : Constraints p) : clause p c2493 = true :=
  Snake9.LocalRup.prove_clause [c1655, c1656, c650, c651, c1912] c2493 (by decide) p (sat_cons (step1655 p h) (sat_cons (step1656 p h) (sat_cons (step650 p h) (sat_cons (step651 p h) (sat_cons (step1912 p h) (sat_nil p))))))
def c2494 : List Lit := [(103, false), (106, false), (1720, true), (108, false)]
theorem step2494 (p : Nat → Bool) (h : Constraints p) : clause p c2494 = true :=
  Snake9.LocalRup.prove_clause [c598, c595, c1657] c2494 (by decide) p (sat_cons (step598 p h) (sat_cons (step595 p h) (sat_cons (step1657 p h) (sat_nil p))))
def c2495 : List Lit := [(1713, true), (1712, true), (225, true), (121, true), (117, false)]
theorem step2495 (p : Nat → Bool) (h : Constraints p) : clause p c2495 = true :=
  Snake9.LocalRup.prove_clause [c1644, c1645, c571, c570, c526, c545, c1643] c2495 (by decide) p (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step571 p h) (sat_cons (step570 p h) (sat_cons (step526 p h) (sat_cons (step545 p h) (sat_cons (step1643 p h) (sat_nil p))))))))
def c2496 : List Lit := [(101, false), (95, false), (225, true), (121, true), (117, false)]
theorem step2496 (p : Nat → Bool) (h : Constraints p) : clause p c2496 = true :=
  Snake9.LocalRup.prove_clause [c571, c526] c2496 (by decide) p (sat_cons (step571 p h) (sat_cons (step526 p h) (sat_nil p)))
def c2497 : List Lit := [(7, false), (6, false), (4, false)]
theorem step2497 (p : Nat → Bool) (h : Constraints p) : clause p c2497 = true :=
  Snake9.LocalRup.prove_clause [c17, c19] c2497 (by decide) p (sat_cons (step17 p h) (sat_cons (step19 p h) (sat_nil p)))
def c2498 : List Lit := [(110, false), (1740, true), (123, false), (121, true), (122, false), (234, true), (55, true)]
theorem step2498 (p : Nat → Bool) (h : Constraints p) : clause p c2498 = true :=
  Snake9.LocalRup.prove_clause [c699, c2301, c708, c1695, c1692, c1700] c2498 (by decide) p (sat_cons (step699 p h) (sat_cons (step2301 p h) (sat_cons (step708 p h) (sat_cons (step1695 p h) (sat_cons (step1692 p h) (sat_cons (step1700 p h) (sat_nil p)))))))
def c2499 : List Lit := [(1752, true), (123, false), (121, true), (122, false), (234, true), (55, true)]
theorem step2499 (p : Nat → Bool) (h : Constraints p) : clause p c2499 = true :=
  Snake9.LocalRup.prove_clause [c1728, c1702, c2498, c1691, c1693, c1699, c1700, c1724, c1694, c1695, c1713, c709, c939, c1705, c918, c856] c2499 (by decide) p (sat_cons (step1728 p h) (sat_cons (step1702 p h) (sat_cons (step2498 p h) (sat_cons (step1691 p h) (sat_cons (step1693 p h) (sat_cons (step1699 p h) (sat_cons (step1700 p h) (sat_cons (step1724 p h) (sat_cons (step1694 p h) (sat_cons (step1695 p h) (sat_cons (step1713 p h) (sat_cons (step709 p h) (sat_cons (step939 p h) (sat_cons (step1705 p h) (sat_cons (step918 p h) (sat_cons (step856 p h) (sat_nil p)))))))))))))))))
def c2500 : List Lit := [(31, false), (40, false), (33, false), (155, true), (34, true)]
theorem step2500 (p : Nat → Bool) (h : Constraints p) : clause p c2500 = true :=
  Snake9.LocalRup.prove_clause [c130, c124] c2500 (by decide) p (sat_cons (step130 p h) (sat_cons (step124 p h) (sat_nil p)))
def c2501 : List Lit := [(1739, true), (121, true), (122, false), (234, true), (55, true)]
theorem step2501 (p : Nat → Bool) (h : Constraints p) : clause p c2501 = true :=
  Snake9.LocalRup.prove_clause [c1697, c1699, c1695, c1691, c710, c699] c2501 (by decide) p (sat_cons (step1697 p h) (sat_cons (step1699 p h) (sat_cons (step1695 p h) (sat_cons (step1691 p h) (sat_cons (step710 p h) (sat_cons (step699 p h) (sat_nil p)))))))
def c2502 : List Lit := [(1747, true), (121, false), (122, false)]
theorem step2502 (p : Nat → Bool) (h : Constraints p) : clause p c2502 = true :=
  Snake9.LocalRup.prove_clause [c1711, c1713, c1708, c1705, c909] c2502 (by decide) p (sat_cons (step1711 p h) (sat_cons (step1713 p h) (sat_cons (step1708 p h) (sat_cons (step1705 p h) (sat_cons (step909 p h) (sat_nil p))))))
def c2503 : List Lit := [(1752, true), (1747, false), (121, false)]
theorem step2503 (p : Nat → Bool) (h : Constraints p) : clause p c2503 = true :=
  Snake9.LocalRup.prove_clause [c1720, c1724, c2058, c1699, c1691] c2503 (by decide) p (sat_cons (step1720 p h) (sat_cons (step1724 p h) (sat_cons (step2058 p h) (sat_cons (step1699 p h) (sat_cons (step1691 p h) (sat_nil p))))))
def c2504 : List Lit := [(1752, true), (121, true), (246, true), (234, true), (55, true)]
theorem step2504 (p : Nat → Bool) (h : Constraints p) : clause p c2504 = true :=
  Snake9.LocalRup.prove_clause [c1728, c2043, c698, c699, c1920, c1695, c1697, c1700, c1724, c1692, c1711, c708, c1709] c2504 (by decide) p (sat_cons (step1728 p h) (sat_cons (step2043 p h) (sat_cons (step698 p h) (sat_cons (step699 p h) (sat_cons (step1920 p h) (sat_cons (step1695 p h) (sat_cons (step1697 p h) (sat_cons (step1700 p h) (sat_cons (step1724 p h) (sat_cons (step1692 p h) (sat_cons (step1711 p h) (sat_cons (step708 p h) (sat_cons (step1709 p h) (sat_nil p))))))))))))))
end B112E105
