import B112E260Part0005
namespace B112E260
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2487 : List Lit := [(437, false), (499, false)]
theorem step2487 (p : Nat → Bool) (h : Constraints p) : clause p c2487 = true :=
  Snake9.LocalRup.prove_clause [c2107, c1137] c2487 (by decide) p (sat_cons (step2107 p h) (sat_cons (step1137 p h) (sat_nil p)))
def c2488 : List Lit := [(377, false), (501, false)]
theorem step2488 (p : Nat → Bool) (h : Constraints p) : clause p c2488 = true :=
  Snake9.LocalRup.prove_clause [c1142, c1140] c2488 (by decide) p (sat_cons (step1142 p h) (sat_cons (step1140 p h) (sat_nil p)))
def c2489 : List Lit := [(972, false), (1125, false)]
theorem step2489 (p : Nat → Bool) (h : Constraints p) : clause p c2489 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1743] c2489 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1743 p h) (sat_nil p)))
def c2490 : List Lit := [(973, false), (1124, false)]
theorem step2490 (p : Nat → Bool) (h : Constraints p) : clause p c2490 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1744] c2490 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1744 p h) (sat_nil p)))
def c2491 : List Lit := [(974, false), (1123, false)]
theorem step2491 (p : Nat → Bool) (h : Constraints p) : clause p c2491 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1745] c2491 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1745 p h) (sat_nil p)))
def c2492 : List Lit := [(975, false), (1122, false)]
theorem step2492 (p : Nat → Bool) (h : Constraints p) : clause p c2492 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1746] c2492 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1746 p h) (sat_nil p)))
def c2493 : List Lit := [(976, false), (1121, false)]
theorem step2493 (p : Nat → Bool) (h : Constraints p) : clause p c2493 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1747] c2493 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1747 p h) (sat_nil p)))
def c2494 : List Lit := [(977, false), (1120, false)]
theorem step2494 (p : Nat → Bool) (h : Constraints p) : clause p c2494 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1748] c2494 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1748 p h) (sat_nil p)))
def c2495 : List Lit := [(978, false), (1119, false)]
theorem step2495 (p : Nat → Bool) (h : Constraints p) : clause p c2495 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1749] c2495 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1749 p h) (sat_nil p)))
def c2496 : List Lit := [(979, false), (1118, false)]
theorem step2496 (p : Nat → Bool) (h : Constraints p) : clause p c2496 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1750] c2496 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1750 p h) (sat_nil p)))
def c2497 : List Lit := [(980, false), (1117, false)]
theorem step2497 (p : Nat → Bool) (h : Constraints p) : clause p c2497 = true :=
  Snake9.LocalRup.prove_clause [c1752, c1751] c2497 (by decide) p (sat_cons (step1752 p h) (sat_cons (step1751 p h) (sat_nil p)))
def c2498 : List Lit := [(1781, false), (1798, true)]
theorem step2498 (p : Nat → Bool) (h : Constraints p) : clause p c2498 = true :=
  Snake9.LocalRup.prove_clause [c2174, c2040] c2498 (by decide) p (sat_cons (step2174 p h) (sat_cons (step2040 p h) (sat_nil p)))
def c2499 : List Lit := [(1782, false), (1799, true)]
theorem step2499 (p : Nat → Bool) (h : Constraints p) : clause p c2499 = true :=
  Snake9.LocalRup.prove_clause [c2174, c2042] c2499 (by decide) p (sat_cons (step2174 p h) (sat_cons (step2042 p h) (sat_nil p)))
def c2500 : List Lit := [(1809, true), (1771, false)]
theorem step2500 (p : Nat → Bool) (h : Constraints p) : clause p c2500 = true :=
  Snake9.LocalRup.prove_clause [c2175, c2044] c2500 (by decide) p (sat_cons (step2175 p h) (sat_cons (step2044 p h) (sat_nil p)))
def c2501 : List Lit := [(1672, false), (1838, false)]
theorem step2501 (p : Nat → Bool) (h : Constraints p) : clause p c2501 = true :=
  Snake9.LocalRup.prove_clause [c2059, c2055] c2501 (by decide) p (sat_cons (step2059 p h) (sat_cons (step2055 p h) (sat_nil p)))
def c2502 : List Lit := [(1676, false), (1834, false)]
theorem step2502 (p : Nat → Bool) (h : Constraints p) : clause p c2502 = true :=
  Snake9.LocalRup.prove_clause [c2059, c2056] c2502 (by decide) p (sat_cons (step2059 p h) (sat_cons (step2056 p h) (sat_nil p)))
def c2503 : List Lit := [(1678, false), (1832, false)]
theorem step2503 (p : Nat → Bool) (h : Constraints p) : clause p c2503 = true :=
  Snake9.LocalRup.prove_clause [c2059, c2057] c2503 (by decide) p (sat_cons (step2059 p h) (sat_cons (step2057 p h) (sat_nil p)))
def c2504 : List Lit := [(1679, false), (1831, false)]
theorem step2504 (p : Nat → Bool) (h : Constraints p) : clause p c2504 = true :=
  Snake9.LocalRup.prove_clause [c2059, c2058] c2504 (by decide) p (sat_cons (step2059 p h) (sat_cons (step2058 p h) (sat_nil p)))
def c2505 : List Lit := [(65, false), (27, true), (56, false), (69, false), (63, true)]
theorem step2505 (p : Nat → Bool) (h : Constraints p) : clause p c2505 = true :=
  Snake9.LocalRup.prove_clause [c478, c423] c2505 (by decide) p (sat_cons (step478 p h) (sat_cons (step423 p h) (sat_nil p)))
def c2506 : List Lit := [(52, false), (47, false), (37, false)]
theorem step2506 (p : Nat → Bool) (h : Constraints p) : clause p c2506 = true :=
  Snake9.LocalRup.prove_clause [c2378, c357] c2506 (by decide) p (sat_cons (step2378 p h) (sat_cons (step357 p h) (sat_nil p)))
def c2507 : List Lit := [(1087, true), (119, false)]
theorem step2507 (p : Nat → Bool) (h : Constraints p) : clause p c2507 = true :=
  Snake9.LocalRup.prove_clause [c1651, c1655, c1643, c1645, c1629, c1640, c1641, c1637, c1638, c1627, c765, c803, c787, c814, c808, c2482] c2507 (by decide) p (sat_cons (step1651 p h) (sat_cons (step1655 p h) (sat_cons (step1643 p h) (sat_cons (step1645 p h) (sat_cons (step1629 p h) (sat_cons (step1640 p h) (sat_cons (step1641 p h) (sat_cons (step1637 p h) (sat_cons (step1638 p h) (sat_cons (step1627 p h) (sat_cons (step765 p h) (sat_cons (step803 p h) (sat_cons (step787 p h) (sat_cons (step814 p h) (sat_cons (step808 p h) (sat_cons (step2482 p h) (sat_nil p)))))))))))))))))
def c2508 : List Lit := [(96, false), (82, false), (206, true), (104, true), (117, false), (79, false)]
theorem step2508 (p : Nat → Bool) (h : Constraints p) : clause p c2508 = true :=
  Snake9.LocalRup.prove_clause [c582, c620, c562] c2508 (by decide) p (sat_cons (step582 p h) (sat_cons (step620 p h) (sat_cons (step562 p h) (sat_nil p))))
def c2509 : List Lit := [(73, false), (200, true), (62, false), (67, false)]
theorem step2509 (p : Nat → Bool) (h : Constraints p) : clause p c2509 = true :=
  Snake9.LocalRup.prove_clause [c518, c505] c2509 (by decide) p (sat_cons (step518 p h) (sat_cons (step505 p h) (sat_nil p)))
def c2510 : List Lit := [(1016, true)]
theorem step2510 (p : Nat → Bool) (h : Constraints p) : clause p c2510 = true :=
  Snake9.LocalRup.prove_clause [c1511, c1512, c2411] c2510 (by decide) p (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step2411 p h) (sat_nil p))))
def c2511 : List Lit := [(1020, true)]
theorem step2511 (p : Nat → Bool) (h : Constraints p) : clause p c2511 = true :=
  Snake9.LocalRup.prove_clause [c2510, c1517] c2511 (by decide) p (sat_cons (step2510 p h) (sat_cons (step1517 p h) (sat_nil p)))
def c2512 : List Lit := [(1024, true)]
theorem step2512 (p : Nat → Bool) (h : Constraints p) : clause p c2512 = true :=
  Snake9.LocalRup.prove_clause [c2511, c1523] c2512 (by decide) p (sat_cons (step2511 p h) (sat_cons (step1523 p h) (sat_nil p)))
def c2513 : List Lit := [(1032, true)]
theorem step2513 (p : Nat → Bool) (h : Constraints p) : clause p c2513 = true :=
  Snake9.LocalRup.prove_clause [c2512, c1540] c2513 (by decide) p (sat_cons (step2512 p h) (sat_cons (step1540 p h) (sat_nil p)))
def c2514 : List Lit := [(74, false), (79, false), (89, false), (201, true)]
theorem step2514 (p : Nat → Bool) (h : Constraints p) : clause p c2514 = true :=
  Snake9.LocalRup.prove_clause [c523, c546] c2514 (by decide) p (sat_cons (step523 p h) (sat_cons (step546 p h) (sat_nil p)))
def c2515 : List Lit := [(106, false), (1060, true), (115, false), (119, false)]
theorem step2515 (p : Nat → Bool) (h : Constraints p) : clause p c2515 = true :=
  Snake9.LocalRup.prove_clause [c721, c720, c1596, c1594, c1602] c2515 (by decide) p (sat_cons (step721 p h) (sat_cons (step720 p h) (sat_cons (step1596 p h) (sat_cons (step1594 p h) (sat_cons (step1602 p h) (sat_nil p))))))
def c2516 : List Lit := [(1084, true), (99, true), (119, false), (127, true), (117, false), (253, true)]
theorem step2516 (p : Nat → Bool) (h : Constraints p) : clause p c2516 = true :=
  Snake9.LocalRup.prove_clause [c1640, c1644, c1646, c1642, c1637, c764, c803, c810] c2516 (by decide) p (sat_cons (step1640 p h) (sat_cons (step1644 p h) (sat_cons (step1646 p h) (sat_cons (step1642 p h) (sat_cons (step1637 p h) (sat_cons (step764 p h) (sat_cons (step803 p h) (sat_cons (step810 p h) (sat_nil p)))))))))
def c2517 : List Lit := [(871, false), (16, true), (887, true), (155, true), (89, false)]
theorem step2517 (p : Nat → Bool) (h : Constraints p) : clause p c2517 = true :=
  Snake9.LocalRup.prove_clause [c1184, c1226, c1193, c1196, c1222, c1186, c1204, c1202, c210, c109] c2517 (by decide) p (sat_cons (step1184 p h) (sat_cons (step1226 p h) (sat_cons (step1193 p h) (sat_cons (step1196 p h) (sat_cons (step1222 p h) (sat_cons (step1186 p h) (sat_cons (step1204 p h) (sat_cons (step1202 p h) (sat_cons (step210 p h) (sat_cons (step109 p h) (sat_nil p)))))))))))
def c2518 : List Lit := [(874, false), (897, true), (155, true), (851, false), (854, false)]
theorem step2518 (p : Nat → Bool) (h : Constraints p) : clause p c2518 = true :=
  Snake9.LocalRup.prove_clause [c1160, c1171, c1252, c1221, c1222, c1259, c1204, c1172, c1202, c1161, c209, c210, c1155, c2072] c2518 (by decide) p (sat_cons (step1160 p h) (sat_cons (step1171 p h) (sat_cons (step1252 p h) (sat_cons (step1221 p h) (sat_cons (step1222 p h) (sat_cons (step1259 p h) (sat_cons (step1204 p h) (sat_cons (step1172 p h) (sat_cons (step1202 p h) (sat_cons (step1161 p h) (sat_cons (step209 p h) (sat_cons (step210 p h) (sat_cons (step1155 p h) (sat_cons (step2072 p h) (sat_nil p)))))))))))))))
def c2519 : List Lit := [(28, false), (15, false), (155, true), (89, false)]
theorem step2519 (p : Nat → Bool) (h : Constraints p) : clause p c2519 = true :=
  Snake9.LocalRup.prove_clause [c210, c109] c2519 (by decide) p (sat_cons (step210 p h) (sat_cons (step109 p h) (sat_nil p)))
def c2520 : List Lit := [(952, true)]
theorem step2520 (p : Nat → Bool) (h : Constraints p) : clause p c2520 = true :=
  Snake9.LocalRup.prove_clause [c1368, c1375, c1345, c1349, c1300, c1337, c1323, c1292, c1294, c1335, c1320, c1289, c1290, c1286, c1287, c305, c2171] c2520 (by decide) p (sat_cons (step1368 p h) (sat_cons (step1375 p h) (sat_cons (step1345 p h) (sat_cons (step1349 p h) (sat_cons (step1300 p h) (sat_cons (step1337 p h) (sat_cons (step1323 p h) (sat_cons (step1292 p h) (sat_cons (step1294 p h) (sat_cons (step1335 p h) (sat_cons (step1320 p h) (sat_cons (step1289 p h) (sat_cons (step1290 p h) (sat_cons (step1286 p h) (sat_cons (step1287 p h) (sat_cons (step305 p h) (sat_cons (step2171 p h) (sat_nil p))))))))))))))))))
def c2521 : List Lit := [(37, true), (944, true), (11, true)]
theorem step2521 (p : Nat → Bool) (h : Constraints p) : clause p c2521 = true :=
  Snake9.LocalRup.prove_clause [c1349, c1325, c1317, c1318, c1323, c1321, c350, c1320, c1345, c1337, c1335, c365, c354, c976, c2379, c980, c2462, c982, c977, c993, c381, c380, c995, c2463, c2067, c1000, c2464, c972, c2342, c2488, c941, c943, c954, c1136, c936, c908, c948, c1065, c931, c904, c947, c1036, c929, c901, c902, c1033, c926, c900, c899, c1026, c210, c139, c122, c1024, c2346, c2356, c233, c2509, c2363] c2521 (by decide) p (sat_cons (step1349 p h) (sat_cons (step1325 p h) (sat_cons (step1317 p h) (sat_cons (step1318 p h) (sat_cons (step1323 p h) (sat_cons (step1321 p h) (sat_cons (step350 p h) (sat_cons (step1320 p h) (sat_cons (step1345 p h) (sat_cons (step1337 p h) (sat_cons (step1335 p h) (sat_cons (step365 p h) (sat_cons (step354 p h) (sat_cons (step976 p h) (sat_cons (step2379 p h) (sat_cons (step980 p h) (sat_cons (step2462 p h) (sat_cons (step982 p h) (sat_cons (step977 p h) (sat_cons (step993 p h) (sat_cons (step381 p h) (sat_cons (step380 p h) (sat_cons (step995 p h) (sat_cons (step2463 p h) (sat_cons (step2067 p h) (sat_cons (step1000 p h) (sat_cons (step2464 p h) (sat_cons (step972 p h) (sat_cons (step2342 p h) (sat_cons (step2488 p h) (sat_cons (step941 p h) (sat_cons (step943 p h) (sat_cons (step954 p h) (sat_cons (step1136 p h) (sat_cons (step936 p h) (sat_cons (step908 p h) (sat_cons (step948 p h) (sat_cons (step1065 p h) (sat_cons (step931 p h) (sat_cons (step904 p h) (sat_cons (step947 p h) (sat_cons (step1036 p h) (sat_cons (step929 p h) (sat_cons (step901 p h) (sat_cons (step902 p h) (sat_cons (step1033 p h) (sat_cons (step926 p h) (sat_cons (step900 p h) (sat_cons (step899 p h) (sat_cons (step1026 p h) (sat_cons (step210 p h) (sat_cons (step139 p h) (sat_cons (step122 p h) (sat_cons (step1024 p h) (sat_cons (step2346 p h) (sat_cons (step2356 p h) (sat_cons (step233 p h) (sat_cons (step2509 p h) (sat_cons (step2363 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2522 : List Lit := [(377, true), (944, true), (11, true)]
theorem step2522 (p : Nat → Bool) (h : Constraints p) : clause p c2522 = true :=
  Snake9.TreeRup.prove_clause [c1349, c1325, c1317, c1318, c1323, c1321, c350, c1320, c1345, c1339, c1332, c1337, c1335, c1000, c1002, c995, c997, c941, c943, c993, c972, c936, c908, c982, c954, c931, c904, c979, c980, c948, c929, c901, c902, c977, c976, c947, c926, c900, c899, c381, c380, c363, c210, c2067, c2379, c2342, c139, c122, c2346, c2356, c233, c482, c409, c2363, c505, c2509, c490, c1024, c1010, c1026, c1014, c1033, c1017, c2472] c2522 (by decide) p (sat_cons (step1349 p h) (sat_cons (step1325 p h) (sat_cons (step1317 p h) (sat_cons (step1318 p h) (sat_cons (step1323 p h) (sat_cons (step1321 p h) (sat_cons (step350 p h) (sat_cons (step1320 p h) (sat_cons (step1345 p h) (sat_cons (step1339 p h) (sat_cons (step1332 p h) (sat_cons (step1337 p h) (sat_cons (step1335 p h) (sat_cons (step1000 p h) (sat_cons (step1002 p h) (sat_cons (step995 p h) (sat_cons (step997 p h) (sat_cons (step941 p h) (sat_cons (step943 p h) (sat_cons (step993 p h) (sat_cons (step972 p h) (sat_cons (step936 p h) (sat_cons (step908 p h) (sat_cons (step982 p h) (sat_cons (step954 p h) (sat_cons (step931 p h) (sat_cons (step904 p h) (sat_cons (step979 p h) (sat_cons (step980 p h) (sat_cons (step948 p h) (sat_cons (step929 p h) (sat_cons (step901 p h) (sat_cons (step902 p h) (sat_cons (step977 p h) (sat_cons (step976 p h) (sat_cons (step947 p h) (sat_cons (step926 p h) (sat_cons (step900 p h) (sat_cons (step899 p h) (sat_cons (step381 p h) (sat_cons (step380 p h) (sat_cons (step363 p h) (sat_cons (step210 p h) (sat_cons (step2067 p h) (sat_cons (step2379 p h) (sat_cons (step2342 p h) (sat_cons (step139 p h) (sat_cons (step122 p h) (sat_cons (step2346 p h) (sat_cons (step2356 p h) (sat_cons (step233 p h) (sat_cons (step482 p h) (sat_cons (step409 p h) (sat_cons (step2363 p h) (sat_cons (step505 p h) (sat_cons (step2509 p h) (sat_cons (step490 p h) (sat_cons (step1024 p h) (sat_cons (step1010 p h) (sat_cons (step1026 p h) (sat_cons (step1014 p h) (sat_cons (step1033 p h) (sat_cons (step1017 p h) (sat_cons (step2472 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2523 : List Lit := [(1057, true), (109, false), (108, false)]
theorem step2523 (p : Nat → Bool) (h : Constraints p) : clause p c2523 = true :=
  Snake9.LocalRup.prove_clause [c1596, c1597, c728] c2523 (by decide) p (sat_cons (step1596 p h) (sat_cons (step1597 p h) (sat_cons (step728 p h) (sat_nil p))))
def c2524 : List Lit := [(1003, true), (995, false), (988, false), (192, true), (56, false), (63, true)]
theorem step2524 (p : Nat → Bool) (h : Constraints p) : clause p c2524 = true :=
  Snake9.LocalRup.prove_clause [c1474, c1463, c1487, c1491, c1477, c1466, c1469, c479, c423] c2524 (by decide) p (sat_cons (step1474 p h) (sat_cons (step1463 p h) (sat_cons (step1487 p h) (sat_cons (step1491 p h) (sat_cons (step1477 p h) (sat_cons (step1466 p h) (sat_cons (step1469 p h) (sat_cons (step479 p h) (sat_cons (step423 p h) (sat_nil p))))))))))
def c2525 : List Lit := [(922, true), (34, true), (37, false), (48, false)]
theorem step2525 (p : Nat → Bool) (h : Constraints p) : clause p c2525 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1281, c1309, c1305, c1282, c1294, c1280, c1287, c247] c2525 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_cons (step1309 p h) (sat_cons (step1305 p h) (sat_cons (step1282 p h) (sat_cons (step1294 p h) (sat_cons (step1280 p h) (sat_cons (step1287 p h) (sat_cons (step247 p h) (sat_nil p))))))))))
def c2526 : List Lit := [(1052, true), (103, true), (1081, true)]
theorem step2526 (p : Nat → Bool) (h : Constraints p) : clause p c2526 = true :=
  Snake9.LocalRup.prove_clause [c1582, c1641, c1640, c1586, c1588, c1584, c1580, c763, c679, c813] c2526 (by decide) p (sat_cons (step1582 p h) (sat_cons (step1641 p h) (sat_cons (step1640 p h) (sat_cons (step1586 p h) (sat_cons (step1588 p h) (sat_cons (step1584 p h) (sat_cons (step1580 p h) (sat_cons (step763 p h) (sat_cons (step679 p h) (sat_cons (step813 p h) (sat_nil p)))))))))))
def c2527 : List Lit := [(96, false), (100, false), (1081, true)]
theorem step2527 (p : Nat → Bool) (h : Constraints p) : clause p c2527 = true :=
  Snake9.LocalRup.prove_clause [c1641, c1640, c763, c679, c813] c2527 (by decide) p (sat_cons (step1641 p h) (sat_cons (step1640 p h) (sat_cons (step763 p h) (sat_cons (step679 p h) (sat_cons (step813 p h) (sat_nil p))))))
def c2528 : List Lit := [(120, false), (126, false), (127, false), (1074, true)]
theorem step2528 (p : Nat → Bool) (h : Constraints p) : clause p c2528 = true :=
  Snake9.LocalRup.prove_clause [c767, c766, c1628] c2528 (by decide) p (sat_cons (step767 p h) (sat_cons (step766 p h) (sat_cons (step1628 p h) (sat_nil p))))
def c2529 : List Lit := [(15, false), (11, false), (17, true), (142, true)]
theorem step2529 (p : Nat → Bool) (h : Constraints p) : clause p c2529 = true :=
  Snake9.LocalRup.prove_clause [c137, c2378, c2073] c2529 (by decide) p (sat_cons (step137 p h) (sat_cons (step2378 p h) (sat_cons (step2073 p h) (sat_nil p))))
def c2530 : List Lit := [(877, true), (32, false), (939, true), (60, false), (151, true)]
theorem step2530 (p : Nat → Bool) (h : Constraints p) : clause p c2530 = true :=
  Snake9.LocalRup.prove_clause [c1198, c1199, c181, c190, c191, c438, c2079, c1336] c2530 (by decide) p (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step181 p h) (sat_cons (step190 p h) (sat_cons (step191 p h) (sat_cons (step438 p h) (sat_cons (step2079 p h) (sat_cons (step1336 p h) (sat_nil p)))))))))
def c2531 : List Lit := [(192, true), (21, false), (65, false), (63, true)]
theorem step2531 (p : Nat → Bool) (h : Constraints p) : clause p c2531 = true :=
  Snake9.LocalRup.prove_clause [c480, c479, c2075] c2531 (by decide) p (sat_cons (step480 p h) (sat_cons (step479 p h) (sat_cons (step2075 p h) (sat_nil p))))
def c2532 : List Lit := [(127, false), (389, false), (1012, true)]
theorem step2532 (p : Nat → Bool) (h : Constraints p) : clause p c2532 = true :=
  Snake9.LocalRup.prove_clause [c1038, c1065, c2487, c1129, c1124, c1120, c1116, c1113, c2472, c1032, c1031, c1030, c1506, c1499, c1504, c1502, c815, c814, c2099, c2401, c2432, c532, c630] c2532 (by decide) p (sat_cons (step1038 p h) (sat_cons (step1065 p h) (sat_cons (step2487 p h) (sat_cons (step1129 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1116 p h) (sat_cons (step1113 p h) (sat_cons (step2472 p h) (sat_cons (step1032 p h) (sat_cons (step1031 p h) (sat_cons (step1030 p h) (sat_cons (step1506 p h) (sat_cons (step1499 p h) (sat_cons (step1504 p h) (sat_cons (step1502 p h) (sat_cons (step815 p h) (sat_cons (step814 p h) (sat_cons (step2099 p h) (sat_cons (step2401 p h) (sat_cons (step2432 p h) (sat_cons (step532 p h) (sat_cons (step630 p h) (sat_nil p))))))))))))))))))))))))
def c2533 : List Lit := [(77, true), (203, true), (1012, true)]
theorem step2533 (p : Nat → Bool) (h : Constraints p) : clause p c2533 = true :=
  Snake9.LocalRup.prove_clause [c1506, c1499, c1504, c1502, c534, c532, c2089] c2533 (by decide) p (sat_cons (step1506 p h) (sat_cons (step1499 p h) (sat_cons (step1504 p h) (sat_cons (step1502 p h) (sat_cons (step534 p h) (sat_cons (step532 p h) (sat_cons (step2089 p h) (sat_nil p))))))))
def c2534 : List Lit := [(72, false), (60, false), (32, false), (199, true), (63, true)]
theorem step2534 (p : Nat → Bool) (h : Constraints p) : clause p c2534 = true :=
  Snake9.LocalRup.prove_clause [c512, c502] c2534 (by decide) p (sat_cons (step512 p h) (sat_cons (step502 p h) (sat_nil p)))
def c2535 : List Lit := [(69, false), (56, false), (65, false), (989, true), (63, true)]
theorem step2535 (p : Nat → Bool) (h : Constraints p) : clause p c2535 = true :=
  Snake9.LocalRup.prove_clause [c423, c479, c1005, c1006, c2468, c1013, c1014, c1012, c1009, c499, c495, c485, c1462] c2535 (by decide) p (sat_cons (step423 p h) (sat_cons (step479 p h) (sat_cons (step1005 p h) (sat_cons (step1006 p h) (sat_cons (step2468 p h) (sat_cons (step1013 p h) (sat_cons (step1014 p h) (sat_cons (step1012 p h) (sat_cons (step1009 p h) (sat_cons (step499 p h) (sat_cons (step495 p h) (sat_cons (step485 p h) (sat_cons (step1462 p h) (sat_nil p))))))))))))))
def c2536 : List Lit := [(72, false), (32, false), (60, false), (21, true), (65, false), (63, true)]
theorem step2536 (p : Nat → Bool) (h : Constraints p) : clause p c2536 = true :=
  Snake9.LocalRup.prove_clause [c502, c2534, c1022, c1028, c1033, c1036, c2472, c1065, c1019, c1136, c1006, c2488, c1005, c1000, c480, c997, c2355, c972, c181, c954, c226, c949, c946] c2536 (by decide) p (sat_cons (step502 p h) (sat_cons (step2534 p h) (sat_cons (step1022 p h) (sat_cons (step1028 p h) (sat_cons (step1033 p h) (sat_cons (step1036 p h) (sat_cons (step2472 p h) (sat_cons (step1065 p h) (sat_cons (step1019 p h) (sat_cons (step1136 p h) (sat_cons (step1006 p h) (sat_cons (step2488 p h) (sat_cons (step1005 p h) (sat_cons (step1000 p h) (sat_cons (step480 p h) (sat_cons (step997 p h) (sat_cons (step2355 p h) (sat_cons (step972 p h) (sat_cons (step181 p h) (sat_cons (step954 p h) (sat_cons (step226 p h) (sat_cons (step949 p h) (sat_cons (step946 p h) (sat_nil p))))))))))))))))))))))))
def c2537 : List Lit := [(17, true), (142, true), (15, false)]
theorem step2537 (p : Nat → Bool) (h : Constraints p) : clause p c2537 = true :=
  Snake9.LocalRup.prove_clause [c139, c2529] c2537 (by decide) p (sat_cons (step139 p h) (sat_cons (step2529 p h) (sat_nil p)))
def c2538 : List Lit := [(932, true), (11, false), (178, true), (15, false)]
theorem step2538 (p : Nat → Bool) (h : Constraints p) : clause p c2538 = true :=
  Snake9.LocalRup.prove_clause [c1323, c1325, c1320, c1318, c381, c380, c103, c2067, c2342] c2538 (by decide) p (sat_cons (step1323 p h) (sat_cons (step1325 p h) (sat_cons (step1320 p h) (sat_cons (step1318 p h) (sat_cons (step381 p h) (sat_cons (step380 p h) (sat_cons (step103 p h) (sat_cons (step2067 p h) (sat_cons (step2342 p h) (sat_nil p))))))))))
def c2539 : List Lit := [(65, false), (877, false), (20, true), (56, false), (28, true), (157, true), (192, true), (889, true), (989, true), (63, true)]
theorem step2539 (p : Nat → Bool) (h : Constraints p) : clause p c2539 = true :=
  Snake9.LocalRup.prove_clause [c2531, c2535, c1189, c2359, c1191, c218, c1224, c1203, c1208] c2539 (by decide) p (sat_cons (step2531 p h) (sat_cons (step2535 p h) (sat_cons (step1189 p h) (sat_cons (step2359 p h) (sat_cons (step1191 p h) (sat_cons (step218 p h) (sat_cons (step1224 p h) (sat_cons (step1203 p h) (sat_cons (step1208 p h) (sat_nil p))))))))))
def c2540 : List Lit := [(1071, false), (1089, true), (254, true), (119, true)]
theorem step2540 (p : Nat → Bool) (h : Constraints p) : clause p c2540 = true :=
  Snake9.LocalRup.prove_clause [c1664, c1626, c1632, c1633, c1661, c1628, c1643, c1640, c1641, c814, c766] c2540 (by decide) p (sat_cons (step1664 p h) (sat_cons (step1626 p h) (sat_cons (step1632 p h) (sat_cons (step1633 p h) (sat_cons (step1661 p h) (sat_cons (step1628 p h) (sat_cons (step1643 p h) (sat_cons (step1640 p h) (sat_cons (step1641 p h) (sat_cons (step814 p h) (sat_cons (step766 p h) (sat_nil p))))))))))))
def c2541 : List Lit := [(1088, true), (254, true), (119, true)]
theorem step2541 (p : Nat → Bool) (h : Constraints p) : clause p c2541 = true :=
  Snake9.LocalRup.prove_clause [c1626, c1629, c1660, c1656, c1630, c1643, c1628, c1640, c1641, c814, c766] c2541 (by decide) p (sat_cons (step1626 p h) (sat_cons (step1629 p h) (sat_cons (step1660 p h) (sat_cons (step1656 p h) (sat_cons (step1630 p h) (sat_cons (step1643 p h) (sat_cons (step1628 p h) (sat_cons (step1640 p h) (sat_cons (step1641 p h) (sat_cons (step814 p h) (sat_cons (step766 p h) (sat_nil p))))))))))))
def c2542 : List Lit := [(100, false), (227, true), (127, true), (89, false), (115, false)]
theorem step2542 (p : Nat → Bool) (h : Constraints p) : clause p c2542 = true :=
  Snake9.LocalRup.prove_clause [c614, c677, c678, c2431, c2096] c2542 (by decide) p (sat_cons (step614 p h) (sat_cons (step677 p h) (sat_cons (step678 p h) (sat_cons (step2431 p h) (sat_cons (step2096 p h) (sat_nil p))))))
def c2543 : List Lit := [(91, true), (1002, true), (1035, true), (11, true), (89, false)]
theorem step2543 (p : Nat → Bool) (h : Constraints p) : clause p c2543 = true :=
  Snake9.LocalRup.prove_clause [c2511, c603, c606, c1052, c1055, c1057, c1059, c2475, c1038, c1017, c1014, c1009, c495, c1460, c1463, c1485, c1486, c1548, c1474, c1532, c1471, c548, c546, c1502, c1498, c1507] c2543 (by decide) p (sat_cons (step2511 p h) (sat_cons (step603 p h) (sat_cons (step606 p h) (sat_cons (step1052 p h) (sat_cons (step1055 p h) (sat_cons (step1057 p h) (sat_cons (step1059 p h) (sat_cons (step2475 p h) (sat_cons (step1038 p h) (sat_cons (step1017 p h) (sat_cons (step1014 p h) (sat_cons (step1009 p h) (sat_cons (step495 p h) (sat_cons (step1460 p h) (sat_cons (step1463 p h) (sat_cons (step1485 p h) (sat_cons (step1486 p h) (sat_cons (step1548 p h) (sat_cons (step1474 p h) (sat_cons (step1532 p h) (sat_cons (step1471 p h) (sat_cons (step548 p h) (sat_cons (step546 p h) (sat_cons (step1502 p h) (sat_cons (step1498 p h) (sat_cons (step1507 p h) (sat_nil p)))))))))))))))))))))))))))
def c2544 : List Lit := [(127, false), (100, true), (254, true)]
theorem step2544 (p : Nat → Bool) (h : Constraints p) : clause p c2544 = true :=
  Snake9.LocalRup.prove_clause [c815, c814, c2099, c2432] c2544 (by decide) p (sat_cons (step815 p h) (sat_cons (step814 p h) (sat_cons (step2099 p h) (sat_cons (step2432 p h) (sat_nil p)))))
def c2545 : List Lit := [(1088, true), (119, false), (127, true), (120, false), (1083, false)]
theorem step2545 (p : Nat → Bool) (h : Constraints p) : clause p c2545 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1656, c1644, c1629, c1642, c1627, c764] c2545 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1656 p h) (sat_cons (step1644 p h) (sat_cons (step1629 p h) (sat_cons (step1642 p h) (sat_cons (step1627 p h) (sat_cons (step764 p h) (sat_nil p))))))))
def c2546 : List Lit := [(403, true), (76, false), (79, false), (81, true), (89, false), (77, true)]
theorem step2546 (p : Nat → Bool) (h : Constraints p) : clause p c2546 = true :=
  Snake9.LocalRup.prove_clause [c1032, c1033, c1031, c1026, c1030, c1023, c534, c2514, c2399] c2546 (by decide) p (sat_cons (step1032 p h) (sat_cons (step1033 p h) (sat_cons (step1031 p h) (sat_cons (step1026 p h) (sat_cons (step1030 p h) (sat_cons (step1023 p h) (sat_cons (step534 p h) (sat_cons (step2514 p h) (sat_cons (step2399 p h) (sat_nil p))))))))))
def c2547 : List Lit := [(113, false), (240, true), (79, false), (117, false)]
theorem step2547 (p : Nat → Bool) (h : Constraints p) : clause p c2547 = true :=
  Snake9.LocalRup.prove_clause [c699, c741] c2547 (by decide) p (sat_cons (step699 p h) (sat_cons (step741 p h) (sat_nil p)))
def c2548 : List Lit := [(203, true), (81, false), (76, false), (77, true)]
theorem step2548 (p : Nat → Bool) (h : Constraints p) : clause p c2548 = true :=
  Snake9.LocalRup.prove_clause [c534, c532, c2089] c2548 (by decide) p (sat_cons (step534 p h) (sat_cons (step532 p h) (sat_cons (step2089 p h) (sat_nil p))))
def c2549 : List Lit := [(1059, false), (104, false), (117, false), (1101, true), (1048, false), (100, true), (119, true), (254, true)]
theorem step2549 (p : Nat → Bool) (h : Constraints p) : clause p c2549 = true :=
  Snake9.LocalRup.prove_clause [c2541, c1697, c1583, c1591, c1618, c1622, c1693, c1592, c2540, c1584, c1624, c702] c2549 (by decide) p (sat_cons (step2541 p h) (sat_cons (step1697 p h) (sat_cons (step1583 p h) (sat_cons (step1591 p h) (sat_cons (step1618 p h) (sat_cons (step1622 p h) (sat_cons (step1693 p h) (sat_cons (step1592 p h) (sat_cons (step2540 p h) (sat_cons (step1584 p h) (sat_cons (step1624 p h) (sat_cons (step702 p h) (sat_nil p)))))))))))))
def c2550 : List Lit := [(104, false), (117, false), (254, true), (1101, true), (1048, false), (100, true), (119, true)]
theorem step2550 (p : Nat → Bool) (h : Constraints p) : clause p c2550 = true :=
  Snake9.LocalRup.prove_clause [c2549, c1599, c1597, c701, c703, c1584, c1624, c1592, c2540, c1621, c1693] c2550 (by decide) p (sat_cons (step2549 p h) (sat_cons (step1599 p h) (sat_cons (step1597 p h) (sat_cons (step701 p h) (sat_cons (step703 p h) (sat_cons (step1584 p h) (sat_cons (step1624 p h) (sat_cons (step1592 p h) (sat_cons (step2540 p h) (sat_cons (step1621 p h) (sat_cons (step1693 p h) (sat_nil p))))))))))))
end B112E260
