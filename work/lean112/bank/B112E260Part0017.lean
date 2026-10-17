import B112E260Part0016
namespace B112E260
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c3191 : List Lit := [(10, false), (137, true), (935, true), (36, false), (51, true), (11, true)]
theorem step3191 (p : Nat → Bool) (h : Constraints p) : clause p c3191 = true :=
  Snake9.LocalRup.prove_clause [c75, c343, c341, c342, c1322, c1319, c1330] c3191 (by decide) p (sat_cons (step75 p h) (sat_cons (step343 p h) (sat_cons (step341 p h) (sat_cons (step342 p h) (sat_cons (step1322 p h) (sat_cons (step1319 p h) (sat_cons (step1330 p h) (sat_nil p))))))))
def c3192 : List Lit := [(10, false), (956, true), (137, true), (51, true), (940, false), (11, true)]
theorem step3192 (p : Nat → Bool) (h : Constraints p) : clause p c3192 = true :=
  Snake9.LocalRup.prove_clause [c1372, c1365, c3191, c3189, c1278, c1360, c1281, c1379, c1304] c3192 (by decide) p (sat_cons (step1372 p h) (sat_cons (step1365 p h) (sat_cons (step3191 p h) (sat_cons (step3189 p h) (sat_cons (step1278 p h) (sat_cons (step1360 p h) (sat_cons (step1281 p h) (sat_cons (step1379 p h) (sat_cons (step1304 p h) (sat_nil p))))))))))
def c3193 : List Lit := [(151, false), (62, false), (46, false), (7, false)]
theorem step3193 (p : Nat → Bool) (h : Constraints p) : clause p c3193 = true :=
  Snake9.LocalRup.prove_clause [c184, c921, c192, c924, c2641, c933, c886, c936, c889, c2456, c892, c910] c3193 (by decide) p (sat_cons (step184 p h) (sat_cons (step921 p h) (sat_cons (step192 p h) (sat_cons (step924 p h) (sat_cons (step2641 p h) (sat_cons (step933 p h) (sat_cons (step886 p h) (sat_cons (step936 p h) (sat_cons (step889 p h) (sat_cons (step2456 p h) (sat_cons (step892 p h) (sat_cons (step910 p h) (sat_nil p)))))))))))))
def c3194 : List Lit := [(955, true), (10, false), (137, true), (51, true), (11, true)]
theorem step3194 (p : Nat → Bool) (h : Constraints p) : clause p c3194 = true :=
  Snake9.LocalRup.prove_clause [c3189, c1359, c1371, c1378, c1364, c1304, c3191, c1281, c1278] c3194 (by decide) p (sat_cons (step3189 p h) (sat_cons (step1359 p h) (sat_cons (step1371 p h) (sat_cons (step1378 p h) (sat_cons (step1364 p h) (sat_cons (step1304 p h) (sat_cons (step3191 p h) (sat_cons (step1281 p h) (sat_cons (step1278 p h) (sat_nil p))))))))))
def c3195 : List Lit := [(941, true), (26, false), (24, false), (151, true), (62, true)]
theorem step3195 (p : Nat → Bool) (h : Constraints p) : clause p c3195 = true :=
  Snake9.LocalRup.prove_clause [c1335, c2654, c1340, c190, c1331, c179] c3195 (by decide) p (sat_cons (step1335 p h) (sat_cons (step2654 p h) (sat_cons (step1340 p h) (sat_cons (step190 p h) (sat_cons (step1331 p h) (sat_cons (step179 p h) (sat_nil p)))))))
def c3196 : List Lit := [(128, true), (81, false), (1, false), (37, true), (11, true)]
theorem step3196 (p : Nat → Bool) (h : Constraints p) : clause p c3196 = true :=
  Snake9.LocalRup.prove_clause [c6, c9, c2060] c3196 (by decide) p (sat_cons (step6 p h) (sat_cons (step9 p h) (sat_cons (step2060 p h) (sat_nil p))))
def c3197 : List Lit := [(932, false), (856, false), (24, false), (977, true), (151, true), (887, false), (852, false), (62, true), (922, false)]
theorem step3197 (p : Nat → Bool) (h : Constraints p) : clause p c3197 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1176, c1260, c1440, c1386, c1335, c1337, c1350, c1351, c1385, c3138, c1446, c1153, c1266, c1161, c1177] c3197 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1176 p h) (sat_cons (step1260 p h) (sat_cons (step1440 p h) (sat_cons (step1386 p h) (sat_cons (step1335 p h) (sat_cons (step1337 p h) (sat_cons (step1350 p h) (sat_cons (step1351 p h) (sat_cons (step1385 p h) (sat_cons (step3138 p h) (sat_cons (step1446 p h) (sat_cons (step1153 p h) (sat_cons (step1266 p h) (sat_cons (step1161 p h) (sat_cons (step1177 p h) (sat_nil p)))))))))))))))))
def c3198 : List Lit := [(257, true), (134, true), (133, true), (277, true), (192, true), (194, true), (195, true), (196, true), (199, true), (200, true), (201, true), (203, true), (206, true), (208, true), (209, true), (212, true), (213, true), (216, true), (217, true), (223, true), (225, true), (227, true), (230, true), (232, true), (235, true), (237, true), (238, true), (240, true), (242, true), (244, true), (246, true), (249, true), (251, true), (253, true), (254, true), (191, true), (159, true), (161, true), (163, true), (169, true), (171, true), (173, true), (175, true), (176, true), (178, true), (183, true), (187, true), (143, true), (147, true), (148, true), (153, true), (157, true), (177, true), (137, true), (151, true), (155, true), (189, true), (132, true), (167, true)]
theorem step3198 (p : Nat → Bool) (h : Constraints p) : clause p c3198 = true :=
  Snake9.LocalRup.prove_clause [c902, c899, c901, c900, c882, c883, c881, c2155] c3198 (by decide) p (sat_cons (step902 p h) (sat_cons (step899 p h) (sat_cons (step901 p h) (sat_cons (step900 p h) (sat_cons (step882 p h) (sat_cons (step883 p h) (sat_cons (step881 p h) (sat_cons (step2155 p h) (sat_nil p)))))))))
def c3199 : List Lit := [(128, true), (78, false), (203, true), (1, false), (1013, true), (5, true), (40, true), (37, true), (11, true)]
theorem step3199 (p : Nat → Bool) (h : Constraints p) : clause p c3199 = true :=
  Snake9.LocalRup.prove_clause [c9, c3196, c2323, c1502, c2646, c1507, c537, c1498] c3199 (by decide) p (sat_cons (step9 p h) (sat_cons (step3196 p h) (sat_cons (step2323 p h) (sat_cons (step1502 p h) (sat_cons (step2646 p h) (sat_cons (step1507 p h) (sat_cons (step537 p h) (sat_cons (step1498 p h) (sat_nil p)))))))))
def c3200 : List Lit := [(81, true), (78, false), (203, true), (1, false), (1013, true)]
theorem step3200 (p : Nat → Bool) (h : Constraints p) : clause p c3200 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1507, c1498, c1499, c537, c2665, c2399] c3200 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1507 p h) (sat_cons (step1498 p h) (sat_cons (step1499 p h) (sat_cons (step537 p h) (sat_cons (step2665 p h) (sat_cons (step2399 p h) (sat_nil p))))))))
def c3201 : List Lit := [(78, false), (1037, true), (990, false), (90, true), (201, true), (203, true), (1, false), (1013, true)]
theorem step3201 (p : Nat → Bool) (h : Constraints p) : clause p c3201 = true :=
  Snake9.LocalRup.prove_clause [c3200, c2649, c543, c541, c1471, c1516, c1498, c1474, c2669, c1506, c1486, c1529, c1556] c3201 (by decide) p (sat_cons (step3200 p h) (sat_cons (step2649 p h) (sat_cons (step543 p h) (sat_cons (step541 p h) (sat_cons (step1471 p h) (sat_cons (step1516 p h) (sat_cons (step1498 p h) (sat_cons (step1474 p h) (sat_cons (step2669 p h) (sat_cons (step1506 p h) (sat_cons (step1486 p h) (sat_cons (step1529 p h) (sat_cons (step1556 p h) (sat_nil p))))))))))))))
def c3202 : List Lit := [(89, false), (216, true), (81, false), (78, false), (11, true)]
theorem step3202 (p : Nat → Bool) (h : Constraints p) : clause p c3202 = true :=
  Snake9.LocalRup.prove_clause [c2093, c606] c3202 (by decide) p (sat_cons (step2093 p h) (sat_cons (step606 p h) (sat_nil p)))
def c3203 : List Lit := [(990, false), (1022, false), (81, false), (1036, true), (78, false)]
theorem step3203 (p : Nat → Bool) (h : Constraints p) : clause p c3203 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1555, c1485, c1486, c1549, c1474, c1529, c1471, c1506, c544, c1498] c3203 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1555 p h) (sat_cons (step1485 p h) (sat_cons (step1486 p h) (sat_cons (step1549 p h) (sat_cons (step1474 p h) (sat_cons (step1529 p h) (sat_cons (step1471 p h) (sat_cons (step1506 p h) (sat_cons (step544 p h) (sat_cons (step1498 p h) (sat_nil p))))))))))))
def c3204 : List Lit := [(75, false), (115, false), (81, false), (242, true), (78, false)]
theorem step3204 (p : Nat → Bool) (h : Constraints p) : clause p c3204 = true :=
  Snake9.LocalRup.prove_clause [c571, c569, c746] c3204 (by decide) p (sat_cons (step571 p h) (sat_cons (step569 p h) (sat_cons (step746 p h) (sat_nil p))))
def c3205 : List Lit := [(1010, false), (1017, false), (1027, true), (201, true), (203, true), (78, false), (1013, true)]
theorem step3205 (p : Nat → Bool) (h : Constraints p) : clause p c3205 = true :=
  Snake9.LocalRup.prove_clause [c1504, c1507, c1529, c1498, c1499, c1521, c2665, c1515, c2688] c3205 (by decide) p (sat_cons (step1504 p h) (sat_cons (step1507 p h) (sat_cons (step1529 p h) (sat_cons (step1498 p h) (sat_cons (step1499 p h) (sat_cons (step1521 p h) (sat_cons (step2665 p h) (sat_cons (step1515 p h) (sat_cons (step2688 p h) (sat_nil p))))))))))
def c3206 : List Lit := [(1010, false), (1027, true), (90, true), (201, true), (203, true), (78, false), (1013, true)]
theorem step3206 (p : Nat → Bool) (h : Constraints p) : clause p c3206 = true :=
  Snake9.LocalRup.prove_clause [c1504, c1507, c1529, c1498, c1499, c2669, c2665, c1516, c2688] c3206 (by decide) p (sat_cons (step1504 p h) (sat_cons (step1507 p h) (sat_cons (step1529 p h) (sat_cons (step1498 p h) (sat_cons (step1499 p h) (sat_cons (step2669 p h) (sat_cons (step2665 p h) (sat_cons (step1516 p h) (sat_cons (step2688 p h) (sat_nil p))))))))))
def c3207 : List Lit := [(60, false), (65, false), (72, false), (21, true), (32, false)]
theorem step3207 (p : Nat → Bool) (h : Constraints p) : clause p c3207 = true :=
  Snake9.LocalRup.prove_clause [c2536, c470] c3207 (by decide) p (sat_cons (step2536 p h) (sat_cons (step470 p h) (sat_nil p)))
def c3208 : List Lit := [(81, true), (78, true), (1013, true), (403, true)]
theorem step3208 (p : Nat → Bool) (h : Constraints p) : clause p c3208 = true :=
  Snake9.LocalRup.prove_clause [c1502, c3075, c1507, c1499] c3208 (by decide) p (sat_cons (step1502 p h) (sat_cons (step3075 p h) (sat_cons (step1507 p h) (sat_cons (step1499 p h) (sat_nil p)))))
def c3209 : List Lit := [(1002, false), (1017, false), (1120, true), (1013, false)]
theorem step3209 (p : Nat → Bool) (h : Constraints p) : clause p c3209 = true :=
  Snake9.LocalRup.prove_clause [c1520, c1533, c2684, c1557, c1556, c1534, c1723, c1521, c2743, c1515] c3209 (by decide) p (sat_cons (step1520 p h) (sat_cons (step1533 p h) (sat_cons (step2684 p h) (sat_cons (step1557 p h) (sat_cons (step1556 p h) (sat_cons (step1534 p h) (sat_cons (step1723 p h) (sat_cons (step1521 p h) (sat_cons (step2743 p h) (sat_cons (step1515 p h) (sat_nil p)))))))))))
def c3210 : List Lit := [(932, false), (24, false), (864, false), (977, true), (151, true), (879, false), (874, false), (62, true), (922, false)]
theorem step3210 (p : Nat → Bool) (h : Constraints p) : clause p c3210 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1222, c1260, c1440, c1386, c1335, c1337, c1350, c1351, c1385, c3195, c1446, c1198, c1261, c1207, c1223] c3210 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1222 p h) (sat_cons (step1260 p h) (sat_cons (step1440 p h) (sat_cons (step1386 p h) (sat_cons (step1335 p h) (sat_cons (step1337 p h) (sat_cons (step1350 p h) (sat_cons (step1351 p h) (sat_cons (step1385 p h) (sat_cons (step3195 p h) (sat_cons (step1446 p h) (sat_cons (step1198 p h) (sat_cons (step1261 p h) (sat_cons (step1207 p h) (sat_cons (step1223 p h) (sat_nil p)))))))))))))))))
def c3211 : List Lit := [(936, true), (1002, true), (389, true)]
theorem step3211 (p : Nat → Bool) (h : Constraints p) : clause p c3211 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1332, c3027] c3211 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1332 p h) (sat_cons (step3027 p h) (sat_nil p))))
def c3212 : List Lit := [(24, false), (26, false), (60, false), (64, false), (151, true)]
theorem step3212 (p : Nat → Bool) (h : Constraints p) : clause p c3212 = true :=
  Snake9.LocalRup.prove_clause [c438, c179, c190] c3212 (by decide) p (sat_cons (step438 p h) (sat_cons (step179 p h) (sat_cons (step190 p h) (sat_nil p))))
def c3213 : List Lit := [(81, true), (74, true), (203, true), (1013, true)]
theorem step3213 (p : Nat → Bool) (h : Constraints p) : clause p c3213 = true :=
  Snake9.LocalRup.prove_clause [c1502, c2399, c1507, c2665, c1499] c3213 (by decide) p (sat_cons (step1502 p h) (sat_cons (step2399 p h) (sat_cons (step1507 p h) (sat_cons (step2665 p h) (sat_cons (step1499 p h) (sat_nil p))))))
def c3214 : List Lit := [(405, true), (1002, true), (90, true), (1036, true), (78, false), (1013, true)]
theorem step3214 (p : Nat → Bool) (h : Constraints p) : clause p c3214 = true :=
  Snake9.LocalRup.prove_clause [c1036, c1038, c1032, c1033, c1017, c1031, c1026, c1014, c1030, c1023, c1009, c495, c1460, c1463, c1485, c1486, c1549, c1474, c3206, c1471, c1502, c2649] c3214 (by decide) p (sat_cons (step1036 p h) (sat_cons (step1038 p h) (sat_cons (step1032 p h) (sat_cons (step1033 p h) (sat_cons (step1017 p h) (sat_cons (step1031 p h) (sat_cons (step1026 p h) (sat_cons (step1014 p h) (sat_cons (step1030 p h) (sat_cons (step1023 p h) (sat_cons (step1009 p h) (sat_cons (step495 p h) (sat_cons (step1460 p h) (sat_cons (step1463 p h) (sat_cons (step1485 p h) (sat_cons (step1486 p h) (sat_cons (step1549 p h) (sat_cons (step1474 p h) (sat_cons (step3206 p h) (sat_cons (step1471 p h) (sat_cons (step1502 p h) (sat_cons (step2649 p h) (sat_nil p)))))))))))))))))))))))
def c3215 : List Lit := [(1003, true), (66, true), (23, true), (50, false), (26, false), (6, true), (153, true), (988, false), (995, false), (196, true), (199, true)]
theorem step3215 (p : Nat → Bool) (h : Constraints p) : clause p c3215 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1487, c2689, c1477, c3009, c1468, c2327, c2070, c388, c514] c3215 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1487 p h) (sat_cons (step2689 p h) (sat_cons (step1477 p h) (sat_cons (step3009 p h) (sat_cons (step1468 p h) (sat_cons (step2327 p h) (sat_cons (step2070 p h) (sat_cons (step388 p h) (sat_cons (step514 p h) (sat_nil p)))))))))))
def c3216 : List Lit := [(26, false), (942, true), (24, false), (1003, true), (988, false), (995, false), (192, true), (151, true), (62, true)]
theorem step3216 (p : Nat → Bool) (h : Constraints p) : clause p c3216 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1343, c1463, c1487, c1477, c1468, c1474, c1491, c1466, c460, c2524, c1332, c1333, c1341, c3212, c1336] c3216 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1343 p h) (sat_cons (step1463 p h) (sat_cons (step1487 p h) (sat_cons (step1477 p h) (sat_cons (step1468 p h) (sat_cons (step1474 p h) (sat_cons (step1491 p h) (sat_cons (step1466 p h) (sat_cons (step460 p h) (sat_cons (step2524 p h) (sat_cons (step1332 p h) (sat_cons (step1333 p h) (sat_cons (step1341 p h) (sat_cons (step3212 p h) (sat_cons (step1336 p h) (sat_nil p)))))))))))))))))
def c3217 : List Lit := [(63, true), (26, true), (65, false), (192, true)]
theorem step3217 (p : Nat → Bool) (h : Constraints p) : clause p c3217 = true :=
  Snake9.LocalRup.prove_clause [c2531, c480, c2355] c3217 (by decide) p (sat_cons (step2531 p h) (sat_cons (step480 p h) (sat_cons (step2355 p h) (sat_nil p))))
def c3218 : List Lit := [(942, true), (24, false), (1003, true), (988, false), (995, false), (192, true), (151, true), (62, true)]
theorem step3218 (p : Nat → Bool) (h : Constraints p) : clause p c3218 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1487, c1477, c1468, c1474, c1491, c1466, c3216, c3217, c470, c471, c1331, c1336, c1341] c3218 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1487 p h) (sat_cons (step1477 p h) (sat_cons (step1468 p h) (sat_cons (step1474 p h) (sat_cons (step1491 p h) (sat_cons (step1466 p h) (sat_cons (step3216 p h) (sat_cons (step3217 p h) (sat_cons (step470 p h) (sat_cons (step471 p h) (sat_cons (step1331 p h) (sat_cons (step1336 p h) (sat_cons (step1341 p h) (sat_nil p)))))))))))))))
def c3219 : List Lit := [(74, false), (81, false), (78, false), (1009, true)]
theorem step3219 (p : Nat → Bool) (h : Constraints p) : clause p c3219 = true :=
  Snake9.LocalRup.prove_clause [c2649, c544, c2088, c1023, c1500, c2665, c1026, c1030, c2471, c1031] c3219 (by decide) p (sat_cons (step2649 p h) (sat_cons (step544 p h) (sat_cons (step2088 p h) (sat_cons (step1023 p h) (sat_cons (step1500 p h) (sat_cons (step2665 p h) (sat_cons (step1026 p h) (sat_cons (step1030 p h) (sat_cons (step2471 p h) (sat_cons (step1031 p h) (sat_nil p)))))))))))
def c3220 : List Lit := [(865, false), (900, true), (977, true), (151, true), (879, false), (874, false), (62, true), (922, false)]
theorem step3220 (p : Nat → Bool) (h : Constraints p) : clause p c3220 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1222, c1266, c1267, c1446, c1223, c1385, c1207, c1346, c1198, c1199, c3195] c3220 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1222 p h) (sat_cons (step1266 p h) (sat_cons (step1267 p h) (sat_cons (step1446 p h) (sat_cons (step1223 p h) (sat_cons (step1385 p h) (sat_cons (step1207 p h) (sat_cons (step1346 p h) (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step3195 p h) (sat_nil p)))))))))))))
def c3221 : List Lit := [(27, true), (44, false), (23, true), (26, false), (153, true)]
theorem step3221 (p : Nat → Bool) (h : Constraints p) : clause p c3221 = true :=
  Snake9.LocalRup.prove_clause [c202, c199, c2070] c3221 (by decide) p (sat_cons (step202 p h) (sat_cons (step199 p h) (sat_cons (step2070 p h) (sat_nil p))))
def c3222 : List Lit := [(1075, true), (110, false), (240, true)]
theorem step3222 (p : Nat → Bool) (h : Constraints p) : clause p c3222 = true :=
  Snake9.LocalRup.prove_clause [c1629, c1631, c1627, c1624, c741, c703] c3222 (by decide) p (sat_cons (step1629 p h) (sat_cons (step1631 p h) (sat_cons (step1627 p h) (sat_cons (step1624 p h) (sat_cons (step741 p h) (sat_cons (step703 p h) (sat_nil p)))))))
def c3223 : List Lit := [(1055, false), (1065, true), (99, true), (94, true), (1049, false), (225, true)]
theorem step3223 (p : Nat → Bool) (h : Constraints p) : clause p c3223 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1611, c1601, c1602, c1614, c1596, c1588, c1579, c667, c669, c2095] c3223 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1611 p h) (sat_cons (step1601 p h) (sat_cons (step1602 p h) (sat_cons (step1614 p h) (sat_cons (step1596 p h) (sat_cons (step1588 p h) (sat_cons (step1579 p h) (sat_cons (step667 p h) (sat_cons (step669 p h) (sat_cons (step2095 p h) (sat_nil p))))))))))))
def c3224 : List Lit := [(98, false), (99, true), (94, true), (85, true), (81, true), (225, true)]
theorem step3224 (p : Nat → Bool) (h : Constraints p) : clause p c3224 = true :=
  Snake9.LocalRup.prove_clause [c667, c669, c2095, c2414] c3224 (by decide) p (sat_cons (step667 p h) (sat_cons (step669 p h) (sat_cons (step2095 p h) (sat_cons (step2414 p h) (sat_nil p)))))
def c3225 : List Lit := [(1075, false), (1055, false), (1089, true), (1100, true), (1052, false), (1083, false), (99, true), (120, true), (127, true), (253, true)]
theorem step3225 (p : Nat → Bool) (h : Constraints p) : clause p c3225 = true :=
  Snake9.LocalRup.prove_clause [c1656, c1657, c1692, c2553, c1615, c1596, c1602] c3225 (by decide) p (sat_cons (step1656 p h) (sat_cons (step1657 p h) (sat_cons (step1692 p h) (sat_cons (step2553 p h) (sat_cons (step1615 p h) (sat_cons (step1596 p h) (sat_cons (step1602 p h) (sat_nil p))))))))
def c3226 : List Lit := [(1055, false), (1089, true), (1100, true), (1052, false), (1083, false), (99, true), (120, true), (127, true), (497, true)]
theorem step3226 (p : Nat → Bool) (h : Constraints p) : clause p c3226 = true :=
  Snake9.LocalRup.prove_clause [c1126, c1107, c1100, c1097, c1124, c1120, c1116, c1114, c3225, c1629, c3222, c1626, c1627, c1597, c2516, c1602, c1652, c1615, c1692] c3226 (by decide) p (sat_cons (step1126 p h) (sat_cons (step1107 p h) (sat_cons (step1100 p h) (sat_cons (step1097 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1116 p h) (sat_cons (step1114 p h) (sat_cons (step3225 p h) (sat_cons (step1629 p h) (sat_cons (step3222 p h) (sat_cons (step1626 p h) (sat_cons (step1627 p h) (sat_cons (step1597 p h) (sat_cons (step2516 p h) (sat_cons (step1602 p h) (sat_cons (step1652 p h) (sat_cons (step1615 p h) (sat_cons (step1692 p h) (sat_nil p))))))))))))))))))))
def c3227 : List Lit := [(1100, true), (1055, false), (1065, false), (1052, false), (1083, false), (99, true), (120, true), (127, true), (497, true)]
theorem step3227 (p : Nat → Bool) (h : Constraints p) : clause p c3227 = true :=
  Snake9.LocalRup.prove_clause [c1687, c3226] c3227 (by decide) p (sat_cons (step1687 p h) (sat_cons (step3226 p h) (sat_nil p)))
def c3228 : List Lit := [(1055, false), (1053, false), (1083, false), (1100, true), (240, true)]
theorem step3228 (p : Nat → Bool) (h : Constraints p) : clause p c3228 = true :=
  Snake9.LocalRup.prove_clause [c2680, c1619, c1601, c1602, c1618, c1597, c1692, c3222, c1656] c3228 (by decide) p (sat_cons (step2680 p h) (sat_cons (step1619 p h) (sat_cons (step1601 p h) (sat_cons (step1602 p h) (sat_cons (step1618 p h) (sat_cons (step1597 p h) (sat_cons (step1692 p h) (sat_cons (step3222 p h) (sat_cons (step1656 p h) (sat_nil p))))))))))
def c3229 : List Lit := [(1055, false), (99, false), (96, false), (1089, true), (1050, false), (127, true), (1100, true), (240, true)]
theorem step3229 (p : Nat → Bool) (h : Constraints p) : clause p c3229 = true :=
  Snake9.LocalRup.prove_clause [c1640, c1643, c1586, c3228, c1589, c1579, c670, c1642, c1644, c1652, c1657, c1692, c3222, c1615, c1597, c1602] c3229 (by decide) p (sat_cons (step1640 p h) (sat_cons (step1643 p h) (sat_cons (step1586 p h) (sat_cons (step3228 p h) (sat_cons (step1589 p h) (sat_cons (step1579 p h) (sat_cons (step670 p h) (sat_cons (step1642 p h) (sat_cons (step1644 p h) (sat_cons (step1652 p h) (sat_cons (step1657 p h) (sat_cons (step1692 p h) (sat_cons (step3222 p h) (sat_cons (step1615 p h) (sat_cons (step1597 p h) (sat_cons (step1602 p h) (sat_nil p)))))))))))))))))
def c3230 : List Lit := [(1090, true), (1084, false), (110, false), (115, true), (127, true), (497, true)]
theorem step3230 (p : Nat → Bool) (h : Constraints p) : clause p c3230 = true :=
  Snake9.LocalRup.prove_clause [c1623, c1126, c1107, c1100, c1097, c1124, c1120, c1116, c1114, c1113, c2691, c1662, c1625, c1632, c741, c703, c1627] c3230 (by decide) p (sat_cons (step1623 p h) (sat_cons (step1126 p h) (sat_cons (step1107 p h) (sat_cons (step1100 p h) (sat_cons (step1097 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1116 p h) (sat_cons (step1114 p h) (sat_cons (step1113 p h) (sat_cons (step2691 p h) (sat_cons (step1662 p h) (sat_cons (step1625 p h) (sat_cons (step1632 p h) (sat_cons (step741 p h) (sat_cons (step703 p h) (sat_cons (step1627 p h) (sat_nil p))))))))))))))))))
def c3231 : List Lit := [(1055, false), (1100, true), (115, true), (1049, false), (127, true), (94, true), (96, false), (1065, true), (499, true)]
theorem step3231 (p : Nat → Bool) (h : Constraints p) : clause p c3231 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1611, c1131, c1094, c1077, c1070, c1069, c1129, c1601, c3223, c1602, c1614, c1610, c1597, c1588, c1681, c1579, c3230, c670, c1644, c1642] c3231 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1611 p h) (sat_cons (step1131 p h) (sat_cons (step1094 p h) (sat_cons (step1077 p h) (sat_cons (step1070 p h) (sat_cons (step1069 p h) (sat_cons (step1129 p h) (sat_cons (step1601 p h) (sat_cons (step3223 p h) (sat_cons (step1602 p h) (sat_cons (step1614 p h) (sat_cons (step1610 p h) (sat_cons (step1597 p h) (sat_cons (step1588 p h) (sat_cons (step1681 p h) (sat_cons (step1579 p h) (sat_cons (step3230 p h) (sat_cons (step670 p h) (sat_cons (step1644 p h) (sat_cons (step1642 p h) (sat_nil p))))))))))))))))))))))
def c3232 : List Lit := [(99, true), (1060, false), (85, true), (1049, false), (1055, false), (1083, false), (127, true), (94, true), (1100, true), (1065, false), (81, true), (499, true)]
theorem step3232 (p : Nat → Bool) (h : Constraints p) : clause p c3232 = true :=
  Snake9.LocalRup.prove_clause [c1131, c1094, c1077, c1070, c1069, c1129, c1124, c1120, c1116, c1113, c3224, c1579, c1588, c1615, c3227, c1692, c2541, c2545] c3232 (by decide) p (sat_cons (step1131 p h) (sat_cons (step1094 p h) (sat_cons (step1077 p h) (sat_cons (step1070 p h) (sat_cons (step1069 p h) (sat_cons (step1129 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1116 p h) (sat_cons (step1113 p h) (sat_cons (step3224 p h) (sat_cons (step1579 p h) (sat_cons (step1588 p h) (sat_cons (step1615 p h) (sat_cons (step3227 p h) (sat_cons (step1692 p h) (sat_cons (step2541 p h) (sat_cons (step2545 p h) (sat_nil p)))))))))))))))))))
def c3233 : List Lit := [(1075, true), (104, false), (79, false)]
theorem step3233 (p : Nat → Bool) (h : Constraints p) : clause p c3233 = true :=
  Snake9.LocalRup.prove_clause [c1629, c1631, c1627, c1624, c699] c3233 (by decide) p (sat_cons (step1629 p h) (sat_cons (step1631 p h) (sat_cons (step1627 p h) (sat_cons (step1624 p h) (sat_cons (step699 p h) (sat_nil p))))))
def c3234 : List Lit := [(1083, false), (1055, false), (1049, false), (127, false), (96, true), (94, true), (85, true), (1089, true), (1100, true), (81, true), (499, true)]
theorem step3234 (p : Nat → Bool) (h : Constraints p) : clause p c3234 = true :=
  Snake9.LocalRup.prove_clause [c1129, c1124, c1120, c1116, c1113, c814, c1131, c1094, c1077, c1070, c1069, c1126, c1107, c1100, c1097, c1661, c3228, c1630, c1591, c2528, c1581, c2429, c3224] c3234 (by decide) p (sat_cons (step1129 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1116 p h) (sat_cons (step1113 p h) (sat_cons (step814 p h) (sat_cons (step1131 p h) (sat_cons (step1094 p h) (sat_cons (step1077 p h) (sat_cons (step1070 p h) (sat_cons (step1069 p h) (sat_cons (step1126 p h) (sat_cons (step1107 p h) (sat_cons (step1100 p h) (sat_cons (step1097 p h) (sat_cons (step1661 p h) (sat_cons (step3228 p h) (sat_cons (step1630 p h) (sat_cons (step1591 p h) (sat_cons (step2528 p h) (sat_cons (step1581 p h) (sat_cons (step2429 p h) (sat_cons (step3224 p h) (sat_nil p))))))))))))))))))))))))
def c3235 : List Lit := [(1055, false), (79, false), (1049, false), (127, false), (96, true), (94, true), (85, true), (1089, true), (1100, true), (81, true), (499, true)]
theorem step3235 (p : Nat → Bool) (h : Constraints p) : clause p c3235 = true :=
  Snake9.LocalRup.prove_clause [c1580, c1588, c1129, c1124, c1120, c1116, c1113, c814, c1664, c1126, c1107, c1100, c1097, c3234, c1643, c1641, c2528, c767, c1633, c2541, c1624, c1692, c741, c697, c1615, c1597, c1602] c3235 (by decide) p (sat_cons (step1580 p h) (sat_cons (step1588 p h) (sat_cons (step1129 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1116 p h) (sat_cons (step1113 p h) (sat_cons (step814 p h) (sat_cons (step1664 p h) (sat_cons (step1126 p h) (sat_cons (step1107 p h) (sat_cons (step1100 p h) (sat_cons (step1097 p h) (sat_cons (step3234 p h) (sat_cons (step1643 p h) (sat_cons (step1641 p h) (sat_cons (step2528 p h) (sat_cons (step767 p h) (sat_cons (step1633 p h) (sat_cons (step2541 p h) (sat_cons (step1624 p h) (sat_cons (step1692 p h) (sat_cons (step741 p h) (sat_cons (step697 p h) (sat_cons (step1615 p h) (sat_cons (step1597 p h) (sat_cons (step1602 p h) (sat_nil p))))))))))))))))))))))))))))
def c3236 : List Lit := [(96, false), (101, false), (119, false), (1089, true), (1071, false), (100, false), (253, true)]
theorem step3236 (p : Nat → Bool) (h : Constraints p) : clause p c3236 = true :=
  Snake9.LocalRup.prove_clause [c1631, c1657, c1644, c2527, c679, c1643, c1646, c1642, c1661, c1637, c1638, c761, c803, c1632, c808, c1627, c787] c3236 (by decide) p (sat_cons (step1631 p h) (sat_cons (step1657 p h) (sat_cons (step1644 p h) (sat_cons (step2527 p h) (sat_cons (step679 p h) (sat_cons (step1643 p h) (sat_cons (step1646 p h) (sat_cons (step1642 p h) (sat_cons (step1661 p h) (sat_cons (step1637 p h) (sat_cons (step1638 p h) (sat_cons (step761 p h) (sat_cons (step803 p h) (sat_cons (step1632 p h) (sat_cons (step808 p h) (sat_cons (step1627 p h) (sat_cons (step787 p h) (sat_nil p))))))))))))))))))
def c3237 : List Lit := [(127, false), (96, false), (254, true)]
theorem step3237 (p : Nat → Bool) (h : Constraints p) : clause p c3237 = true :=
  Snake9.LocalRup.prove_clause [c814, c815, c2099] c3237 (by decide) p (sat_cons (step814 p h) (sat_cons (step815 p h) (sat_cons (step2099 p h) (sat_nil p))))
def c3238 : List Lit := [(127, true), (1084, true), (123, false), (110, false)]
theorem step3238 (p : Nat → Bool) (h : Constraints p) : clause p c3238 = true :=
  Snake9.LocalRup.prove_clause [c1644, c1640, c1642, c1646, c786, c1638] c3238 (by decide) p (sat_cons (step1644 p h) (sat_cons (step1640 p h) (sat_cons (step1642 p h) (sat_cons (step1646 p h) (sat_cons (step786 p h) (sat_cons (step1638 p h) (sat_nil p)))))))
def c3239 : List Lit := [(106, true), (45, true), (98, false), (109, true), (111, false), (238, true)]
theorem step3239 (p : Nat → Bool) (h : Constraints p) : clause p c3239 = true :=
  Snake9.LocalRup.prove_clause [c735, c733, c2095] c3239 (by decide) p (sat_cons (step735 p h) (sat_cons (step733 p h) (sat_cons (step2095 p h) (sat_nil p))))
def c3240 : List Lit := [(1088, true), (127, true), (491, true)]
theorem step3240 (p : Nat → Bool) (h : Constraints p) : clause p c3240 = true :=
  Snake9.LocalRup.prove_clause [c1640, c1643, c1114, c1113, c1652, c2541, c1656, c1644, c1646, c1629, c1642, c1638, c1627, c2610, c787] c3240 (by decide) p (sat_cons (step1640 p h) (sat_cons (step1643 p h) (sat_cons (step1114 p h) (sat_cons (step1113 p h) (sat_cons (step1652 p h) (sat_cons (step2541 p h) (sat_cons (step1656 p h) (sat_cons (step1644 p h) (sat_cons (step1646 p h) (sat_cons (step1629 p h) (sat_cons (step1642 p h) (sat_cons (step1638 p h) (sat_cons (step1627 p h) (sat_cons (step2610 p h) (sat_cons (step787 p h) (sat_nil p))))))))))))))))
def c3241 : List Lit := [(1089, true), (1071, false), (100, false), (96, false), (499, true)]
theorem step3241 (p : Nat → Bool) (h : Constraints p) : clause p c3241 = true :=
  Snake9.LocalRup.prove_clause [c1131, c1094, c1076, c1075, c1072, c1129, c1124, c1120, c1116, c1114, c1113, c2540, c643, c3236, c676] c3241 (by decide) p (sat_cons (step1131 p h) (sat_cons (step1094 p h) (sat_cons (step1076 p h) (sat_cons (step1075 p h) (sat_cons (step1072 p h) (sat_cons (step1129 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1116 p h) (sat_cons (step1114 p h) (sat_cons (step1113 p h) (sat_cons (step2540 p h) (sat_cons (step643 p h) (sat_cons (step3236 p h) (sat_cons (step676 p h) (sat_nil p))))))))))))))))
def c3242 : List Lit := [(100, false), (91, false), (89, false), (96, false), (1089, true), (499, true)]
theorem step3242 (p : Nat → Bool) (h : Constraints p) : clause p c3242 = true :=
  Snake9.LocalRup.prove_clause [c614, c3241, c1623] c3242 (by decide) p (sat_cons (step614 p h) (sat_cons (step3241 p h) (sat_cons (step1623 p h) (sat_nil p))))
def c3243 : List Lit := [(1055, false), (1050, false), (96, false), (1089, true), (1100, true), (497, true)]
theorem step3243 (p : Nat → Bool) (h : Constraints p) : clause p c3243 = true :=
  Snake9.LocalRup.prove_clause [c1124, c1120, c1116, c1113, c3237, c3240, c1692, c1586, c1615, c1640, c1643, c1126, c1107, c1100, c1097, c1114, c3228, c3229, c1602, c1589, c1596, c1597, c1579, c3222, c1657, c1644, c3238, c1642, c809, c796] c3243 (by decide) p (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1116 p h) (sat_cons (step1113 p h) (sat_cons (step3237 p h) (sat_cons (step3240 p h) (sat_cons (step1692 p h) (sat_cons (step1586 p h) (sat_cons (step1615 p h) (sat_cons (step1640 p h) (sat_cons (step1643 p h) (sat_cons (step1126 p h) (sat_cons (step1107 p h) (sat_cons (step1100 p h) (sat_cons (step1097 p h) (sat_cons (step1114 p h) (sat_cons (step3228 p h) (sat_cons (step3229 p h) (sat_cons (step1602 p h) (sat_cons (step1589 p h) (sat_cons (step1596 p h) (sat_cons (step1597 p h) (sat_cons (step1579 p h) (sat_cons (step3222 p h) (sat_cons (step1657 p h) (sat_cons (step1644 p h) (sat_cons (step3238 p h) (sat_cons (step1642 p h) (sat_cons (step809 p h) (sat_cons (step796 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c3244 : List Lit := [(1088, true), (491, true)]
theorem step3244 (p : Nat → Bool) (h : Constraints p) : clause p c3244 = true :=
  Snake9.LocalRup.prove_clause [c1113, c1660, c2541, c3240, c1630, c814, c2609, c2528, c1627, c1641, c1629, c1643, c1656] c3244 (by decide) p (sat_cons (step1113 p h) (sat_cons (step1660 p h) (sat_cons (step2541 p h) (sat_cons (step3240 p h) (sat_cons (step1630 p h) (sat_cons (step814 p h) (sat_cons (step2609 p h) (sat_cons (step2528 p h) (sat_cons (step1627 p h) (sat_cons (step1641 p h) (sat_cons (step1629 p h) (sat_cons (step1643 p h) (sat_cons (step1656 p h) (sat_nil p))))))))))))))
def c3245 : List Lit := [(89, false), (81, false), (216, true), (11, true)]
theorem step3245 (p : Nat → Bool) (h : Constraints p) : clause p c3245 = true :=
  Snake9.LocalRup.prove_clause [c607, c3202] c3245 (by decide) p (sat_cons (step607 p h) (sat_cons (step3202 p h) (sat_nil p)))
def c3246 : List Lit := [(78, false), (103, false), (91, false), (81, false), (1009, true), (203, true)]
theorem step3246 (p : Nat → Bool) (h : Constraints p) : clause p c3246 = true :=
  Snake9.LocalRup.prove_clause [c569, c554, c2665, c1500] c3246 (by decide) p (sat_cons (step569 p h) (sat_cons (step554 p h) (sat_cons (step2665 p h) (sat_cons (step1500 p h) (sat_nil p)))))
def c3247 : List Lit := [(1099, true), (1055, false), (103, false), (1089, false), (115, true), (127, true), (497, true)]
theorem step3247 (p : Nat → Bool) (h : Constraints p) : clause p c3247 = true :=
  Snake9.LocalRup.prove_clause [c1601, c1606, c1126, c1107, c1100, c1097, c1124, c1120, c1116, c1114, c1113, c1680, c1676, c1607, c2691, c1602, c1625, c1597, c741, c700] c3247 (by decide) p (sat_cons (step1601 p h) (sat_cons (step1606 p h) (sat_cons (step1126 p h) (sat_cons (step1107 p h) (sat_cons (step1100 p h) (sat_cons (step1097 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step1116 p h) (sat_cons (step1114 p h) (sat_cons (step1113 p h) (sat_cons (step1680 p h) (sat_cons (step1676 p h) (sat_cons (step1607 p h) (sat_cons (step2691 p h) (sat_cons (step1602 p h) (sat_cons (step1625 p h) (sat_cons (step1597 p h) (sat_cons (step741 p h) (sat_cons (step700 p h) (sat_nil p)))))))))))))))))))))
def c3248 : List Lit := [(1120, true), (1057, false), (1052, false), (1035, false), (1010, false), (78, false), (1013, true), (1088, false), (1001, false), (201, true), (203, true)]
theorem step3248 (p : Nat → Bool) (h : Constraints p) : clause p c3248 = true :=
  Snake9.LocalRup.prove_clause [c1599, c1614, c1686, c1712, c1718, c1692, c1549, c1615, c3205, c1602, c2703, c1593] c3248 (by decide) p (sat_cons (step1599 p h) (sat_cons (step1614 p h) (sat_cons (step1686 p h) (sat_cons (step1712 p h) (sat_cons (step1718 p h) (sat_cons (step1692 p h) (sat_cons (step1549 p h) (sat_cons (step1615 p h) (sat_cons (step3205 p h) (sat_cons (step1602 p h) (sat_cons (step2703 p h) (sat_cons (step1593 p h) (sat_nil p)))))))))))))
def c3249 : List Lit := [(451, true), (98, false), (77, false), (94, true), (96, false), (85, true), (100, false), (81, true)]
theorem step3249 (p : Nat → Bool) (h : Constraints p) : clause p c3249 = true :=
  Snake9.LocalRup.prove_clause [c1076, c1077, c1075, c1070, c1072, c1069, c676, c3224, c655] c3249 (by decide) p (sat_cons (step1076 p h) (sat_cons (step1077 p h) (sat_cons (step1075 p h) (sat_cons (step1070 p h) (sat_cons (step1072 p h) (sat_cons (step1069 p h) (sat_cons (step676 p h) (sat_cons (step3224 p h) (sat_cons (step655 p h) (sat_nil p))))))))))
def c3250 : List Lit := [(1079, true), (108, false), (249, true), (69, false), (72, false), (65, false), (989, true)]
theorem step3250 (p : Nat → Bool) (h : Constraints p) : clause p c3250 = true :=
  Snake9.LocalRup.prove_clause [c2413, c2427, c1637, c1638, c2554, c472, c780, c2577, c2535, c2437] c3250 (by decide) p (sat_cons (step2413 p h) (sat_cons (step2427 p h) (sat_cons (step1637 p h) (sat_cons (step1638 p h) (sat_cons (step2554 p h) (sat_cons (step472 p h) (sat_cons (step780 p h) (sat_cons (step2577 p h) (sat_cons (step2535 p h) (sat_cons (step2437 p h) (sat_nil p)))))))))))
def c3251 : List Lit := [(854, false), (975, true), (941, false), (852, false), (885, false), (922, false), (11, true)]
theorem step3251 (p : Nat → Bool) (h : Constraints p) : clause p c3251 = true :=
  Snake9.LocalRup.prove_clause [c1346, c1385, c1432, c1264, c1177, c1160, c1161, c1176, c1156, c1258, c1259, c1425, c1213, c1386, c1205, c1351, c3186] c3251 (by decide) p (sat_cons (step1346 p h) (sat_cons (step1385 p h) (sat_cons (step1432 p h) (sat_cons (step1264 p h) (sat_cons (step1177 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1176 p h) (sat_cons (step1156 p h) (sat_cons (step1258 p h) (sat_cons (step1259 p h) (sat_cons (step1425 p h) (sat_cons (step1213 p h) (sat_cons (step1386 p h) (sat_cons (step1205 p h) (sat_cons (step1351 p h) (sat_cons (step3186 p h) (sat_nil p))))))))))))))))))
def c3252 : List Lit := [(936, true), (4, true), (21, false), (1002, true), (2, false)]
theorem step3252 (p : Nat → Bool) (h : Constraints p) : clause p c3252 = true :=
  Snake9.LocalRup.prove_clause [c1332, c3211, c2562, c1038, c881, c1065, c882, c1136, c894, c2488, c910, c1002, c943] c3252 (by decide) p (sat_cons (step1332 p h) (sat_cons (step3211 p h) (sat_cons (step2562 p h) (sat_cons (step1038 p h) (sat_cons (step881 p h) (sat_cons (step1065 p h) (sat_cons (step882 p h) (sat_cons (step1136 p h) (sat_cons (step894 p h) (sat_cons (step2488 p h) (sat_cons (step910 p h) (sat_cons (step1002 p h) (sat_cons (step943 p h) (sat_nil p))))))))))))))
def c3253 : List Lit := [(1101, true), (1089, false), (1084, false), (108, true), (127, true), (497, true), (1052, false), (91, true)]
theorem step3253 (p : Nat → Bool) (h : Constraints p) : clause p c3253 = true :=
  Snake9.LocalRup.prove_clause [c1593, c1601, c1614, c1126, c1107, c1099, c1098, c1688, c1693, c1615, c1604, c1602, c1595, c1596, c1597, c3230, c746, c718] c3253 (by decide) p (sat_cons (step1593 p h) (sat_cons (step1601 p h) (sat_cons (step1614 p h) (sat_cons (step1126 p h) (sat_cons (step1107 p h) (sat_cons (step1099 p h) (sat_cons (step1098 p h) (sat_cons (step1688 p h) (sat_cons (step1693 p h) (sat_cons (step1615 p h) (sat_cons (step1604 p h) (sat_cons (step1602 p h) (sat_cons (step1595 p h) (sat_cons (step1596 p h) (sat_cons (step1597 p h) (sat_cons (step3230 p h) (sat_cons (step746 p h) (sat_cons (step718 p h) (sat_nil p)))))))))))))))))))
def c3254 : List Lit := [(877, true), (941, true), (151, true), (62, true)]
theorem step3254 (p : Nat → Bool) (h : Constraints p) : clause p c3254 = true :=
  Snake9.LocalRup.prove_clause [c1198, c1199, c3195] c3254 (by decide) p (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step3195 p h) (sat_nil p))))
end B112E260
