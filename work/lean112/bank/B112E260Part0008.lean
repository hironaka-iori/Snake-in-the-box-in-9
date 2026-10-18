import B112E260Part0007
namespace B112E260
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2615 : List Lit := [(309, false), (869, true), (11, true), (10, false), (42, true)]
theorem step2615 (p : Nat → Bool) (h : Constraints p) : clause p c2615 = true :=
  Snake9.LocalRup.prove_clause [c1185, c1184, c936, c2455, c2456, c919, c908, c914, c904, c906, c913, c901, c898, c2344, c900, c897, c2380, c138, c75, c344, c2378] c2615 (by decide) p (sat_cons (step1185 p h) (sat_cons (step1184 p h) (sat_cons (step936 p h) (sat_cons (step2455 p h) (sat_cons (step2456 p h) (sat_cons (step919 p h) (sat_cons (step908 p h) (sat_cons (step914 p h) (sat_cons (step904 p h) (sat_cons (step906 p h) (sat_cons (step913 p h) (sat_cons (step901 p h) (sat_cons (step898 p h) (sat_cons (step2344 p h) (sat_cons (step900 p h) (sat_cons (step897 p h) (sat_cons (step2380 p h) (sat_cons (step138 p h) (sat_cons (step75 p h) (sat_cons (step344 p h) (sat_cons (step2378 p h) (sat_nil p))))))))))))))))))))))
def c2616 : List Lit := [(279, true), (49, false), (15, false), (11, true), (10, false)]
theorem step2616 (p : Nat → Bool) (h : Constraints p) : clause p c2616 = true :=
  Snake9.LocalRup.prove_clause [c904, c906, c901, c898, c900, c897, c138, c75, c2378, c344] c2616 (by decide) p (sat_cons (step904 p h) (sat_cons (step906 p h) (sat_cons (step901 p h) (sat_cons (step898 p h) (sat_cons (step900 p h) (sat_cons (step897 p h) (sat_cons (step138 p h) (sat_cons (step75 p h) (sat_cons (step2378 p h) (sat_cons (step344 p h) (sat_nil p)))))))))))
def c2617 : List Lit := [(849, true), (38, true), (129, true), (56, true)]
theorem step2617 (p : Nat → Bool) (h : Constraints p) : clause p c2617 = true :=
  Snake9.LocalRup.prove_clause [c1144, c1145, c13, c14, c2348, c26] c2617 (by decide) p (sat_cons (step1144 p h) (sat_cons (step1145 p h) (sat_cons (step13 p h) (sat_cons (step14 p h) (sat_cons (step2348 p h) (sat_cons (step26 p h) (sat_nil p)))))))
def c2618 : List Lit := [(1059, false), (1097, true), (110, false)]
theorem step2618 (p : Nat → Bool) (h : Constraints p) : clause p c2618 = true :=
  Snake9.LocalRup.prove_clause [c2573, c1678, c1607, c2580, c2584, c1610, c1629, c1638, c1585, c1627, c1582, c784, c2604, c2606] c2618 (by decide) p (sat_cons (step2573 p h) (sat_cons (step1678 p h) (sat_cons (step1607 p h) (sat_cons (step2580 p h) (sat_cons (step2584 p h) (sat_cons (step1610 p h) (sat_cons (step1629 p h) (sat_cons (step1638 p h) (sat_cons (step1585 p h) (sat_cons (step1627 p h) (sat_cons (step1582 p h) (sat_cons (step784 p h) (sat_cons (step2604 p h) (sat_cons (step2606 p h) (sat_nil p)))))))))))))))
def c2619 : List Lit := [(103, true), (1079, false), (1097, true)]
theorem step2619 (p : Nat → Bool) (h : Constraints p) : clause p c2619 = true :=
  Snake9.LocalRup.prove_clause [c2573, c1678, c1613, c1582, c2526, c1585, c1646, c1609, c1652, c1674] c2619 (by decide) p (sat_cons (step2573 p h) (sat_cons (step1678 p h) (sat_cons (step1613 p h) (sat_cons (step1582 p h) (sat_cons (step2526 p h) (sat_cons (step1585 p h) (sat_cons (step1646 p h) (sat_cons (step1609 p h) (sat_cons (step1652 p h) (sat_cons (step1674 p h) (sat_nil p)))))))))))
def c2620 : List Lit := [(1084, false), (1059, true), (1097, true)]
theorem step2620 (p : Nat → Bool) (h : Constraints p) : clause p c2620 = true :=
  Snake9.LocalRup.prove_clause [c1599, c1597, c1671, c1601, c1593, c1596, c728, c2581, c1645, c1661, c2619, c2607, c2611, c1653, c1647, c2576, c1652, c1657, c1674, c1629, c1609, c1627, c1585, c1587, c785, c1583, c1580, c1642, c758, c679, c813] c2620 (by decide) p (sat_cons (step1599 p h) (sat_cons (step1597 p h) (sat_cons (step1671 p h) (sat_cons (step1601 p h) (sat_cons (step1593 p h) (sat_cons (step1596 p h) (sat_cons (step728 p h) (sat_cons (step2581 p h) (sat_cons (step1645 p h) (sat_cons (step1661 p h) (sat_cons (step2619 p h) (sat_cons (step2607 p h) (sat_cons (step2611 p h) (sat_cons (step1653 p h) (sat_cons (step1647 p h) (sat_cons (step2576 p h) (sat_cons (step1652 p h) (sat_cons (step1657 p h) (sat_cons (step1674 p h) (sat_cons (step1629 p h) (sat_cons (step1609 p h) (sat_cons (step1627 p h) (sat_cons (step1585 p h) (sat_cons (step1587 p h) (sat_cons (step785 p h) (sat_cons (step1583 p h) (sat_cons (step1580 p h) (sat_cons (step1642 p h) (sat_cons (step758 p h) (sat_cons (step679 p h) (sat_cons (step813 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2621 : List Lit := [(1059, true), (1097, true)]
theorem step2621 (p : Nat → Bool) (h : Constraints p) : clause p c2621 = true :=
  Snake9.LocalRup.prove_clause [c1671, c1599, c1601, c1596, c1597, c1593, c728, c2581, c2576, c1645, c1661, c2619, c2607, c2611, c2620, c1646, c1640, c1641, c785, c767, c1627, c814, c1632, c1113, c1624, c1116, c741, c1120, c1097, c2485, c1100, c1107] c2621 (by decide) p (sat_cons (step1671 p h) (sat_cons (step1599 p h) (sat_cons (step1601 p h) (sat_cons (step1596 p h) (sat_cons (step1597 p h) (sat_cons (step1593 p h) (sat_cons (step728 p h) (sat_cons (step2581 p h) (sat_cons (step2576 p h) (sat_cons (step1645 p h) (sat_cons (step1661 p h) (sat_cons (step2619 p h) (sat_cons (step2607 p h) (sat_cons (step2611 p h) (sat_cons (step2620 p h) (sat_cons (step1646 p h) (sat_cons (step1640 p h) (sat_cons (step1641 p h) (sat_cons (step785 p h) (sat_cons (step767 p h) (sat_cons (step1627 p h) (sat_cons (step814 p h) (sat_cons (step1632 p h) (sat_cons (step1113 p h) (sat_cons (step1624 p h) (sat_cons (step1116 p h) (sat_cons (step741 p h) (sat_cons (step1120 p h) (sat_cons (step1097 p h) (sat_cons (step2485 p h) (sat_cons (step1100 p h) (sat_cons (step1107 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c2622 : List Lit := [(1097, true)]
theorem step2622 (p : Nat → Bool) (h : Constraints p) : clause p c2622 = true :=
  Snake9.LocalRup.prove_clause [c2573, c1671, c1678, c2621, c2584, c1610, c2618, c1638, c2605] c2622 (by decide) p (sat_cons (step2573 p h) (sat_cons (step1671 p h) (sat_cons (step1678 p h) (sat_cons (step2621 p h) (sat_cons (step2584 p h) (sat_cons (step1610 p h) (sat_cons (step2618 p h) (sat_cons (step1638 p h) (sat_cons (step2605 p h) (sat_nil p))))))))))
def c2623 : List Lit := [(885, true), (864, true), (155, true)]
theorem step2623 (p : Nat → Bool) (h : Constraints p) : clause p c2623 = true :=
  Snake9.LocalRup.prove_clause [c1212, c1216, c1204, c1192, c1202, c1185, c210, c96, c86, c102, c1149, c1157, c1172, c1159] c2623 (by decide) p (sat_cons (step1212 p h) (sat_cons (step1216 p h) (sat_cons (step1204 p h) (sat_cons (step1192 p h) (sat_cons (step1202 p h) (sat_cons (step1185 p h) (sat_cons (step210 p h) (sat_cons (step96 p h) (sat_cons (step86 p h) (sat_cons (step102 p h) (sat_cons (step1149 p h) (sat_cons (step1157 p h) (sat_cons (step1172 p h) (sat_cons (step1159 p h) (sat_nil p)))))))))))))))
def c2624 : List Lit := [(915, true), (45, false), (111, false)]
theorem step2624 (p : Nat → Bool) (h : Constraints p) : clause p c2624 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1290, c327] c2624 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1290 p h) (sat_cons (step327 p h) (sat_nil p))))
def c2625 : List Lit := [(877, true), (60, false), (939, true), (38, true), (42, false), (32, false), (49, false)]
theorem step2625 (p : Nat → Bool) (h : Constraints p) : clause p c2625 = true :=
  Snake9.LocalRup.prove_clause [c1198, c2530, c181, c921, c924, c933, c936, c941, c2464, c997, c970, c972, c968, c954, c959, c949, c958, c946, c298, c227, c384, c2362] c2625 (by decide) p (sat_cons (step1198 p h) (sat_cons (step2530 p h) (sat_cons (step181 p h) (sat_cons (step921 p h) (sat_cons (step924 p h) (sat_cons (step933 p h) (sat_cons (step936 p h) (sat_cons (step941 p h) (sat_cons (step2464 p h) (sat_cons (step997 p h) (sat_cons (step970 p h) (sat_cons (step972 p h) (sat_cons (step968 p h) (sat_cons (step954 p h) (sat_cons (step959 p h) (sat_cons (step949 p h) (sat_cons (step958 p h) (sat_cons (step946 p h) (sat_cons (step298 p h) (sat_cons (step227 p h) (sat_cons (step384 p h) (sat_cons (step2362 p h) (sat_nil p)))))))))))))))))))))))
def c2626 : List Lit := [(941, true), (38, true), (42, false), (32, false), (877, true), (938, false), (49, false)]
theorem step2626 (p : Nat → Bool) (h : Constraints p) : clause p c2626 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1340, c2625, c1331] c2626 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1340 p h) (sat_cons (step2625 p h) (sat_cons (step1331 p h) (sat_nil p)))))
def c2627 : List Lit := [(5, false), (12, false), (51, false), (46, false)]
theorem step2627 (p : Nat → Bool) (h : Constraints p) : clause p c2627 = true :=
  Snake9.LocalRup.prove_clause [c128, c286, c378] c2627 (by decide) p (sat_cons (step128 p h) (sat_cons (step286 p h) (sat_cons (step378 p h) (sat_nil p))))
def c2628 : List Lit := [(47, true), (880, true), (11, true), (50, false), (10, false)]
theorem step2628 (p : Nat → Bool) (h : Constraints p) : clause p c2628 = true :=
  Snake9.LocalRup.prove_clause [c75, c71, c897, c124, c898, c1203, c906, c210, c908, c926, c2456, c929, c936, c931] c2628 (by decide) p (sat_cons (step75 p h) (sat_cons (step71 p h) (sat_cons (step897 p h) (sat_cons (step124 p h) (sat_cons (step898 p h) (sat_cons (step1203 p h) (sat_cons (step906 p h) (sat_cons (step210 p h) (sat_cons (step908 p h) (sat_cons (step926 p h) (sat_cons (step2456 p h) (sat_cons (step929 p h) (sat_cons (step936 p h) (sat_cons (step931 p h) (sat_nil p)))))))))))))))
def c2629 : List Lit := [(47, false), (929, true), (50, false), (10, false)]
theorem step2629 (p : Nat → Bool) (h : Constraints p) : clause p c2629 = true :=
  Snake9.LocalRup.prove_clause [c346, c345, c1319] c2629 (by decide) p (sat_cons (step346 p h) (sat_cons (step345 p h) (sat_cons (step1319 p h) (sat_nil p))))
def c2630 : List Lit := [(6, false), (23, true), (44, false), (26, false), (133, true)]
theorem step2630 (p : Nat → Bool) (h : Constraints p) : clause p c2630 = true :=
  Snake9.LocalRup.prove_clause [c62, c54] c2630 (by decide) p (sat_cons (step62 p h) (sat_cons (step54 p h) (sat_nil p)))
def c2631 : List Lit := [(178, true), (12, true), (51, false)]
theorem step2631 (p : Nat → Bool) (h : Constraints p) : clause p c2631 = true :=
  Snake9.LocalRup.prove_clause [c2560, c381, c2342] c2631 (by decide) p (sat_cons (step2560 p h) (sat_cons (step381 p h) (sat_cons (step2342 p h) (sat_nil p))))
def c2632 : List Lit := [(913, true), (62, false), (51, false), (915, true)]
theorem step2632 (p : Nat → Bool) (h : Constraints p) : clause p c2632 = true :=
  Snake9.LocalRup.prove_clause [c1290, c1289, c1286, c1287, c305, c2171] c2632 (by decide) p (sat_cons (step1290 p h) (sat_cons (step1289 p h) (sat_cons (step1286 p h) (sat_cons (step1287 p h) (sat_cons (step305 p h) (sat_cons (step2171 p h) (sat_nil p)))))))
def c2633 : List Lit := [(20, false), (22, true), (3, true), (147, true), (40, false), (64, false)]
theorem step2633 (p : Nat → Bool) (h : Constraints p) : clause p c2633 = true :=
  Snake9.LocalRup.prove_clause [c413, c153] c2633 (by decide) p (sat_cons (step413 p h) (sat_cons (step153 p h) (sat_nil p)))
def c2634 : List Lit := [(24, false), (26, false), (854, true), (151, true), (941, true)]
theorem step2634 (p : Nat → Bool) (h : Constraints p) : clause p c2634 = true :=
  Snake9.LocalRup.prove_clause [c1153, c1152, c1338, c172, c191, c192, c190, c1335, c1336, c438, c1340, c1331] c2634 (by decide) p (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step1338 p h) (sat_cons (step172 p h) (sat_cons (step191 p h) (sat_cons (step192 p h) (sat_cons (step190 p h) (sat_cons (step1335 p h) (sat_cons (step1336 p h) (sat_cons (step438 p h) (sat_cons (step1340 p h) (sat_cons (step1331 p h) (sat_nil p)))))))))))))
def c2635 : List Lit := [(10, false), (11, true), (137, true), (928, true)]
theorem step2635 (p : Nat → Bool) (h : Constraints p) : clause p c2635 = true :=
  Snake9.LocalRup.prove_clause [c1318, c1317, c344, c75] c2635 (by decide) p (sat_cons (step1318 p h) (sat_cons (step1317 p h) (sat_cons (step344 p h) (sat_cons (step75 p h) (sat_nil p)))))
def c2636 : List Lit := [(917, true), (45, false), (46, false)]
theorem step2636 (p : Nat → Bool) (h : Constraints p) : clause p c2636 = true :=
  Snake9.LocalRup.prove_clause [c1292, c1294, c1290, c1287, c321] c2636 (by decide) p (sat_cons (step1292 p h) (sat_cons (step1294 p h) (sat_cons (step1290 p h) (sat_cons (step1287 p h) (sat_cons (step321 p h) (sat_nil p))))))
def c2637 : List Lit := [(9, true), (45, true), (43, true), (46, false), (7, false)]
theorem step2637 (p : Nat → Bool) (h : Constraints p) : clause p c2637 = true :=
  Snake9.LocalRup.prove_clause [c60, c338, c886, c962, c889, c963, c892, c966, c910, c970, c943, c997, c2464] c2637 (by decide) p (sat_cons (step60 p h) (sat_cons (step338 p h) (sat_cons (step886 p h) (sat_cons (step962 p h) (sat_cons (step889 p h) (sat_cons (step963 p h) (sat_cons (step892 p h) (sat_cons (step966 p h) (sat_cons (step910 p h) (sat_cons (step970 p h) (sat_cons (step943 p h) (sat_cons (step997 p h) (sat_cons (step2464 p h) (sat_nil p))))))))))))))
def c2638 : List Lit := [(928, false), (910, false), (954, true), (915, true), (62, false)]
theorem step2638 (p : Nat → Bool) (h : Constraints p) : clause p c2638 = true :=
  Snake9.LocalRup.prove_clause [c1304, c1377, c1354, c1325, c1326, c1349, c1320, c1384, c2632, c1305, c1294] c2638 (by decide) p (sat_cons (step1304 p h) (sat_cons (step1377 p h) (sat_cons (step1354 p h) (sat_cons (step1325 p h) (sat_cons (step1326 p h) (sat_cons (step1349 p h) (sat_cons (step1320 p h) (sat_cons (step1384 p h) (sat_cons (step2632 p h) (sat_cons (step1305 p h) (sat_cons (step1294 p h) (sat_nil p))))))))))))
def c2639 : List Lit := [(928, true), (914, true), (17, false), (175, true), (36, false), (53, false), (16, false)]
theorem step2639 (p : Nat → Bool) (h : Constraints p) : clause p c2639 = true :=
  Snake9.LocalRup.prove_clause [c2347, c1317, c1318, c384, c347, c1288, c247, c365, c362, c134] c2639 (by decide) p (sat_cons (step2347 p h) (sat_cons (step1317 p h) (sat_cons (step1318 p h) (sat_cons (step384 p h) (sat_cons (step347 p h) (sat_cons (step1288 p h) (sat_cons (step247 p h) (sat_cons (step365 p h) (sat_cons (step362 p h) (sat_cons (step134 p h) (sat_nil p)))))))))))
def c2640 : List Lit := [(12, false), (67, true), (155, true), (139, true), (48, false), (15, false)]
theorem step2640 (p : Nat → Bool) (h : Constraints p) : clause p c2640 = true :=
  Snake9.LocalRup.prove_clause [c103, c210, c122, c2356] c2640 (by decide) p (sat_cons (step103 p h) (sat_cons (step210 p h) (sat_cons (step122 p h) (sat_cons (step2356 p h) (sat_nil p)))))
def c2641 : List Lit := [(134, true), (7, false), (25, true), (46, false)]
theorem step2641 (p : Nat → Bool) (h : Constraints p) : clause p c2641 = true :=
  Snake9.LocalRup.prove_clause [c59, c61, c2068] c2641 (by decide) p (sat_cons (step59 p h) (sat_cons (step61 p h) (sat_cons (step2068 p h) (sat_nil p))))
def c2642 : List Lit := [(74, false), (1026, true), (201, true)]
theorem step2642 (p : Nat → Bool) (h : Constraints p) : clause p c2642 = true :=
  Snake9.LocalRup.prove_clause [c2595, c523, c524, c1502, c2088] c2642 (by decide) p (sat_cons (step2595 p h) (sat_cons (step523 p h) (sat_cons (step524 p h) (sat_cons (step1502 p h) (sat_cons (step2088 p h) (sat_nil p))))))
def c2643 : List Lit := [(40, true), (923, true), (915, false), (38, false), (2, false)]
theorem step2643 (p : Nat → Bool) (h : Constraints p) : clause p c2643 = true :=
  Snake9.LocalRup.prove_clause [c1302, c1298, c1287, c1288, c1295, c253, c1306, c1278, c1281] c2643 (by decide) p (sat_cons (step1302 p h) (sat_cons (step1298 p h) (sat_cons (step1287 p h) (sat_cons (step1288 p h) (sat_cons (step1295 p h) (sat_cons (step253 p h) (sat_cons (step1306 p h) (sat_cons (step1278 p h) (sat_cons (step1281 p h) (sat_nil p))))))))))
def c2644 : List Lit := [(1036, true), (1025, false), (993, false), (381, false)]
theorem step2644 (p : Nat → Bool) (h : Constraints p) : clause p c2644 = true :=
  Snake9.LocalRup.prove_clause [c2468, c1014, c1009, c495, c1460, c1463, c1476, c1486, c1019, c2472, c1033, c1026, c1023, c1555, c1561, c2642, c1487, c1471, c1477] c2644 (by decide) p (sat_cons (step2468 p h) (sat_cons (step1014 p h) (sat_cons (step1009 p h) (sat_cons (step495 p h) (sat_cons (step1460 p h) (sat_cons (step1463 p h) (sat_cons (step1476 p h) (sat_cons (step1486 p h) (sat_cons (step1019 p h) (sat_cons (step2472 p h) (sat_cons (step1033 p h) (sat_cons (step1026 p h) (sat_cons (step1023 p h) (sat_cons (step1555 p h) (sat_cons (step1561 p h) (sat_cons (step2642 p h) (sat_cons (step1487 p h) (sat_cons (step1471 p h) (sat_cons (step1477 p h) (sat_nil p))))))))))))))))))))
def c2645 : List Lit := [(81, true), (94, false), (20, false), (203, true), (74, true), (1013, true)]
theorem step2645 (p : Nat → Bool) (h : Constraints p) : clause p c2645 = true :=
  Snake9.LocalRup.prove_clause [c1502, c2399, c1507, c1499, c534, c624, c2401] c2645 (by decide) p (sat_cons (step1502 p h) (sat_cons (step2399 p h) (sat_cons (step1507 p h) (sat_cons (step1499 p h) (sat_cons (step534 p h) (sat_cons (step624 p h) (sat_cons (step2401 p h) (sat_nil p))))))))
def c2646 : List Lit := [(81, true), (20, false), (203, true), (74, true), (1013, true)]
theorem step2646 (p : Nat → Bool) (h : Constraints p) : clause p c2646 = true :=
  Snake9.LocalRup.prove_clause [c1502, c2399, c2645, c1507, c533, c1499] c2646 (by decide) p (sat_cons (step1502 p h) (sat_cons (step2399 p h) (sat_cons (step2645 p h) (sat_cons (step1507 p h) (sat_cons (step533 p h) (sat_cons (step1499 p h) (sat_nil p)))))))
def c2647 : List Lit := [(206, true), (96, true), (78, true), (83, true), (79, false)]
theorem step2647 (p : Nat → Bool) (h : Constraints p) : clause p c2647 = true :=
  Snake9.LocalRup.prove_clause [c563, c564, c2423, c2094] c2647 (by decide) p (sat_cons (step563 p h) (sat_cons (step564 p h) (sat_cons (step2423 p h) (sat_cons (step2094 p h) (sat_nil p)))))
def c2648 : List Lit := [(32, false), (159, true), (60, false), (33, true)]
theorem step2648 (p : Nat → Bool) (h : Constraints p) : clause p c2648 = true :=
  Snake9.LocalRup.prove_clause [c227, c225, c2078] c2648 (by decide) p (sat_cons (step227 p h) (sat_cons (step225 p h) (sat_cons (step2078 p h) (sat_nil p))))
def c2649 : List Lit := [(74, false), (201, true), (81, false)]
theorem step2649 (p : Nat → Bool) (h : Constraints p) : clause p c2649 = true :=
  Snake9.LocalRup.prove_clause [c523, c524, c2088] c2649 (by decide) p (sat_cons (step523 p h) (sat_cons (step524 p h) (sat_cons (step2088 p h) (sat_nil p))))
def c2650 : List Lit := [(877, true), (25, true), (60, false), (151, true)]
theorem step2650 (p : Nat → Bool) (h : Constraints p) : clause p c2650 = true :=
  Snake9.LocalRup.prove_clause [c1198, c1199, c179, c191] c2650 (by decide) p (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step179 p h) (sat_cons (step191 p h) (sat_nil p)))))
def c2651 : List Lit := [(855, false), (864, true), (11, false)]
theorem step2651 (p : Nat → Bool) (h : Constraints p) : clause p c2651 = true :=
  Snake9.LocalRup.prove_clause [c1168, c1163, c1164, c1172, c1155, c1156, c1149, c77] c2651 (by decide) p (sat_cons (step1168 p h) (sat_cons (step1163 p h) (sat_cons (step1164 p h) (sat_cons (step1172 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1149 p h) (sat_cons (step77 p h) (sat_nil p)))))))))
def c2652 : List Lit := [(28, false), (11, false), (67, true), (155, true)]
theorem step2652 (p : Nat → Bool) (h : Constraints p) : clause p c2652 = true :=
  Snake9.LocalRup.prove_clause [c209, c2072, c2357] c2652 (by decide) p (sat_cons (step209 p h) (sat_cons (step2072 p h) (sat_cons (step2357 p h) (sat_nil p))))
def c2653 : List Lit := [(1037, true), (991, false), (73, true), (201, true), (1025, false)]
theorem step2653 (p : Nat → Bool) (h : Constraints p) : clause p c2653 = true :=
  Snake9.LocalRup.prove_clause [c1472, c1474, c1491, c1568, c1562, c1492, c2642, c1475, c1473] c2653 (by decide) p (sat_cons (step1472 p h) (sat_cons (step1474 p h) (sat_cons (step1491 p h) (sat_cons (step1568 p h) (sat_cons (step1562 p h) (sat_cons (step1492 p h) (sat_cons (step2642 p h) (sat_cons (step1475 p h) (sat_cons (step1473 p h) (sat_nil p))))))))))
def c2654 : List Lit := [(941, true), (61, false), (62, true), (24, false)]
theorem step2654 (p : Nat → Bool) (h : Constraints p) : clause p c2654 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1338, c1340, c1336, c1331, c438] c2654 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1338 p h) (sat_cons (step1340 p h) (sat_cons (step1336 p h) (sat_cons (step1331 p h) (sat_cons (step438 p h) (sat_nil p)))))))
def c2655 : List Lit := [(917, true), (46, false), (7, true), (173, true), (43, true)]
theorem step2655 (p : Nat → Bool) (h : Constraints p) : clause p c2655 = true :=
  Snake9.LocalRup.prove_clause [c1294, c2636, c1287, c337, c338, c284, c2330] c2655 (by decide) p (sat_cons (step1294 p h) (sat_cons (step2636 p h) (sat_cons (step1287 p h) (sat_cons (step337 p h) (sat_cons (step338 p h) (sat_cons (step284 p h) (sat_cons (step2330 p h) (sat_nil p))))))))
def c2656 : List Lit := [(9, true), (40, false), (46, false), (173, true), (43, true)]
theorem step2656 (p : Nat → Bool) (h : Constraints p) : clause p c2656 = true :=
  Snake9.LocalRup.prove_clause [c338, c340, c2083] c2656 (by decide) p (sat_cons (step338 p h) (sat_cons (step340 p h) (sat_cons (step2083 p h) (sat_nil p))))
def c2657 : List Lit := [(403, false), (991, true), (30, false), (4, true), (21, false), (2, false)]
theorem step2657 (p : Nat → Bool) (h : Constraints p) : clause p c2657 = true :=
  Snake9.LocalRup.prove_clause [c1036, c2472, c1065, c1017, c1019, c1136, c1014, c1006, c2488, c1009, c1005, c1002, c495, c941, c943, c1460, c936, c910, c1466, c931, c894, c928, c882, c927, c881, c218, c15, c166, c164, c481] c2657 (by decide) p (sat_cons (step1036 p h) (sat_cons (step2472 p h) (sat_cons (step1065 p h) (sat_cons (step1017 p h) (sat_cons (step1019 p h) (sat_cons (step1136 p h) (sat_cons (step1014 p h) (sat_cons (step1006 p h) (sat_cons (step2488 p h) (sat_cons (step1009 p h) (sat_cons (step1005 p h) (sat_cons (step1002 p h) (sat_cons (step495 p h) (sat_cons (step941 p h) (sat_cons (step943 p h) (sat_cons (step1460 p h) (sat_cons (step936 p h) (sat_cons (step910 p h) (sat_cons (step1466 p h) (sat_cons (step931 p h) (sat_cons (step894 p h) (sat_cons (step928 p h) (sat_cons (step882 p h) (sat_cons (step927 p h) (sat_cons (step881 p h) (sat_cons (step218 p h) (sat_cons (step15 p h) (sat_cons (step166 p h) (sat_cons (step164 p h) (sat_cons (step481 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2658 : List Lit := [(393, true), (1026, true), (996, true), (67, false), (62, false)]
theorem step2658 (p : Nat → Bool) (h : Constraints p) : clause p c2658 = true :=
  Snake9.LocalRup.prove_clause [c1023, c1024, c2642, c2509, c1473] c2658 (by decide) p (sat_cons (step1023 p h) (sat_cons (step1024 p h) (sat_cons (step2642 p h) (sat_cons (step2509 p h) (sat_cons (step1473 p h) (sat_nil p))))))
def c2659 : List Lit := [(1012, true), (203, true), (94, false)]
theorem step2659 (p : Nat → Bool) (h : Constraints p) : clause p c2659 = true :=
  Snake9.LocalRup.prove_clause [c1506, c2533, c1499, c2401, c2090] c2659 (by decide) p (sat_cons (step1506 p h) (sat_cons (step2533 p h) (sat_cons (step1499 p h) (sat_cons (step2401 p h) (sat_cons (step2090 p h) (sat_nil p))))))
def c2660 : List Lit := [(73, false), (35, true), (67, false), (62, false)]
theorem step2660 (p : Nat → Bool) (h : Constraints p) : clause p c2660 = true :=
  Snake9.LocalRup.prove_clause [c516, c505] c2660 (by decide) p (sat_cons (step516 p h) (sat_cons (step505 p h) (sat_nil p)))
def c2661 : List Lit := [(60, false), (32, false), (26, false), (199, true), (72, false)]
theorem step2661 (p : Nat → Bool) (h : Constraints p) : clause p c2661 = true :=
  Snake9.LocalRup.prove_clause [c456, c2534] c2661 (by decide) p (sat_cons (step456 p h) (sat_cons (step2534 p h) (sat_nil p)))
def c2662 : List Lit := [(11, false), (48, false), (864, true), (28, false)]
theorem step2662 (p : Nat → Bool) (h : Constraints p) : clause p c2662 = true :=
  Snake9.LocalRup.prove_clause [c99, c105, c89, c1157, c1149, c1159, c1172] c2662 (by decide) p (sat_cons (step99 p h) (sat_cons (step105 p h) (sat_cons (step89 p h) (sat_cons (step1157 p h) (sat_cons (step1149 p h) (sat_cons (step1159 p h) (sat_cons (step1172 p h) (sat_nil p))))))))
def c2663 : List Lit := [(1, false), (922, true), (37, false), (48, false)]
theorem step2663 (p : Nat → Bool) (h : Constraints p) : clause p c2663 = true :=
  Snake9.LocalRup.prove_clause [c245, c244, c1287, c1278, c1294, c1281, c1305] c2663 (by decide) p (sat_cons (step245 p h) (sat_cons (step244 p h) (sat_cons (step1287 p h) (sat_cons (step1278 p h) (sat_cons (step1294 p h) (sat_cons (step1281 p h) (sat_cons (step1305 p h) (sat_nil p))))))))
def c2664 : List Lit := [(94, false), (77, false), (76, false)]
theorem step2664 (p : Nat → Bool) (h : Constraints p) : clause p c2664 = true :=
  Snake9.LocalRup.prove_clause [c2090, c2401] c2664 (by decide) p (sat_cons (step2090 p h) (sat_cons (step2401 p h) (sat_nil p)))
def c2665 : List Lit := [(76, false), (75, true), (203, true)]
theorem step2665 (p : Nat → Bool) (h : Constraints p) : clause p c2665 = true :=
  Snake9.LocalRup.prove_clause [c533, c534, c2664] c2665 (by decide) p (sat_cons (step533 p h) (sat_cons (step534 p h) (sat_cons (step2664 p h) (sat_nil p))))
def c2666 : List Lit := [(899, false), (974, true)]
theorem step2666 (p : Nat → Bool) (h : Constraints p) : clause p c2666 = true :=
  Snake9.LocalRup.prove_clause [c2520, c1443] c2666 (by decide) p (sat_cons (step2520 p h) (sat_cons (step1443 p h) (sat_nil p)))
def c2667 : List Lit := [(900, false), (975, true)]
theorem step2667 (p : Nat → Bool) (h : Constraints p) : clause p c2667 = true :=
  Snake9.LocalRup.prove_clause [c2520, c1449] c2667 (by decide) p (sat_cons (step2520 p h) (sat_cons (step1449 p h) (sat_nil p)))
def c2668 : List Lit := [(1018, false), (1021, true)]
theorem step2668 (p : Nat → Bool) (h : Constraints p) : clause p c2668 = true :=
  Snake9.LocalRup.prove_clause [c2510, c1518] c2668 (by decide) p (sat_cons (step2510 p h) (sat_cons (step1518 p h) (sat_nil p)))
def c2669 : List Lit := [(1019, false), (1022, true)]
theorem step2669 (p : Nat → Bool) (h : Constraints p) : clause p c2669 = true :=
  Snake9.LocalRup.prove_clause [c2510, c1519] c2669 (by decide) p (sat_cons (step2510 p h) (sat_cons (step1519 p h) (sat_nil p)))
def c2670 : List Lit := [(1025, true), (1012, false)]
theorem step2670 (p : Nat → Bool) (h : Constraints p) : clause p c2670 = true :=
  Snake9.LocalRup.prove_clause [c2511, c1527] c2670 (by decide) p (sat_cons (step2511 p h) (sat_cons (step1527 p h) (sat_nil p)))
def c2671 : List Lit := [(1013, false), (1026, true)]
theorem step2671 (p : Nat → Bool) (h : Constraints p) : clause p c2671 = true :=
  Snake9.LocalRup.prove_clause [c2511, c1532] c2671 (by decide) p (sat_cons (step2511 p h) (sat_cons (step1532 p h) (sat_nil p)))
def c2672 : List Lit := [(1014, false), (1027, true)]
theorem step2672 (p : Nat → Bool) (h : Constraints p) : clause p c2672 = true :=
  Snake9.LocalRup.prove_clause [c2511, c1536] c2672 (by decide) p (sat_cons (step2511 p h) (sat_cons (step1536 p h) (sat_nil p)))
def c2673 : List Lit := [(1033, true), (1001, false)]
theorem step2673 (p : Nat → Bool) (h : Constraints p) : clause p c2673 = true :=
  Snake9.LocalRup.prove_clause [c2512, c1546] c2673 (by decide) p (sat_cons (step2512 p h) (sat_cons (step1546 p h) (sat_nil p)))
def c2674 : List Lit := [(1034, true), (1002, false)]
theorem step2674 (p : Nat → Bool) (h : Constraints p) : clause p c2674 = true :=
  Snake9.LocalRup.prove_clause [c2512, c1553] c2674 (by decide) p (sat_cons (step2512 p h) (sat_cons (step1553 p h) (sat_nil p)))
def c2675 : List Lit := [(1035, true), (1003, false)]
theorem step2675 (p : Nat → Bool) (h : Constraints p) : clause p c2675 = true :=
  Snake9.LocalRup.prove_clause [c2512, c1560] c2675 (by decide) p (sat_cons (step2512 p h) (sat_cons (step1560 p h) (sat_nil p)))
def c2676 : List Lit := [(1036, true), (1004, false)]
theorem step2676 (p : Nat → Bool) (h : Constraints p) : clause p c2676 = true :=
  Snake9.LocalRup.prove_clause [c2512, c1567] c2676 (by decide) p (sat_cons (step2512 p h) (sat_cons (step1567 p h) (sat_nil p)))
def c2677 : List Lit := [(1037, true), (1005, false)]
theorem step2677 (p : Nat → Bool) (h : Constraints p) : clause p c2677 = true :=
  Snake9.LocalRup.prove_clause [c2512, c1572] c2677 (by decide) p (sat_cons (step2512 p h) (sat_cons (step1572 p h) (sat_nil p)))
def c2678 : List Lit := [(1065, false), (1098, true)]
theorem step2678 (p : Nat → Bool) (h : Constraints p) : clause p c2678 = true :=
  Snake9.LocalRup.prove_clause [c2573, c1685] c2678 (by decide) p (sat_cons (step2573 p h) (sat_cons (step1685 p h) (sat_nil p)))
end B112E260
