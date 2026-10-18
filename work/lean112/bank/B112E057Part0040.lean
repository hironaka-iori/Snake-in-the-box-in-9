import B112E057Part0039
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4585 : List Lit := [(1115, false), (124, false), (109, false), (1125, true), (89, false), (79, false), (88, true)]
theorem step4585 (p : Nat → Bool) (h : Constraints p) : clause p c4585 = true :=
  Snake9.LocalRup.prove_clause [c4414, c1751, c1742, c1743, c1754, c1740, c1730, c949, c2171, c1728, c1724, c4561] c4585 (by decide) p (sat_cons (step4414 p h) (sat_cons (step1751 p h) (sat_cons (step1742 p h) (sat_cons (step1743 p h) (sat_cons (step1754 p h) (sat_cons (step1740 p h) (sat_cons (step1730 p h) (sat_cons (step949 p h) (sat_cons (step2171 p h) (sat_cons (step1728 p h) (sat_cons (step1724 p h) (sat_cons (step4561 p h) (sat_nil p)))))))))))))
def c4586 : List Lit := [(1115, false), (1125, true), (118, true), (76, true), (109, false), (89, false), (79, false), (88, true)]
theorem step4586 (p : Nat → Bool) (h : Constraints p) : clause p c4586 = true :=
  Snake9.LocalRup.prove_clause [c4414, c1751, c1726, c1742, c1743, c4585, c1754, c1740, c1730, c1732, c1728, c1723, c2360, c909] c4586 (by decide) p (sat_cons (step4414 p h) (sat_cons (step1751 p h) (sat_cons (step1726 p h) (sat_cons (step1742 p h) (sat_cons (step1743 p h) (sat_cons (step4585 p h) (sat_cons (step1754 p h) (sat_cons (step1740 p h) (sat_cons (step1730 p h) (sat_cons (step1732 p h) (sat_cons (step1728 p h) (sat_cons (step1723 p h) (sat_cons (step2360 p h) (sat_cons (step909 p h) (sat_nil p)))))))))))))))
def c4587 : List Lit := [(1115, false), (1125, true), (109, false), (76, true), (89, false), (79, false), (88, true)]
theorem step4587 (p : Nat → Bool) (h : Constraints p) : clause p c4587 = true :=
  Snake9.LocalRup.prove_clause [c4414, c1751, c1742, c1743, c4585, c4586, c1754, c1740, c4561, c1734, c1724, c1725, c2811, c2360, c909] c4587 (by decide) p (sat_cons (step4414 p h) (sat_cons (step1751 p h) (sat_cons (step1742 p h) (sat_cons (step1743 p h) (sat_cons (step4585 p h) (sat_cons (step4586 p h) (sat_cons (step1754 p h) (sat_cons (step1740 p h) (sat_cons (step4561 p h) (sat_cons (step1734 p h) (sat_cons (step1724 p h) (sat_cons (step1725 p h) (sat_cons (step2811 p h) (sat_cons (step2360 p h) (sat_cons (step909 p h) (sat_nil p))))))))))))))))
def c4588 : List Lit := [(1097, true), (109, true), (84, true), (1091, false), (90, false), (88, true)]
theorem step4588 (p : Nat → Bool) (h : Constraints p) : clause p c4588 = true :=
  Snake9.LocalRup.prove_clause [c1699, c4497] c4588 (by decide) p (sat_cons (step1699 p h) (sat_cons (step4497 p h) (sat_nil p)))
def c4589 : List Lit := [(1040, false), (1075, true), (1043, false), (79, false), (1124, false), (1160, true), (88, true)]
theorem step4589 (p : Nat → Bool) (h : Constraints p) : clause p c4589 = true :=
  Snake9.LocalRup.prove_clause [c3437, c1582, c1659, c4163, c2978, c3643] c4589 (by decide) p (sat_cons (step3437 p h) (sat_cons (step1582 p h) (sat_cons (step1659 p h) (sat_cons (step4163 p h) (sat_cons (step2978 p h) (sat_cons (step3643 p h) (sat_nil p)))))))
def c4590 : List Lit := [(82, false), (84, true), (89, false), (79, false), (70, true)]
theorem step4590 (p : Nat → Bool) (h : Constraints p) : clause p c4590 = true :=
  Snake9.LocalRup.prove_clause [c629, c2310] c4590 (by decide) p (sat_cons (step629 p h) (sat_cons (step2310 p h) (sat_nil p)))
def c4591 : List Lit := [(1056, false), (1063, true), (1075, true), (84, false), (83, true), (1048, false), (1045, false), (1032, false), (90, false)]
theorem step4591 (p : Nat → Bool) (h : Constraints p) : clause p c4591 = true :=
  Snake9.LocalRup.prove_clause [c1618, c1623, c1652, c1591, c1571, c1581, c2081, c675, c1543] c4591 (by decide) p (sat_cons (step1618 p h) (sat_cons (step1623 p h) (sat_cons (step1652 p h) (sat_cons (step1591 p h) (sat_cons (step1571 p h) (sat_cons (step1581 p h) (sat_cons (step2081 p h) (sat_cons (step675 p h) (sat_cons (step1543 p h) (sat_nil p))))))))))
def c4592 : List Lit := [(69, true), (1061, false), (1096, true), (79, false), (1032, false), (90, false), (1076, true), (1124, false), (1160, true), (88, true)]
theorem step4592 (p : Nat → Bool) (h : Constraints p) : clause p c4592 = true :=
  Snake9.LocalRup.prove_clause [c4085, c3437, c1582, c3003, c2836, c1545, c1599, c2082, c3643, c1576, c1713, c1659, c1772, c1810] c4592 (by decide) p (sat_cons (step4085 p h) (sat_cons (step3437 p h) (sat_cons (step1582 p h) (sat_cons (step3003 p h) (sat_cons (step2836 p h) (sat_cons (step1545 p h) (sat_cons (step1599 p h) (sat_cons (step2082 p h) (sat_cons (step3643 p h) (sat_cons (step1576 p h) (sat_cons (step1713 p h) (sat_cons (step1659 p h) (sat_cons (step1772 p h) (sat_cons (step1810 p h) (sat_nil p)))))))))))))))
def c4593 : List Lit := [(920, false), (919, false), (931, false), (1005, true), (23, false)]
theorem step4593 (p : Nat → Bool) (h : Constraints p) : clause p c4593 = true :=
  Snake9.LocalRup.prove_clause [c1523, c1396, c1528, c4368, c2271, c2655, c1452, c1421, c2066, c1486, c1463, c1466, c1491, c1443, c1445, c1425, c1422, c1441, c1438, c1397, c2455, c307, c1392] c4593 (by decide) p (sat_cons (step1523 p h) (sat_cons (step1396 p h) (sat_cons (step1528 p h) (sat_cons (step4368 p h) (sat_cons (step2271 p h) (sat_cons (step2655 p h) (sat_cons (step1452 p h) (sat_cons (step1421 p h) (sat_cons (step2066 p h) (sat_cons (step1486 p h) (sat_cons (step1463 p h) (sat_cons (step1466 p h) (sat_cons (step1491 p h) (sat_cons (step1443 p h) (sat_cons (step1445 p h) (sat_cons (step1425 p h) (sat_cons (step1422 p h) (sat_cons (step1441 p h) (sat_cons (step1438 p h) (sat_cons (step1397 p h) (sat_cons (step2455 p h) (sat_cons (step307 p h) (sat_cons (step1392 p h) (sat_nil p))))))))))))))))))))))))
def c4594 : List Lit := [(893, true), (23, false), (95, false)]
theorem step4594 (p : Nat → Bool) (h : Constraints p) : clause p c4594 = true :=
  Snake9.LocalRup.prove_clause [c1315, c1316, c210] c4594 (by decide) p (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step210 p h) (sat_nil p))))
def c4595 : List Lit := [(1041, true), (71, true), (84, true), (69, true), (1033, false), (79, true), (73, true), (90, false), (70, true)]
theorem step4595 (p : Nat → Bool) (h : Constraints p) : clause p c4595 = true :=
  Snake9.LocalRup.prove_clause [c1544, c2081, c1577, c1573, c2082, c1545, c2289, c598, c597, c1555, c1552, c1563] c4595 (by decide) p (sat_cons (step1544 p h) (sat_cons (step2081 p h) (sat_cons (step1577 p h) (sat_cons (step1573 p h) (sat_cons (step2082 p h) (sat_cons (step1545 p h) (sat_cons (step2289 p h) (sat_cons (step598 p h) (sat_cons (step597 p h) (sat_cons (step1555 p h) (sat_cons (step1552 p h) (sat_cons (step1563 p h) (sat_nil p)))))))))))))
def c4596 : List Lit := [(891, false), (931, false), (23, false), (95, false), (885, false), (1005, true)]
theorem step4596 (p : Nat → Bool) (h : Constraints p) : clause p c4596 = true :=
  Snake9.LocalRup.prove_clause [c4594, c2125, c1321, c1374, c4593, c1375, c1354, c1350, c1322, c1332, c1329, c215, c212, c1317] c4596 (by decide) p (sat_cons (step4594 p h) (sat_cons (step2125 p h) (sat_cons (step1321 p h) (sat_cons (step1374 p h) (sat_cons (step4593 p h) (sat_cons (step1375 p h) (sat_cons (step1354 p h) (sat_cons (step1350 p h) (sat_cons (step1322 p h) (sat_cons (step1332 p h) (sat_cons (step1329 p h) (sat_cons (step215 p h) (sat_cons (step212 p h) (sat_cons (step1317 p h) (sat_nil p)))))))))))))))
def c4597 : List Lit := [(891, true), (18, false), (86, false), (13, false), (88, true)]
theorem step4597 (p : Nat → Bool) (h : Constraints p) : clause p c4597 = true :=
  Snake9.LocalRup.prove_clause [c1312, c1313, c3166] c4597 (by decide) p (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step3166 p h) (sat_nil p))))
def c4598 : List Lit := [(107, true), (97, true), (105, true), (1097, true), (99, false), (84, true), (83, true)]
theorem step4598 (p : Nat → Bool) (h : Constraints p) : clause p c4598 = true :=
  Snake9.LocalRup.prove_clause [c1693, c827, c1701, c1194, c1691, c2398, c2345, c1195, c845] c4598 (by decide) p (sat_cons (step1693 p h) (sat_cons (step827 p h) (sat_cons (step1701 p h) (sat_cons (step1194 p h) (sat_cons (step1691 p h) (sat_cons (step2398 p h) (sat_cons (step2345 p h) (sat_cons (step1195 p h) (sat_cons (step845 p h) (sat_nil p))))))))))
def c4599 : List Lit := [(101, false), (91, false), (104, true)]
theorem step4599 (p : Nat → Bool) (h : Constraints p) : clause p c4599 = true :=
  Snake9.LocalRup.prove_clause [c2341, c2340, c2018] c4599 (by decide) p (sat_cons (step2341 p h) (sat_cons (step2340 p h) (sat_cons (step2018 p h) (sat_nil p))))
def c4600 : List Lit := [(931, false), (949, true), (920, false), (59, false), (919, false), (1005, true)]
theorem step4600 (p : Nat → Bool) (h : Constraints p) : clause p c4600 = true :=
  Snake9.LocalRup.prove_clause [c1523, c4368, c2655, c2442, c1425, c1397] c4600 (by decide) p (sat_cons (step1523 p h) (sat_cons (step4368 p h) (sat_cons (step2655 p h) (sat_cons (step2442 p h) (sat_cons (step1425 p h) (sat_cons (step1397 p h) (sat_nil p)))))))
def c4601 : List Lit := [(982, true), (920, false), (931, false), (1005, true), (919, false)]
theorem step4601 (p : Nat → Bool) (h : Constraints p) : clause p c4601 = true :=
  Snake9.LocalRup.prove_clause [c1396, c1523, c4368, c2655, c1421, c2073, c1485, c4600, c1463, c1452, c2066] c4601 (by decide) p (sat_cons (step1396 p h) (sat_cons (step1523 p h) (sat_cons (step4368 p h) (sat_cons (step2655 p h) (sat_cons (step1421 p h) (sat_cons (step2073 p h) (sat_cons (step1485 p h) (sat_cons (step4600 p h) (sat_cons (step1463 p h) (sat_cons (step1452 p h) (sat_cons (step2066 p h) (sat_nil p))))))))))))
def c4602 : List Lit := [(904, true), (36, false), (23, true), (30, true), (18, false), (5, true)]
theorem step4602 (p : Nat → Bool) (h : Constraints p) : clause p c4602 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1333, c1335, c1331, c1327, c2239, c2234, c270] c4602 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1333 p h) (sat_cons (step1335 p h) (sat_cons (step1331 p h) (sat_cons (step1327 p h) (sat_cons (step2239 p h) (sat_cons (step2234 p h) (sat_cons (step270 p h) (sat_nil p)))))))))
def c4603 : List Lit := [(36, false), (23, true), (931, false), (1005, true), (30, true), (891, false), (18, false), (885, false), (5, true)]
theorem step4603 (p : Nat → Bool) (h : Constraints p) : clause p c4603 = true :=
  Snake9.LocalRup.prove_clause [c2125, c1374, c2732, c1375, c4601, c1533, c1376, c4602, c2770, c1351, c1327, c1321, c2234, c1316, c270, c2229] c4603 (by decide) p (sat_cons (step2125 p h) (sat_cons (step1374 p h) (sat_cons (step2732 p h) (sat_cons (step1375 p h) (sat_cons (step4601 p h) (sat_cons (step1533 p h) (sat_cons (step1376 p h) (sat_cons (step4602 p h) (sat_cons (step2770 p h) (sat_cons (step1351 p h) (sat_cons (step1327 p h) (sat_cons (step1321 p h) (sat_cons (step2234 p h) (sat_cons (step1316 p h) (sat_cons (step270 p h) (sat_cons (step2229 p h) (sat_nil p)))))))))))))))))
def c4604 : List Lit := [(50, true), (973, true), (931, true)]
theorem step4604 (p : Nat → Bool) (h : Constraints p) : clause p c4604 = true :=
  Snake9.LocalRup.prove_clause [c1438, c2761] c4604 (by decide) p (sat_cons (step1438 p h) (sat_cons (step2761 p h) (sat_nil p)))
def c4605 : List Lit := [(23, true), (904, false), (931, true), (1005, true), (891, false), (885, false), (5, true)]
theorem step4605 (p : Nat → Bool) (h : Constraints p) : clause p c4605 = true :=
  Snake9.LocalRup.prove_clause [c2118, c1327, c2444, c1388, c2770, c1376, c1533, c2416, c1485, c2615, c1424, c1451, c1452, c1395, c4604, c2185, c3091, c2606, c2927] c4605 (by decide) p (sat_cons (step2118 p h) (sat_cons (step1327 p h) (sat_cons (step2444 p h) (sat_cons (step1388 p h) (sat_cons (step2770 p h) (sat_cons (step1376 p h) (sat_cons (step1533 p h) (sat_cons (step2416 p h) (sat_cons (step1485 p h) (sat_cons (step2615 p h) (sat_cons (step1424 p h) (sat_cons (step1451 p h) (sat_cons (step1452 p h) (sat_cons (step1395 p h) (sat_cons (step4604 p h) (sat_cons (step2185 p h) (sat_cons (step3091 p h) (sat_cons (step2606 p h) (sat_cons (step2927 p h) (sat_nil p))))))))))))))))))))
def c4606 : List Lit := [(905, false), (23, false), (931, true), (1005, true), (891, false), (885, false)]
theorem step4606 (p : Nat → Bool) (h : Constraints p) : clause p c4606 = true :=
  Snake9.LocalRup.prove_clause [c2444, c2415, c1536, c1377, c1320, c1347, c1352, c1376, c1321, c1533, c1315, c1316, c2416, c209, c2615, c1452] c4606 (by decide) p (sat_cons (step2444 p h) (sat_cons (step2415 p h) (sat_cons (step1536 p h) (sat_cons (step1377 p h) (sat_cons (step1320 p h) (sat_cons (step1347 p h) (sat_cons (step1352 p h) (sat_cons (step1376 p h) (sat_cons (step1321 p h) (sat_cons (step1533 p h) (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step2416 p h) (sat_cons (step209 p h) (sat_cons (step2615 p h) (sat_cons (step1452 p h) (sat_nil p)))))))))))))))))
def c4607 : List Lit := [(1040, true), (1030, false), (94, false), (1033, false), (73, true), (90, false), (88, true)]
theorem step4607 (p : Nat → Bool) (h : Constraints p) : clause p c4607 = true :=
  Snake9.LocalRup.prove_clause [c2087, c1572, c1563, c2081, c1552, c1543, c597, c2298, c444] c4607 (by decide) p (sat_cons (step2087 p h) (sat_cons (step1572 p h) (sat_cons (step1563 p h) (sat_cons (step2081 p h) (sat_cons (step1552 p h) (sat_cons (step1543 p h) (sat_cons (step597 p h) (sat_cons (step2298 p h) (sat_cons (step444 p h) (sat_nil p))))))))))
def c4608 : List Lit := [(891, true), (90, false), (86, false), (13, false), (88, true)]
theorem step4608 (p : Nat → Bool) (h : Constraints p) : clause p c4608 = true :=
  Snake9.LocalRup.prove_clause [c1312, c1313, c4597, c153, c2224, c188] c4608 (by decide) p (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step4597 p h) (sat_cons (step153 p h) (sat_cons (step2224 p h) (sat_cons (step188 p h) (sat_nil p)))))))
def c4609 : List Lit := [(69, false), (82, false), (79, false), (112, false), (114, false), (7, false)]
theorem step4609 (p : Nat → Bool) (h : Constraints p) : clause p c4609 = true :=
  Snake9.LocalRup.prove_clause [c538, c622, c2102] c4609 (by decide) p (sat_cons (step538 p h) (sat_cons (step622 p h) (sat_cons (step2102 p h) (sat_nil p))))
def c4610 : List Lit := [(1117, false), (1124, true), (86, false), (88, true)]
theorem step4610 (p : Nat → Bool) (h : Constraints p) : clause p c4610 = true :=
  Snake9.LocalRup.prove_clause [c1747, c1741, c1743, c1750, c1737, c4330, c1729, c937, c1726] c4610 (by decide) p (sat_cons (step1747 p h) (sat_cons (step1741 p h) (sat_cons (step1743 p h) (sat_cons (step1750 p h) (sat_cons (step1737 p h) (sat_cons (step4330 p h) (sat_cons (step1729 p h) (sat_cons (step937 p h) (sat_cons (step1726 p h) (sat_nil p))))))))))
def c4611 : List Lit := [(77, false), (251, true), (89, true), (112, false), (114, false), (7, false)]
theorem step4611 (p : Nat → Bool) (h : Constraints p) : clause p c4611 = true :=
  Snake9.LocalRup.prove_clause [c545, c905, c2134] c4611 (by decide) p (sat_cons (step545 p h) (sat_cons (step905 p h) (sat_cons (step2134 p h) (sat_nil p))))
def c4612 : List Lit := [(1101, true), (84, true), (83, true), (1096, false), (90, true), (86, false), (88, true)]
theorem step4612 (p : Nat → Bool) (h : Constraints p) : clause p c4612 = true :=
  Snake9.LocalRup.prove_clause [c1709, c4563, c1681, c2344, c2345, c4576, c1678, c845, c2813, c1195, c872, c1196, c1207, c1199, c1210, c2401, c1211] c4612 (by decide) p (sat_cons (step1709 p h) (sat_cons (step4563 p h) (sat_cons (step1681 p h) (sat_cons (step2344 p h) (sat_cons (step2345 p h) (sat_cons (step4576 p h) (sat_cons (step1678 p h) (sat_cons (step845 p h) (sat_cons (step2813 p h) (sat_cons (step1195 p h) (sat_cons (step872 p h) (sat_cons (step1196 p h) (sat_cons (step1207 p h) (sat_cons (step1199 p h) (sat_cons (step1210 p h) (sat_cons (step2401 p h) (sat_cons (step1211 p h) (sat_nil p))))))))))))))))))
def c4613 : List Lit := [(109, false), (118, false), (122, true), (59, false), (984, true), (47, true), (112, false), (70, true)]
theorem step4613 (p : Nat → Bool) (h : Constraints p) : clause p c4613 = true :=
  Snake9.LocalRup.prove_clause [c878, c2356, c2365, c2445, c913, c1409, c1407] c4613 (by decide) p (sat_cons (step878 p h) (sat_cons (step2356 p h) (sat_cons (step2365 p h) (sat_cons (step2445 p h) (sat_cons (step913 p h) (sat_cons (step1409 p h) (sat_cons (step1407 p h) (sat_nil p))))))))
def c4614 : List Lit := [(1088, true), (59, false), (1005, true), (96, true), (91, false), (1054, true), (891, false), (885, false), (70, true), (5, true)]
theorem step4614 (p : Nat → Bool) (h : Constraints p) : clause p c4614 = true :=
  Snake9.LocalRup.prove_clause [c1675, c1686, c4498, c1684, c1677, c4596, c217, c1678, c2845, c2118, c4606, c2342, c1327, c832, c1336, c1331] c4614 (by decide) p (sat_cons (step1675 p h) (sat_cons (step1686 p h) (sat_cons (step4498 p h) (sat_cons (step1684 p h) (sat_cons (step1677 p h) (sat_cons (step4596 p h) (sat_cons (step217 p h) (sat_cons (step1678 p h) (sat_cons (step2845 p h) (sat_cons (step2118 p h) (sat_cons (step4606 p h) (sat_cons (step2342 p h) (sat_cons (step1327 p h) (sat_cons (step832 p h) (sat_cons (step1336 p h) (sat_cons (step1331 p h) (sat_nil p)))))))))))))))))
def c4615 : List Lit := [(105, true), (84, true), (1096, true)]
theorem step4615 (p : Nat → Bool) (h : Constraints p) : clause p c4615 = true :=
  Snake9.LocalRup.prove_clause [c1700, c1689, c1691, c1698, c4576, c1693] c4615 (by decide) p (sat_cons (step1700 p h) (sat_cons (step1689 p h) (sat_cons (step1691 p h) (sat_cons (step1698 p h) (sat_cons (step4576 p h) (sat_cons (step1693 p h) (sat_nil p)))))))
def c4616 : List Lit := [(103, false), (80, false), (83, false), (82, false), (70, true)]
theorem step4616 (p : Nat → Bool) (h : Constraints p) : clause p c4616 = true :=
  Snake9.LocalRup.prove_clause [c685, c2345, c2310, c654] c4616 (by decide) p (sat_cons (step685 p h) (sat_cons (step2345 p h) (sat_cons (step2310 p h) (sat_cons (step654 p h) (sat_nil p)))))
def c4617 : List Lit := [(984, true), (118, false), (122, true), (985, true), (47, true), (109, false), (112, false), (113, false), (45, false), (70, true)]
theorem step4617 (p : Nat → Bool) (h : Constraints p) : clause p c4617 = true :=
  Snake9.LocalRup.prove_clause [c4435, c4613] c4617 (by decide) p (sat_cons (step4435 p h) (sat_cons (step4613 p h) (sat_nil p)))
def c4618 : List Lit := [(1107, false), (1125, true), (76, true), (89, false), (1115, false), (77, false)]
theorem step4618 (p : Nat → Bool) (h : Constraints p) : clause p c4618 = true :=
  Snake9.LocalRup.prove_clause [c1742, c1754, c1734, c1731, c1732, c1751, c1727, c1743, c1740, c949, c4565, c2360, c905, c909, c1725] c4618 (by decide) p (sat_cons (step1742 p h) (sat_cons (step1754 p h) (sat_cons (step1734 p h) (sat_cons (step1731 p h) (sat_cons (step1732 p h) (sat_cons (step1751 p h) (sat_cons (step1727 p h) (sat_cons (step1743 p h) (sat_cons (step1740 p h) (sat_cons (step949 p h) (sat_cons (step4565 p h) (sat_cons (step2360 p h) (sat_cons (step905 p h) (sat_cons (step909 p h) (sat_cons (step1725 p h) (sat_nil p))))))))))))))))
def c4619 : List Lit := [(1091, true), (90, false), (121, false)]
theorem step4619 (p : Nat → Bool) (h : Constraints p) : clause p c4619 = true :=
  Snake9.LocalRup.prove_clause [c1689, c1690, c866, c693, c2344] c4619 (by decide) p (sat_cons (step1689 p h) (sat_cons (step1690 p h) (sat_cons (step866 p h) (sat_cons (step693 p h) (sat_cons (step2344 p h) (sat_nil p))))))
def c4620 : List Lit := [(69, false), (1044, true), (76, true), (89, false), (70, true)]
theorem step4620 (p : Nat → Bool) (h : Constraints p) : clause p c4620 = true :=
  Snake9.LocalRup.prove_clause [c2286, c2976, c626, c1581] c4620 (by decide) p (sat_cons (step2286 p h) (sat_cons (step2976 p h) (sat_cons (step626 p h) (sat_cons (step1581 p h) (sat_nil p)))))
def c4621 : List Lit := [(1056, false), (1075, true), (76, true), (73, true), (89, false), (90, false), (70, true), (77, false)]
theorem step4621 (p : Nat → Bool) (h : Constraints p) : clause p c4621 = true :=
  Snake9.LocalRup.prove_clause [c1551, c2882, c1645, c2859, c2840, c1588, c1618, c1623, c1652, c1589, c1591, c4620, c1544, c2081, c1571, c1561, c1559, c1552, c1553, c2809, c3012, c2866, c1584] c4621 (by decide) p (sat_cons (step1551 p h) (sat_cons (step2882 p h) (sat_cons (step1645 p h) (sat_cons (step2859 p h) (sat_cons (step2840 p h) (sat_cons (step1588 p h) (sat_cons (step1618 p h) (sat_cons (step1623 p h) (sat_cons (step1652 p h) (sat_cons (step1589 p h) (sat_cons (step1591 p h) (sat_cons (step4620 p h) (sat_cons (step1544 p h) (sat_cons (step2081 p h) (sat_cons (step1571 p h) (sat_cons (step1561 p h) (sat_cons (step1559 p h) (sat_cons (step1552 p h) (sat_cons (step1553 p h) (sat_cons (step2809 p h) (sat_cons (step3012 p h) (sat_cons (step2866 p h) (sat_cons (step1584 p h) (sat_nil p))))))))))))))))))))))))
def c4622 : List Lit := [(1124, true), (88, true), (115, false), (77, false)]
theorem step4622 (p : Nat → Bool) (h : Constraints p) : clause p c4622 = true :=
  Snake9.LocalRup.prove_clause [c2817, c4433, c905, c1724] c4622 (by decide) p (sat_cons (step2817 p h) (sat_cons (step4433 p h) (sat_cons (step905 p h) (sat_cons (step1724 p h) (sat_nil p)))))
def c4623 : List Lit := [(13, true), (40, true), (4, false), (885, false), (59, false), (931, false), (70, true), (1005, true)]
theorem step4623 (p : Nat → Bool) (h : Constraints p) : clause p c4623 = true :=
  Snake9.LocalRup.prove_clause [c2194, c2567, c4130, c2574, c1329, c1374, c1319, c1332, c4593, c1350, c1375] c4623 (by decide) p (sat_cons (step2194 p h) (sat_cons (step2567 p h) (sat_cons (step4130 p h) (sat_cons (step2574 p h) (sat_cons (step1329 p h) (sat_cons (step1374 p h) (sat_cons (step1319 p h) (sat_cons (step1332 p h) (sat_cons (step4593 p h) (sat_cons (step1350 p h) (sat_cons (step1375 p h) (sat_nil p))))))))))))
def c4624 : List Lit := [(886, true), (878, false), (4, false), (7, true)]
theorem step4624 (p : Nat → Bool) (h : Constraints p) : clause p c4624 = true :=
  Snake9.LocalRup.prove_clause [c1285, c1267, c1270, c1303, c1299, c1271, c1273, c1288, c1269, c1265, c1278, c2144, c7] c4624 (by decide) p (sat_cons (step1285 p h) (sat_cons (step1267 p h) (sat_cons (step1270 p h) (sat_cons (step1303 p h) (sat_cons (step1299 p h) (sat_cons (step1271 p h) (sat_cons (step1273 p h) (sat_cons (step1288 p h) (sat_cons (step1269 p h) (sat_cons (step1265 p h) (sat_cons (step1278 p h) (sat_cons (step2144 p h) (sat_cons (step7 p h) (sat_nil p))))))))))))))
def c4625 : List Lit := [(891, true), (20, false), (90, false)]
theorem step4625 (p : Nat → Bool) (h : Constraints p) : clause p c4625 = true :=
  Snake9.LocalRup.prove_clause [c1312, c1313, c188] c4625 (by decide) p (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step188 p h) (sat_nil p))))
def c4626 : List Lit := [(89, false), (1050, true), (86, true), (76, true), (69, false), (73, false), (70, true), (88, true)]
theorem step4626 (p : Nat → Bool) (h : Constraints p) : clause p c4626 = true :=
  Snake9.LocalRup.prove_clause [c4620, c1592, c1584, c699, c2316] c4626 (by decide) p (sat_cons (step4620 p h) (sat_cons (step1592 p h) (sat_cons (step1584 p h) (sat_cons (step699 p h) (sat_cons (step2316 p h) (sat_nil p))))))
def c4627 : List Lit := [(79, true), (1038, true), (88, true)]
theorem step4627 (p : Nat → Bool) (h : Constraints p) : clause p c4627 = true :=
  Snake9.LocalRup.prove_clause [c2085, c1557, c1553, c1555, c1556, c1559, c1570, c1550, c1551, c2081, c516, c4573, c1543] c4627 (by decide) p (sat_cons (step2085 p h) (sat_cons (step1557 p h) (sat_cons (step1553 p h) (sat_cons (step1555 p h) (sat_cons (step1556 p h) (sat_cons (step1559 p h) (sat_cons (step1570 p h) (sat_cons (step1550 p h) (sat_cons (step1551 p h) (sat_cons (step2081 p h) (sat_cons (step516 p h) (sat_cons (step4573 p h) (sat_cons (step1543 p h) (sat_nil p))))))))))))))
def c4628 : List Lit := [(85, false), (1062, true), (1043, false), (73, false), (79, false)]
theorem step4628 (p : Nat → Bool) (h : Constraints p) : clause p c4628 = true :=
  Snake9.LocalRup.prove_clause [c696, c2112, c1594, c1589, c1601, c1622] c4628 (by decide) p (sat_cons (step696 p h) (sat_cons (step2112 p h) (sat_cons (step1594 p h) (sat_cons (step1589 p h) (sat_cons (step1601 p h) (sat_cons (step1622 p h) (sat_nil p)))))))
def c4629 : List Lit := [(872, true), (7, true), (5, false), (73, false)]
theorem step4629 (p : Nat → Bool) (h : Constraints p) : clause p c4629 = true :=
  Snake9.LocalRup.prove_clause [c1267, c1271, c1273, c1269, c1265, c33] c4629 (by decide) p (sat_cons (step1267 p h) (sat_cons (step1271 p h) (sat_cons (step1273 p h) (sat_cons (step1269 p h) (sat_cons (step1265 p h) (sat_cons (step33 p h) (sat_nil p)))))))
def c4630 : List Lit := [(1083, false), (1096, false), (1124, false), (1089, true), (1043, false), (79, false), (1039, false), (97, true), (1160, true)]
theorem step4630 (p : Nat → Bool) (h : Constraints p) : clause p c4630 = true :=
  Snake9.LocalRup.prove_clause [c1679, c1684, c1685, c1714, c1680, c1777, c2894, c1805, c2978, c1651] c4630 (by decide) p (sat_cons (step1679 p h) (sat_cons (step1684 p h) (sat_cons (step1685 p h) (sat_cons (step1714 p h) (sat_cons (step1680 p h) (sat_cons (step1777 p h) (sat_cons (step2894 p h) (sat_cons (step1805 p h) (sat_cons (step2978 p h) (sat_cons (step1651 p h) (sat_nil p)))))))))))
def c4631 : List Lit := [(1053, true), (1089, true), (79, false), (97, true)]
theorem step4631 (p : Nat → Bool) (h : Constraints p) : clause p c4631 = true :=
  Snake9.LocalRup.prove_clause [c2110, c2894, c1675, c1680, c1685] c4631 (by decide) p (sat_cons (step2110 p h) (sat_cons (step2894 p h) (sat_cons (step1675 p h) (sat_cons (step1680 p h) (sat_cons (step1685 p h) (sat_nil p))))))
def c4632 : List Lit := [(1049, true), (1096, true), (1043, false), (1045, false), (90, false)]
theorem step4632 (p : Nat → Bool) (h : Constraints p) : clause p c4632 = true :=
  Snake9.LocalRup.prove_clause [c1591, c1589, c4070, c2814, c757, c760, c1584] c4632 (by decide) p (sat_cons (step1591 p h) (sat_cons (step1589 p h) (sat_cons (step4070 p h) (sat_cons (step2814 p h) (sat_cons (step757 p h) (sat_cons (step760 p h) (sat_cons (step1584 p h) (sat_nil p))))))))
def c4633 : List Lit := [(1124, true), (114, true), (88, false), (1046, true), (90, false)]
theorem step4633 (p : Nat → Bool) (h : Constraints p) : clause p c4633 = true :=
  Snake9.LocalRup.prove_clause [c1727, c1729, c1750, c3285, c1742, c1584, c1737, c761] c4633 (by decide) p (sat_cons (step1727 p h) (sat_cons (step1729 p h) (sat_cons (step1750 p h) (sat_cons (step3285 p h) (sat_cons (step1742 p h) (sat_cons (step1584 p h) (sat_cons (step1737 p h) (sat_cons (step761 p h) (sat_nil p)))))))))
def c4634 : List Lit := [(918, true), (7, true), (73, false)]
theorem step4634 (p : Nat → Bool) (h : Constraints p) : clause p c4634 = true :=
  Snake9.LocalRup.prove_clause [c1267, c2411, c2181, c2512, c1271, c1273, c4629, c1282, c1269, c1265, c2192, c14] c4634 (by decide) p (sat_cons (step1267 p h) (sat_cons (step2411 p h) (sat_cons (step2181 p h) (sat_cons (step2512 p h) (sat_cons (step1271 p h) (sat_cons (step1273 p h) (sat_cons (step4629 p h) (sat_cons (step1282 p h) (sat_cons (step1269 p h) (sat_cons (step1265 p h) (sat_cons (step2192 p h) (sat_cons (step14 p h) (sat_nil p)))))))))))))
def c4635 : List Lit := [(1061, true), (1043, false), (89, true), (73, false)]
theorem step4635 (p : Nat → Bool) (h : Constraints p) : clause p c4635 = true :=
  Snake9.LocalRup.prove_clause [c1594, c1601, c3028, c1617, c1583, c1588] c4635 (by decide) p (sat_cons (step1594 p h) (sat_cons (step1601 p h) (sat_cons (step3028 p h) (sat_cons (step1617 p h) (sat_cons (step1583 p h) (sat_cons (step1588 p h) (sat_nil p)))))))
def c4636 : List Lit := [(79, true), (1039, true), (1027, false), (76, false), (73, false)]
theorem step4636 (p : Nat → Bool) (h : Constraints p) : clause p c4636 = true :=
  Snake9.LocalRup.prove_clause [c2086, c1560, c1553, c1555, c1559, c549, c1571, c1544, c2081] c4636 (by decide) p (sat_cons (step2086 p h) (sat_cons (step1560 p h) (sat_cons (step1553 p h) (sat_cons (step1555 p h) (sat_cons (step1559 p h) (sat_cons (step549 p h) (sat_cons (step1571 p h) (sat_cons (step1544 p h) (sat_cons (step2081 p h) (sat_nil p))))))))))
def c4637 : List Lit := [(1091, true), (1116, true), (88, false), (90, false)]
theorem step4637 (p : Nat → Bool) (h : Constraints p) : clause p c4637 = true :=
  Snake9.LocalRup.prove_clause [c1689, c4619, c763, c1739] c4637 (by decide) p (sat_cons (step1689 p h) (sat_cons (step4619 p h) (sat_cons (step763 p h) (sat_cons (step1739 p h) (sat_nil p)))))
def c4638 : List Lit := [(1096, true), (1124, true), (88, false), (90, false), (79, false)]
theorem step4638 (p : Nat → Bool) (h : Constraints p) : clause p c4638 = true :=
  Snake9.LocalRup.prove_clause [c1747, c1744, c4637, c2122, c1698, c1742, c1692, c1750, c4414] c4638 (by decide) p (sat_cons (step1747 p h) (sat_cons (step1744 p h) (sat_cons (step4637 p h) (sat_cons (step2122 p h) (sat_cons (step1698 p h) (sat_cons (step1742 p h) (sat_cons (step1692 p h) (sat_cons (step1750 p h) (sat_cons (step4414 p h) (sat_nil p))))))))))
def c4639 : List Lit := [(123, false), (1046, true), (88, false), (90, false)]
theorem step4639 (p : Nat → Bool) (h : Constraints p) : clause p c4639 = true :=
  Snake9.LocalRup.prove_clause [c758, c761, c1584] c4639 (by decide) p (sat_cons (step758 p h) (sat_cons (step761 p h) (sat_cons (step1584 p h) (sat_nil p))))
def c4640 : List Lit := [(918, true), (5, false), (73, false)]
theorem step4640 (p : Nat → Bool) (h : Constraints p) : clause p c4640 = true :=
  Snake9.LocalRup.prove_clause [c2181, c4634, c36, c42, c1265, c1268, c1273] c4640 (by decide) p (sat_cons (step2181 p h) (sat_cons (step4634 p h) (sat_cons (step36 p h) (sat_cons (step42 p h) (sat_cons (step1265 p h) (sat_cons (step1268 p h) (sat_cons (step1273 p h) (sat_nil p))))))))
def c4641 : List Lit := [(1039, false), (1062, false), (1049, false), (1051, false), (1124, false), (1096, false), (1160, true)]
theorem step4641 (p : Nat → Bool) (h : Constraints p) : clause p c4641 = true :=
  Snake9.LocalRup.prove_clause [c1704, c1767, c1816, c1652, c1653, c1810, c1623, c1772, c1602, c1709, c2110, c1683, c1675] c4641 (by decide) p (sat_cons (step1704 p h) (sat_cons (step1767 p h) (sat_cons (step1816 p h) (sat_cons (step1652 p h) (sat_cons (step1653 p h) (sat_cons (step1810 p h) (sat_cons (step1623 p h) (sat_cons (step1772 p h) (sat_cons (step1602 p h) (sat_cons (step1709 p h) (sat_cons (step2110 p h) (sat_cons (step1683 p h) (sat_cons (step1675 p h) (sat_nil p))))))))))))))
def c4642 : List Lit := [(1021, true), (82, false), (83, false)]
theorem step4642 (p : Nat → Bool) (h : Constraints p) : clause p c4642 = true :=
  Snake9.LocalRup.prove_clause [c3022, c2884] c4642 (by decide) p (sat_cons (step3022 p h) (sat_cons (step2884 p h) (sat_nil p)))
def c4643 : List Lit := [(1039, true), (1027, false), (70, false), (1043, true)]
theorem step4643 (p : Nat → Bool) (h : Constraints p) : clause p c4643 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1579, c1580, c4642, c2081, c1575, c1571, c2082, c1559, c2143, c1554] c4643 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step4642 p h) (sat_cons (step2081 p h) (sat_cons (step1575 p h) (sat_cons (step1571 p h) (sat_cons (step2082 p h) (sat_cons (step1559 p h) (sat_cons (step2143 p h) (sat_cons (step1554 p h) (sat_nil p))))))))))))
def c4644 : List Lit := [(1049, false), (1051, false), (1124, false), (1039, false), (1096, false), (1160, true)]
theorem step4644 (p : Nat → Bool) (h : Constraints p) : clause p c4644 = true :=
  Snake9.LocalRup.prove_clause [c1601, c1622, c4641] c4644 (by decide) p (sat_cons (step1601 p h) (sat_cons (step1622 p h) (sat_cons (step4641 p h) (sat_nil p))))
def c4645 : List Lit := [(1062, false), (1076, true), (1124, false), (1039, false), (1027, false), (1091, false), (1160, true), (70, false), (82, false)]
theorem step4645 (p : Nat → Bool) (h : Constraints p) : clause p c4645 = true :=
  Snake9.LocalRup.prove_clause [c1660, c1652, c1810, c1772, c2109, c486, c483, c477, c1554, c1545, c1559, c2082, c1576] c4645 (by decide) p (sat_cons (step1660 p h) (sat_cons (step1652 p h) (sat_cons (step1810 p h) (sat_cons (step1772 p h) (sat_cons (step2109 p h) (sat_cons (step486 p h) (sat_cons (step483 p h) (sat_cons (step477 p h) (sat_cons (step1554 p h) (sat_cons (step1545 p h) (sat_cons (step1559 p h) (sat_cons (step2082 p h) (sat_cons (step1576 p h) (sat_nil p))))))))))))))
def c4646 : List Lit := [(1136, true), (1083, false), (123, true), (89, false), (1096, false), (112, true), (95, false), (1124, false), (1043, true)]
theorem step4646 (p : Nat → Bool) (h : Constraints p) : clause p c4646 = true :=
  Snake9.LocalRup.prove_clause [c1683, c1709, c1737, c1742, c1580, c1579, c631, c1724, c1731, c1777, c1773, c1714, c1751, c2869, c1754, c1684, c1743, c1727, c1734, c1679, c1740, c1725, c568, c909, c949, c2360] c4646 (by decide) p (sat_cons (step1683 p h) (sat_cons (step1709 p h) (sat_cons (step1737 p h) (sat_cons (step1742 p h) (sat_cons (step1580 p h) (sat_cons (step1579 p h) (sat_cons (step631 p h) (sat_cons (step1724 p h) (sat_cons (step1731 p h) (sat_cons (step1777 p h) (sat_cons (step1773 p h) (sat_cons (step1714 p h) (sat_cons (step1751 p h) (sat_cons (step2869 p h) (sat_cons (step1754 p h) (sat_cons (step1684 p h) (sat_cons (step1743 p h) (sat_cons (step1727 p h) (sat_cons (step1734 p h) (sat_cons (step1679 p h) (sat_cons (step1740 p h) (sat_cons (step1725 p h) (sat_cons (step568 p h) (sat_cons (step909 p h) (sat_cons (step949 p h) (sat_cons (step2360 p h) (sat_nil p)))))))))))))))))))))))))))
def c4647 : List Lit := [(114, false), (120, true), (126, true), (113, false), (125, false), (89, false)]
theorem step4647 (p : Nat → Bool) (h : Constraints p) : clause p c4647 = true :=
  Snake9.LocalRup.prove_clause [c949, c909, c2376] c4647 (by decide) p (sat_cons (step949 p h) (sat_cons (step909 p h) (sat_cons (step2376 p h) (sat_nil p))))
def c4648 : List Lit := [(73, false), (1134, true), (76, false), (1100, false), (1051, true)]
theorem step4648 (p : Nat → Bool) (h : Constraints p) : clause p c4648 = true :=
  Snake9.LocalRup.prove_clause [c1594, c1593, c562, c563, c1679, c2860, c1681] c4648 (by decide) p (sat_cons (step1594 p h) (sat_cons (step1593 p h) (sat_cons (step562 p h) (sat_cons (step563 p h) (sat_cons (step1679 p h) (sat_cons (step2860 p h) (sat_cons (step1681 p h) (sat_nil p))))))))
end B112E057
