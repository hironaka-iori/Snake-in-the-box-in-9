import B112E089Part0182
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c13724 : List Lit := [(333, false), (47, false), (1763, true), (1653, false), (114, true), (1660, false), (115, true), (44, false), (1600, true), (39, false), (1784, true), (74, true), (75, false)]
theorem step13724 (p : Nat → Bool) (h : Constraints p) : clause p c13724 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1478, c13629, c1479, c2659, c1614, c1483, c1475, c4901, c1157, c2337, c1160, c1152, c2361, c1136, c1294, c1128, c1289, c1291, c1126, c1284, c2094, c12667, c2781, c1865, c13599, c1860, c3512, c8357] c13724 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1478 p h) (sat_cons (step13629 p h) (sat_cons (step1479 p h) (sat_cons (step2659 p h) (sat_cons (step1614 p h) (sat_cons (step1483 p h) (sat_cons (step1475 p h) (sat_cons (step4901 p h) (sat_cons (step1157 p h) (sat_cons (step2337 p h) (sat_cons (step1160 p h) (sat_cons (step1152 p h) (sat_cons (step2361 p h) (sat_cons (step1136 p h) (sat_cons (step1294 p h) (sat_cons (step1128 p h) (sat_cons (step1289 p h) (sat_cons (step1291 p h) (sat_cons (step1126 p h) (sat_cons (step1284 p h) (sat_cons (step2094 p h) (sat_cons (step12667 p h) (sat_cons (step2781 p h) (sat_cons (step1865 p h) (sat_cons (step13599 p h) (sat_cons (step1860 p h) (sat_cons (step3512 p h) (sat_cons (step8357 p h) (sat_nil p))))))))))))))))))))))))))))))
def c13725 : List Lit := [(1574, true), (1606, true), (39, false), (1616, true), (74, true), (1670, true)]
theorem step13725 (p : Nat → Bool) (h : Constraints p) : clause p c13725 = true :=
  Snake9.TreeRup.prove_clause [c12893, c13720, c3305, c1499, c1481, c1478, c13629, c1483, c1476, c1475, c4464, c1479, c1503, c1648, c2848, c1498, c1534, c1447, c1438, c10133, c13707, c2383, c3027, c1430, c1431, c13693, c610, c611, c6459, c4025, c12817, c2303, c1610, c2375, c1892, c13722, c298, c380, c1466, c1471, c1461, c213, c13723, c1429, c207, c360, c13724, c1121, c1118, c1105, c1106, c1104, c1103, c220, c222, c5279, c2775, c210, c5384, c1664, c1852, c2408, c1913, c1738, c13141, c511, c4716, c237] c13725 (by decide) p (sat_cons (step12893 p h) (sat_cons (step13720 p h) (sat_cons (step3305 p h) (sat_cons (step1499 p h) (sat_cons (step1481 p h) (sat_cons (step1478 p h) (sat_cons (step13629 p h) (sat_cons (step1483 p h) (sat_cons (step1476 p h) (sat_cons (step1475 p h) (sat_cons (step4464 p h) (sat_cons (step1479 p h) (sat_cons (step1503 p h) (sat_cons (step1648 p h) (sat_cons (step2848 p h) (sat_cons (step1498 p h) (sat_cons (step1534 p h) (sat_cons (step1447 p h) (sat_cons (step1438 p h) (sat_cons (step10133 p h) (sat_cons (step13707 p h) (sat_cons (step2383 p h) (sat_cons (step3027 p h) (sat_cons (step1430 p h) (sat_cons (step1431 p h) (sat_cons (step13693 p h) (sat_cons (step610 p h) (sat_cons (step611 p h) (sat_cons (step6459 p h) (sat_cons (step4025 p h) (sat_cons (step12817 p h) (sat_cons (step2303 p h) (sat_cons (step1610 p h) (sat_cons (step2375 p h) (sat_cons (step1892 p h) (sat_cons (step13722 p h) (sat_cons (step298 p h) (sat_cons (step380 p h) (sat_cons (step1466 p h) (sat_cons (step1471 p h) (sat_cons (step1461 p h) (sat_cons (step213 p h) (sat_cons (step13723 p h) (sat_cons (step1429 p h) (sat_cons (step207 p h) (sat_cons (step360 p h) (sat_cons (step13724 p h) (sat_cons (step1121 p h) (sat_cons (step1118 p h) (sat_cons (step1105 p h) (sat_cons (step1106 p h) (sat_cons (step1104 p h) (sat_cons (step1103 p h) (sat_cons (step220 p h) (sat_cons (step222 p h) (sat_cons (step5279 p h) (sat_cons (step2775 p h) (sat_cons (step210 p h) (sat_cons (step5384 p h) (sat_cons (step1664 p h) (sat_cons (step1852 p h) (sat_cons (step2408 p h) (sat_cons (step1913 p h) (sat_cons (step1738 p h) (sat_cons (step13141 p h) (sat_cons (step511 p h) (sat_cons (step4716 p h) (sat_cons (step237 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c13726 : List Lit := [(45, false), (1572, true), (1606, true), (1577, true), (39, false), (51, true), (1784, true), (74, true), (75, false)]
theorem step13726 (p : Nat → Bool) (h : Constraints p) : clause p c13726 = true :=
  Snake9.LocalRup.prove_clause [c12893, c3305, c1499, c1483, c1476, c1427, c366, c2502, c1428, c1481, c1478, c1503, c353, c13693, c610, c611, c6459, c13682, c4188, c1610, c1138, c13723, c1142, c2215, c1969, c1147, c2149, c1150, c1103, c2337, c1106, c1121, c1118] c13726 (by decide) p (sat_cons (step12893 p h) (sat_cons (step3305 p h) (sat_cons (step1499 p h) (sat_cons (step1483 p h) (sat_cons (step1476 p h) (sat_cons (step1427 p h) (sat_cons (step366 p h) (sat_cons (step2502 p h) (sat_cons (step1428 p h) (sat_cons (step1481 p h) (sat_cons (step1478 p h) (sat_cons (step1503 p h) (sat_cons (step353 p h) (sat_cons (step13693 p h) (sat_cons (step610 p h) (sat_cons (step611 p h) (sat_cons (step6459 p h) (sat_cons (step13682 p h) (sat_cons (step4188 p h) (sat_cons (step1610 p h) (sat_cons (step1138 p h) (sat_cons (step13723 p h) (sat_cons (step1142 p h) (sat_cons (step2215 p h) (sat_cons (step1969 p h) (sat_cons (step1147 p h) (sat_cons (step2149 p h) (sat_cons (step1150 p h) (sat_cons (step1103 p h) (sat_cons (step2337 p h) (sat_cons (step1106 p h) (sat_cons (step1121 p h) (sat_cons (step1118 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c13727 : List Lit := [(1606, true), (39, false), (1616, true), (74, true), (1670, true)]
theorem step13727 (p : Nat → Bool) (h : Constraints p) : clause p c13727 = true :=
  Snake9.LocalRup.prove_clause [c1648, c2848, c13720, c3305, c1498, c1534, c1447, c1434, c13707, c2383, c1503, c1499, c1481, c1483, c1478, c1479, c4464, c1475, c1476, c416, c13725, c1436, c1427, c1428, c2502, c366, c208, c13726, c1432, c13680, c207, c360, c4188, c12671, c372, c1138, c2231, c1142, c347, c1147, c2335, c1150, c2336, c1145, c2337, c1136, c1144, c1121, c1128, c1118, c1127, c1105, c312, c1104, c2631, c4006] c13727 (by decide) p (sat_cons (step1648 p h) (sat_cons (step2848 p h) (sat_cons (step13720 p h) (sat_cons (step3305 p h) (sat_cons (step1498 p h) (sat_cons (step1534 p h) (sat_cons (step1447 p h) (sat_cons (step1434 p h) (sat_cons (step13707 p h) (sat_cons (step2383 p h) (sat_cons (step1503 p h) (sat_cons (step1499 p h) (sat_cons (step1481 p h) (sat_cons (step1483 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step4464 p h) (sat_cons (step1475 p h) (sat_cons (step1476 p h) (sat_cons (step416 p h) (sat_cons (step13725 p h) (sat_cons (step1436 p h) (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step2502 p h) (sat_cons (step366 p h) (sat_cons (step208 p h) (sat_cons (step13726 p h) (sat_cons (step1432 p h) (sat_cons (step13680 p h) (sat_cons (step207 p h) (sat_cons (step360 p h) (sat_cons (step4188 p h) (sat_cons (step12671 p h) (sat_cons (step372 p h) (sat_cons (step1138 p h) (sat_cons (step2231 p h) (sat_cons (step1142 p h) (sat_cons (step347 p h) (sat_cons (step1147 p h) (sat_cons (step2335 p h) (sat_cons (step1150 p h) (sat_cons (step2336 p h) (sat_cons (step1145 p h) (sat_cons (step2337 p h) (sat_cons (step1136 p h) (sat_cons (step1144 p h) (sat_cons (step1121 p h) (sat_cons (step1128 p h) (sat_cons (step1118 p h) (sat_cons (step1127 p h) (sat_cons (step1105 p h) (sat_cons (step312 p h) (sat_cons (step1104 p h) (sat_cons (step2631 p h) (sat_cons (step4006 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c13728 : List Lit := [(54, false), (46, false), (61, false), (55, false), (39, false), (1616, true), (74, true), (1670, true)]
theorem step13728 (p : Nat → Bool) (h : Constraints p) : clause p c13728 = true :=
  Snake9.TreeRup.prove_clause [c12893, c1648, c2848, c13727, c1527, c1446, c1433, c1430, c6459, c1610, c611, c610, c1435, c1428, c1427, c1431, c3084, c13720, c3305, c1498, c1534, c1447, c13707, c2383, c1445, c1520, c1647, c366, c4649, c4188, c1138, c1142, c1147, c1150, c2336, c1155, c1136, c1160, c1128, c2361, c1126, c1294, c1296, c1289, c1291, c1222, c1284, c1252, c1195, c12667, c13173, c2376, c1899, c1859, c4165, c2781, c1664, c2094, c2408, c1461, c1730, c1471, c1906, c1504, c13585, c1481] c13728 (by decide) p (sat_cons (step12893 p h) (sat_cons (step1648 p h) (sat_cons (step2848 p h) (sat_cons (step13727 p h) (sat_cons (step1527 p h) (sat_cons (step1446 p h) (sat_cons (step1433 p h) (sat_cons (step1430 p h) (sat_cons (step6459 p h) (sat_cons (step1610 p h) (sat_cons (step611 p h) (sat_cons (step610 p h) (sat_cons (step1435 p h) (sat_cons (step1428 p h) (sat_cons (step1427 p h) (sat_cons (step1431 p h) (sat_cons (step3084 p h) (sat_cons (step13720 p h) (sat_cons (step3305 p h) (sat_cons (step1498 p h) (sat_cons (step1534 p h) (sat_cons (step1447 p h) (sat_cons (step13707 p h) (sat_cons (step2383 p h) (sat_cons (step1445 p h) (sat_cons (step1520 p h) (sat_cons (step1647 p h) (sat_cons (step366 p h) (sat_cons (step4649 p h) (sat_cons (step4188 p h) (sat_cons (step1138 p h) (sat_cons (step1142 p h) (sat_cons (step1147 p h) (sat_cons (step1150 p h) (sat_cons (step2336 p h) (sat_cons (step1155 p h) (sat_cons (step1136 p h) (sat_cons (step1160 p h) (sat_cons (step1128 p h) (sat_cons (step2361 p h) (sat_cons (step1126 p h) (sat_cons (step1294 p h) (sat_cons (step1296 p h) (sat_cons (step1289 p h) (sat_cons (step1291 p h) (sat_cons (step1222 p h) (sat_cons (step1284 p h) (sat_cons (step1252 p h) (sat_cons (step1195 p h) (sat_cons (step12667 p h) (sat_cons (step13173 p h) (sat_cons (step2376 p h) (sat_cons (step1899 p h) (sat_cons (step1859 p h) (sat_cons (step4165 p h) (sat_cons (step2781 p h) (sat_cons (step1664 p h) (sat_cons (step2094 p h) (sat_cons (step2408 p h) (sat_cons (step1461 p h) (sat_cons (step1730 p h) (sat_cons (step1471 p h) (sat_cons (step1906 p h) (sat_cons (step1504 p h) (sat_cons (step13585 p h) (sat_cons (step1481 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c13729 : List Lit := [(487, true), (1762, true), (103, true), (115, true), (74, true), (75, false)]
theorem step13729 (p : Nat → Bool) (h : Constraints p) : clause p c13729 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1291, c1284, c2781, c12667, c1859] c13729 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1291 p h) (sat_cons (step1284 p h) (sat_cons (step2781 p h) (sat_cons (step12667 p h) (sat_cons (step1859 p h) (sat_nil p)))))))
def c13730 : List Lit := [(455, true), (1728, true), (1762, true), (103, true), (1598, true), (115, true), (114, true), (1745, false)]
theorem step13730 (p : Nat → Bool) (h : Constraints p) : clause p c13730 = true :=
  Snake9.LocalRup.prove_clause [c2781, c3512, c1859, c12679, c1832] c13730 (by decide) p (sat_cons (step2781 p h) (sat_cons (step3512 p h) (sat_cons (step1859 p h) (sat_cons (step12679 p h) (sat_cons (step1832 p h) (sat_nil p))))))
def c13731 : List Lit := [(46, false), (61, false), (331, true), (39, false), (1616, true), (74, true), (1670, true)]
theorem step13731 (p : Nat → Bool) (h : Constraints p) : clause p c13731 = true :=
  Snake9.TreeRup.prove_clause [c12893, c1648, c2848, c13727, c1527, c1446, c1433, c1430, c6459, c1610, c611, c610, c1116, c1112, c1109, c3085, c3084, c302, c1118, c1106, c1103, c1435, c1427, c13720, c3305, c1498, c1534, c1447, c10133, c13707, c2383, c1445, c1520, c4901, c3027, c13728, c1476, c1483, c1484, c1504, c4454, c2149, c5180, c2775, c1640, c5384, c2376, c1899, c1864, c13730, c2359, c1284, c12667, c1853, c1859, c1906, c1730, c2408, c8968, c1664, c6293] c13731 (by decide) p (sat_cons (step12893 p h) (sat_cons (step1648 p h) (sat_cons (step2848 p h) (sat_cons (step13727 p h) (sat_cons (step1527 p h) (sat_cons (step1446 p h) (sat_cons (step1433 p h) (sat_cons (step1430 p h) (sat_cons (step6459 p h) (sat_cons (step1610 p h) (sat_cons (step611 p h) (sat_cons (step610 p h) (sat_cons (step1116 p h) (sat_cons (step1112 p h) (sat_cons (step1109 p h) (sat_cons (step3085 p h) (sat_cons (step3084 p h) (sat_cons (step302 p h) (sat_cons (step1118 p h) (sat_cons (step1106 p h) (sat_cons (step1103 p h) (sat_cons (step1435 p h) (sat_cons (step1427 p h) (sat_cons (step13720 p h) (sat_cons (step3305 p h) (sat_cons (step1498 p h) (sat_cons (step1534 p h) (sat_cons (step1447 p h) (sat_cons (step10133 p h) (sat_cons (step13707 p h) (sat_cons (step2383 p h) (sat_cons (step1445 p h) (sat_cons (step1520 p h) (sat_cons (step4901 p h) (sat_cons (step3027 p h) (sat_cons (step13728 p h) (sat_cons (step1476 p h) (sat_cons (step1483 p h) (sat_cons (step1484 p h) (sat_cons (step1504 p h) (sat_cons (step4454 p h) (sat_cons (step2149 p h) (sat_cons (step5180 p h) (sat_cons (step2775 p h) (sat_cons (step1640 p h) (sat_cons (step5384 p h) (sat_cons (step2376 p h) (sat_cons (step1899 p h) (sat_cons (step1864 p h) (sat_cons (step13730 p h) (sat_cons (step2359 p h) (sat_cons (step1284 p h) (sat_cons (step12667 p h) (sat_cons (step1853 p h) (sat_cons (step1859 p h) (sat_cons (step1906 p h) (sat_cons (step1730 p h) (sat_cons (step2408 p h) (sat_cons (step8968 p h) (sat_cons (step1664 p h) (sat_cons (step6293 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c13732 : List Lit := [(46, true), (55, false), (163, true), (41, false), (42, false), (44, false), (45, false), (39, false), (1601, true), (51, true), (1616, true), (1568, false)]
theorem step13732 (p : Nat → Bool) (h : Constraints p) : clause p c13732 = true :=
  Snake9.LocalRup.prove_clause [c3305, c1498, c1534, c1447, c1445, c1520, c1508, c13692, c1479, c4464, c2083, c208, c213, c13680, c1463, c1504, c1474, c1483, c4427, c1476] c13732 (by decide) p (sat_cons (step3305 p h) (sat_cons (step1498 p h) (sat_cons (step1534 p h) (sat_cons (step1447 p h) (sat_cons (step1445 p h) (sat_cons (step1520 p h) (sat_cons (step1508 p h) (sat_cons (step13692 p h) (sat_cons (step1479 p h) (sat_cons (step4464 p h) (sat_cons (step2083 p h) (sat_cons (step208 p h) (sat_cons (step213 p h) (sat_cons (step13680 p h) (sat_cons (step1463 p h) (sat_cons (step1504 p h) (sat_cons (step1474 p h) (sat_cons (step1483 p h) (sat_cons (step4427 p h) (sat_cons (step1476 p h) (sat_nil p)))))))))))))))))))))
def c13733 : List Lit := [(331, true), (39, false), (1616, true), (74, true), (1670, true)]
theorem step13733 (p : Nat → Bool) (h : Constraints p) : clause p c13733 = true :=
  Snake9.TreeRup.prove_clause [c1648, c2848, c13727, c1527, c1446, c1435, c1428, c1427, c1433, c1431, c1430, c12812, c3084, c13720, c3305, c1498, c1534, c1447, c10133, c1482, c13707, c2383, c1445, c1520, c1116, c1118, c1112, c1114, c1105, c1106, c1109, c1108, c1104, c1103, c302, c13732, c13731, c1478, c1480, c13028, c1481, c1484, c1504, c1475, c1476, c4006, c366, c4649, c511, c513, c512, c255, c253, c1471, c1608, c1957, c1461, c1613, c1650, c213, c3796, c222, c223, c448, c1970, c5178] c13733 (by decide) p (sat_cons (step1648 p h) (sat_cons (step2848 p h) (sat_cons (step13727 p h) (sat_cons (step1527 p h) (sat_cons (step1446 p h) (sat_cons (step1435 p h) (sat_cons (step1428 p h) (sat_cons (step1427 p h) (sat_cons (step1433 p h) (sat_cons (step1431 p h) (sat_cons (step1430 p h) (sat_cons (step12812 p h) (sat_cons (step3084 p h) (sat_cons (step13720 p h) (sat_cons (step3305 p h) (sat_cons (step1498 p h) (sat_cons (step1534 p h) (sat_cons (step1447 p h) (sat_cons (step10133 p h) (sat_cons (step1482 p h) (sat_cons (step13707 p h) (sat_cons (step2383 p h) (sat_cons (step1445 p h) (sat_cons (step1520 p h) (sat_cons (step1116 p h) (sat_cons (step1118 p h) (sat_cons (step1112 p h) (sat_cons (step1114 p h) (sat_cons (step1105 p h) (sat_cons (step1106 p h) (sat_cons (step1109 p h) (sat_cons (step1108 p h) (sat_cons (step1104 p h) (sat_cons (step1103 p h) (sat_cons (step302 p h) (sat_cons (step13732 p h) (sat_cons (step13731 p h) (sat_cons (step1478 p h) (sat_cons (step1480 p h) (sat_cons (step13028 p h) (sat_cons (step1481 p h) (sat_cons (step1484 p h) (sat_cons (step1504 p h) (sat_cons (step1475 p h) (sat_cons (step1476 p h) (sat_cons (step4006 p h) (sat_cons (step366 p h) (sat_cons (step4649 p h) (sat_cons (step511 p h) (sat_cons (step513 p h) (sat_cons (step512 p h) (sat_cons (step255 p h) (sat_cons (step253 p h) (sat_cons (step1471 p h) (sat_cons (step1608 p h) (sat_cons (step1957 p h) (sat_cons (step1461 p h) (sat_cons (step1613 p h) (sat_cons (step1650 p h) (sat_cons (step213 p h) (sat_cons (step3796 p h) (sat_cons (step222 p h) (sat_cons (step223 p h) (sat_cons (step448 p h) (sat_cons (step1970 p h) (sat_cons (step5178 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c13734 : List Lit := [(1598, false), (178, true), (41, false), (42, false), (45, false), (43, true), (39, false), (1601, true), (51, true), (1616, true), (1568, false), (75, false)]
theorem step13734 (p : Nat → Bool) (h : Constraints p) : clause p c13734 = true :=
  Snake9.LocalRup.prove_clause [c3305, c1498, c1534, c1447, c1438, c1445, c1520, c1481, c1484, c13692, c1504, c1476, c13722, c13018] c13734 (by decide) p (sat_cons (step3305 p h) (sat_cons (step1498 p h) (sat_cons (step1534 p h) (sat_cons (step1447 p h) (sat_cons (step1438 p h) (sat_cons (step1445 p h) (sat_cons (step1520 p h) (sat_cons (step1481 p h) (sat_cons (step1484 p h) (sat_cons (step13692 p h) (sat_cons (step1504 p h) (sat_cons (step1476 p h) (sat_cons (step13722 p h) (sat_cons (step13018 p h) (sat_nil p)))))))))))))))
def c13735 : List Lit := [(39, false), (1616, true), (74, true), (1670, true)]
theorem step13735 (p : Nat → Bool) (h : Constraints p) : clause p c13735 = true :=
  Snake9.LocalRup.prove_clause [c12893, c1648, c13720, c10133, c13707, c2383, c2848, c1647, c13727, c1527, c1446, c1433, c1435, c3084, c1430, c1431, c1427, c1428, c13733, c1121, c1157, c2337, c1160, c1150, c2361, c1147, c1294, c1296, c1142, c1222, c1138, c1195, c1190, c1192, c1186, c1180, c1183, c1177, c3550, c13734, c1478, c1479, c4464, c611, c6459, c2659, c4476, c13585, c1610, c1899, c1906, c13173, c6580, c1730, c1664, c2408] c13735 (by decide) p (sat_cons (step12893 p h) (sat_cons (step1648 p h) (sat_cons (step13720 p h) (sat_cons (step10133 p h) (sat_cons (step13707 p h) (sat_cons (step2383 p h) (sat_cons (step2848 p h) (sat_cons (step1647 p h) (sat_cons (step13727 p h) (sat_cons (step1527 p h) (sat_cons (step1446 p h) (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step3084 p h) (sat_cons (step1430 p h) (sat_cons (step1431 p h) (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step13733 p h) (sat_cons (step1121 p h) (sat_cons (step1157 p h) (sat_cons (step2337 p h) (sat_cons (step1160 p h) (sat_cons (step1150 p h) (sat_cons (step2361 p h) (sat_cons (step1147 p h) (sat_cons (step1294 p h) (sat_cons (step1296 p h) (sat_cons (step1142 p h) (sat_cons (step1222 p h) (sat_cons (step1138 p h) (sat_cons (step1195 p h) (sat_cons (step1190 p h) (sat_cons (step1192 p h) (sat_cons (step1186 p h) (sat_cons (step1180 p h) (sat_cons (step1183 p h) (sat_cons (step1177 p h) (sat_cons (step3550 p h) (sat_cons (step13734 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step4464 p h) (sat_cons (step611 p h) (sat_cons (step6459 p h) (sat_cons (step2659 p h) (sat_cons (step4476 p h) (sat_cons (step13585 p h) (sat_cons (step1610 p h) (sat_cons (step1899 p h) (sat_cons (step1906 p h) (sat_cons (step13173 p h) (sat_cons (step6580 p h) (sat_cons (step1730 p h) (sat_cons (step1664 p h) (sat_cons (step2408 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c13736 : List Lit := [(489, true), (44, false), (1598, true), (1651, false), (115, true), (67, true), (1784, true), (74, true), (1670, true)]
theorem step13736 (p : Nat → Bool) (h : Constraints p) : clause p c13736 = true :=
  Snake9.LocalRup.prove_clause [c1610, c1648, c1647, c1294, c1296, c13585, c1222, c1906, c1195, c13173, c2376, c1730, c1899, c2408, c6580, c1664] c13736 (by decide) p (sat_cons (step1610 p h) (sat_cons (step1648 p h) (sat_cons (step1647 p h) (sat_cons (step1294 p h) (sat_cons (step1296 p h) (sat_cons (step13585 p h) (sat_cons (step1222 p h) (sat_cons (step1906 p h) (sat_cons (step1195 p h) (sat_cons (step13173 p h) (sat_cons (step2376 p h) (sat_cons (step1730 p h) (sat_cons (step1899 p h) (sat_cons (step2408 p h) (sat_cons (step6580 p h) (sat_cons (step1664 p h) (sat_nil p)))))))))))))))))
def c13737 : List Lit := [(1593, true), (1598, true), (1653, false), (115, true), (67, true), (193, true), (1616, true), (74, true), (1670, true)]
theorem step13737 (p : Nat → Bool) (h : Constraints p) : clause p c13737 = true :=
  Snake9.LocalRup.prove_clause [c2303, c13720, c13707, c2383, c1648, c4901, c3027, c2505, c5198, c5384, c2730, c1640, c2376, c1899, c1864, c13730, c2359, c1284, c12667, c1853, c1859, c1906, c1730, c2408, c8968, c1664, c6293] c13737 (by decide) p (sat_cons (step2303 p h) (sat_cons (step13720 p h) (sat_cons (step13707 p h) (sat_cons (step2383 p h) (sat_cons (step1648 p h) (sat_cons (step4901 p h) (sat_cons (step3027 p h) (sat_cons (step2505 p h) (sat_cons (step5198 p h) (sat_cons (step5384 p h) (sat_cons (step2730 p h) (sat_cons (step1640 p h) (sat_cons (step2376 p h) (sat_cons (step1899 p h) (sat_cons (step1864 p h) (sat_cons (step13730 p h) (sat_cons (step2359 p h) (sat_cons (step1284 p h) (sat_cons (step12667 p h) (sat_cons (step1853 p h) (sat_cons (step1859 p h) (sat_cons (step1906 p h) (sat_cons (step1730 p h) (sat_cons (step2408 p h) (sat_cons (step8968 p h) (sat_cons (step1664 p h) (sat_cons (step6293 p h) (sat_nil p))))))))))))))))))))))))))))
def c13738 : List Lit := [(1572, true), (42, false), (178, true), (54, false), (45, false), (1594, true), (1577, true), (75, false)]
theorem step13738 (p : Nat → Bool) (h : Constraints p) : clause p c13738 = true :=
  Snake9.LocalRup.prove_clause [c366, c1428, c2494, c13018, c377] c13738 (by decide) p (sat_cons (step366 p h) (sat_cons (step1428 p h) (sat_cons (step2494 p h) (sat_cons (step13018 p h) (sat_cons (step377 p h) (sat_nil p))))))
def c13739 : List Lit := [(1598, true), (61, false), (45, false), (1616, true), (74, true), (1670, true)]
theorem step13739 (p : Nat → Bool) (h : Constraints p) : clause p c13739 = true :=
  Snake9.LocalRup.prove_clause [c12893, c6459, c1610, c611, c610, c13629, c1648, c13735, c3565, c1450, c1527, c1503, c13720, c1464, c1467, c1493, c1541, c1452, c13707, c2383, c13737, c1498, c1499, c1534, c1483, c1476, c1451, c1433, c1431, c13736, c2361, c1160, c1155, c1150, c1147, c1142, c1138, c1435, c1427, c13738] c13739 (by decide) p (sat_cons (step12893 p h) (sat_cons (step6459 p h) (sat_cons (step1610 p h) (sat_cons (step611 p h) (sat_cons (step610 p h) (sat_cons (step13629 p h) (sat_cons (step1648 p h) (sat_cons (step13735 p h) (sat_cons (step3565 p h) (sat_cons (step1450 p h) (sat_cons (step1527 p h) (sat_cons (step1503 p h) (sat_cons (step13720 p h) (sat_cons (step1464 p h) (sat_cons (step1467 p h) (sat_cons (step1493 p h) (sat_cons (step1541 p h) (sat_cons (step1452 p h) (sat_cons (step13707 p h) (sat_cons (step2383 p h) (sat_cons (step13737 p h) (sat_cons (step1498 p h) (sat_cons (step1499 p h) (sat_cons (step1534 p h) (sat_cons (step1483 p h) (sat_cons (step1476 p h) (sat_cons (step1451 p h) (sat_cons (step1433 p h) (sat_cons (step1431 p h) (sat_cons (step13736 p h) (sat_cons (step2361 p h) (sat_cons (step1160 p h) (sat_cons (step1155 p h) (sat_cons (step1150 p h) (sat_cons (step1147 p h) (sat_cons (step1142 p h) (sat_cons (step1138 p h) (sat_cons (step1435 p h) (sat_cons (step1427 p h) (sat_cons (step13738 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c13740 : List Lit := [(1598, false), (45, false), (1569, false), (1601, true), (51, true), (1616, true)]
theorem step13740 (p : Nat → Bool) (h : Constraints p) : clause p c13740 = true :=
  Snake9.LocalRup.prove_clause [c1450, c1527, c1464, c1467, c1481, c1484, c1494, c1499, c1476, c1534, c13136, c1451, c1428, c1435] c13740 (by decide) p (sat_cons (step1450 p h) (sat_cons (step1527 p h) (sat_cons (step1464 p h) (sat_cons (step1467 p h) (sat_cons (step1481 p h) (sat_cons (step1484 p h) (sat_cons (step1494 p h) (sat_cons (step1499 p h) (sat_cons (step1476 p h) (sat_cons (step1534 p h) (sat_cons (step13136 p h) (sat_cons (step1451 p h) (sat_cons (step1428 p h) (sat_cons (step1435 p h) (sat_nil p)))))))))))))))
def c13741 : List Lit := [(45, false), (1616, true), (74, true), (1670, true)]
theorem step13741 (p : Nat → Bool) (h : Constraints p) : clause p c13741 = true :=
  Snake9.LocalRup.prove_clause [c1648, c13735, c3565, c13720, c10133, c13740, c1478, c13739] c13741 (by decide) p (sat_cons (step1648 p h) (sat_cons (step13735 p h) (sat_cons (step3565 p h) (sat_cons (step13720 p h) (sat_cons (step10133 p h) (sat_cons (step13740 p h) (sat_cons (step1478 p h) (sat_cons (step13739 p h) (sat_nil p)))))))))
def c13742 : List Lit := [(1616, true), (74, true), (1670, true)]
theorem step13742 (p : Nat → Bool) (h : Constraints p) : clause p c13742 = true :=
  Snake9.LocalRup.prove_clause [c1648, c4901, c3027, c13707, c2383, c13720, c1464, c1467, c1493, c1541, c13735, c3565, c1452, c1434, c13741, c1430, c12735, c1432, c1433, c1436, c1478, c1451, c1428, c13629, c1534, c1498, c1494, c4543, c2505, c5198, c1483, c1155, c2486, c1475, c13118, c1160, c511, c513, c514, c512, c2361, c1797, c1608, c1294, c13562, c1613, c1899, c1644, c2376] c13742 (by decide) p (sat_cons (step1648 p h) (sat_cons (step4901 p h) (sat_cons (step3027 p h) (sat_cons (step13707 p h) (sat_cons (step2383 p h) (sat_cons (step13720 p h) (sat_cons (step1464 p h) (sat_cons (step1467 p h) (sat_cons (step1493 p h) (sat_cons (step1541 p h) (sat_cons (step13735 p h) (sat_cons (step3565 p h) (sat_cons (step1452 p h) (sat_cons (step1434 p h) (sat_cons (step13741 p h) (sat_cons (step1430 p h) (sat_cons (step12735 p h) (sat_cons (step1432 p h) (sat_cons (step1433 p h) (sat_cons (step1436 p h) (sat_cons (step1478 p h) (sat_cons (step1451 p h) (sat_cons (step1428 p h) (sat_cons (step13629 p h) (sat_cons (step1534 p h) (sat_cons (step1498 p h) (sat_cons (step1494 p h) (sat_cons (step4543 p h) (sat_cons (step2505 p h) (sat_cons (step5198 p h) (sat_cons (step1483 p h) (sat_cons (step1155 p h) (sat_cons (step2486 p h) (sat_cons (step1475 p h) (sat_cons (step13118 p h) (sat_cons (step1160 p h) (sat_cons (step511 p h) (sat_cons (step513 p h) (sat_cons (step514 p h) (sat_cons (step512 p h) (sat_cons (step2361 p h) (sat_cons (step1797 p h) (sat_cons (step1608 p h) (sat_cons (step1294 p h) (sat_cons (step13562 p h) (sat_cons (step1613 p h) (sat_cons (step1899 p h) (sat_cons (step1644 p h) (sat_cons (step2376 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))
def c13743 : List Lit := [(67, false), (115, false), (27, false)]
theorem step13743 (p : Nat → Bool) (h : Constraints p) : clause p c13743 = true :=
  Snake9.LocalRup.prove_clause [c12893, c607] c13743 (by decide) p (sat_cons (step12893 p h) (sat_cons (step607 p h) (sat_nil p)))
def c13744 : List Lit := [(115, false), (66, false), (27, false)]
theorem step13744 (p : Nat → Bool) (h : Constraints p) : clause p c13744 = true :=
  Snake9.LocalRup.prove_clause [c12893, c606] c13744 (by decide) p (sat_cons (step12893 p h) (sat_cons (step606 p h) (sat_nil p)))
def c13745 : List Lit := [(115, false), (27, false), (61, false)]
theorem step13745 (p : Nat → Bool) (h : Constraints p) : clause p c13745 = true :=
  Snake9.LocalRup.prove_clause [c12893, c601] c13745 (by decide) p (sat_cons (step12893 p h) (sat_cons (step601 p h) (sat_nil p)))
def c13746 : List Lit := [(77, false), (66, false), (63, false)]
theorem step13746 (p : Nat → Bool) (h : Constraints p) : clause p c13746 = true :=
  Snake9.LocalRup.prove_clause [c12893, c570] c13746 (by decide) p (sat_cons (step12893 p h) (sat_cons (step570 p h) (sat_nil p)))
def c13747 : List Lit := [(64, false), (63, false), (66, false)]
theorem step13747 (p : Nat → Bool) (h : Constraints p) : clause p c13747 = true :=
  Snake9.LocalRup.prove_clause [c12893, c1997] c13747 (by decide) p (sat_cons (step12893 p h) (sat_cons (step1997 p h) (sat_nil p)))
def c13748 : List Lit := [(65, false), (63, false), (66, false)]
theorem step13748 (p : Nat → Bool) (h : Constraints p) : clause p c13748 = true :=
  Snake9.LocalRup.prove_clause [c12893, c569] c13748 (by decide) p (sat_cons (step12893 p h) (sat_cons (step569 p h) (sat_nil p)))
def c13749 : List Lit := [(1667, true), (62, true), (1657, false), (45, false), (69, true)]
theorem step13749 (p : Nat → Bool) (h : Constraints p) : clause p c13749 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2420] c13749 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2420 p h) (sat_nil p)))
def c13750 : List Lit := [(1666, true), (62, true), (45, false), (69, true)]
theorem step13750 (p : Nat → Bool) (h : Constraints p) : clause p c13750 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2148] c13750 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2148 p h) (sat_nil p)))
def c13751 : List Lit := [(115, false), (67, false), (45, false)]
theorem step13751 (p : Nat → Bool) (h : Constraints p) : clause p c13751 = true :=
  Snake9.LocalRup.prove_clause [c12893, c617] c13751 (by decide) p (sat_cons (step12893 p h) (sat_cons (step617 p h) (sat_nil p)))
def c13752 : List Lit := [(66, false), (115, false), (45, false)]
theorem step13752 (p : Nat → Bool) (h : Constraints p) : clause p c13752 = true :=
  Snake9.LocalRup.prove_clause [c12893, c616] c13752 (by decide) p (sat_cons (step12893 p h) (sat_cons (step616 p h) (sat_nil p)))
def c13753 : List Lit := [(115, false), (27, false), (45, false)]
theorem step13753 (p : Nat → Bool) (h : Constraints p) : clause p c13753 = true :=
  Snake9.LocalRup.prove_clause [c12893, c597] c13753 (by decide) p (sat_cons (step12893 p h) (sat_cons (step597 p h) (sat_nil p)))
def c13754 : List Lit := [(188, false), (43, false)]
theorem step13754 (p : Nat → Bool) (h : Constraints p) : clause p c13754 = true :=
  Snake9.LocalRup.prove_clause [c12893, c537] c13754 (by decide) p (sat_cons (step12893 p h) (sat_cons (step537 p h) (sat_nil p)))
def c13755 : List Lit := [(115, false), (1651, true), (61, false)]
theorem step13755 (p : Nat → Bool) (h : Constraints p) : clause p c13755 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2154] c13755 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2154 p h) (sat_nil p)))
def c13756 : List Lit := [(66, false), (115, false), (61, false)]
theorem step13756 (p : Nat → Bool) (h : Constraints p) : clause p c13756 = true :=
  Snake9.LocalRup.prove_clause [c12893, c622] c13756 (by decide) p (sat_cons (step12893 p h) (sat_cons (step622 p h) (sat_nil p)))
def c13757 : List Lit := [(115, false), (67, false), (61, false)]
theorem step13757 (p : Nat → Bool) (h : Constraints p) : clause p c13757 = true :=
  Snake9.LocalRup.prove_clause [c12893, c623] c13757 (by decide) p (sat_cons (step12893 p h) (sat_cons (step623 p h) (sat_nil p)))
def c13758 : List Lit := [(66, false), (115, false), (67, false)]
theorem step13758 (p : Nat → Bool) (h : Constraints p) : clause p c13758 = true :=
  Snake9.LocalRup.prove_clause [c12893, c627] c13758 (by decide) p (sat_cons (step12893 p h) (sat_cons (step627 p h) (sat_nil p)))
def c13759 : List Lit := [(124, false), (114, false), (115, false)]
theorem step13759 (p : Nat → Bool) (h : Constraints p) : clause p c13759 = true :=
  Snake9.LocalRup.prove_clause [c12893, c913] c13759 (by decide) p (sat_cons (step12893 p h) (sat_cons (step913 p h) (sat_nil p)))
def c13760 : List Lit := [(64, false), (115, false), (66, false)]
theorem step13760 (p : Nat → Bool) (h : Constraints p) : clause p c13760 = true :=
  Snake9.LocalRup.prove_clause [c12893, c625] c13760 (by decide) p (sat_cons (step12893 p h) (sat_cons (step625 p h) (sat_nil p)))
def c13761 : List Lit := [(64, false), (115, false), (67, false)]
theorem step13761 (p : Nat → Bool) (h : Constraints p) : clause p c13761 = true :=
  Snake9.LocalRup.prove_clause [c12893, c626] c13761 (by decide) p (sat_cons (step12893 p h) (sat_cons (step626 p h) (sat_nil p)))
def c13762 : List Lit := [(115, false), (61, false), (45, false)]
theorem step13762 (p : Nat → Bool) (h : Constraints p) : clause p c13762 = true :=
  Snake9.LocalRup.prove_clause [c12893, c611] c13762 (by decide) p (sat_cons (step12893 p h) (sat_cons (step611 p h) (sat_nil p)))
def c13763 : List Lit := [(64, false), (115, false), (61, false)]
theorem step13763 (p : Nat → Bool) (h : Constraints p) : clause p c13763 = true :=
  Snake9.LocalRup.prove_clause [c12893, c620] c13763 (by decide) p (sat_cons (step12893 p h) (sat_cons (step620 p h) (sat_nil p)))
def c13764 : List Lit := [(66, false), (27, false), (45, false)]
theorem step13764 (p : Nat → Bool) (h : Constraints p) : clause p c13764 = true :=
  Snake9.LocalRup.prove_clause [c12893, c595] c13764 (by decide) p (sat_cons (step12893 p h) (sat_cons (step595 p h) (sat_nil p)))
def c13765 : List Lit := [(64, false), (27, false), (45, false)]
theorem step13765 (p : Nat → Bool) (h : Constraints p) : clause p c13765 = true :=
  Snake9.LocalRup.prove_clause [c12893, c594] c13765 (by decide) p (sat_cons (step12893 p h) (sat_cons (step594 p h) (sat_nil p)))
def c13766 : List Lit := [(67, false), (27, false), (45, false)]
theorem step13766 (p : Nat → Bool) (h : Constraints p) : clause p c13766 = true :=
  Snake9.LocalRup.prove_clause [c12893, c596] c13766 (by decide) p (sat_cons (step12893 p h) (sat_cons (step596 p h) (sat_nil p)))
def c13767 : List Lit := [(27, false), (61, false), (45, false)]
theorem step13767 (p : Nat → Bool) (h : Constraints p) : clause p c13767 = true :=
  Snake9.LocalRup.prove_clause [c12893, c593] c13767 (by decide) p (sat_cons (step12893 p h) (sat_cons (step593 p h) (sat_nil p)))
def c13768 : List Lit := [(45, false), (1650, true)]
theorem step13768 (p : Nat → Bool) (h : Constraints p) : clause p c13768 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2147] c13768 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2147 p h) (sat_nil p)))
def c13769 : List Lit := [(64, false), (43, false), (45, false)]
theorem step13769 (p : Nat → Bool) (h : Constraints p) : clause p c13769 = true :=
  Snake9.LocalRup.prove_clause [c12893, c1978] c13769 (by decide) p (sat_cons (step12893 p h) (sat_cons (step1978 p h) (sat_nil p)))
def c13770 : List Lit := [(114, false), (115, false), (67, false)]
theorem step13770 (p : Nat → Bool) (h : Constraints p) : clause p c13770 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2000] c13770 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2000 p h) (sat_nil p)))
def c13771 : List Lit := [(67, false), (61, false), (45, false)]
theorem step13771 (p : Nat → Bool) (h : Constraints p) : clause p c13771 = true :=
  Snake9.LocalRup.prove_clause [c12893, c610] c13771 (by decide) p (sat_cons (step12893 p h) (sat_cons (step610 p h) (sat_nil p)))
def c13772 : List Lit := [(65, false), (67, false), (26, false)]
theorem step13772 (p : Nat → Bool) (h : Constraints p) : clause p c13772 = true :=
  Snake9.LocalRup.prove_clause [c12893, c578] c13772 (by decide) p (sat_cons (step12893 p h) (sat_cons (step578 p h) (sat_nil p)))
def c13773 : List Lit := [(60, false), (67, false), (61, false)]
theorem step13773 (p : Nat → Bool) (h : Constraints p) : clause p c13773 = true :=
  Snake9.LocalRup.prove_clause [c12893, c1990] c13773 (by decide) p (sat_cons (step12893 p h) (sat_cons (step1990 p h) (sat_nil p)))
def c13774 : List Lit := [(65, false), (60, false), (67, false)]
theorem step13774 (p : Nat → Bool) (h : Constraints p) : clause p c13774 = true :=
  Snake9.LocalRup.prove_clause [c12893, c583] c13774 (by decide) p (sat_cons (step12893 p h) (sat_cons (step583 p h) (sat_nil p)))
def c13775 : List Lit := [(78, false), (60, false), (67, false)]
theorem step13775 (p : Nat → Bool) (h : Constraints p) : clause p c13775 = true :=
  Snake9.LocalRup.prove_clause [c12893, c585] c13775 (by decide) p (sat_cons (step12893 p h) (sat_cons (step585 p h) (sat_nil p)))
def c13776 : List Lit := [(67, false), (27, false), (61, false)]
theorem step13776 (p : Nat → Bool) (h : Constraints p) : clause p c13776 = true :=
  Snake9.LocalRup.prove_clause [c12893, c600] c13776 (by decide) p (sat_cons (step12893 p h) (sat_cons (step600 p h) (sat_nil p)))
def c13777 : List Lit := [(114, false), (60, false), (67, false)]
theorem step13777 (p : Nat → Bool) (h : Constraints p) : clause p c13777 = true :=
  Snake9.LocalRup.prove_clause [c12893, c586] c13777 (by decide) p (sat_cons (step12893 p h) (sat_cons (step586 p h) (sat_nil p)))
def c13778 : List Lit := [(66, false), (67, false), (45, false)]
theorem step13778 (p : Nat → Bool) (h : Constraints p) : clause p c13778 = true :=
  Snake9.LocalRup.prove_clause [c12893, c615] c13778 (by decide) p (sat_cons (step12893 p h) (sat_cons (step615 p h) (sat_nil p)))
def c13779 : List Lit := [(26, false), (67, false), (27, false)]
theorem step13779 (p : Nat → Bool) (h : Constraints p) : clause p c13779 = true :=
  Snake9.LocalRup.prove_clause [c12893, c1963] c13779 (by decide) p (sat_cons (step12893 p h) (sat_cons (step1963 p h) (sat_nil p)))
def c13780 : List Lit := [(115, true), (27, true), (64, true), (66, true), (61, true), (67, true)]
theorem step13780 (p : Nat → Bool) (h : Constraints p) : clause p c13780 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2243] c13780 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2243 p h) (sat_nil p)))
def c13781 : List Lit := [(115, true), (27, true), (67, true), (45, true), (64, true), (61, true)]
theorem step13781 (p : Nat → Bool) (h : Constraints p) : clause p c13781 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2246] c13781 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2246 p h) (sat_nil p)))
def c13782 : List Lit := [(61, true), (66, true), (27, true), (67, true), (45, true), (64, true)]
theorem step13782 (p : Nat → Bool) (h : Constraints p) : clause p c13782 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2248] c13782 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2248 p h) (sat_nil p)))
def c13783 : List Lit := [(115, true), (61, true), (64, true), (66, true), (67, true), (45, true)]
theorem step13783 (p : Nat → Bool) (h : Constraints p) : clause p c13783 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2242] c13783 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2242 p h) (sat_nil p)))
def c13784 : List Lit := [(61, true), (115, true), (64, true), (66, true), (45, true), (27, true)]
theorem step13784 (p : Nat → Bool) (h : Constraints p) : clause p c13784 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2247] c13784 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2247 p h) (sat_nil p)))
def c13785 : List Lit := [(185, false), (60, false)]
theorem step13785 (p : Nat → Bool) (h : Constraints p) : clause p c13785 = true :=
  Snake9.LocalRup.prove_clause [c12893, c470] c13785 (by decide) p (sat_cons (step12893 p h) (sat_cons (step470 p h) (sat_nil p)))
def c13786 : List Lit := [(115, true), (27, true), (66, true), (45, true), (61, true), (67, true)]
theorem step13786 (p : Nat → Bool) (h : Constraints p) : clause p c13786 = true :=
  Snake9.LocalRup.prove_clause [c12893, c2245] c13786 (by decide) p (sat_cons (step12893 p h) (sat_cons (step2245 p h) (sat_nil p)))
def c13787 : List Lit := [(55, false), (169, false)]
theorem step13787 (p : Nat → Bool) (h : Constraints p) : clause p c13787 = true :=
  Snake9.LocalRup.prove_clause [c12893, c299] c13787 (by decide) p (sat_cons (step12893 p h) (sat_cons (step299 p h) (sat_nil p)))
end B112E089
