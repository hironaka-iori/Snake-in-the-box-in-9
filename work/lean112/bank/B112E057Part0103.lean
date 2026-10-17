import B112E057Part0102
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c8617 : List Lit := [(1049, false), (1088, false), (15, false), (95, true), (89, true), (1124, false), (88, true)]
theorem step8617 (p : Nat → Bool) (h : Constraints p) : clause p c8617 = true :=
  Snake9.LocalRup.prove_clause [c1594, c1601, c3003, c1622, c6650, c6646, c1595, c5315, c4692, c1777, c1714] c8617 (by decide) p (sat_cons (step1594 p h) (sat_cons (step1601 p h) (sat_cons (step3003 p h) (sat_cons (step1622 p h) (sat_cons (step6650 p h) (sat_cons (step6646 p h) (sat_cons (step1595 p h) (sat_cons (step5315 p h) (sat_cons (step4692 p h) (sat_cons (step1777 p h) (sat_cons (step1714 p h) (sat_nil p))))))))))))
def c8618 : List Lit := [(1136, true), (83, false), (86, false), (1084, false), (15, false), (984, true), (112, true), (1124, false), (88, true)]
theorem step8618 (p : Nat → Bool) (h : Constraints p) : clause p c8618 = true :=
  Snake9.LocalRup.prove_clause [c3003, c1686, c1713, c1777, c1773, c1717, c1714, c7474, c1687, c1738, c1678, c670, c2813, c4615] c8618 (by decide) p (sat_cons (step3003 p h) (sat_cons (step1686 p h) (sat_cons (step1713 p h) (sat_cons (step1777 p h) (sat_cons (step1773 p h) (sat_cons (step1717 p h) (sat_cons (step1714 p h) (sat_cons (step7474 p h) (sat_cons (step1687 p h) (sat_cons (step1738 p h) (sat_cons (step1678 p h) (sat_cons (step670 p h) (sat_cons (step2813 p h) (sat_cons (step4615 p h) (sat_nil p)))))))))))))))
def c8619 : List Lit := [(1084, false), (82, true), (11, false), (15, false), (984, true), (95, true), (89, true), (112, true), (1124, false), (1045, false), (88, true), (1137, true)]
theorem step8619 (p : Nat → Bool) (h : Constraints p) : clause p c8619 = true :=
  Snake9.LocalRup.prove_clause [c8056, c1724, c1588, c1686, c8617, c1591, c3958, c1581, c8618, c5315, c6646, c1618, c1604, c1595, c4692, c1714, c1778, c2811, c7447] c8619 (by decide) p (sat_cons (step8056 p h) (sat_cons (step1724 p h) (sat_cons (step1588 p h) (sat_cons (step1686 p h) (sat_cons (step8617 p h) (sat_cons (step1591 p h) (sat_cons (step3958 p h) (sat_cons (step1581 p h) (sat_cons (step8618 p h) (sat_cons (step5315 p h) (sat_cons (step6646 p h) (sat_cons (step1618 p h) (sat_cons (step1604 p h) (sat_cons (step1595 p h) (sat_cons (step4692 p h) (sat_cons (step1714 p h) (sat_cons (step1778 p h) (sat_cons (step2811 p h) (sat_cons (step7447 p h) (sat_nil p))))))))))))))))))))
def c8620 : List Lit := [(1049, false), (1056, false), (919, false), (95, true), (89, true), (112, true), (1124, false), (88, true)]
theorem step8620 (p : Nat → Bool) (h : Constraints p) : clause p c8620 = true :=
  Snake9.LocalRup.prove_clause [c2969, c1724, c3003, c1623, c6650, c6642, c1595, c5309, c7438, c1768, c2811] c8620 (by decide) p (sat_cons (step2969 p h) (sat_cons (step1724 p h) (sat_cons (step3003 p h) (sat_cons (step1623 p h) (sat_cons (step6650 p h) (sat_cons (step6642 p h) (sat_cons (step1595 p h) (sat_cons (step5309 p h) (sat_cons (step7438 p h) (sat_cons (step1768 p h) (sat_cons (step2811 p h) (sat_nil p))))))))))))
def c8621 : List Lit := [(82, true), (11, false), (15, false), (984, true), (919, false), (95, true), (89, true), (112, true), (1124, false), (1045, false), (88, true), (1137, true)]
theorem step8621 (p : Nat → Bool) (h : Constraints p) : clause p c8621 = true :=
  Snake9.LocalRup.prove_clause [c8056, c1594, c1724, c1588, c8619, c1677, c2110, c1602, c1618, c6646, c5315, c8620, c3958, c3927, c1772, c1773, c5309, c2811, c6642, c7447, c1619, c1595, c1605] c8621 (by decide) p (sat_cons (step8056 p h) (sat_cons (step1594 p h) (sat_cons (step1724 p h) (sat_cons (step1588 p h) (sat_cons (step8619 p h) (sat_cons (step1677 p h) (sat_cons (step2110 p h) (sat_cons (step1602 p h) (sat_cons (step1618 p h) (sat_cons (step6646 p h) (sat_cons (step5315 p h) (sat_cons (step8620 p h) (sat_cons (step3958 p h) (sat_cons (step3927 p h) (sat_cons (step1772 p h) (sat_cons (step1773 p h) (sat_cons (step5309 p h) (sat_cons (step2811 p h) (sat_cons (step6642 p h) (sat_cons (step7447 p h) (sat_cons (step1619 p h) (sat_cons (step1595 p h) (sat_cons (step1605 p h) (sat_nil p))))))))))))))))))))))))
def c8622 : List Lit := [(919, false), (4, true), (76, true), (1005, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8622 (p : Nat → Bool) (h : Constraints p) : clause p c8622 = true :=
  Snake9.LocalRup.prove_clause [c8612, c8586, c8494, c8474, c8143, c8409, c6639, c5311, c1523, c8613, c8616, c8610, c1281, c1282, c8621, c2884, c6581, c2081] c8622 (by decide) p (sat_cons (step8612 p h) (sat_cons (step8586 p h) (sat_cons (step8494 p h) (sat_cons (step8474 p h) (sat_cons (step8143 p h) (sat_cons (step8409 p h) (sat_cons (step6639 p h) (sat_cons (step5311 p h) (sat_cons (step1523 p h) (sat_cons (step8613 p h) (sat_cons (step8616 p h) (sat_cons (step8610 p h) (sat_cons (step1281 p h) (sat_cons (step1282 p h) (sat_cons (step8621 p h) (sat_cons (step2884 p h) (sat_cons (step6581 p h) (sat_cons (step2081 p h) (sat_nil p)))))))))))))))))))
def c8623 : List Lit := [(82, true), (1032, false), (86, true), (877, true), (95, true), (89, true), (1124, false), (88, true)]
theorem step8623 (p : Nat → Bool) (h : Constraints p) : clause p c8623 = true :=
  Snake9.LocalRup.prove_clause [c8056, c1282, c1281, c2969, c1767, c5316, c6643, c1676, c1683, c8607, c3958, c1571, c1624, c8617, c2081, c1686, c1543, c1677, c6654, c2110] c8623 (by decide) p (sat_cons (step8056 p h) (sat_cons (step1282 p h) (sat_cons (step1281 p h) (sat_cons (step2969 p h) (sat_cons (step1767 p h) (sat_cons (step5316 p h) (sat_cons (step6643 p h) (sat_cons (step1676 p h) (sat_cons (step1683 p h) (sat_cons (step8607 p h) (sat_cons (step3958 p h) (sat_cons (step1571 p h) (sat_cons (step1624 p h) (sat_cons (step8617 p h) (sat_cons (step2081 p h) (sat_cons (step1686 p h) (sat_cons (step1543 p h) (sat_cons (step1677 p h) (sat_cons (step6654 p h) (sat_cons (step2110 p h) (sat_nil p)))))))))))))))))))))
def c8624 : List Lit := [(23, true), (919, true), (4, true), (95, true), (89, true), (76, true), (1103, true), (1124, false), (73, false), (70, false), (88, true), (79, true)]
theorem step8624 (p : Nat → Bool) (h : Constraints p) : clause p c8624 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5928, c1676, c1683, c8143, c1588, c5935, c5931, c1282, c47, c2973, c3009, c4485, c2619, c1333, c8623, c2884, c7667, c2081, c2241, c1571, c1331, c5365, c8374, c2124] c8624 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5928 p h) (sat_cons (step1676 p h) (sat_cons (step1683 p h) (sat_cons (step8143 p h) (sat_cons (step1588 p h) (sat_cons (step5935 p h) (sat_cons (step5931 p h) (sat_cons (step1282 p h) (sat_cons (step47 p h) (sat_cons (step2973 p h) (sat_cons (step3009 p h) (sat_cons (step4485 p h) (sat_cons (step2619 p h) (sat_cons (step1333 p h) (sat_cons (step8623 p h) (sat_cons (step2884 p h) (sat_cons (step7667 p h) (sat_cons (step2081 p h) (sat_cons (step2241 p h) (sat_cons (step1571 p h) (sat_cons (step1331 p h) (sat_cons (step5365 p h) (sat_cons (step8374 p h) (sat_cons (step2124 p h) (sat_nil p))))))))))))))))))))))))))
def c8625 : List Lit := [(4, true), (76, true), (1005, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8625 (p : Nat → Bool) (h : Constraints p) : clause p c8625 = true :=
  Snake9.TreeRup.prove_clause [c8612, c8586, c5319, c6639, c5311, c8474, c1781, c8409, c5445, c8622, c2412, c6220, c1368, c5928, c1396, c8624, c8273, c6097, c5833, c2284, c1452, c6319, c6340, c2662, c6315, c1138, c2066, c1497, c1421, c1139, c1471, c1430, c1423, c1488, c1486, c1143, c1448, c1528, c1158, c6341, c5396, c1188, c1400, c2202, c1256, c5427, c2408, c1330, c1133, c1135, c1332, c5405, c1130, c1074, c2234, c1098, c1043, c1086, c1032, c1080, c1031, c1077, c1030, c6454, c1315, c1316, c6004, c208, c270, c254] c8625 (by decide) p (sat_cons (step8612 p h) (sat_cons (step8586 p h) (sat_cons (step5319 p h) (sat_cons (step6639 p h) (sat_cons (step5311 p h) (sat_cons (step8474 p h) (sat_cons (step1781 p h) (sat_cons (step8409 p h) (sat_cons (step5445 p h) (sat_cons (step8622 p h) (sat_cons (step2412 p h) (sat_cons (step6220 p h) (sat_cons (step1368 p h) (sat_cons (step5928 p h) (sat_cons (step1396 p h) (sat_cons (step8624 p h) (sat_cons (step8273 p h) (sat_cons (step6097 p h) (sat_cons (step5833 p h) (sat_cons (step2284 p h) (sat_cons (step1452 p h) (sat_cons (step6319 p h) (sat_cons (step6340 p h) (sat_cons (step2662 p h) (sat_cons (step6315 p h) (sat_cons (step1138 p h) (sat_cons (step2066 p h) (sat_cons (step1497 p h) (sat_cons (step1421 p h) (sat_cons (step1139 p h) (sat_cons (step1471 p h) (sat_cons (step1430 p h) (sat_cons (step1423 p h) (sat_cons (step1488 p h) (sat_cons (step1486 p h) (sat_cons (step1143 p h) (sat_cons (step1448 p h) (sat_cons (step1528 p h) (sat_cons (step1158 p h) (sat_cons (step6341 p h) (sat_cons (step5396 p h) (sat_cons (step1188 p h) (sat_cons (step1400 p h) (sat_cons (step2202 p h) (sat_cons (step1256 p h) (sat_cons (step5427 p h) (sat_cons (step2408 p h) (sat_cons (step1330 p h) (sat_cons (step1133 p h) (sat_cons (step1135 p h) (sat_cons (step1332 p h) (sat_cons (step5405 p h) (sat_cons (step1130 p h) (sat_cons (step1074 p h) (sat_cons (step2234 p h) (sat_cons (step1098 p h) (sat_cons (step1043 p h) (sat_cons (step1086 p h) (sat_cons (step1032 p h) (sat_cons (step1080 p h) (sat_cons (step1031 p h) (sat_cons (step1077 p h) (sat_cons (step1030 p h) (sat_cons (step6454 p h) (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step6004 p h) (sat_cons (step208 p h) (sat_cons (step270 p h) (sat_cons (step254 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c8626 : List Lit := [(76, true), (1005, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8626 (p : Nat → Bool) (h : Constraints p) : clause p c8626 = true :=
  Snake9.LocalRup.prove_clause [c8056, c8474, c8143, c1588, c8409, c3003, c1553, c1556, c8586, c8612, c1676, c5347, c1683, c8625, c7030, c5335, c8374, c1595, c2110, c7232, c1677, c1576, c1686, c2082, c5349, c7028] c8626 (by decide) p (sat_cons (step8056 p h) (sat_cons (step8474 p h) (sat_cons (step8143 p h) (sat_cons (step1588 p h) (sat_cons (step8409 p h) (sat_cons (step3003 p h) (sat_cons (step1553 p h) (sat_cons (step1556 p h) (sat_cons (step8586 p h) (sat_cons (step8612 p h) (sat_cons (step1676 p h) (sat_cons (step5347 p h) (sat_cons (step1683 p h) (sat_cons (step8625 p h) (sat_cons (step7030 p h) (sat_cons (step5335 p h) (sat_cons (step8374 p h) (sat_cons (step1595 p h) (sat_cons (step2110 p h) (sat_cons (step7232 p h) (sat_cons (step1677 p h) (sat_cons (step1576 p h) (sat_cons (step1686 p h) (sat_cons (step2082 p h) (sat_cons (step5349 p h) (sat_cons (step7028 p h) (sat_nil p)))))))))))))))))))))))))))
def c8627 : List Lit := [(89, false), (1136, true), (1039, false), (76, false), (1107, false), (73, false), (88, true)]
theorem step8627 (p : Nat → Bool) (h : Constraints p) : clause p c8627 = true :=
  Snake9.LocalRup.prove_clause [c8056, c8143, c1588, c3003, c563, c562, c2811, c1679, c1773, c1681, c1713, c1709, c1708, c1684, c1768, c1675, c5309, c2110, c1652, c6554] c8627 (by decide) p (sat_cons (step8056 p h) (sat_cons (step8143 p h) (sat_cons (step1588 p h) (sat_cons (step3003 p h) (sat_cons (step563 p h) (sat_cons (step562 p h) (sat_cons (step2811 p h) (sat_cons (step1679 p h) (sat_cons (step1773 p h) (sat_cons (step1681 p h) (sat_cons (step1713 p h) (sat_cons (step1709 p h) (sat_cons (step1708 p h) (sat_cons (step1684 p h) (sat_cons (step1768 p h) (sat_cons (step1675 p h) (sat_cons (step5309 p h) (sat_cons (step2110 p h) (sat_cons (step1652 p h) (sat_cons (step6554 p h) (sat_nil p)))))))))))))))))))))
def c8628 : List Lit := [(1083, false), (1088, true), (1136, true), (1039, false), (76, false), (1107, false), (73, false), (88, true)]
theorem step8628 (p : Nat → Bool) (h : Constraints p) : clause p c8628 = true :=
  Snake9.LocalRup.prove_clause [c8627, c8143, c3003, c1683, c1684, c1708, c8597, c1679, c2811, c564] c8628 (by decide) p (sat_cons (step8627 p h) (sat_cons (step8143 p h) (sat_cons (step3003 p h) (sat_cons (step1683 p h) (sat_cons (step1684 p h) (sat_cons (step1708 p h) (sat_cons (step8597 p h) (sat_cons (step1679 p h) (sat_cons (step2811 p h) (sat_cons (step564 p h) (sat_nil p)))))))))))
def c8629 : List Lit := [(1053, false), (89, true), (1039, false), (76, false), (1107, false), (1124, false), (73, false), (88, true)]
theorem step8629 (p : Nat → Bool) (h : Constraints p) : clause p c8629 = true :=
  Snake9.LocalRup.prove_clause [c8056, c1594, c8143, c1588, c5346, c1602, c1681, c1618, c1679, c1652, c564, c5309, c2811, c1768, c2907, c6014, c5316, c1653, c3845, c4996] c8629 (by decide) p (sat_cons (step8056 p h) (sat_cons (step1594 p h) (sat_cons (step8143 p h) (sat_cons (step1588 p h) (sat_cons (step5346 p h) (sat_cons (step1602 p h) (sat_cons (step1681 p h) (sat_cons (step1618 p h) (sat_cons (step1679 p h) (sat_cons (step1652 p h) (sat_cons (step564 p h) (sat_cons (step5309 p h) (sat_cons (step2811 p h) (sat_cons (step1768 p h) (sat_cons (step2907 p h) (sat_cons (step6014 p h) (sat_cons (step5316 p h) (sat_cons (step1653 p h) (sat_cons (step3845 p h) (sat_cons (step4996 p h) (sat_nil p)))))))))))))))))))))
def c8630 : List Lit := [(95, false), (1005, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8630 (p : Nat → Bool) (h : Constraints p) : clause p c8630 = true :=
  Snake9.LocalRup.prove_clause [c8056, c8409, c8626, c8491, c8494, c1724, c8474, c8143, c1588, c6585, c1651, c5315, c8627, c8629, c2110, c1675, c8628, c5349, c477, c4786, c8587] c8630 (by decide) p (sat_cons (step8056 p h) (sat_cons (step8409 p h) (sat_cons (step8626 p h) (sat_cons (step8491 p h) (sat_cons (step8494 p h) (sat_cons (step1724 p h) (sat_cons (step8474 p h) (sat_cons (step8143 p h) (sat_cons (step1588 p h) (sat_cons (step6585 p h) (sat_cons (step1651 p h) (sat_cons (step5315 p h) (sat_cons (step8627 p h) (sat_cons (step8629 p h) (sat_cons (step2110 p h) (sat_cons (step1675 p h) (sat_cons (step8628 p h) (sat_cons (step5349 p h) (sat_cons (step477 p h) (sat_cons (step4786 p h) (sat_cons (step8587 p h) (sat_nil p))))))))))))))))))))))
def c8631 : List Lit := [(89, false), (1022, true), (95, true), (76, false), (1107, false), (1124, false), (73, false), (88, true), (79, true), (1137, true)]
theorem step8631 (p : Nat → Bool) (h : Constraints p) : clause p c8631 = true :=
  Snake9.LocalRup.prove_clause [c8056, c8143, c1588, c563, c562, c550, c2811, c1679, c6519, c1545, c1778, c5099] c8631 (by decide) p (sat_cons (step8056 p h) (sat_cons (step8143 p h) (sat_cons (step1588 p h) (sat_cons (step563 p h) (sat_cons (step562 p h) (sat_cons (step550 p h) (sat_cons (step2811 p h) (sat_cons (step1679 p h) (sat_cons (step6519 p h) (sat_cons (step1545 p h) (sat_cons (step1778 p h) (sat_cons (step5099 p h) (sat_nil p)))))))))))))
def c8632 : List Lit := [(1039, false), (89, true), (95, true), (1032, false), (76, false), (1107, false), (1124, false), (73, false), (88, true), (1061, false)]
theorem step8632 (p : Nat → Bool) (h : Constraints p) : clause p c8632 = true :=
  Snake9.LocalRup.prove_clause [c8056, c1594, c1601, c1676, c1683, c2969, c8143, c1588, c3003, c1651, c5335, c5315, c1595, c8628, c8597, c5332, c2811, c552] c8632 (by decide) p (sat_cons (step8056 p h) (sat_cons (step1594 p h) (sat_cons (step1601 p h) (sat_cons (step1676 p h) (sat_cons (step1683 p h) (sat_cons (step2969 p h) (sat_cons (step8143 p h) (sat_cons (step1588 p h) (sat_cons (step3003 p h) (sat_cons (step1651 p h) (sat_cons (step5335 p h) (sat_cons (step5315 p h) (sat_cons (step1595 p h) (sat_cons (step8628 p h) (sat_cons (step8597 p h) (sat_cons (step5332 p h) (sat_cons (step2811 p h) (sat_cons (step552 p h) (sat_nil p)))))))))))))))))))
def c8633 : List Lit := [(1005, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8633 (p : Nat → Bool) (h : Constraints p) : clause p c8633 = true :=
  Snake9.LocalRup.prove_clause [c8056, c8474, c8143, c8409, c6639, c5311, c8494, c1724, c8626, c8491, c8630, c2969, c5347, c1576, c2082, c8631, c8632, c6519, c4636, c1571, c1992, c552, c1550, c2081, c2811, c1543, c1768, c5098, c5309, c6642] c8633 (by decide) p (sat_cons (step8056 p h) (sat_cons (step8474 p h) (sat_cons (step8143 p h) (sat_cons (step8409 p h) (sat_cons (step6639 p h) (sat_cons (step5311 p h) (sat_cons (step8494 p h) (sat_cons (step1724 p h) (sat_cons (step8626 p h) (sat_cons (step8491 p h) (sat_cons (step8630 p h) (sat_cons (step2969 p h) (sat_cons (step5347 p h) (sat_cons (step1576 p h) (sat_cons (step2082 p h) (sat_cons (step8631 p h) (sat_cons (step8632 p h) (sat_cons (step6519 p h) (sat_cons (step4636 p h) (sat_cons (step1571 p h) (sat_cons (step1992 p h) (sat_cons (step552 p h) (sat_cons (step1550 p h) (sat_cons (step2081 p h) (sat_cons (step2811 p h) (sat_cons (step1543 p h) (sat_cons (step1768 p h) (sat_cons (step5098 p h) (sat_cons (step5309 p h) (sat_cons (step6642 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c8634 : List Lit := [(112, false), (95, false), (76, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8634 (p : Nat → Bool) (h : Constraints p) : clause p c8634 = true :=
  Snake9.LocalRup.prove_clause [c8056, c8474, c8633, c2427, c8409, c6585, c1651, c1804, c1772, c8143, c8268, c1588, c3003, c488, c489, c4824, c8487, c1555, c2082, c2110, c1557, c1576, c1675, c3826, c3566, c1683, c5174, c1709] c8634 (by decide) p (sat_cons (step8056 p h) (sat_cons (step8474 p h) (sat_cons (step8633 p h) (sat_cons (step2427 p h) (sat_cons (step8409 p h) (sat_cons (step6585 p h) (sat_cons (step1651 p h) (sat_cons (step1804 p h) (sat_cons (step1772 p h) (sat_cons (step8143 p h) (sat_cons (step8268 p h) (sat_cons (step1588 p h) (sat_cons (step3003 p h) (sat_cons (step488 p h) (sat_cons (step489 p h) (sat_cons (step4824 p h) (sat_cons (step8487 p h) (sat_cons (step1555 p h) (sat_cons (step2082 p h) (sat_cons (step2110 p h) (sat_cons (step1557 p h) (sat_cons (step1576 p h) (sat_cons (step1675 p h) (sat_cons (step3826 p h) (sat_cons (step3566 p h) (sat_cons (step1683 p h) (sat_cons (step5174 p h) (sat_cons (step1709 p h) (sat_nil p)))))))))))))))))))))))))))))
def c8635 : List Lit := [(1087, false), (112, true), (1039, false), (76, true), (1159, true), (1124, false), (73, false), (88, true), (1061, false)]
theorem step8635 (p : Nat → Bool) (h : Constraints p) : clause p c8635 = true :=
  Snake9.LocalRup.prove_clause [c1724, c3003, c1651, c1804, c1772, c1713, c8143, c8268, c6449, c1708, c8495, c1709, c1767, c1768, c1809, c2811, c4981, c1652, c4829, c1737, c1738, c4330, c1726, c4363, c6009, c937, c1584] c8635 (by decide) p (sat_cons (step1724 p h) (sat_cons (step3003 p h) (sat_cons (step1651 p h) (sat_cons (step1804 p h) (sat_cons (step1772 p h) (sat_cons (step1713 p h) (sat_cons (step8143 p h) (sat_cons (step8268 p h) (sat_cons (step6449 p h) (sat_cons (step1708 p h) (sat_cons (step8495 p h) (sat_cons (step1709 p h) (sat_cons (step1767 p h) (sat_cons (step1768 p h) (sat_cons (step1809 p h) (sat_cons (step2811 p h) (sat_cons (step4981 p h) (sat_cons (step1652 p h) (sat_cons (step4829 p h) (sat_cons (step1737 p h) (sat_cons (step1738 p h) (sat_cons (step4330 p h) (sat_cons (step1726 p h) (sat_cons (step4363 p h) (sat_cons (step6009 p h) (sat_cons (step937 p h) (sat_cons (step1584 p h) (sat_nil p))))))))))))))))))))))))))))
def c8636 : List Lit := [(1125, true), (1053, false), (112, true), (89, false), (1063, true), (76, true), (73, false), (88, true)]
theorem step8636 (p : Nat → Bool) (h : Constraints p) : clause p c8636 = true :=
  Snake9.LocalRup.prove_clause [c8056, c1724, c2811, c4981, c4829, c1737, c4330, c1726, c938, c937, c4782, c4996] c8636 (by decide) p (sat_cons (step8056 p h) (sat_cons (step1724 p h) (sat_cons (step2811 p h) (sat_cons (step4981 p h) (sat_cons (step4829 p h) (sat_cons (step1737 p h) (sat_cons (step4330 p h) (sat_cons (step1726 p h) (sat_cons (step938 p h) (sat_cons (step937 p h) (sat_cons (step4782 p h) (sat_cons (step4996 p h) (sat_nil p)))))))))))))
def c8637 : List Lit := [(95, false), (76, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8637 (p : Nat → Bool) (h : Constraints p) : clause p c8637 = true :=
  Snake9.LocalRup.prove_clause [c8474, c2906, c8633, c2427, c1815, c8143, c8409, c5691, c6585, c2081, c1651, c1653, c8268, c1804, c8634, c8635, c1683, c1675, c2110, c8636, c1768, c8539, c3845] c8637 (by decide) p (sat_cons (step8474 p h) (sat_cons (step2906 p h) (sat_cons (step8633 p h) (sat_cons (step2427 p h) (sat_cons (step1815 p h) (sat_cons (step8143 p h) (sat_cons (step8409 p h) (sat_cons (step5691 p h) (sat_cons (step6585 p h) (sat_cons (step2081 p h) (sat_cons (step1651 p h) (sat_cons (step1653 p h) (sat_cons (step8268 p h) (sat_cons (step1804 p h) (sat_cons (step8634 p h) (sat_cons (step8635 p h) (sat_cons (step1683 p h) (sat_cons (step1675 p h) (sat_cons (step2110 p h) (sat_cons (step8636 p h) (sat_cons (step1768 p h) (sat_cons (step8539 p h) (sat_cons (step3845 p h) (sat_nil p))))))))))))))))))))))))
def c8638 : List Lit := [(1039, false), (89, false), (76, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8638 (p : Nat → Bool) (h : Constraints p) : clause p c8638 = true :=
  Snake9.LocalRup.prove_clause [c8637, c1676, c1683, c8633, c2427, c8474, c3003, c1651, c8635, c1804, c8487, c1772, c2110, c1713, c1677, c1686] c8638 (by decide) p (sat_cons (step8637 p h) (sat_cons (step1676 p h) (sat_cons (step1683 p h) (sat_cons (step8633 p h) (sat_cons (step2427 p h) (sat_cons (step8474 p h) (sat_cons (step3003 p h) (sat_cons (step1651 p h) (sat_cons (step8635 p h) (sat_cons (step1804 p h) (sat_cons (step8487 p h) (sat_cons (step1772 p h) (sat_cons (step2110 p h) (sat_cons (step1713 p h) (sat_cons (step1677 p h) (sat_cons (step1686 p h) (sat_nil p)))))))))))))))))
def c8639 : List Lit := [(112, false), (89, false), (76, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8639 (p : Nat → Bool) (h : Constraints p) : clause p c8639 = true :=
  Snake9.LocalRup.prove_clause [c8638, c8474, c8409, c5653, c8487, c2081, c2110, c1571, c8479] c8639 (by decide) p (sat_cons (step8638 p h) (sat_cons (step8474 p h) (sat_cons (step8409 p h) (sat_cons (step5653 p h) (sat_cons (step8487 p h) (sat_cons (step2081 p h) (sat_cons (step2110 p h) (sat_cons (step1571 p h) (sat_cons (step8479 p h) (sat_nil p))))))))))
def c8640 : List Lit := [(1088, false), (112, true), (89, false), (76, true), (1136, true), (1159, true), (1124, false), (73, false), (88, true)]
theorem step8640 (p : Nat → Bool) (h : Constraints p) : clause p c8640 = true :=
  Snake9.LocalRup.prove_clause [c8056, c1724, c6449, c3003, c1713, c1772, c1773, c1804, c4981, c2811, c6646, c1737, c1738, c4330, c4829, c5688, c1726, c1593, c937, c1601, c1584, c1622, c1589] c8640 (by decide) p (sat_cons (step8056 p h) (sat_cons (step1724 p h) (sat_cons (step6449 p h) (sat_cons (step3003 p h) (sat_cons (step1713 p h) (sat_cons (step1772 p h) (sat_cons (step1773 p h) (sat_cons (step1804 p h) (sat_cons (step4981 p h) (sat_cons (step2811 p h) (sat_cons (step6646 p h) (sat_cons (step1737 p h) (sat_cons (step1738 p h) (sat_cons (step4330 p h) (sat_cons (step4829 p h) (sat_cons (step5688 p h) (sat_cons (step1726 p h) (sat_cons (step1593 p h) (sat_cons (step937 p h) (sat_cons (step1601 p h) (sat_cons (step1584 p h) (sat_cons (step1622 p h) (sat_cons (step1589 p h) (sat_nil p))))))))))))))))))))))))
def c8641 : List Lit := [(89, false), (76, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8641 (p : Nat → Bool) (h : Constraints p) : clause p c8641 = true :=
  Snake9.LocalRup.prove_clause [c8633, c2427, c8474, c8637, c2969, c1767, c1809, c6642, c6639, c1798, c8409, c6449, c8638, c8639, c8640, c1686, c1677, c2110, c1599, c8252, c1627, c7232, c8578] c8641 (by decide) p (sat_cons (step8633 p h) (sat_cons (step2427 p h) (sat_cons (step8474 p h) (sat_cons (step8637 p h) (sat_cons (step2969 p h) (sat_cons (step1767 p h) (sat_cons (step1809 p h) (sat_cons (step6642 p h) (sat_cons (step6639 p h) (sat_cons (step1798 p h) (sat_cons (step8409 p h) (sat_cons (step6449 p h) (sat_cons (step8638 p h) (sat_cons (step8639 p h) (sat_cons (step8640 p h) (sat_cons (step1686 p h) (sat_cons (step1677 p h) (sat_cons (step2110 p h) (sat_cons (step1599 p h) (sat_cons (step8252 p h) (sat_cons (step1627 p h) (sat_cons (step7232 p h) (sat_cons (step8578 p h) (sat_nil p))))))))))))))))))))))))
def c8642 : List Lit := [(76, true), (73, false), (88, true), (79, true), (1061, false)]
theorem step8642 (p : Nat → Bool) (h : Constraints p) : clause p c8642 = true :=
  Snake9.LocalRup.prove_clause [c8056, c8633, c2427, c8474, c8143, c1588, c8637, c1676, c1683, c8641, c6649, c6648, c1686, c2110, c1677] c8642 (by decide) p (sat_cons (step8056 p h) (sat_cons (step8633 p h) (sat_cons (step2427 p h) (sat_cons (step8474 p h) (sat_cons (step8143 p h) (sat_cons (step1588 p h) (sat_cons (step8637 p h) (sat_cons (step1676 p h) (sat_cons (step1683 p h) (sat_cons (step8641 p h) (sat_cons (step6649 p h) (sat_cons (step6648 p h) (sat_cons (step1686 p h) (sat_cons (step2110 p h) (sat_cons (step1677 p h) (sat_nil p))))))))))))))))
def c8643 : List Lit := [(73, false), (88, true), (79, true), (1061, false)]
theorem step8643 (p : Nat → Bool) (h : Constraints p) : clause p c8643 = true :=
  Snake9.LocalRup.prove_clause [c8056, c3003, c8143, c1588, c8474, c8633, c2427, c8642, c8284, c8266, c8263, c1550] c8643 (by decide) p (sat_cons (step8056 p h) (sat_cons (step3003 p h) (sat_cons (step8143 p h) (sat_cons (step1588 p h) (sat_cons (step8474 p h) (sat_cons (step8633 p h) (sat_cons (step2427 p h) (sat_cons (step8642 p h) (sat_cons (step8284 p h) (sat_cons (step8266 p h) (sat_cons (step8263 p h) (sat_cons (step1550 p h) (sat_nil p)))))))))))))
def c8644 : List Lit := [(931, false), (15, false), (5, true), (47, true), (40, true), (885, false), (919, false), (944, false), (30, true), (94, false), (23, true), (1005, true), (4, true), (121, false)]
theorem step8644 (p : Nat → Bool) (h : Constraints p) : clause p c8644 = true :=
  Snake9.LocalRup.prove_clause [c1523, c1396, c4368, c8496, c2538, c1422, c1375, c8595, c1391, c2492, c1492, c1312, c2070, c6539, c1448, c1439] c8644 (by decide) p (sat_cons (step1523 p h) (sat_cons (step1396 p h) (sat_cons (step4368 p h) (sat_cons (step8496 p h) (sat_cons (step2538 p h) (sat_cons (step1422 p h) (sat_cons (step1375 p h) (sat_cons (step8595 p h) (sat_cons (step1391 p h) (sat_cons (step2492 p h) (sat_cons (step1492 p h) (sat_cons (step1312 p h) (sat_cons (step2070 p h) (sat_cons (step6539 p h) (sat_cons (step1448 p h) (sat_cons (step1439 p h) (sat_nil p)))))))))))))))))
def c8645 : List Lit := [(931, true), (5, true), (921, true), (901, false), (94, false), (45, true), (23, true), (1005, true), (4, true), (89, false), (76, true), (88, true)]
theorem step8645 (p : Nat → Bool) (h : Constraints p) : clause p c8645 = true :=
  Snake9.LocalRup.prove_clause [c8506, c8528] c8645 (by decide) p (sat_cons (step8506 p h) (sat_cons (step8528 p h) (sat_nil p)))
def c8646 : List Lit := [(5, true), (47, true), (40, true), (877, false), (944, false), (30, true), (94, false), (45, true), (23, true), (1005, true), (4, true), (121, false), (89, false), (76, true), (88, true)]
theorem step8646 (p : Nat → Bool) (h : Constraints p) : clause p c8646 = true :=
  Snake9.LocalRup.prove_clause [c5935, c1523, c2644, c3063, c1533, c7663, c1330, c8645, c4368, c8496, c8644, c5543, c1375, c8595, c6300, c5159] c8646 (by decide) p (sat_cons (step5935 p h) (sat_cons (step1523 p h) (sat_cons (step2644 p h) (sat_cons (step3063 p h) (sat_cons (step1533 p h) (sat_cons (step7663 p h) (sat_cons (step1330 p h) (sat_cons (step8645 p h) (sat_cons (step4368 p h) (sat_cons (step8496 p h) (sat_cons (step8644 p h) (sat_cons (step5543 p h) (sat_cons (step1375 p h) (sat_cons (step8595 p h) (sat_cons (step6300 p h) (sat_cons (step5159 p h) (sat_nil p)))))))))))))))))
def c8647 : List Lit := [(1073, true), (1039, false)]
theorem step8647 (p : Nat → Bool) (h : Constraints p) : clause p c8647 = true :=
  Snake9.LocalRup.prove_clause [c8058, c1650] c8647 (by decide) p (sat_cons (step8058 p h) (sat_cons (step1650 p h) (sat_nil p)))
def c8648 : List Lit := [(1104, false), (1124, false)]
theorem step8648 (p : Nat → Bool) (h : Constraints p) : clause p c8648 = true :=
  Snake9.LocalRup.prove_clause [c8060, c1785] c8648 (by decide) p (sat_cons (step8060 p h) (sat_cons (step1785 p h) (sat_nil p)))
def c8649 : List Lit := [(1101, false), (114, true), (1055, false), (90, false), (1025, false), (1107, false), (73, true), (1029, false), (1061, false)]
theorem step8649 (p : Nat → Bool) (h : Constraints p) : clause p c8649 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5308] c8649 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5308 p h) (sat_nil p)))
def c8650 : List Lit := [(1137, false), (1159, true)]
theorem step8650 (p : Nat → Bool) (h : Constraints p) : clause p c8650 = true :=
  Snake9.LocalRup.prove_clause [c8059, c1793] c8650 (by decide) p (sat_cons (step8059 p h) (sat_cons (step1793 p h) (sat_nil p)))
def c8651 : List Lit := [(1048, true), (1045, false)]
theorem step8651 (p : Nat → Bool) (h : Constraints p) : clause p c8651 = true :=
  Snake9.LocalRup.prove_clause [c8056, c1588] c8651 (by decide) p (sat_cons (step8056 p h) (sat_cons (step1588 p h) (sat_nil p)))
def c8652 : List Lit := [(88, false), (123, false), (86, true), (1062, true), (89, true)]
theorem step8652 (p : Nat → Bool) (h : Constraints p) : clause p c8652 = true :=
  Snake9.LocalRup.prove_clause [c8056, c2157] c8652 (by decide) p (sat_cons (step8056 p h) (sat_cons (step2157 p h) (sat_nil p)))
def c8653 : List Lit := [(1049, true), (1046, false)]
theorem step8653 (p : Nat → Bool) (h : Constraints p) : clause p c8653 = true :=
  Snake9.LocalRup.prove_clause [c8056, c1589] c8653 (by decide) p (sat_cons (step8056 p h) (sat_cons (step1589 p h) (sat_nil p)))
def c8654 : List Lit := [(1057, false), (1062, true)]
theorem step8654 (p : Nat → Bool) (h : Constraints p) : clause p c8654 = true :=
  Snake9.LocalRup.prove_clause [c8057, c1614] c8654 (by decide) p (sat_cons (step8057 p h) (sat_cons (step1614 p h) (sat_nil p)))
def c8655 : List Lit := [(1058, false), (1063, true)]
theorem step8655 (p : Nat → Bool) (h : Constraints p) : clause p c8655 = true :=
  Snake9.LocalRup.prove_clause [c8057, c1615] c8655 (by decide) p (sat_cons (step8057 p h) (sat_cons (step1615 p h) (sat_nil p)))
def c8656 : List Lit := [(921, false), (983, false)]
theorem step8656 (p : Nat → Bool) (h : Constraints p) : clause p c8656 = true :=
  Snake9.LocalRup.prove_clause [c6907, c1534] c8656 (by decide) p (sat_cons (step6907 p h) (sat_cons (step1534 p h) (sat_nil p)))
def c8657 : List Lit := [(1041, false), (1075, true)]
theorem step8657 (p : Nat → Bool) (h : Constraints p) : clause p c8657 = true :=
  Snake9.LocalRup.prove_clause [c8058, c1665] c8657 (by decide) p (sat_cons (step8058 p h) (sat_cons (step1665 p h) (sat_nil p)))
def c8658 : List Lit := [(920, false), (984, false)]
theorem step8658 (p : Nat → Bool) (h : Constraints p) : clause p c8658 = true :=
  Snake9.LocalRup.prove_clause [c6907, c1529] c8658 (by decide) p (sat_cons (step6907 p h) (sat_cons (step1529 p h) (sat_nil p)))
def c8659 : List Lit := [(1042, false), (1076, true)]
theorem step8659 (p : Nat → Bool) (h : Constraints p) : clause p c8659 = true :=
  Snake9.LocalRup.prove_clause [c8058, c1671] c8659 (by decide) p (sat_cons (step8058 p h) (sat_cons (step1671 p h) (sat_nil p)))
def c8660 : List Lit := [(90, false), (73, true), (1029, false), (1061, false), (1055, false), (1076, true), (1026, false), (88, false)]
theorem step8660 (p : Nat → Bool) (h : Constraints p) : clause p c8660 = true :=
  Snake9.LocalRup.prove_clause [c8056, c2827] c8660 (by decide) p (sat_cons (step8056 p h) (sat_cons (step2827 p h) (sat_nil p)))
def c8661 : List Lit := [(974, false), (950, false)]
theorem step8661 (p : Nat → Bool) (h : Constraints p) : clause p c8661 = true :=
  Snake9.LocalRup.prove_clause [c6908, c1498] c8661 (by decide) p (sat_cons (step6908 p h) (sat_cons (step1498 p h) (sat_nil p)))
def c8662 : List Lit := [(1074, true), (1040, false)]
theorem step8662 (p : Nat → Bool) (h : Constraints p) : clause p c8662 = true :=
  Snake9.LocalRup.prove_clause [c8058, c1658] c8662 (by decide) p (sat_cons (step8058 p h) (sat_cons (step1658 p h) (sat_nil p)))
def c8663 : List Lit := [(1056, false), (1061, true)]
theorem step8663 (p : Nat → Bool) (h : Constraints p) : clause p c8663 = true :=
  Snake9.LocalRup.prove_clause [c8057, c1613] c8663 (by decide) p (sat_cons (step8057 p h) (sat_cons (step1613 p h) (sat_nil p)))
def c8664 : List Lit := [(951, false), (973, false)]
theorem step8664 (p : Nat → Bool) (h : Constraints p) : clause p c8664 = true :=
  Snake9.LocalRup.prove_clause [c6908, c1502] c8664 (by decide) p (sat_cons (step6908 p h) (sat_cons (step1502 p h) (sat_nil p)))
def c8665 : List Lit := [(17, false), (89, true), (88, false), (86, true), (1063, true), (123, false)]
theorem step8665 (p : Nat → Bool) (h : Constraints p) : clause p c8665 = true :=
  Snake9.LocalRup.prove_clause [c8056, c2156] c8665 (by decide) p (sat_cons (step8056 p h) (sat_cons (step2156 p h) (sat_nil p)))
def c8666 : List Lit := [(85, false), (1053, false), (90, true), (86, true), (73, false), (1063, true)]
theorem step8666 (p : Nat → Bool) (h : Constraints p) : clause p c8666 = true :=
  Snake9.LocalRup.prove_clause [c8056, c2106] c8666 (by decide) p (sat_cons (step8056 p h) (sat_cons (step2106 p h) (sat_nil p)))
def c8667 : List Lit := [(85, false), (1053, false), (73, false), (1025, false), (77, true), (1075, true), (86, true)]
theorem step8667 (p : Nat → Bool) (h : Constraints p) : clause p c8667 = true :=
  Snake9.LocalRup.prove_clause [c8056, c2108] c8667 (by decide) p (sat_cons (step8056 p h) (sat_cons (step2108 p h) (sat_nil p)))
def c8668 : List Lit := [(85, false), (1053, false), (73, false), (77, true), (1075, true), (1025, false), (1039, true)]
theorem step8668 (p : Nat → Bool) (h : Constraints p) : clause p c8668 = true :=
  Snake9.LocalRup.prove_clause [c8056, c2111] c8668 (by decide) p (sat_cons (step8056 p h) (sat_cons (step2111 p h) (sat_nil p)))
def c8669 : List Lit := [(1103, false), (1125, false)]
theorem step8669 (p : Nat → Bool) (h : Constraints p) : clause p c8669 = true :=
  Snake9.LocalRup.prove_clause [c8060, c1782] c8669 (by decide) p (sat_cons (step8060 p h) (sat_cons (step1782 p h) (sat_nil p)))
def c8670 : List Lit := [(922, false), (982, false)]
theorem step8670 (p : Nat → Bool) (h : Constraints p) : clause p c8670 = true :=
  Snake9.LocalRup.prove_clause [c6907, c1537] c8670 (by decide) p (sat_cons (step6907 p h) (sat_cons (step1537 p h) (sat_nil p)))
def c8671 : List Lit := [(923, false), (981, false)]
theorem step8671 (p : Nat → Bool) (h : Constraints p) : clause p c8671 = true :=
  Snake9.LocalRup.prove_clause [c6907, c1539] c8671 (by decide) p (sat_cons (step6907 p h) (sat_cons (step1539 p h) (sat_nil p)))
def c8672 : List Lit := [(1061, true), (1053, false)]
theorem step8672 (p : Nat → Bool) (h : Constraints p) : clause p c8672 = true :=
  Snake9.LocalRup.prove_clause [c8056, c2978] c8672 (by decide) p (sat_cons (step8056 p h) (sat_cons (step2978 p h) (sat_nil p)))
def c8673 : List Lit := [(73, true), (88, false), (1029, false), (1053, false), (1048, false), (1075, true), (1025, false)]
theorem step8673 (p : Nat → Bool) (h : Constraints p) : clause p c8673 = true :=
  Snake9.LocalRup.prove_clause [c8056, c3228] c8673 (by decide) p (sat_cons (step8056 p h) (sat_cons (step3228 p h) (sat_nil p)))
def c8674 : List Lit := [(1062, true), (1032, true), (1053, false), (89, true)]
theorem step8674 (p : Nat → Bool) (h : Constraints p) : clause p c8674 = true :=
  Snake9.LocalRup.prove_clause [c8056, c2970] c8674 (by decide) p (sat_cons (step8056 p h) (sat_cons (step2970 p h) (sat_nil p)))
def c8675 : List Lit := [(1040, false), (1053, false), (1124, false), (89, true), (1087, false), (88, true)]
theorem step8675 (p : Nat → Bool) (h : Constraints p) : clause p c8675 = true :=
  Snake9.LocalRup.prove_clause [c8056, c5328] c8675 (by decide) p (sat_cons (step8056 p h) (sat_cons (step5328 p h) (sat_nil p)))
def c8676 : List Lit := [(40, false), (23, false), (4, false)]
theorem step8676 (p : Nat → Bool) (h : Constraints p) : clause p c8676 = true :=
  Snake9.LocalRup.prove_clause [c6907, c2964] c8676 (by decide) p (sat_cons (step6907 p h) (sat_cons (step2964 p h) (sat_nil p)))
def c8677 : List Lit := [(90, false), (1039, false), (88, true), (1124, false), (1159, true), (89, true), (1045, false)]
theorem step8677 (p : Nat → Bool) (h : Constraints p) : clause p c8677 = true :=
  Snake9.LocalRup.prove_clause [c8056, c3591] c8677 (by decide) p (sat_cons (step8056 p h) (sat_cons (step3591 p h) (sat_nil p)))
def c8678 : List Lit := [(17, false), (88, false), (1061, true), (86, true)]
theorem step8678 (p : Nat → Bool) (h : Constraints p) : clause p c8678 = true :=
  Snake9.LocalRup.prove_clause [c8056, c3021] c8678 (by decide) p (sat_cons (step8056 p h) (sat_cons (step3021 p h) (sat_nil p)))
def c8679 : List Lit := [(97, true), (1084, false), (77, true), (1095, false), (1025, false), (1027, false), (1124, false), (1053, true)]
theorem step8679 (p : Nat → Bool) (h : Constraints p) : clause p c8679 = true :=
  Snake9.LocalRup.prove_clause [c8058, c5338] c8679 (by decide) p (sat_cons (step8058 p h) (sat_cons (step5338 p h) (sat_nil p)))
def c8680 : List Lit := [(1049, true), (86, true), (82, true), (73, false), (79, false)]
theorem step8680 (p : Nat → Bool) (h : Constraints p) : clause p c8680 = true :=
  Snake9.LocalRup.prove_clause [c8056, c3815] c8680 (by decide) p (sat_cons (step8056 p h) (sat_cons (step3815 p h) (sat_nil p)))
end B112E057
