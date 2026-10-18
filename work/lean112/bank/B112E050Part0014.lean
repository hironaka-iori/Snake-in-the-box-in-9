import B112E050Part0013
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2712 : List Lit := [(1744, false), (1707, false), (1751, true), (1763, true), (1734, false), (72, true), (1718, false), (1721, false), (1736, false)]
theorem step2712 (p : Nat → Bool) (h : Constraints p) : clause p c2712 = true :=
  Snake9.LocalRup.prove_clause [c1377, c1458, c1463, c1508, c1429, c1409, c1405, c1378, c1396, c1373, c1385, c1955] c2712 (by decide) p (sat_cons (step1377 p h) (sat_cons (step1458 p h) (sat_cons (step1463 p h) (sat_cons (step1508 p h) (sat_cons (step1429 p h) (sat_cons (step1409 p h) (sat_cons (step1405 p h) (sat_cons (step1378 p h) (sat_cons (step1396 p h) (sat_cons (step1373 p h) (sat_cons (step1385 p h) (sat_cons (step1955 p h) (sat_nil p)))))))))))))
def c2713 : List Lit := [(90, false), (102, false), (27, true), (94, false), (91, false), (1774, true), (30, false), (24, false), (218, true), (88, true), (87, true), (17, false)]
theorem step2713 (p : Nat → Bool) (h : Constraints p) : clause p c2713 = true :=
  Snake9.LocalRup.prove_clause [c1795, c437, c526, c532, c1523, c2043, c589, c1931] c2713 (by decide) p (sat_cons (step1795 p h) (sat_cons (step437 p h) (sat_cons (step526 p h) (sat_cons (step532 p h) (sat_cons (step1523 p h) (sat_cons (step2043 p h) (sat_cons (step589 p h) (sat_cons (step1931 p h) (sat_nil p)))))))))
def c2714 : List Lit := [(102, false), (1790, true), (1829, true), (123, false), (1811, true), (1783, false), (96, true)]
theorem step2714 (p : Nat → Bool) (h : Constraints p) : clause p c2714 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1561, c1528, c2263, c2662, c1527, c1530, c1536, c1556, c1557, c1520, c1641, c1539, c1541, c1537, c1532, c2001, c2272, c1587, c2558] c2714 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1561 p h) (sat_cons (step1528 p h) (sat_cons (step2263 p h) (sat_cons (step2662 p h) (sat_cons (step1527 p h) (sat_cons (step1530 p h) (sat_cons (step1536 p h) (sat_cons (step1556 p h) (sat_cons (step1557 p h) (sat_cons (step1520 p h) (sat_cons (step1641 p h) (sat_cons (step1539 p h) (sat_cons (step1541 p h) (sat_cons (step1537 p h) (sat_cons (step1532 p h) (sat_cons (step2001 p h) (sat_cons (step2272 p h) (sat_cons (step1587 p h) (sat_cons (step2558 p h) (sat_nil p)))))))))))))))))))))
def c2715 : List Lit := [(1647, true), (56, false), (46, true), (93, true)]
theorem step2715 (p : Nat → Bool) (h : Constraints p) : clause p c2715 = true :=
  Snake9.LocalRup.prove_clause [c1233, c1243, c1241, c1234, c1235, c1236, c1985, c200] c2715 (by decide) p (sat_cons (step1233 p h) (sat_cons (step1243 p h) (sat_cons (step1241 p h) (sat_cons (step1234 p h) (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step1985 p h) (sat_cons (step200 p h) (sat_nil p)))))))))
def c2716 : List Lit := [(91, false), (102, true), (123, false), (1783, false), (1830, true), (89, true), (96, true), (1810, false)]
theorem step2716 (p : Nat → Bool) (h : Constraints p) : clause p c2716 = true :=
  Snake9.LocalRup.prove_clause [c2697, c2119, c1556, c752, c749, c751, c1642, c1573, c1572, c1617, c1582] c2716 (by decide) p (sat_cons (step2697 p h) (sat_cons (step2119 p h) (sat_cons (step1556 p h) (sat_cons (step752 p h) (sat_cons (step749 p h) (sat_cons (step751 p h) (sat_cons (step1642 p h) (sat_cons (step1573 p h) (sat_cons (step1572 p h) (sat_cons (step1617 p h) (sat_cons (step1582 p h) (sat_nil p))))))))))))
def c2717 : List Lit := [(1637, true), (1618, false), (1628, false), (36, true), (1630, false), (44, false), (7, false)]
theorem step2717 (p : Nat → Bool) (h : Constraints p) : clause p c2717 = true :=
  Snake9.LocalRup.prove_clause [c1189, c1195, c1227, c1224, c1196, c1209, c1191, c1200, c139] c2717 (by decide) p (sat_cons (step1189 p h) (sat_cons (step1195 p h) (sat_cons (step1227 p h) (sat_cons (step1224 p h) (sat_cons (step1196 p h) (sat_cons (step1209 p h) (sat_cons (step1191 p h) (sat_cons (step1200 p h) (sat_cons (step139 p h) (sat_nil p))))))))))
def c2718 : List Lit := [(1636, true), (1628, false), (36, true), (1630, false), (44, false), (7, false)]
theorem step2718 (p : Nat → Bool) (h : Constraints p) : clause p c2718 = true :=
  Snake9.LocalRup.prove_clause [c1189, c1192, c1220, c1223, c1209, c1193, c1200, c1191, c139] c2718 (by decide) p (sat_cons (step1189 p h) (sat_cons (step1192 p h) (sat_cons (step1220 p h) (sat_cons (step1223 p h) (sat_cons (step1209 p h) (sat_cons (step1193 p h) (sat_cons (step1200 p h) (sat_cons (step1191 p h) (sat_cons (step139 p h) (sat_nil p))))))))))
def c2719 : List Lit := [(60, false), (1646, true), (68, false), (62, false)]
theorem step2719 (p : Nat → Bool) (h : Constraints p) : clause p c2719 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1236, c1240, c1232, c1235, c167, c221, c170, c2061] c2719 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1236 p h) (sat_cons (step1240 p h) (sat_cons (step1232 p h) (sat_cons (step1235 p h) (sat_cons (step167 p h) (sat_cons (step221 p h) (sat_cons (step170 p h) (sat_cons (step2061 p h) (sat_nil p))))))))))
def c2720 : List Lit := [(1652, false), (46, true), (1655, true), (1660, true), (93, true)]
theorem step2720 (p : Nat → Bool) (h : Constraints p) : clause p c2720 = true :=
  Snake9.LocalRup.prove_clause [c1252, c1255, c1270, c1247, c2715] c2720 (by decide) p (sat_cons (step1252 p h) (sat_cons (step1255 p h) (sat_cons (step1270 p h) (sat_cons (step1247 p h) (sat_cons (step2715 p h) (sat_nil p))))))
def c2721 : List Lit := [(1776, true), (30, false), (102, false), (88, false), (96, true)]
theorem step2721 (p : Nat → Bool) (h : Constraints p) : clause p c2721 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1529, c1527, c1520, c1521, c1522, c434, c1807, c646, c2135] c2721 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1529 p h) (sat_cons (step1527 p h) (sat_cons (step1520 p h) (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step434 p h) (sat_cons (step1807 p h) (sat_cons (step646 p h) (sat_cons (step2135 p h) (sat_nil p)))))))))))
def c2722 : List Lit := [(43, false), (36, true), (1637, true), (1618, false), (44, false), (7, false)]
theorem step2722 (p : Nat → Bool) (h : Constraints p) : clause p c2722 = true :=
  Snake9.LocalRup.prove_clause [c140, c142, c1191, c1200, c1196, c1208, c1227] c2722 (by decide) p (sat_cons (step140 p h) (sat_cons (step142 p h) (sat_cons (step1191 p h) (sat_cons (step1200 p h) (sat_cons (step1196 p h) (sat_cons (step1208 p h) (sat_cons (step1227 p h) (sat_nil p))))))))
def c2723 : List Lit := [(36, true), (1637, true), (7, false), (1618, false), (44, false)]
theorem step2723 (p : Nat → Bool) (h : Constraints p) : clause p c2723 = true :=
  Snake9.LocalRup.prove_clause [c2722, c1204, c1206, c2717] c2723 (by decide) p (sat_cons (step2722 p h) (sat_cons (step1204 p h) (sat_cons (step1206 p h) (sat_cons (step2717 p h) (sat_nil p)))))
def c2724 : List Lit := [(1660, true), (46, true), (1652, false), (93, true)]
theorem step2724 (p : Nat → Bool) (h : Constraints p) : clause p c2724 = true :=
  Snake9.LocalRup.prove_clause [c1233, c1240, c2720, c1266] c2724 (by decide) p (sat_cons (step1233 p h) (sat_cons (step1240 p h) (sat_cons (step2720 p h) (sat_cons (step1266 p h) (sat_nil p)))))
def c2725 : List Lit := [(43, false), (109, false), (1636, true), (39, false), (44, false), (7, false)]
theorem step2725 (p : Nat → Bool) (h : Constraints p) : clause p c2725 = true :=
  Snake9.LocalRup.prove_clause [c140, c142, c2355, c1200, c1223, c1208] c2725 (by decide) p (sat_cons (step140 p h) (sat_cons (step142 p h) (sat_cons (step2355 p h) (sat_cons (step1200 p h) (sat_cons (step1223 p h) (sat_cons (step1208 p h) (sat_nil p)))))))
def c2726 : List Lit := [(109, false), (1631, true), (1636, true), (39, false), (44, false), (7, false)]
theorem step2726 (p : Nat → Bool) (h : Constraints p) : clause p c2726 = true :=
  Snake9.LocalRup.prove_clause [c2725, c1204, c1206, c1209, c1223, c1200, c2355, c139] c2726 (by decide) p (sat_cons (step2725 p h) (sat_cons (step1204 p h) (sat_cons (step1206 p h) (sat_cons (step1209 p h) (sat_cons (step1223 p h) (sat_cons (step1200 p h) (sat_cons (step2355 p h) (sat_cons (step139 p h) (sat_nil p)))))))))
def c2727 : List Lit := [(63, false), (1707, true), (81, true)]
theorem step2727 (p : Nat → Bool) (h : Constraints p) : clause p c2727 = true :=
  Snake9.LocalRup.prove_clause [c1370, c1369, c2083, c238] c2727 (by decide) p (sat_cons (step1370 p h) (sat_cons (step1369 p h) (sat_cons (step2083 p h) (sat_cons (step238 p h) (sat_nil p)))))
def c2728 : List Lit := [(1776, true), (66, false), (102, false), (88, false), (96, true)]
theorem step2728 (p : Nat → Bool) (h : Constraints p) : clause p c2728 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1529, c1527, c1520, c1521, c1522, c434, c1807, c656, c2135] c2728 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1529 p h) (sat_cons (step1527 p h) (sat_cons (step1520 p h) (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step434 p h) (sat_cons (step1807 p h) (sat_cons (step656 p h) (sat_cons (step2135 p h) (sat_nil p)))))))))))
def c2729 : List Lit := [(91, false), (102, true), (1777, true), (88, false), (89, true), (96, true)]
theorem step2729 (p : Nat → Bool) (h : Constraints p) : clause p c2729 = true :=
  Snake9.LocalRup.prove_clause [c2121, c433, c432, c1521, c1520, c1530] c2729 (by decide) p (sat_cons (step2121 p h) (sat_cons (step433 p h) (sat_cons (step432 p h) (sat_cons (step1521 p h) (sat_cons (step1520 p h) (sat_cons (step1530 p h) (sat_nil p)))))))
def c2730 : List Lit := [(1776, true), (102, true), (88, false), (96, true)]
theorem step2730 (p : Nat → Bool) (h : Constraints p) : clause p c2730 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1529, c1527, c1520, c1521, c1522, c434, c543, c2136] c2730 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1529 p h) (sat_cons (step1527 p h) (sat_cons (step1520 p h) (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step434 p h) (sat_cons (step543 p h) (sat_cons (step2136 p h) (sat_nil p))))))))))
def c2731 : List Lit := [(1829, true), (125, false), (1788, false), (1783, true), (1817, false), (93, true)]
theorem step2731 (p : Nat → Bool) (h : Constraints p) : clause p c2731 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1536, c1540, c2623, c1532, c1635, c1641, c2235, c1560, c2278, c2297] c2731 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1536 p h) (sat_cons (step1540 p h) (sat_cons (step2623 p h) (sat_cons (step1532 p h) (sat_cons (step1635 p h) (sat_cons (step1641 p h) (sat_cons (step2235 p h) (sat_cons (step1560 p h) (sat_cons (step2278 p h) (sat_cons (step2297 p h) (sat_nil p))))))))))))
def c2732 : List Lit := [(1776, true), (66, false), (96, true), (88, false)]
theorem step2732 (p : Nat → Bool) (h : Constraints p) : clause p c2732 = true :=
  Snake9.LocalRup.prove_clause [c2728, c2730] c2732 (by decide) p (sat_cons (step2728 p h) (sat_cons (step2730 p h) (sat_nil p)))
def c2733 : List Lit := [(1776, true), (30, false), (88, false), (96, true)]
theorem step2733 (p : Nat → Bool) (h : Constraints p) : clause p c2733 = true :=
  Snake9.LocalRup.prove_clause [c2730, c2721] c2733 (by decide) p (sat_cons (step2730 p h) (sat_cons (step2721 p h) (sat_nil p)))
def c2734 : List Lit := [(46, false), (123, true), (1800, true), (1812, true), (1780, true), (1776, false), (37, true), (1830, true)]
theorem step2734 (p : Nat → Bool) (h : Constraints p) : clause p c2734 = true :=
  Snake9.LocalRup.prove_clause [c2058, c2278, c1935, c1532, c1534, c2374, c2515, c640, c2173, c2373, c1603, c2375, c1586, c1587, c822] c2734 (by decide) p (sat_cons (step2058 p h) (sat_cons (step2278 p h) (sat_cons (step1935 p h) (sat_cons (step1532 p h) (sat_cons (step1534 p h) (sat_cons (step2374 p h) (sat_cons (step2515 p h) (sat_cons (step640 p h) (sat_cons (step2173 p h) (sat_cons (step2373 p h) (sat_cons (step1603 p h) (sat_cons (step2375 p h) (sat_cons (step1586 p h) (sat_cons (step1587 p h) (sat_cons (step822 p h) (sat_nil p))))))))))))))))
def c2735 : List Lit := [(102, false), (91, false), (27, false), (1774, true)]
theorem step2735 (p : Nat → Bool) (h : Constraints p) : clause p c2735 = true :=
  Snake9.LocalRup.prove_clause [c569, c568, c1523] c2735 (by decide) p (sat_cons (step569 p h) (sat_cons (step568 p h) (sat_cons (step1523 p h) (sat_nil p))))
def c2736 : List Lit := [(102, false), (1784, true), (1777, true), (1817, true), (123, false), (1811, true), (96, true)]
theorem step2736 (p : Nat → Bool) (h : Constraints p) : clause p c2736 = true :=
  Snake9.LocalRup.prove_clause [c1539, c1519, c1528, c2662, c2263, c1536, c1537, c1530, c1541, c1520, c1532, c2001, c2272, c1587, c2558] c2736 (by decide) p (sat_cons (step1539 p h) (sat_cons (step1519 p h) (sat_cons (step1528 p h) (sat_cons (step2662 p h) (sat_cons (step2263 p h) (sat_cons (step1536 p h) (sat_cons (step1537 p h) (sat_cons (step1530 p h) (sat_cons (step1541 p h) (sat_cons (step1520 p h) (sat_cons (step1532 p h) (sat_cons (step2001 p h) (sat_cons (step2272 p h) (sat_cons (step1587 p h) (sat_cons (step2558 p h) (sat_nil p))))))))))))))))
def c2737 : List Lit := [(91, false), (102, false), (114, true), (1778, true), (123, false), (88, false), (89, true), (96, true)]
theorem step2737 (p : Nat → Bool) (h : Constraints p) : clause p c2737 = true :=
  Snake9.LocalRup.prove_clause [c590, c592, c2120, c1523, c432, c1531, c1520] c2737 (by decide) p (sat_cons (step590 p h) (sat_cons (step592 p h) (sat_cons (step2120 p h) (sat_cons (step1523 p h) (sat_cons (step432 p h) (sat_cons (step1531 p h) (sat_cons (step1520 p h) (sat_nil p))))))))
def c2738 : List Lit := [(123, true), (109, false), (1800, true), (1812, true), (104, false), (97, false), (93, true)]
theorem step2738 (p : Nat → Bool) (h : Constraints p) : clause p c2738 = true :=
  Snake9.LocalRup.prove_clause [c2278, c1975, c1587, c1588, c670, c2179, c2332, c782] c2738 (by decide) p (sat_cons (step2278 p h) (sat_cons (step1975 p h) (sat_cons (step1587 p h) (sat_cons (step1588 p h) (sat_cons (step670 p h) (sat_cons (step2179 p h) (sat_cons (step2332 p h) (sat_cons (step782 p h) (sat_nil p)))))))))
def c2739 : List Lit := [(102, false), (1783, false), (1811, false), (62, false), (1830, true), (96, true), (93, true)]
theorem step2739 (p : Nat → Bool) (h : Constraints p) : clause p c2739 = true :=
  Snake9.LocalRup.prove_clause [c1519, c2234, c1648, c1561, c1528, c1947, c2680, c1527, c1530, c1536, c1556, c1557, c1520, c1541, c1642, c1539, c1532, c2235, c1613, c1537, c2738, c586, c584, c1523] c2739 (by decide) p (sat_cons (step1519 p h) (sat_cons (step2234 p h) (sat_cons (step1648 p h) (sat_cons (step1561 p h) (sat_cons (step1528 p h) (sat_cons (step1947 p h) (sat_cons (step2680 p h) (sat_cons (step1527 p h) (sat_cons (step1530 p h) (sat_cons (step1536 p h) (sat_cons (step1556 p h) (sat_cons (step1557 p h) (sat_cons (step1520 p h) (sat_cons (step1541 p h) (sat_cons (step1642 p h) (sat_cons (step1539 p h) (sat_cons (step1532 p h) (sat_cons (step2235 p h) (sat_cons (step1613 p h) (sat_cons (step1537 p h) (sat_cons (step2738 p h) (sat_cons (step586 p h) (sat_cons (step584 p h) (sat_cons (step1523 p h) (sat_nil p)))))))))))))))))))))))))
def c2740 : List Lit := [(104, false), (109, false), (30, false), (39, false), (123, true), (1800, true), (1812, true), (93, true)]
theorem step2740 (p : Nat → Bool) (h : Constraints p) : clause p c2740 = true :=
  Snake9.LocalRup.prove_clause [c2278, c1975, c1587, c1588, c654, c2179, c2332, c781] c2740 (by decide) p (sat_cons (step2278 p h) (sat_cons (step1975 p h) (sat_cons (step1587 p h) (sat_cons (step1588 p h) (sat_cons (step654 p h) (sat_cons (step2179 p h) (sat_cons (step2332 p h) (sat_cons (step781 p h) (sat_nil p)))))))))
def c2741 : List Lit := [(31, false), (108, false), (103, false), (67, false), (93, true)]
theorem step2741 (p : Nat → Bool) (h : Constraints p) : clause p c2741 = true :=
  Snake9.LocalRup.prove_clause [c677, c676, c2138] c2741 (by decide) p (sat_cons (step677 p h) (sat_cons (step676 p h) (sat_cons (step2138 p h) (sat_nil p))))
def c2742 : List Lit := [(97, false), (31, true), (108, false), (30, false), (39, false)]
theorem step2742 (p : Nat → Bool) (h : Constraints p) : clause p c2742 = true :=
  Snake9.LocalRup.prove_clause [c648, c62, c2043] c2742 (by decide) p (sat_cons (step648 p h) (sat_cons (step62 p h) (sat_cons (step2043 p h) (sat_nil p))))
def c2743 : List Lit := [(1777, true), (104, false), (108, false), (100, true), (62, false), (88, false), (96, true)]
theorem step2743 (p : Nat → Bool) (h : Constraints p) : clause p c2743 = true :=
  Snake9.LocalRup.prove_clause [c1522, c1519, c1528, c1530, c1523, c2680, c1520, c434, c666, c2134] c2743 (by decide) p (sat_cons (step1522 p h) (sat_cons (step1519 p h) (sat_cons (step1528 p h) (sat_cons (step1530 p h) (sat_cons (step1523 p h) (sat_cons (step2680 p h) (sat_cons (step1520 p h) (sat_cons (step434 p h) (sat_cons (step666 p h) (sat_cons (step2134 p h) (sat_nil p)))))))))))
def c2744 : List Lit := [(102, false), (123, false), (1811, true), (62, false), (1791, true), (1830, true), (96, true)]
theorem step2744 (p : Nat → Bool) (h : Constraints p) : clause p c2744 = true :=
  Snake9.LocalRup.prove_clause [c2693, c1566, c1519, c587, c586, c584, c1536, c1523, c1528, c1531, c1561, c1562, c1520, c1648, c1539, c1541, c1537, c1532, c2001, c2272, c1587, c2558] c2744 (by decide) p (sat_cons (step2693 p h) (sat_cons (step1566 p h) (sat_cons (step1519 p h) (sat_cons (step587 p h) (sat_cons (step586 p h) (sat_cons (step584 p h) (sat_cons (step1536 p h) (sat_cons (step1523 p h) (sat_cons (step1528 p h) (sat_cons (step1531 p h) (sat_cons (step1561 p h) (sat_cons (step1562 p h) (sat_cons (step1520 p h) (sat_cons (step1648 p h) (sat_cons (step1539 p h) (sat_cons (step1541 p h) (sat_cons (step1537 p h) (sat_cons (step1532 p h) (sat_cons (step2001 p h) (sat_cons (step2272 p h) (sat_cons (step1587 p h) (sat_cons (step2558 p h) (sat_nil p)))))))))))))))))))))))
def c2745 : List Lit := [(1784, true), (226, true), (109, true), (93, true)]
theorem step2745 (p : Nat → Bool) (h : Constraints p) : clause p c2745 = true :=
  Snake9.LocalRup.prove_clause [c1535, c1539, c1541, c1537, c1533, c2623, c2140, c2138, c541, c637] c2745 (by decide) p (sat_cons (step1535 p h) (sat_cons (step1539 p h) (sat_cons (step1541 p h) (sat_cons (step1537 p h) (sat_cons (step1533 p h) (sat_cons (step2623 p h) (sat_cons (step2140 p h) (sat_cons (step2138 p h) (sat_cons (step541 p h) (sat_cons (step637 p h) (sat_nil p)))))))))))
def c2746 : List Lit := [(45, false), (47, true), (168, true)]
theorem step2746 (p : Nat → Bool) (h : Constraints p) : clause p c2746 = true :=
  Snake9.LocalRup.prove_clause [c2056, c2257, c126] c2746 (by decide) p (sat_cons (step2056 p h) (sat_cons (step2257 p h) (sat_cons (step126 p h) (sat_nil p))))
def c2747 : List Lit := [(1636, true), (36, true), (7, false), (1630, false), (44, false)]
theorem step2747 (p : Nat → Bool) (h : Constraints p) : clause p c2747 = true :=
  Snake9.LocalRup.prove_clause [c2718, c1223, c1204, c1193, c140, c1191] c2747 (by decide) p (sat_cons (step2718 p h) (sat_cons (step1223 p h) (sat_cons (step1204 p h) (sat_cons (step1193 p h) (sat_cons (step140 p h) (sat_cons (step1191 p h) (sat_nil p)))))))
def c2748 : List Lit := [(27, false), (1637, true), (36, true), (44, false), (7, false)]
theorem step2748 (p : Nat → Bool) (h : Constraints p) : clause p c2748 = true :=
  Snake9.LocalRup.prove_clause [c137, c135, c136, c1204, c1191, c1200, c1193, c1209, c1224] c2748 (by decide) p (sat_cons (step137 p h) (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step1204 p h) (sat_cons (step1191 p h) (sat_cons (step1200 p h) (sat_cons (step1193 p h) (sat_cons (step1209 p h) (sat_cons (step1224 p h) (sat_nil p))))))))))
def c2749 : List Lit := [(1744, true), (1782, true), (102, false), (62, false), (88, false), (93, true), (95, true)]
theorem step2749 (p : Nat → Bool) (h : Constraints p) : clause p c2749 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1440, c1442, c1438, c1433, c2704, c580, c1537] c2749 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1440 p h) (sat_cons (step1442 p h) (sat_cons (step1438 p h) (sat_cons (step1433 p h) (sat_cons (step2704 p h) (sat_cons (step580 p h) (sat_cons (step1537 p h) (sat_nil p)))))))))
def c2750 : List Lit := [(1659, true), (46, true), (93, true)]
theorem step2750 (p : Nat → Bool) (h : Constraints p) : clause p c2750 = true :=
  Snake9.LocalRup.prove_clause [c1233, c1269, c1992, c1241, c1236] c2750 (by decide) p (sat_cons (step1233 p h) (sat_cons (step1269 p h) (sat_cons (step1992 p h) (sat_cons (step1241 p h) (sat_cons (step1236 p h) (sat_nil p))))))
def c2751 : List Lit := [(1636, true), (33, true), (46, true), (32, false), (39, false), (1622, false), (44, false), (7, false)]
theorem step2751 (p : Nat → Bool) (h : Constraints p) : clause p c2751 = true :=
  Snake9.LocalRup.prove_clause [c1220, c1207, c2726, c93, c940, c943, c946, c949, c954, c2192, c1002, c974, c976, c971, c963, c970, c962, c969, c961, c163, c2746, c1203, c1205, c1209, c142, c1200] c2751 (by decide) p (sat_cons (step1220 p h) (sat_cons (step1207 p h) (sat_cons (step2726 p h) (sat_cons (step93 p h) (sat_cons (step940 p h) (sat_cons (step943 p h) (sat_cons (step946 p h) (sat_cons (step949 p h) (sat_cons (step954 p h) (sat_cons (step2192 p h) (sat_cons (step1002 p h) (sat_cons (step974 p h) (sat_cons (step976 p h) (sat_cons (step971 p h) (sat_cons (step963 p h) (sat_cons (step970 p h) (sat_cons (step962 p h) (sat_cons (step969 p h) (sat_cons (step961 p h) (sat_cons (step163 p h) (sat_cons (step2746 p h) (sat_cons (step1203 p h) (sat_cons (step1205 p h) (sat_cons (step1209 p h) (sat_cons (step142 p h) (sat_cons (step1200 p h) (sat_nil p)))))))))))))))))))))))))))
def c2752 : List Lit := [(73, false), (56, false), (8, false), (4, false), (3, false)]
theorem step2752 (p : Nat → Bool) (h : Constraints p) : clause p c2752 = true :=
  Snake9.LocalRup.prove_clause [c2360, c292] c2752 (by decide) p (sat_cons (step2360 p h) (sat_cons (step292 p h) (sat_nil p)))
def c2753 : List Lit := [(1745, false), (68, false), (1711, false), (1752, true), (1763, true), (80, false), (1736, false), (87, true), (7, false)]
theorem step2753 (p : Nat → Bool) (h : Constraints p) : clause p c2753 = true :=
  Snake9.LocalRup.prove_clause [c1459, c1464, c1502, c2700, c1404] c2753 (by decide) p (sat_cons (step1459 p h) (sat_cons (step1464 p h) (sat_cons (step1502 p h) (sat_cons (step2700 p h) (sat_cons (step1404 p h) (sat_nil p))))))
def c2754 : List Lit := [(1788, true), (1771, false), (93, true)]
theorem step2754 (p : Nat → Bool) (h : Constraints p) : clause p c2754 = true :=
  Snake9.LocalRup.prove_clause [c1526, c1555, c1551, c1527, c2696, c1522] c2754 (by decide) p (sat_cons (step1526 p h) (sat_cons (step1555 p h) (sat_cons (step1551 p h) (sat_cons (step1527 p h) (sat_cons (step2696 p h) (sat_cons (step1522 p h) (sat_nil p)))))))
def c2755 : List Lit := [(123, true), (97, false), (1830, true), (1776, false), (108, true), (93, true), (81, true)]
theorem step2755 (p : Nat → Bool) (h : Constraints p) : clause p c2755 = true :=
  Snake9.LocalRup.prove_clause [c1536, c1538, c1556, c1642, c2235, c1956, c2515, c2234, c1613, c1532, c1648, c2738, c1557, c1537, c1539] c2755 (by decide) p (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1556 p h) (sat_cons (step1642 p h) (sat_cons (step2235 p h) (sat_cons (step1956 p h) (sat_cons (step2515 p h) (sat_cons (step2234 p h) (sat_cons (step1613 p h) (sat_cons (step1532 p h) (sat_cons (step1648 p h) (sat_cons (step2738 p h) (sat_cons (step1557 p h) (sat_cons (step1537 p h) (sat_cons (step1539 p h) (sat_nil p))))))))))))))))
def c2756 : List Lit := [(1830, true), (1776, false), (108, true), (102, false), (27, false), (96, true), (93, true), (81, true)]
theorem step2756 (p : Nat → Bool) (h : Constraints p) : clause p c2756 = true :=
  Snake9.LocalRup.prove_clause [c1536, c1538, c1519, c2630, c2233, c1654, c2597, c1520, c2755, c2340, c1528, c1561, c1562, c1648, c1539, c1541, c2234, c1537, c1532, c2001, c2272, c1587, c2558] c2756 (by decide) p (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1519 p h) (sat_cons (step2630 p h) (sat_cons (step2233 p h) (sat_cons (step1654 p h) (sat_cons (step2597 p h) (sat_cons (step1520 p h) (sat_cons (step2755 p h) (sat_cons (step2340 p h) (sat_cons (step1528 p h) (sat_cons (step1561 p h) (sat_cons (step1562 p h) (sat_cons (step1648 p h) (sat_cons (step1539 p h) (sat_cons (step1541 p h) (sat_cons (step2234 p h) (sat_cons (step1537 p h) (sat_cons (step1532 p h) (sat_cons (step2001 p h) (sat_cons (step2272 p h) (sat_cons (step1587 p h) (sat_cons (step2558 p h) (sat_nil p))))))))))))))))))))))))
def c2757 : List Lit := [(1745, true), (1773, false), (1830, true), (1811, false), (123, true), (88, true), (89, false), (96, true), (95, true), (93, true), (18, false)]
theorem step2757 (p : Nat → Bool) (h : Constraints p) : clause p c2757 = true :=
  Snake9.LocalRup.prove_clause [c2234, c1648, c1519, c1527, c1557, c1434, c1436, c1445, c1443, c1435, c1438, c401, c402, c2122, c2678, c1570, c1581, c1579, c1572, c1573, c748, c2314, c1535, c1538, c1541, c1561, c1532, c1530, c493, c1520] c2757 (by decide) p (sat_cons (step2234 p h) (sat_cons (step1648 p h) (sat_cons (step1519 p h) (sat_cons (step1527 p h) (sat_cons (step1557 p h) (sat_cons (step1434 p h) (sat_cons (step1436 p h) (sat_cons (step1445 p h) (sat_cons (step1443 p h) (sat_cons (step1435 p h) (sat_cons (step1438 p h) (sat_cons (step401 p h) (sat_cons (step402 p h) (sat_cons (step2122 p h) (sat_cons (step2678 p h) (sat_cons (step1570 p h) (sat_cons (step1581 p h) (sat_cons (step1579 p h) (sat_cons (step1572 p h) (sat_cons (step1573 p h) (sat_cons (step748 p h) (sat_cons (step2314 p h) (sat_cons (step1535 p h) (sat_cons (step1538 p h) (sat_cons (step1541 p h) (sat_cons (step1561 p h) (sat_cons (step1532 p h) (sat_cons (step1530 p h) (sat_cons (step493 p h) (sat_cons (step1520 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2758 : List Lit := [(1817, true), (113, true), (93, true), (1810, false)]
theorem step2758 (p : Nat → Bool) (h : Constraints p) : clause p c2758 = true :=
  Snake9.LocalRup.prove_clause [c1612, c2010, c1999, c1590, c2374, c1588] c2758 (by decide) p (sat_cons (step1612 p h) (sat_cons (step2010 p h) (sat_cons (step1999 p h) (sat_cons (step1590 p h) (sat_cons (step2374 p h) (sat_cons (step1588 p h) (sat_nil p)))))))
def c2759 : List Lit := [(91, false), (1773, true), (88, false)]
theorem step2759 (p : Nat → Bool) (h : Constraints p) : clause p c2759 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1522, c543, c588, c433, c2136] c2759 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step543 p h) (sat_cons (step588 p h) (sat_cons (step433 p h) (sat_cons (step2136 p h) (sat_nil p)))))))
def c2760 : List Lit := [(1741, true), (93, false), (19, false)]
theorem step2760 (p : Nat → Bool) (h : Constraints p) : clause p c2760 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1437, c454] c2760 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step454 p h) (sat_nil p))))
def c2761 : List Lit := [(1644, true), (95, true), (1771, false), (1855, true), (88, true), (89, false), (93, false), (18, false), (1736, false), (1810, false), (19, false), (1725, false)]
theorem step2761 (p : Nat → Bool) (h : Constraints p) : clause p c2761 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1236, c2686, c453, c452, c395, c394, c1460, c1574, c1533, c1570, c1522, c1496, c1540, c1579, c1527, c1719, c1612, c1556, c1641] c2761 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step2686 p h) (sat_cons (step453 p h) (sat_cons (step452 p h) (sat_cons (step395 p h) (sat_cons (step394 p h) (sat_cons (step1460 p h) (sat_cons (step1574 p h) (sat_cons (step1533 p h) (sat_cons (step1570 p h) (sat_cons (step1522 p h) (sat_cons (step1496 p h) (sat_cons (step1540 p h) (sat_cons (step1579 p h) (sat_cons (step1527 p h) (sat_cons (step1719 p h) (sat_cons (step1612 p h) (sat_cons (step1556 p h) (sat_cons (step1641 p h) (sat_nil p)))))))))))))))))))))
def c2762 : List Lit := [(1646, true), (96, false), (93, true)]
theorem step2762 (p : Nat → Bool) (h : Constraints p) : clause p c2762 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1240, c1235, c2404, c1232, c1985] c2762 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1235 p h) (sat_cons (step2404 p h) (sat_cons (step1232 p h) (sat_cons (step1985 p h) (sat_nil p)))))))
def c2763 : List Lit := [(46, true), (1647, true), (96, false), (93, true)]
theorem step2763 (p : Nat → Bool) (h : Constraints p) : clause p c2763 = true :=
  Snake9.LocalRup.prove_clause [c1243, c1233, c1234, c1241, c1235, c2404, c1985] c2763 (by decide) p (sat_cons (step1243 p h) (sat_cons (step1233 p h) (sat_cons (step1234 p h) (sat_cons (step1241 p h) (sat_cons (step1235 p h) (sat_cons (step2404 p h) (sat_cons (step1985 p h) (sat_nil p))))))))
def c2764 : List Lit := [(1773, true), (91, false), (123, false), (97, false), (1774, true), (96, false)]
theorem step2764 (p : Nat → Bool) (h : Constraints p) : clause p c2764 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1522, c2263, c545, c435, c1962] c2764 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step2263 p h) (sat_cons (step545 p h) (sat_cons (step435 p h) (sat_cons (step1962 p h) (sat_nil p)))))))
def c2765 : List Lit := [(27, false), (91, false), (123, false), (26, true), (44, true)]
theorem step2765 (p : Nat → Bool) (h : Constraints p) : clause p c2765 = true :=
  Snake9.LocalRup.prove_clause [c2038, c571] c2765 (by decide) p (sat_cons (step2038 p h) (sat_cons (step571 p h) (sat_nil p)))
def c2766 : List Lit := [(1771, false), (123, false), (1785, true), (1776, true), (1828, true), (96, false), (88, false)]
theorem step2766 (p : Nat → Bool) (h : Constraints p) : clause p c2766 = true :=
  Snake9.LocalRup.prove_clause [c1526, c1527, c1521, c1522, c2263, c543, c419, c2132, c2129, c632, c1806, c2629, c1533] c2766 (by decide) p (sat_cons (step1526 p h) (sat_cons (step1527 p h) (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step2263 p h) (sat_cons (step543 p h) (sat_cons (step419 p h) (sat_cons (step2132 p h) (sat_cons (step2129 p h) (sat_cons (step632 p h) (sat_cons (step1806 p h) (sat_cons (step2629 p h) (sat_cons (step1533 p h) (sat_nil p))))))))))))))
def c2767 : List Lit := [(27, false), (123, false), (1774, true), (26, true), (44, true)]
theorem step2767 (p : Nat → Bool) (h : Constraints p) : clause p c2767 = true :=
  Snake9.LocalRup.prove_clause [c2038, c2340] c2767 (by decide) p (sat_cons (step2038 p h) (sat_cons (step2340 p h) (sat_nil p)))
def c2768 : List Lit := [(91, false), (97, false), (123, false), (96, false), (88, false), (80, false)]
theorem step2768 (p : Nat → Bool) (h : Constraints p) : clause p c2768 = true :=
  Snake9.LocalRup.prove_clause [c416, c432, c2121, c2120, c803] c2768 (by decide) p (sat_cons (step416 p h) (sat_cons (step432 p h) (sat_cons (step2121 p h) (sat_cons (step2120 p h) (sat_cons (step803 p h) (sat_nil p))))))
def c2769 : List Lit := [(27, false), (1774, true), (62, false), (26, true), (44, true)]
theorem step2769 (p : Nat → Bool) (h : Constraints p) : clause p c2769 = true :=
  Snake9.LocalRup.prove_clause [c2038, c2575] c2769 (by decide) p (sat_cons (step2038 p h) (sat_cons (step2575 p h) (sat_nil p)))
def c2770 : List Lit := [(1636, true), (46, false), (1623, false), (1618, false), (7, false), (3, false)]
theorem step2770 (p : Nat → Bool) (h : Constraints p) : clause p c2770 = true :=
  Snake9.LocalRup.prove_clause [c2381, c1223, c2699, c1208, c1201] c2770 (by decide) p (sat_cons (step2381 p h) (sat_cons (step1223 p h) (sat_cons (step2699 p h) (sat_cons (step1208 p h) (sat_cons (step1201 p h) (sat_nil p))))))
def c2771 : List Lit := [(91, false), (227, true), (97, false), (102, true), (101, false), (1774, true), (96, false)]
theorem step2771 (p : Nat → Bool) (h : Constraints p) : clause p c2771 = true :=
  Snake9.LocalRup.prove_clause [c435, c1962] c2771 (by decide) p (sat_cons (step435 p h) (sat_cons (step1962 p h) (sat_nil p)))
def c2772 : List Lit := [(1776, true), (89, true), (91, false), (88, false), (62, false)]
theorem step2772 (p : Nat → Bool) (h : Constraints p) : clause p c2772 = true :=
  Snake9.LocalRup.prove_clause [c2759, c1525, c1527, c1518, c432, c2121, c579, c578, c1523] c2772 (by decide) p (sat_cons (step2759 p h) (sat_cons (step1525 p h) (sat_cons (step1527 p h) (sat_cons (step1518 p h) (sat_cons (step432 p h) (sat_cons (step2121 p h) (sat_cons (step579 p h) (sat_cons (step578 p h) (sat_cons (step1523 p h) (sat_nil p))))))))))
def c2773 : List Lit := [(1762, true), (1750, false), (1744, false), (1707, false), (87, true), (1725, false), (80, false), (7, false)]
theorem step2773 (p : Nat → Bool) (h : Constraints p) : clause p c2773 = true :=
  Snake9.LocalRup.prove_clause [c1377, c2636, c1495, c1501, c1463, c1408, c1404, c1378, c2700, c1373] c2773 (by decide) p (sat_cons (step1377 p h) (sat_cons (step2636 p h) (sat_cons (step1495 p h) (sat_cons (step1501 p h) (sat_cons (step1463 p h) (sat_cons (step1408 p h) (sat_cons (step1404 p h) (sat_cons (step1378 p h) (sat_cons (step2700 p h) (sat_cons (step1373 p h) (sat_nil p)))))))))))
def c2774 : List Lit := [(1790, true), (88, false), (92, false), (1776, false), (96, true), (93, true)]
theorem step2774 (p : Nat → Bool) (h : Constraints p) : clause p c2774 = true :=
  Snake9.LocalRup.prove_clause [c1557, c2706] c2774 (by decide) p (sat_cons (step1557 p h) (sat_cons (step2706 p h) (sat_nil p)))
def c2775 : List Lit := [(92, false), (97, false), (104, false), (93, true)]
theorem step2775 (p : Nat → Bool) (h : Constraints p) : clause p c2775 = true :=
  Snake9.LocalRup.prove_clause [c2122, c493] c2775 (by decide) p (sat_cons (step2122 p h) (sat_cons (step493 p h) (sat_nil p)))
end B112E050
