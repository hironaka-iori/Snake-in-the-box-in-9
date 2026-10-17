import B112E050Part0012
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2648 : List Lit := [(35, true), (1638, true), (39, true), (345, true), (1619, false), (44, true), (33, true)]
theorem step2648 (p : Nat → Bool) (h : Constraints p) : clause p c2648 = true :=
  Snake9.LocalRup.prove_clause [c976, c964, c960, c959, c974, c972, c968, c965, c1190, c105, c1198, c2054, c1228, c1933] c2648 (by decide) p (sat_cons (step976 p h) (sat_cons (step964 p h) (sat_cons (step960 p h) (sat_cons (step959 p h) (sat_cons (step974 p h) (sat_cons (step972 p h) (sat_cons (step968 p h) (sat_cons (step965 p h) (sat_cons (step1190 p h) (sat_cons (step105 p h) (sat_cons (step1198 p h) (sat_cons (step2054 p h) (sat_cons (step1228 p h) (sat_cons (step1933 p h) (sat_nil p)))))))))))))))
def c2649 : List Lit := [(1658, true), (68, false)]
theorem step2649 (p : Nat → Bool) (h : Constraints p) : clause p c2649 = true :=
  Snake9.LocalRup.prove_clause [c1260, c1264, c1252, c1254, c1240, c1250, c1246, c1232, c221, c170, c2077] c2649 (by decide) p (sat_cons (step1260 p h) (sat_cons (step1264 p h) (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step1240 p h) (sat_cons (step1250 p h) (sat_cons (step1246 p h) (sat_cons (step1232 p h) (sat_cons (step221 p h) (sat_cons (step170 p h) (sat_cons (step2077 p h) (sat_nil p))))))))))))
def c2650 : List Lit := [(1736, true), (313, false), (87, true), (80, false)]
theorem step2650 (p : Nat → Bool) (h : Constraints p) : clause p c2650 = true :=
  Snake9.LocalRup.prove_clause [c1426, c1424, c2589, c2288] c2650 (by decide) p (sat_cons (step1426 p h) (sat_cons (step1424 p h) (sat_cons (step2589 p h) (sat_cons (step2288 p h) (sat_nil p)))))
def c2651 : List Lit := [(1637, false), (1736, false), (1670, true), (102, false), (1606, false), (88, true), (19, false)]
theorem step2651 (p : Nat → Bool) (h : Constraints p) : clause p c2651 = true :=
  Snake9.LocalRup.prove_clause [c1303, c1304, c1330, c2568, c2247] c2651 (by decide) p (sat_cons (step1303 p h) (sat_cons (step1304 p h) (sat_cons (step1330 p h) (sat_cons (step2568 p h) (sat_cons (step2247 p h) (sat_nil p))))))
def c2652 : List Lit := [(1736, true), (87, true), (80, false), (81, true)]
theorem step2652 (p : Nat → Bool) (h : Constraints p) : clause p c2652 = true :=
  Snake9.LocalRup.prove_clause [c1422, c1426, c2275, c1428, c1424, c1420, c365, c2106] c2652 (by decide) p (sat_cons (step1422 p h) (sat_cons (step1426 p h) (sat_cons (step2275 p h) (sat_cons (step1428 p h) (sat_cons (step1424 p h) (sat_cons (step1420 p h) (sat_cons (step365 p h) (sat_cons (step2106 p h) (sat_nil p)))))))))
def c2653 : List Lit := [(39, true), (1619, false), (35, true), (1670, true), (44, true), (33, true), (2, false)]
theorem step2653 (p : Nat → Bool) (h : Constraints p) : clause p c2653 = true :=
  Snake9.LocalRup.prove_clause [c1190, c1198, c1309, c1201, c2648, c1208, c1002, c1227, c2192, c1304, c956, c2649, c921, c4, c910, c906] c2653 (by decide) p (sat_cons (step1190 p h) (sat_cons (step1198 p h) (sat_cons (step1309 p h) (sat_cons (step1201 p h) (sat_cons (step2648 p h) (sat_cons (step1208 p h) (sat_cons (step1002 p h) (sat_cons (step1227 p h) (sat_cons (step2192 p h) (sat_cons (step1304 p h) (sat_cons (step956 p h) (sat_cons (step2649 p h) (sat_cons (step921 p h) (sat_cons (step4 p h) (sat_cons (step910 p h) (sat_cons (step906 p h) (sat_nil p)))))))))))))))))
def c2654 : List Lit := [(107, false), (1781, false), (1790, true), (1771, false), (30, false), (97, false)]
theorem step2654 (p : Nat → Bool) (h : Constraints p) : clause p c2654 = true :=
  Snake9.LocalRup.prove_clause [c647, c646, c1532, c1521, c1541, c1527, c1557] c2654 (by decide) p (sat_cons (step647 p h) (sat_cons (step646 p h) (sat_cons (step1532 p h) (sat_cons (step1521 p h) (sat_cons (step1541 p h) (sat_cons (step1527 p h) (sat_cons (step1557 p h) (sat_nil p))))))))
def c2655 : List Lit := [(103, false), (1746, true), (1645, true), (89, false), (93, false), (88, true), (95, true), (19, false), (18, false)]
theorem step2655 (p : Nat → Bool) (h : Constraints p) : clause p c2655 = true :=
  Snake9.LocalRup.prove_clause [c452, c456, c1237, c1438, c392, c1446, c1435] c2655 (by decide) p (sat_cons (step452 p h) (sat_cons (step456 p h) (sat_cons (step1237 p h) (sat_cons (step1438 p h) (sat_cons (step392 p h) (sat_cons (step1446 p h) (sat_cons (step1435 p h) (sat_nil p))))))))
def c2656 : List Lit := [(62, true), (1708, true), (1655, true), (81, true)]
theorem step2656 (p : Nat → Bool) (h : Constraints p) : clause p c2656 = true :=
  Snake9.LocalRup.prove_clause [c1253, c1250, c1251, c1255, c2083, c1247, c235, c236, c1371] c2656 (by decide) p (sat_cons (step1253 p h) (sat_cons (step1250 p h) (sat_cons (step1251 p h) (sat_cons (step1255 p h) (sat_cons (step2083 p h) (sat_cons (step1247 p h) (sat_cons (step235 p h) (sat_cons (step236 p h) (sat_cons (step1371 p h) (sat_nil p))))))))))
def c2657 : List Lit := [(1735, true), (81, true)]
theorem step2657 (p : Nat → Bool) (h : Constraints p) : clause p c2657 = true :=
  Snake9.LocalRup.prove_clause [c1425, c1427, c1423, c1419, c1420, c364, c2106] c2657 (by decide) p (sat_cons (step1425 p h) (sat_cons (step1427 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step364 p h) (sat_cons (step2106 p h) (sat_nil p))))))))
def c2658 : List Lit := [(1636, true), (1620, false), (33, true), (87, true), (21, false), (26, true), (15, false), (7, false)]
theorem step2658 (p : Nat → Bool) (h : Constraints p) : clause p c2658 = true :=
  Snake9.LocalRup.prove_clause [c1186, c1195, c2381, c2607, c1223, c1913, c1206, c1208, c2631, c1203, c1200, c1201, c2192, c2257, c1891, c1002, c163, c974, c969, c971, c970] c2658 (by decide) p (sat_cons (step1186 p h) (sat_cons (step1195 p h) (sat_cons (step2381 p h) (sat_cons (step2607 p h) (sat_cons (step1223 p h) (sat_cons (step1913 p h) (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step2631 p h) (sat_cons (step1203 p h) (sat_cons (step1200 p h) (sat_cons (step1201 p h) (sat_cons (step2192 p h) (sat_cons (step2257 p h) (sat_cons (step1891 p h) (sat_cons (step1002 p h) (sat_cons (step163 p h) (sat_cons (step974 p h) (sat_cons (step969 p h) (sat_cons (step971 p h) (sat_cons (step970 p h) (sat_nil p))))))))))))))))))))))
def c2659 : List Lit := [(1637, true), (175, true), (1619, false), (39, false), (35, true), (21, false)]
theorem step2659 (p : Nat → Bool) (h : Constraints p) : clause p c2659 = true :=
  Snake9.LocalRup.prove_clause [c1190, c1198, c1227, c2646, c1208, c1200] c2659 (by decide) p (sat_cons (step1190 p h) (sat_cons (step1198 p h) (sat_cons (step1227 p h) (sat_cons (step2646 p h) (sat_cons (step1208 p h) (sat_cons (step1200 p h) (sat_nil p)))))))
def c2660 : List Lit := [(1771, false), (107, false), (1790, true), (1812, true), (97, false), (108, true), (102, false), (27, false)]
theorem step2660 (p : Nat → Bool) (h : Constraints p) : clause p c2660 = true :=
  Snake9.LocalRup.prove_clause [c1536, c1538, c1561, c1892, c1527, c1528, c1557, c2340, c1539, c1541, c1537, c1532, c1975, c670, c1587] c2660 (by decide) p (sat_cons (step1536 p h) (sat_cons (step1538 p h) (sat_cons (step1561 p h) (sat_cons (step1892 p h) (sat_cons (step1527 p h) (sat_cons (step1528 p h) (sat_cons (step1557 p h) (sat_cons (step2340 p h) (sat_cons (step1539 p h) (sat_cons (step1541 p h) (sat_cons (step1537 p h) (sat_cons (step1532 p h) (sat_cons (step1975 p h) (sat_cons (step670 p h) (sat_cons (step1587 p h) (sat_nil p))))))))))))))))
def c2661 : List Lit := [(1773, true), (108, false), (102, false)]
theorem step2661 (p : Nat → Bool) (h : Constraints p) : clause p c2661 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1522, c594] c2661 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step594 p h) (sat_nil p))))
def c2662 : List Lit := [(123, false), (1774, true), (108, false), (102, false)]
theorem step2662 (p : Nat → Bool) (h : Constraints p) : clause p c2662 = true :=
  Snake9.LocalRup.prove_clause [c596, c597, c1523] c2662 (by decide) p (sat_cons (step596 p h) (sat_cons (step597 p h) (sat_cons (step1523 p h) (sat_nil p))))
def c2663 : List Lit := [(97, false), (128, false), (125, true), (104, false), (39, false), (108, false)]
theorem step2663 (p : Nat → Bool) (h : Constraints p) : clause p c2663 = true :=
  Snake9.LocalRup.prove_clause [c669, c780, c2179] c2663 (by decide) p (sat_cons (step669 p h) (sat_cons (step780 p h) (sat_cons (step2179 p h) (sat_nil p))))
def c2664 : List Lit := [(123, false), (1828, false), (1637, false), (1765, true), (1606, false), (1745, false), (80, false), (87, true), (81, true), (7, false)]
theorem step2664 (p : Nat → Bool) (h : Constraints p) : clause p c2664 = true :=
  Snake9.LocalRup.prove_clause [c310, c319, c314, c320, c317, c1384, c1424, c1388, c1393, c2450, c2588, c2656, c1718, c1261, c2249, c1305, c1332] c2664 (by decide) p (sat_cons (step310 p h) (sat_cons (step319 p h) (sat_cons (step314 p h) (sat_cons (step320 p h) (sat_cons (step317 p h) (sat_cons (step1384 p h) (sat_cons (step1424 p h) (sat_cons (step1388 p h) (sat_cons (step1393 p h) (sat_cons (step2450 p h) (sat_cons (step2588 p h) (sat_cons (step2656 p h) (sat_cons (step1718 p h) (sat_cons (step1261 p h) (sat_cons (step2249 p h) (sat_cons (step1305 p h) (sat_cons (step1332 p h) (sat_nil p))))))))))))))))))
def c2665 : List Lit := [(39, true), (1637, true), (35, true), (33, true), (44, true), (87, true), (21, false), (26, true), (15, false)]
theorem step2665 (p : Nat → Bool) (h : Constraints p) : clause p c2665 = true :=
  Snake9.LocalRup.prove_clause [c1186, c1190, c1195, c1224, c1201, c1208, c1209, c1227, c1204, c1198, c2054, c1188, c105, c1913, c959, c2631, c960, c2192, c964, c1002, c976] c2665 (by decide) p (sat_cons (step1186 p h) (sat_cons (step1190 p h) (sat_cons (step1195 p h) (sat_cons (step1224 p h) (sat_cons (step1201 p h) (sat_cons (step1208 p h) (sat_cons (step1209 p h) (sat_cons (step1227 p h) (sat_cons (step1204 p h) (sat_cons (step1198 p h) (sat_cons (step2054 p h) (sat_cons (step1188 p h) (sat_cons (step105 p h) (sat_cons (step1913 p h) (sat_cons (step959 p h) (sat_cons (step2631 p h) (sat_cons (step960 p h) (sat_cons (step2192 p h) (sat_cons (step964 p h) (sat_cons (step1002 p h) (sat_cons (step976 p h) (sat_nil p))))))))))))))))))))))
def c2666 : List Lit := [(100, false), (1746, true), (1800, true), (89, false), (93, false), (88, true), (95, true), (19, false), (18, false)]
theorem step2666 (p : Nat → Bool) (h : Constraints p) : clause p c2666 = true :=
  Snake9.LocalRup.prove_clause [c405, c401, c1570, c1435, c1579, c1446, c1574, c1438, c457] c2666 (by decide) p (sat_cons (step405 p h) (sat_cons (step401 p h) (sat_cons (step1570 p h) (sat_cons (step1435 p h) (sat_cons (step1579 p h) (sat_cons (step1446 p h) (sat_cons (step1574 p h) (sat_cons (step1438 p h) (sat_cons (step457 p h) (sat_nil p))))))))))
def c2667 : List Lit := [(103, false), (1800, true), (1645, true), (22, true), (19, false), (18, false)]
theorem step2667 (p : Nat → Bool) (h : Constraints p) : clause p c2667 = true :=
  Snake9.LocalRup.prove_clause [c2028, c2031, c463, c452, c1574, c1237, c1579, c395, c1570] c2667 (by decide) p (sat_cons (step2028 p h) (sat_cons (step2031 p h) (sat_cons (step463 p h) (sat_cons (step452 p h) (sat_cons (step1574 p h) (sat_cons (step1237 p h) (sat_cons (step1579 p h) (sat_cons (step395 p h) (sat_cons (step1570 p h) (sat_nil p))))))))))
def c2668 : List Lit := [(123, false), (1637, true), (1618, false), (44, false), (7, false)]
theorem step2668 (p : Nat → Bool) (h : Constraints p) : clause p c2668 = true :=
  Snake9.LocalRup.prove_clause [c143, c144, c141, c1200, c1204, c1190, c1209, c1195, c1224] c2668 (by decide) p (sat_cons (step143 p h) (sat_cons (step144 p h) (sat_cons (step141 p h) (sat_cons (step1200 p h) (sat_cons (step1204 p h) (sat_cons (step1190 p h) (sat_cons (step1209 p h) (sat_cons (step1195 p h) (sat_cons (step1224 p h) (sat_nil p))))))))))
def c2669 : List Lit := [(1828, true), (1776, false), (1816, false)]
theorem step2669 (p : Nat → Bool) (h : Constraints p) : clause p c2669 = true :=
  Snake9.LocalRup.prove_clause [c1555, c1640, c1634, c1556, c2234, c1538, c1540, c2391] c2669 (by decide) p (sat_cons (step1555 p h) (sat_cons (step1640 p h) (sat_cons (step1634 p h) (sat_cons (step1556 p h) (sat_cons (step2234 p h) (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step2391 p h) (sat_nil p)))))))))
def c2670 : List Lit := [(96, false), (1800, true), (22, true), (19, false), (18, false)]
theorem step2670 (p : Nat → Bool) (h : Constraints p) : clause p c2670 = true :=
  Snake9.LocalRup.prove_clause [c2028, c2031, c404, c462, c1570, c1574, c1579] c2670 (by decide) p (sat_cons (step2028 p h) (sat_cons (step2031 p h) (sat_cons (step404 p h) (sat_cons (step462 p h) (sat_cons (step1570 p h) (sat_cons (step1574 p h) (sat_cons (step1579 p h) (sat_nil p))))))))
def c2671 : List Lit := [(1644, true), (1800, true), (22, true), (19, false), (18, false)]
theorem step2671 (p : Nat → Bool) (h : Constraints p) : clause p c2671 = true :=
  Snake9.LocalRup.prove_clause [c2028, c2031, c1235, c1236, c453, c395, c1574, c1570, c1579] c2671 (by decide) p (sat_cons (step2028 p h) (sat_cons (step2031 p h) (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step453 p h) (sat_cons (step395 p h) (sat_cons (step1574 p h) (sat_cons (step1570 p h) (sat_cons (step1579 p h) (sat_nil p))))))))))
def c2672 : List Lit := [(103, true), (1790, true), (1831, true), (1773, false), (1795, false), (115, true), (1800, false), (96, true), (1776, false), (123, true)]
theorem step2672 (p : Nat → Bool) (h : Constraints p) : clause p c2672 = true :=
  Snake9.LocalRup.prove_clause [c1557, c1543, c1533, c1540, c1556, c1643, c1614, c1561, c1541, c1530, c1534, c1535, c1520, c2278, c2571] c2672 (by decide) p (sat_cons (step1557 p h) (sat_cons (step1543 p h) (sat_cons (step1533 p h) (sat_cons (step1540 p h) (sat_cons (step1556 p h) (sat_cons (step1643 p h) (sat_cons (step1614 p h) (sat_cons (step1561 p h) (sat_cons (step1541 p h) (sat_cons (step1530 p h) (sat_cons (step1534 p h) (sat_cons (step1535 p h) (sat_cons (step1520 p h) (sat_cons (step2278 p h) (sat_cons (step2571 p h) (sat_nil p))))))))))))))))
def c2673 : List Lit := [(1590, true), (1638, true), (44, false), (21, false), (16, false), (7, false)]
theorem step2673 (p : Nat → Bool) (h : Constraints p) : clause p c2673 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1143, c1139, c1135, c137, c135, c136, c2256, c1204, c1190, c1200, c1198, c1209, c1228] c2673 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1139 p h) (sat_cons (step1135 p h) (sat_cons (step137 p h) (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step2256 p h) (sat_cons (step1204 p h) (sat_cons (step1190 p h) (sat_cons (step1200 p h) (sat_cons (step1198 p h) (sat_cons (step1209 p h) (sat_cons (step1228 p h) (sat_nil p)))))))))))))))
def c2674 : List Lit := [(1607, false), (1636, false), (1691, true), (1736, false), (80, true), (88, true), (19, false)]
theorem step2674 (p : Nat → Bool) (h : Constraints p) : clause p c2674 = true :=
  Snake9.LocalRup.prove_clause [c1296, c1339, c1340, c2247, c1297, c2568, c1927] c2674 (by decide) p (sat_cons (step1296 p h) (sat_cons (step1339 p h) (sat_cons (step1340 p h) (sat_cons (step2247 p h) (sat_cons (step1297 p h) (sat_cons (step2568 p h) (sat_cons (step1927 p h) (sat_nil p))))))))
def c2675 : List Lit := [(100, true), (227, true), (1774, true), (107, true), (102, true), (88, true)]
theorem step2675 (p : Nat → Bool) (h : Constraints p) : clause p c2675 = true :=
  Snake9.LocalRup.prove_clause [c1523, c547, c2133] c2675 (by decide) p (sat_cons (step1523 p h) (sat_cons (step547 p h) (sat_cons (step2133 p h) (sat_nil p))))
def c2676 : List Lit := [(96, false), (1746, true), (89, false), (93, false), (88, true), (95, true), (19, false), (18, false)]
theorem step2676 (p : Nat → Bool) (h : Constraints p) : clause p c2676 = true :=
  Snake9.LocalRup.prove_clause [c400, c455, c1435, c1438, c1446] c2676 (by decide) p (sat_cons (step400 p h) (sat_cons (step455 p h) (sat_cons (step1435 p h) (sat_cons (step1438 p h) (sat_cons (step1446 p h) (sat_nil p))))))
def c2677 : List Lit := [(62, false), (102, true), (1725, true), (80, true)]
theorem step2677 (p : Nat → Bool) (h : Constraints p) : clause p c2677 = true :=
  Snake9.LocalRup.prove_clause [c1974, c1993, c2079] c2677 (by decide) p (sat_cons (step1974 p h) (sat_cons (step1993 p h) (sat_cons (step2079 p h) (sat_nil p))))
def c2678 : List Lit := [(1800, false), (100, true), (1771, false), (1776, false), (1811, false), (123, true), (1830, true)]
theorem step2678 (p : Nat → Bool) (h : Constraints p) : clause p c2678 = true :=
  Snake9.LocalRup.prove_clause [c1555, c1636, c1614, c1613, c1642, c1560, c1556, c1528, c1540, c1523, c1532, c2414, c2278] c2678 (by decide) p (sat_cons (step1555 p h) (sat_cons (step1636 p h) (sat_cons (step1614 p h) (sat_cons (step1613 p h) (sat_cons (step1642 p h) (sat_cons (step1560 p h) (sat_cons (step1556 p h) (sat_cons (step1528 p h) (sat_cons (step1540 p h) (sat_cons (step1523 p h) (sat_cons (step1532 p h) (sat_cons (step2414 p h) (sat_cons (step2278 p h) (sat_nil p))))))))))))))
def c2679 : List Lit := [(1644, true), (1655, true), (62, false), (1725, true)]
theorem step2679 (p : Nat → Bool) (h : Constraints p) : clause p c2679 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1236, c2385] c2679 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step2385 p h) (sat_nil p))))
def c2680 : List Lit := [(102, false), (1774, true), (108, false), (62, false)]
theorem step2680 (p : Nat → Bool) (h : Constraints p) : clause p c2680 = true :=
  Snake9.LocalRup.prove_clause [c583, c585, c1523] c2680 (by decide) p (sat_cons (step583 p h) (sat_cons (step585 p h) (sat_cons (step1523 p h) (sat_nil p))))
def c2681 : List Lit := [(1789, true), (1773, false), (108, false), (1776, false), (87, false), (93, false), (19, false)]
theorem step2681 (p : Nat → Bool) (h : Constraints p) : clause p c2681 = true :=
  Snake9.LocalRup.prove_clause [c1556, c2622, c1540, c2643] c2681 (by decide) p (sat_cons (step1556 p h) (sat_cons (step2622 p h) (sat_cons (step1540 p h) (sat_cons (step2643 p h) (sat_nil p)))))
def c2682 : List Lit := [(96, true), (30, false), (102, true), (1776, true), (87, false)]
theorem step2682 (p : Nat → Bool) (h : Constraints p) : clause p c2682 = true :=
  Snake9.LocalRup.prove_clause [c1529, c1519, c1520, c1527, c1521, c646, c431, c2134] c2682 (by decide) p (sat_cons (step1529 p h) (sat_cons (step1519 p h) (sat_cons (step1520 p h) (sat_cons (step1527 p h) (sat_cons (step1521 p h) (sat_cons (step646 p h) (sat_cons (step431 p h) (sat_cons (step2134 p h) (sat_nil p)))))))))
def c2683 : List Lit := [(1644, true), (1776, true), (22, true), (19, false), (18, false)]
theorem step2683 (p : Nat → Bool) (h : Constraints p) : clause p c2683 = true :=
  Snake9.LocalRup.prove_clause [c2028, c2031, c1235, c1236, c451, c394, c1519, c1522, c1527] c2683 (by decide) p (sat_cons (step2028 p h) (sat_cons (step2031 p h) (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step451 p h) (sat_cons (step394 p h) (sat_cons (step1519 p h) (sat_cons (step1522 p h) (sat_cons (step1527 p h) (sat_nil p))))))))))
def c2684 : List Lit := [(1790, true), (100, true), (102, true), (1779, false), (1776, false), (96, true), (87, false)]
theorem step2684 (p : Nat → Bool) (h : Constraints p) : clause p c2684 = true :=
  Snake9.LocalRup.prove_clause [c1522, c1540, c1519, c1557, c1561, c1541, c1528, c1530, c1536, c1523, c1520, c2407] c2684 (by decide) p (sat_cons (step1522 p h) (sat_cons (step1540 p h) (sat_cons (step1519 p h) (sat_cons (step1557 p h) (sat_cons (step1561 p h) (sat_cons (step1541 p h) (sat_cons (step1528 p h) (sat_cons (step1530 p h) (sat_cons (step1536 p h) (sat_cons (step1523 p h) (sat_cons (step1520 p h) (sat_cons (step2407 p h) (sat_nil p)))))))))))))
def c2685 : List Lit := [(27, false), (108, false), (123, false), (44, true), (26, true)]
theorem step2685 (p : Nat → Bool) (h : Constraints p) : clause p c2685 = true :=
  Snake9.LocalRup.prove_clause [c2038, c577] c2685 (by decide) p (sat_cons (step2038 p h) (sat_cons (step577 p h) (sat_nil p)))
def c2686 : List Lit := [(1644, true), (1746, true), (89, false), (93, false), (88, true), (95, true), (19, false), (18, false)]
theorem step2686 (p : Nat → Bool) (h : Constraints p) : clause p c2686 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1236, c449, c392, c1438, c1435, c1446] c2686 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step449 p h) (sat_cons (step392 p h) (sat_cons (step1438 p h) (sat_cons (step1435 p h) (sat_cons (step1446 p h) (sat_nil p))))))))
def c2687 : List Lit := [(1588, true), (44, true), (25, true), (21, false), (26, true)]
theorem step2687 (p : Nat → Bool) (h : Constraints p) : clause p c2687 = true :=
  Snake9.LocalRup.prove_clause [c1138, c1139, c2042, c1913, c65, c2616, c929, c941, c931, c943, c933, c946, c2185] c2687 (by decide) p (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step2042 p h) (sat_cons (step1913 p h) (sat_cons (step65 p h) (sat_cons (step2616 p h) (sat_cons (step929 p h) (sat_cons (step941 p h) (sat_cons (step931 p h) (sat_cons (step943 p h) (sat_cons (step933 p h) (sat_cons (step946 p h) (sat_cons (step2185 p h) (sat_nil p))))))))))))))
def c2688 : List Lit := [(1588, true), (1638, true), (44, false), (33, true), (21, false), (7, false)]
theorem step2688 (p : Nat → Bool) (h : Constraints p) : clause p c2688 = true :=
  Snake9.LocalRup.prove_clause [c1138, c1139, c1913, c137, c135, c136, c1188, c1204, c1190, c1200, c1209, c1198, c1228] c2688 (by decide) p (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1913 p h) (sat_cons (step137 p h) (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step1188 p h) (sat_cons (step1204 p h) (sat_cons (step1190 p h) (sat_cons (step1200 p h) (sat_cons (step1209 p h) (sat_cons (step1198 p h) (sat_cons (step1228 p h) (sat_nil p))))))))))))))
def c2689 : List Lit := [(1644, false), (56, true), (1660, true), (1708, true), (87, false), (81, true)]
theorem step2689 (p : Nat → Bool) (h : Constraints p) : clause p c2689 = true :=
  Snake9.LocalRup.prove_clause [c1247, c1254, c1270, c1238, c1241, c1266, c1232, c1257, c2656, c2377, c1248] c2689 (by decide) p (sat_cons (step1247 p h) (sat_cons (step1254 p h) (sat_cons (step1270 p h) (sat_cons (step1238 p h) (sat_cons (step1241 p h) (sat_cons (step1266 p h) (sat_cons (step1232 p h) (sat_cons (step1257 p h) (sat_cons (step2656 p h) (sat_cons (step2377 p h) (sat_cons (step1248 p h) (sat_nil p))))))))))))
def c2690 : List Lit := [(1645, false), (1660, true), (87, false)]
theorem step2690 (p : Nat → Bool) (h : Constraints p) : clause p c2690 = true :=
  Snake9.LocalRup.prove_clause [c1274, c1239, c1242, c1270, c1232, c1252, c1254, c1246, c1250, c2377] c2690 (by decide) p (sat_cons (step1274 p h) (sat_cons (step1239 p h) (sat_cons (step1242 p h) (sat_cons (step1270 p h) (sat_cons (step1232 p h) (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step1246 p h) (sat_cons (step1250 p h) (sat_cons (step2377 p h) (sat_nil p)))))))))))
def c2691 : List Lit := [(27, false), (1811, false), (123, true), (1776, false), (93, true), (96, true), (30, false), (29, false), (1830, true), (44, true), (26, true)]
theorem step2691 (p : Nat → Bool) (h : Constraints p) : clause p c2691 = true :=
  Snake9.LocalRup.prove_clause [c2234, c1648, c1557, c1539, c2038, c2040, c1755, c84, c1536, c2597, c2515, c1537, c1538, c1520, c1532, c1556, c1642, c2235, c1613, c2278, c1975, c1587, c1588, c2179, c2332, c782] c2691 (by decide) p (sat_cons (step2234 p h) (sat_cons (step1648 p h) (sat_cons (step1557 p h) (sat_cons (step1539 p h) (sat_cons (step2038 p h) (sat_cons (step2040 p h) (sat_cons (step1755 p h) (sat_cons (step84 p h) (sat_cons (step1536 p h) (sat_cons (step2597 p h) (sat_cons (step2515 p h) (sat_cons (step1537 p h) (sat_cons (step1538 p h) (sat_cons (step1520 p h) (sat_cons (step1532 p h) (sat_cons (step1556 p h) (sat_cons (step1642 p h) (sat_cons (step2235 p h) (sat_cons (step1613 p h) (sat_cons (step2278 p h) (sat_cons (step1975 p h) (sat_cons (step1587 p h) (sat_cons (step1588 p h) (sat_cons (step2179 p h) (sat_cons (step2332 p h) (sat_cons (step782 p h) (sat_nil p)))))))))))))))))))))))))))
def c2692 : List Lit := [(1800, false), (103, false), (1811, false), (123, true), (1776, false), (1771, false), (93, true), (1830, true)]
theorem step2692 (p : Nat → Bool) (h : Constraints p) : clause p c2692 = true :=
  Snake9.LocalRup.prove_clause [c1613, c2678, c1642, c1556, c1538, c1987, c1536, c637] c2692 (by decide) p (sat_cons (step1613 p h) (sat_cons (step2678 p h) (sat_cons (step1642 p h) (sat_cons (step1556 p h) (sat_cons (step1538 p h) (sat_cons (step1987 p h) (sat_cons (step1536 p h) (sat_cons (step637 p h) (sat_nil p)))))))))
def c2693 : List Lit := [(1783, true), (1811, true)]
theorem step2693 (p : Nat → Bool) (h : Constraints p) : clause p c2693 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1540, c2391] c2693 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step2391 p h) (sat_nil p))))
def c2694 : List Lit := [(1827, true), (1775, false), (1816, false)]
theorem step2694 (p : Nat → Bool) (h : Constraints p) : clause p c2694 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1628, c1633, c2234, c1551, c2693] c2694 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1628 p h) (sat_cons (step1633 p h) (sat_cons (step2234 p h) (sat_cons (step1551 p h) (sat_cons (step2693 p h) (sat_nil p)))))))
def c2695 : List Lit := [(27, false), (1773, true), (44, true), (26, true)]
theorem step2695 (p : Nat → Bool) (h : Constraints p) : clause p c2695 = true :=
  Snake9.LocalRup.prove_clause [c2038, c1892] c2695 (by decide) p (sat_cons (step2038 p h) (sat_cons (step1892 p h) (sat_nil p)))
def c2696 : List Lit := [(1783, true), (100, false), (93, true)]
theorem step2696 (p : Nat → Bool) (h : Constraints p) : clause p c2696 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1540, c1987, c1536, c1533, c637] c2696 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step1987 p h) (sat_cons (step1536 p h) (sat_cons (step1533 p h) (sat_cons (step637 p h) (sat_nil p)))))))
def c2697 : List Lit := [(1776, true), (91, false), (96, true), (89, true)]
theorem step2697 (p : Nat → Bool) (h : Constraints p) : clause p c2697 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1529, c1527, c1520, c1521, c1522, c435, c588, c2121] c2697 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1529 p h) (sat_cons (step1527 p h) (sat_cons (step1520 p h) (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step435 p h) (sat_cons (step588 p h) (sat_cons (step2121 p h) (sat_nil p))))))))))
def c2698 : List Lit := [(35, false), (1801, true), (91, false), (44, true)]
theorem step2698 (p : Nat → Bool) (h : Constraints p) : clause p c2698 = true :=
  Snake9.LocalRup.prove_clause [c2044, c729, c2281, c1573, c1582] c2698 (by decide) p (sat_cons (step2044 p h) (sat_cons (step729 p h) (sat_cons (step2281 p h) (sat_cons (step1573 p h) (sat_cons (step1582 p h) (sat_nil p))))))
def c2699 : List Lit := [(36, false), (39, false), (46, false), (3, false)]
theorem step2699 (p : Nat → Bool) (h : Constraints p) : clause p c2699 = true :=
  Snake9.LocalRup.prove_clause [c117, c115, c2047] c2699 (by decide) p (sat_cons (step117 p h) (sat_cons (step115 p h) (sat_cons (step2047 p h) (sat_nil p))))
def c2700 : List Lit := [(1721, true), (1737, true), (68, false), (80, false), (87, true), (7, false)]
theorem step2700 (p : Nat → Bool) (h : Constraints p) : clause p c2700 = true :=
  Snake9.LocalRup.prove_clause [c2635, c1895, c1395, c1424, c1429, c1955, c1383, c1385, c1393, c2357] c2700 (by decide) p (sat_cons (step2635 p h) (sat_cons (step1895 p h) (sat_cons (step1395 p h) (sat_cons (step1424 p h) (sat_cons (step1429 p h) (sat_cons (step1955 p h) (sat_cons (step1383 p h) (sat_cons (step1385 p h) (sat_cons (step1393 p h) (sat_cons (step2357 p h) (sat_nil p)))))))))))
def c2701 : List Lit := [(1783, true), (65, false), (93, true)]
theorem step2701 (p : Nat → Bool) (h : Constraints p) : clause p c2701 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1540, c1987, c1536, c1533, c628] c2701 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step1987 p h) (sat_cons (step1536 p h) (sat_cons (step1533 p h) (sat_cons (step628 p h) (sat_nil p)))))))
def c2702 : List Lit := [(1789, true), (46, false), (1813, true), (1776, false), (123, true), (1771, false), (93, true)]
theorem step2702 (p : Nat → Bool) (h : Constraints p) : clause p c2702 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1556, c1528, c1538, c1540, c2696, c1536, c1532, c1533, c1523, c2415, c2276] c2702 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1556 p h) (sat_cons (step1528 p h) (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step2696 p h) (sat_cons (step1536 p h) (sat_cons (step1532 p h) (sat_cons (step1533 p h) (sat_cons (step1523 p h) (sat_cons (step2415 p h) (sat_cons (step2276 p h) (sat_nil p)))))))))))))
def c2703 : List Lit := [(109, true), (30, false), (1784, true), (1776, false), (123, true), (1830, true)]
theorem step2703 (p : Nat → Bool) (h : Constraints p) : clause p c2703 = true :=
  Snake9.LocalRup.prove_clause [c1539, c1535, c1537, c1538, c1541, c1556, c1532, c2623, c1642, c653, c2141, c2235, c2278] c2703 (by decide) p (sat_cons (step1539 p h) (sat_cons (step1535 p h) (sat_cons (step1537 p h) (sat_cons (step1538 p h) (sat_cons (step1541 p h) (sat_cons (step1556 p h) (sat_cons (step1532 p h) (sat_cons (step2623 p h) (sat_cons (step1642 p h) (sat_cons (step653 p h) (sat_cons (step2141 p h) (sat_cons (step2235 p h) (sat_cons (step2278 p h) (sat_nil p))))))))))))))
def c2704 : List Lit := [(92, false), (109, false), (93, true), (88, false)]
theorem step2704 (p : Nat → Bool) (h : Constraints p) : clause p c2704 = true :=
  Snake9.LocalRup.prove_clause [c2124, c372] c2704 (by decide) p (sat_cons (step2124 p h) (sat_cons (step372 p h) (sat_nil p)))
def c2705 : List Lit := [(1783, true), (226, true), (93, true)]
theorem step2705 (p : Nat → Bool) (h : Constraints p) : clause p c2705 = true :=
  Snake9.LocalRup.prove_clause [c1538, c1540, c2696, c1536, c1533, c2623, c541, c2140] c2705 (by decide) p (sat_cons (step1538 p h) (sat_cons (step1540 p h) (sat_cons (step2696 p h) (sat_cons (step1536 p h) (sat_cons (step1533 p h) (sat_cons (step2623 p h) (sat_cons (step541 p h) (sat_cons (step2140 p h) (sat_nil p)))))))))
def c2706 : List Lit := [(92, false), (1784, true), (1790, true), (93, true), (96, true), (88, false)]
theorem step2706 (p : Nat → Bool) (h : Constraints p) : clause p c2706 = true :=
  Snake9.LocalRup.prove_clause [c1539, c2122, c2704, c1535, c1537, c1538, c1541, c1561, c1532, c1533, c2623, c493, c2138, c1520, c637, c1530, c1522] c2706 (by decide) p (sat_cons (step1539 p h) (sat_cons (step2122 p h) (sat_cons (step2704 p h) (sat_cons (step1535 p h) (sat_cons (step1537 p h) (sat_cons (step1538 p h) (sat_cons (step1541 p h) (sat_cons (step1561 p h) (sat_cons (step1532 p h) (sat_cons (step1533 p h) (sat_cons (step2623 p h) (sat_cons (step493 p h) (sat_cons (step2138 p h) (sat_cons (step1520 p h) (sat_cons (step637 p h) (sat_cons (step1530 p h) (sat_cons (step1522 p h) (sat_nil p))))))))))))))))))
def c2707 : List Lit := [(1776, true), (123, false), (96, true), (88, false)]
theorem step2707 (p : Nat → Bool) (h : Constraints p) : clause p c2707 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1529, c1527, c1520, c1521, c1522, c2263, c434, c543, c2136] c2707 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1529 p h) (sat_cons (step1527 p h) (sat_cons (step1520 p h) (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step2263 p h) (sat_cons (step434 p h) (sat_cons (step543 p h) (sat_cons (step2136 p h) (sat_nil p)))))))))))
def c2708 : List Lit := [(1646, true), (65, false), (93, true)]
theorem step2708 (p : Nat → Bool) (h : Constraints p) : clause p c2708 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1240, c1235, c1991, c1232, c1985] c2708 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1235 p h) (sat_cons (step1991 p h) (sat_cons (step1232 p h) (sat_cons (step1985 p h) (sat_nil p)))))))
def c2709 : List Lit := [(1659, true), (1652, false), (93, true)]
theorem step2709 (p : Nat → Bool) (h : Constraints p) : clause p c2709 = true :=
  Snake9.LocalRup.prove_clause [c1252, c1261, c1265, c1255, c1238, c1240, c1247, c1235, c1236, c1232, c200, c1985] c2709 (by decide) p (sat_cons (step1252 p h) (sat_cons (step1261 p h) (sat_cons (step1265 p h) (sat_cons (step1255 p h) (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1247 p h) (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step1232 p h) (sat_cons (step200 p h) (sat_cons (step1985 p h) (sat_nil p)))))))))))))
def c2710 : List Lit := [(1588, false), (1623, false), (1692, true), (46, false), (1659, false), (1618, false), (1586, false), (7, false)]
theorem step2710 (p : Nat → Bool) (h : Constraints p) : clause p c2710 = true :=
  Snake9.LocalRup.prove_clause [c1194, c1963, c1291, c1349, c1144, c1868, c2202, c1341, c1298, c1223, c2562, c1208, c1201] c2710 (by decide) p (sat_cons (step1194 p h) (sat_cons (step1963 p h) (sat_cons (step1291 p h) (sat_cons (step1349 p h) (sat_cons (step1144 p h) (sat_cons (step1868 p h) (sat_cons (step2202 p h) (sat_cons (step1341 p h) (sat_cons (step1298 p h) (sat_cons (step1223 p h) (sat_cons (step2562 p h) (sat_cons (step1208 p h) (sat_cons (step1201 p h) (sat_nil p))))))))))))))
def c2711 : List Lit := [(27, false), (1792, true), (102, false), (109, true), (94, false), (91, false), (92, false), (96, true)]
theorem step2711 (p : Nat → Bool) (h : Constraints p) : clause p c2711 = true :=
  Snake9.LocalRup.prove_clause [c1519, c570, c568, c569, c1537, c1523, c1539, c1528, c1567, c1563, c1531, c1542, c1520, c1532, c493] c2711 (by decide) p (sat_cons (step1519 p h) (sat_cons (step570 p h) (sat_cons (step568 p h) (sat_cons (step569 p h) (sat_cons (step1537 p h) (sat_cons (step1523 p h) (sat_cons (step1539 p h) (sat_cons (step1528 p h) (sat_cons (step1567 p h) (sat_cons (step1563 p h) (sat_cons (step1531 p h) (sat_cons (step1542 p h) (sat_cons (step1520 p h) (sat_cons (step1532 p h) (sat_cons (step493 p h) (sat_nil p))))))))))))))))
end B112E050
