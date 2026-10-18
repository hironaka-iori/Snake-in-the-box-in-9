import B112E008Part0000
namespace B112E008
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1671 : List Lit := [(42, false), (45, false), (35, false), (38, false), (57, false)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c770, c242, c252, c211, c267] c1671 (by decide) p (sat_cons (step770 p h) (sat_cons (step242 p h) (sat_cons (step252 p h) (sat_cons (step211 p h) (sat_cons (step267 p h) (sat_nil p))))))
def c1672 : List Lit := [(40, false), (39, true), (1590, true), (58, true)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c769, c1173, c1172, c250, c300] c1672 (by decide) p (sat_cons (step769 p h) (sat_cons (step1173 p h) (sat_cons (step1172 p h) (sat_cons (step250 p h) (sat_cons (step300 p h) (sat_nil p))))))
def c1673 : List Lit := [(69, false), (46, false), (1590, true)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c773, c1173, c1172, c317, c319, c297] c1673 (by decide) p (sat_cons (step773 p h) (sat_cons (step1173 p h) (sat_cons (step1172 p h) (sat_cons (step317 p h) (sat_cons (step319 p h) (sat_cons (step297 p h) (sat_nil p)))))))
def c1674 : List Lit := [(89, false), (1713, true)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c792, c1386, c1384, c1388, c1380, c1381, c578, c1383, c504, c532, c522] c1674 (by decide) p (sat_cons (step792 p h) (sat_cons (step1386 p h) (sat_cons (step1384 p h) (sat_cons (step1388 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step578 p h) (sat_cons (step1383 p h) (sat_cons (step504 p h) (sat_cons (step532 p h) (sat_cons (step522 p h) (sat_nil p))))))))))))
def c1675 : List Lit := [(1713, true), (1687, true)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c792, c1341, c1333, c1386, c1388, c1383, c1384, c1380, c1381, c578, c1674, c1329, c1331, c1332, c501, c1344, c522, c1322, c529, c1317] c1675 (by decide) p (sat_cons (step792 p h) (sat_cons (step1341 p h) (sat_cons (step1333 p h) (sat_cons (step1386 p h) (sat_cons (step1388 p h) (sat_cons (step1383 p h) (sat_cons (step1384 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step578 p h) (sat_cons (step1674 p h) (sat_cons (step1329 p h) (sat_cons (step1331 p h) (sat_cons (step1332 p h) (sat_cons (step501 p h) (sat_cons (step1344 p h) (sat_cons (step522 p h) (sat_cons (step1322 p h) (sat_cons (step529 p h) (sat_cons (step1317 p h) (sat_nil p)))))))))))))))))))))
def c1676 : List Lit := [(1698, true), (1654, false), (68, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c1657, c783, c1313, c1374, c1369, c1314, c1340, c1343, c1300, c1332, c1334, c1322, c1298, c1329, c1330, c1327, c1316, c408, c432, c488, c414] c1676 (by decide) p (sat_cons (step1657 p h) (sat_cons (step783 p h) (sat_cons (step1313 p h) (sat_cons (step1374 p h) (sat_cons (step1369 p h) (sat_cons (step1314 p h) (sat_cons (step1340 p h) (sat_cons (step1343 p h) (sat_cons (step1300 p h) (sat_cons (step1332 p h) (sat_cons (step1334 p h) (sat_cons (step1322 p h) (sat_cons (step1298 p h) (sat_cons (step1329 p h) (sat_cons (step1330 p h) (sat_cons (step1327 p h) (sat_cons (step1316 p h) (sat_cons (step408 p h) (sat_cons (step432 p h) (sat_cons (step488 p h) (sat_cons (step414 p h) (sat_nil p))))))))))))))))))))))
def c1677 : List Lit := [(71, false), (82, false), (74, false), (86, false), (87, true)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c783, c408, c432, c414] c1677 (by decide) p (sat_cons (step783 p h) (sat_cons (step408 p h) (sat_cons (step432 p h) (sat_cons (step414 p h) (sat_nil p)))))
def c1678 : List Lit := [(47, true), (48, false), (51, false)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c773, c298, c299, c1577] c1678 (by decide) p (sat_cons (step773 p h) (sat_cons (step298 p h) (sat_cons (step299 p h) (sat_cons (step1577 p h) (sat_nil p)))))
def c1679 : List Lit := [(1714, true), (94, true), (98, true), (89, false)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c794, c1380, c1391, c1389, c1382, c1383, c504, c621] c1679 (by decide) p (sat_cons (step794 p h) (sat_cons (step1380 p h) (sat_cons (step1391 p h) (sat_cons (step1389 p h) (sat_cons (step1382 p h) (sat_cons (step1383 p h) (sat_cons (step504 p h) (sat_cons (step621 p h) (sat_nil p)))))))))
def c1680 : List Lit := [(99, false), (98, true), (86, false), (89, false)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c794, c499, c621] c1680 (by decide) p (sat_cons (step794 p h) (sat_cons (step499 p h) (sat_cons (step621 p h) (sat_nil p))))
def c1681 : List Lit := [(1738, true), (87, true), (107, true), (86, false)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c799, c1432, c1442, c1440, c1433, c1434, c709, c702] c1681 (by decide) p (sat_cons (step799 p h) (sat_cons (step1432 p h) (sat_cons (step1442 p h) (sat_cons (step1440 p h) (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step709 p h) (sat_cons (step702 p h) (sat_nil p)))))))))
def c1682 : List Lit := [(1743, true), (123, false), (105, false)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c1448, c1449, c747] c1682 (by decide) p (sat_cons (step1448 p h) (sat_cons (step1449 p h) (sat_cons (step747 p h) (sat_nil p))))
def c1683 : List Lit := [(79, false), (1515, true), (91, true), (85, false), (1674, true), (102, false)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c784, c1032, c1322, c1317, c1321, c1319, c442, c441, c422, c1029, c1030, c29, c1034, c1026] c1683 (by decide) p (sat_cons (step784 p h) (sat_cons (step1032 p h) (sat_cons (step1322 p h) (sat_cons (step1317 p h) (sat_cons (step1321 p h) (sat_cons (step1319 p h) (sat_cons (step442 p h) (sat_cons (step441 p h) (sat_cons (step422 p h) (sat_cons (step1029 p h) (sat_cons (step1030 p h) (sat_cons (step29 p h) (sat_cons (step1034 p h) (sat_cons (step1026 p h) (sat_nil p)))))))))))))))
def c1684 : List Lit := [(1525, true), (15, false), (83, false)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c1053, c1054, c85] c1684 (by decide) p (sat_cons (step1053 p h) (sat_cons (step1054 p h) (sat_cons (step85 p h) (sat_nil p))))
def c1685 : List Lit := [(1543, true), (1525, false)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c1061, c1654, c1062, c1077, c1056, c1652, c1610, c1069] c1685 (by decide) p (sat_cons (step1061 p h) (sat_cons (step1654 p h) (sat_cons (step1062 p h) (sat_cons (step1077 p h) (sat_cons (step1056 p h) (sat_cons (step1652 p h) (sat_cons (step1610 p h) (sat_cons (step1069 p h) (sat_nil p)))))))))
def c1686 : List Lit := [(68, false), (1666, true), (69, false), (51, false), (1657, false)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c782, c1659, c405, c406, c1291, c1311, c1302, c1293, c1294, c402] c1686 (by decide) p (sat_cons (step782 p h) (sat_cons (step1659 p h) (sat_cons (step405 p h) (sat_cons (step406 p h) (sat_cons (step1291 p h) (sat_cons (step1311 p h) (sat_cons (step1302 p h) (sat_cons (step1293 p h) (sat_cons (step1294 p h) (sat_cons (step402 p h) (sat_nil p)))))))))))
def c1687 : List Lit := [(1617, true), (40, true), (33, true), (100, false), (1590, false), (38, true), (1600, false)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c1663, c772, c1122, c1124, c1132, c1136, c1141, c1152, c1199, c1236, c1231, c1153, c1157, c1204, c1144, c1142, c1125, c1178, c1134, c1137, c1123, c1169, c211, c269, c279] c1687 (by decide) p (sat_cons (step1663 p h) (sat_cons (step772 p h) (sat_cons (step1122 p h) (sat_cons (step1124 p h) (sat_cons (step1132 p h) (sat_cons (step1136 p h) (sat_cons (step1141 p h) (sat_cons (step1152 p h) (sat_cons (step1199 p h) (sat_cons (step1236 p h) (sat_cons (step1231 p h) (sat_cons (step1153 p h) (sat_cons (step1157 p h) (sat_cons (step1204 p h) (sat_cons (step1144 p h) (sat_cons (step1142 p h) (sat_cons (step1125 p h) (sat_cons (step1178 p h) (sat_cons (step1134 p h) (sat_cons (step1137 p h) (sat_cons (step1123 p h) (sat_cons (step1169 p h) (sat_cons (step211 p h) (sat_cons (step269 p h) (sat_cons (step279 p h) (sat_nil p))))))))))))))))))))))))))
def c1688 : List Lit := [(1743, true), (105, false), (104, true)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c805, c1448, c1682, c745] c1688 (by decide) p (sat_cons (step805 p h) (sat_cons (step1448 p h) (sat_cons (step1682 p h) (sat_cons (step745 p h) (sat_nil p)))))
def c1689 : List Lit := [(101, true), (91, true), (86, false), (93, true), (89, false)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c791, c514, c515, c1588] c1689 (by decide) p (sat_cons (step791 p h) (sat_cons (step514 p h) (sat_cons (step515 p h) (sat_cons (step1588 p h) (sat_nil p)))))
def c1690 : List Lit := [(97, false), (95, true), (91, true), (51, false), (93, true), (105, false)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c793, c696, c607] c1690 (by decide) p (sat_cons (step793 p h) (sat_cons (step696 p h) (sat_cons (step607 p h) (sat_nil p))))
def c1691 : List Lit := [(1576, true), (39, false), (40, false)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c1138, c1140, c1135, c1132, c240] c1691 (by decide) p (sat_cons (step1138 p h) (sat_cons (step1140 p h) (sat_cons (step1135 p h) (sat_cons (step1132 p h) (sat_cons (step240 p h) (sat_nil p))))))
def c1692 : List Lit := [(60, false), (1597, true), (69, false), (58, false), (40, false)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c775, c364, c384, c382, c1185, c340] c1692 (by decide) p (sat_cons (step775 p h) (sat_cons (step364 p h) (sat_cons (step384 p h) (sat_cons (step382 p h) (sat_cons (step1185 p h) (sat_cons (step340 p h) (sat_nil p)))))))
def c1693 : List Lit := [(1721, true), (74, false), (66, false), (105, false), (38, false)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c797, c1400, c1402, c1398, c1394, c1395, c538, c294, c666, c617, c655] c1693 (by decide) p (sat_cons (step797 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1398 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step538 p h) (sat_cons (step294 p h) (sat_cons (step666 p h) (sat_cons (step617 p h) (sat_cons (step655 p h) (sat_nil p))))))))))))
def c1694 : List Lit := [(1749, true), (56, false), (105, false)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c804, c1456, c1458, c1451, c1437, c1449, c1682, c1434, c721, c744] c1694 (by decide) p (sat_cons (step804 p h) (sat_cons (step1456 p h) (sat_cons (step1458 p h) (sat_cons (step1451 p h) (sat_cons (step1437 p h) (sat_cons (step1449 p h) (sat_cons (step1682 p h) (sat_cons (step1434 p h) (sat_cons (step721 p h) (sat_cons (step744 p h) (sat_nil p)))))))))))
def c1695 : List Lit := [(110, false), (233, true), (114, true), (113, true)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c799, c708, c707, c705, c1590] c1695 (by decide) p (sat_cons (step799 p h) (sat_cons (step708 p h) (sat_cons (step707 p h) (sat_cons (step705 p h) (sat_cons (step1590 p h) (sat_nil p))))))
def c1696 : List Lit := [(1687, true), (1672, false), (41, true), (35, false), (38, false), (39, true)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c768, c1321, c1347, c1344, c1323, c1332, c1316, c1330, c536, c155, c222] c1696 (by decide) p (sat_cons (step768 p h) (sat_cons (step1321 p h) (sat_cons (step1347 p h) (sat_cons (step1344 p h) (sat_cons (step1323 p h) (sat_cons (step1332 p h) (sat_cons (step1316 p h) (sat_cons (step1330 p h) (sat_cons (step536 p h) (sat_cons (step155 p h) (sat_cons (step222 p h) (sat_nil p))))))))))))
def c1697 : List Lit := [(1593, true), (45, true), (40, false)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c773, c1169, c1180, c1178, c1171, c1172, c1173, c306, c300, c297] c1697 (by decide) p (sat_cons (step773 p h) (sat_cons (step1169 p h) (sat_cons (step1180 p h) (sat_cons (step1178 p h) (sat_cons (step1171 p h) (sat_cons (step1172 p h) (sat_cons (step1173 p h) (sat_cons (step306 p h) (sat_cons (step300 p h) (sat_cons (step297 p h) (sat_nil p)))))))))))
def c1698 : List Lit := [(1552, true), (1505, false), (1542, false)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c753, c1020, c1041, c1091, c1096, c1685, c1045, c1042, c1053, c1023, c1031, c1033, c1028, c1026, c94, c49, c24] c1698 (by decide) p (sat_cons (step753 p h) (sat_cons (step1020 p h) (sat_cons (step1041 p h) (sat_cons (step1091 p h) (sat_cons (step1096 p h) (sat_cons (step1685 p h) (sat_cons (step1045 p h) (sat_cons (step1042 p h) (sat_cons (step1053 p h) (sat_cons (step1023 p h) (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1028 p h) (sat_cons (step1026 p h) (sat_cons (step94 p h) (sat_cons (step49 p h) (sat_cons (step24 p h) (sat_nil p))))))))))))))))))
def c1699 : List Lit := [(1519, true), (1505, false), (51, false)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c753, c1020, c1045, c1042, c1023, c1031, c1033, c1028, c1026, c95, c49, c24] c1699 (by decide) p (sat_cons (step753 p h) (sat_cons (step1020 p h) (sat_cons (step1045 p h) (sat_cons (step1042 p h) (sat_cons (step1023 p h) (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1028 p h) (sat_cons (step1026 p h) (sat_cons (step95 p h) (sat_cons (step49 p h) (sat_cons (step24 p h) (sat_nil p)))))))))))))
def c1700 : List Lit := [(58, false), (56, false), (40, false), (1601, true)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c362, c365, c1184, c1186, c1192] c1700 (by decide) p (sat_cons (step362 p h) (sat_cons (step365 p h) (sat_cons (step1184 p h) (sat_cons (step1186 p h) (sat_cons (step1192 p h) (sat_nil p))))))
def c1701 : List Lit := [(60, false), (53, false), (54, false), (58, true), (56, false)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c778, c377, c346, c388] c1701 (by decide) p (sat_cons (step778 p h) (sat_cons (step377 p h) (sat_cons (step346 p h) (sat_cons (step388 p h) (sat_nil p)))))
def c1702 : List Lit := [(1538, false), (1556, true), (1531, false), (1528, false), (1506, false)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c754, c753, c1021, c1045, c1100, c1083, c1086, c1105, c1066, c1049, c1046, c1024, c1031, c1033, c1028, c1029, c1025, c1026, c57, c24, c54, c49, c51, c94, c1055] c1702 (by decide) p (sat_cons (step754 p h) (sat_cons (step753 p h) (sat_cons (step1021 p h) (sat_cons (step1045 p h) (sat_cons (step1100 p h) (sat_cons (step1083 p h) (sat_cons (step1086 p h) (sat_cons (step1105 p h) (sat_cons (step1066 p h) (sat_cons (step1049 p h) (sat_cons (step1046 p h) (sat_cons (step1024 p h) (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1028 p h) (sat_cons (step1029 p h) (sat_cons (step1025 p h) (sat_cons (step1026 p h) (sat_cons (step57 p h) (sat_cons (step24 p h) (sat_cons (step54 p h) (sat_cons (step49 p h) (sat_cons (step51 p h) (sat_cons (step94 p h) (sat_cons (step1055 p h) (sat_nil p))))))))))))))))))))))))))
def c1703 : List Lit := [(1738, true), (112, true), (114, false), (56, false)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1438, c1440, c1436, c1431, c719] c1703 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1438 p h) (sat_cons (step1440 p h) (sat_cons (step1436 p h) (sat_cons (step1431 p h) (sat_cons (step719 p h) (sat_nil p)))))))
def c1704 : List Lit := [(1751, true), (112, true), (114, false), (56, false)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c1703, c1464, c1462, c1451, c1449, c720, c721, c1431, c1436, c1441] c1704 (by decide) p (sat_cons (step1703 p h) (sat_cons (step1464 p h) (sat_cons (step1462 p h) (sat_cons (step1451 p h) (sat_cons (step1449 p h) (sat_cons (step720 p h) (sat_cons (step721 p h) (sat_cons (step1431 p h) (sat_cons (step1436 p h) (sat_cons (step1441 p h) (sat_nil p)))))))))))
def c1705 : List Lit := [(1554, true), (1530, false), (1543, false), (1508, false)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c1045, c1098, c1103, c1080, c1046, c1652, c1031, c1069, c1028, c1609] c1705 (by decide) p (sat_cons (step1045 p h) (sat_cons (step1098 p h) (sat_cons (step1103 p h) (sat_cons (step1080 p h) (sat_cons (step1046 p h) (sat_cons (step1652 p h) (sat_cons (step1031 p h) (sat_cons (step1069 p h) (sat_cons (step1028 p h) (sat_cons (step1609 p h) (sat_nil p)))))))))))
def c1706 : List Lit := [(1565, false), (1571, true), (1584, true), (34, true), (38, true), (36, false), (54, false)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c1121, c1130, c1131, c1162, c1123, c1143, c196, c1134] c1706 (by decide) p (sat_cons (step1121 p h) (sat_cons (step1130 p h) (sat_cons (step1131 p h) (sat_cons (step1162 p h) (sat_cons (step1123 p h) (sat_cons (step1143 p h) (sat_cons (step196 p h) (sat_cons (step1134 p h) (sat_nil p)))))))))
def c1707 : List Lit := [(1528, false), (1555, true), (1556, true), (1525, false), (1506, false)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c1021, c1063, c1655, c1702, c1104, c1652, c1046, c1069, c1031, c1609, c1028] c1707 (by decide) p (sat_cons (step1021 p h) (sat_cons (step1063 p h) (sat_cons (step1655 p h) (sat_cons (step1702 p h) (sat_cons (step1104 p h) (sat_cons (step1652 p h) (sat_cons (step1046 p h) (sat_cons (step1069 p h) (sat_cons (step1031 p h) (sat_cons (step1609 p h) (sat_cons (step1028 p h) (sat_nil p))))))))))))
def c1708 : List Lit := [(18, true), (1525, true)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c757, c1054, c1053, c92, c91, c1560] c1708 (by decide) p (sat_cons (step757 p h) (sat_cons (step1054 p h) (sat_cons (step1053 p h) (sat_cons (step92 p h) (sat_cons (step91 p h) (sat_cons (step1560 p h) (sat_nil p)))))))
def c1709 : List Lit := [(154, false), (13, true), (28, true), (20, true)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c1648, c1636, c762, c840, c841, c842, c144, c847, c127, c837, c1611, c836] c1709 (by decide) p (sat_cons (step1648 p h) (sat_cons (step1636 p h) (sat_cons (step762 p h) (sat_cons (step840 p h) (sat_cons (step841 p h) (sat_cons (step842 p h) (sat_cons (step144 p h) (sat_cons (step847 p h) (sat_cons (step127 p h) (sat_cons (step837 p h) (sat_cons (step1611 p h) (sat_cons (step836 p h) (sat_nil p)))))))))))))
def c1710 : List Lit := [(29, false), (30, true), (14, false), (17, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c764, c84, c140] c1710 (by decide) p (sat_cons (step764 p h) (sat_cons (step84 p h) (sat_cons (step140 p h) (sat_nil p))))
def c1711 : List Lit := [(1515, true), (13, true), (14, false), (17, false)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c755, c1028, c1032, c1034, c1030, c1025, c88, c51, c63] c1711 (by decide) p (sat_cons (step755 p h) (sat_cons (step1028 p h) (sat_cons (step1032 p h) (sat_cons (step1034 p h) (sat_cons (step1030 p h) (sat_cons (step1025 p h) (sat_cons (step88 p h) (sat_cons (step51 p h) (sat_cons (step63 p h) (sat_nil p))))))))))
def c1712 : List Lit := [(89, false), (1682, false), (1781, true), (1665, false), (1751, false)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c797, c1340, c1363, c1514, c1479, c1417, c1674, c1412, c1413, c1473, c1400, c1402, c1520, c1397, c1398, c1394, c1395, c1364, c666, c617, c1344, c1679, c1322, c686, c1316, c652, c548] c1712 (by decide) p (sat_cons (step797 p h) (sat_cons (step1340 p h) (sat_cons (step1363 p h) (sat_cons (step1514 p h) (sat_cons (step1479 p h) (sat_cons (step1417 p h) (sat_cons (step1674 p h) (sat_cons (step1412 p h) (sat_cons (step1413 p h) (sat_cons (step1473 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1520 p h) (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step1364 p h) (sat_cons (step666 p h) (sat_cons (step617 p h) (sat_cons (step1344 p h) (sat_cons (step1679 p h) (sat_cons (step1322 p h) (sat_cons (step686 p h) (sat_cons (step1316 p h) (sat_cons (step652 p h) (sat_cons (step548 p h) (sat_nil p))))))))))))))))))))))))))))
def c1713 : List Lit := [(1678, true), (104, true), (105, false), (15, true)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c789, c1326, c1327, c457, c454] c1713 (by decide) p (sat_cons (step789 p h) (sat_cons (step1326 p h) (sat_cons (step1327 p h) (sat_cons (step457 p h) (sat_cons (step454 p h) (sat_nil p))))))
def c1714 : List Lit := [(1721, false), (1726, true), (1781, true), (1665, false), (1751, false)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1413, c1473, c1675, c1520, c1364] c1714 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1413 p h) (sat_cons (step1473 p h) (sat_cons (step1675 p h) (sat_cons (step1520 p h) (sat_cons (step1364 p h) (sat_nil p)))))))
def c1715 : List Lit := [(1521, true), (1512, false), (6, true), (11, true), (4, true), (8, true)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c750, c1026, c1034, c1017, c1020, c1044, c1047, c1037, c1021, c1023, c1027, c1019, c21, c1] c1715 (by decide) p (sat_cons (step750 p h) (sat_cons (step1026 p h) (sat_cons (step1034 p h) (sat_cons (step1017 p h) (sat_cons (step1020 p h) (sat_cons (step1044 p h) (sat_cons (step1047 p h) (sat_cons (step1037 p h) (sat_cons (step1021 p h) (sat_cons (step1023 p h) (sat_cons (step1027 p h) (sat_cons (step1019 p h) (sat_cons (step21 p h) (sat_cons (step1 p h) (sat_nil p)))))))))))))))
def c1716 : List Lit := [(1583, true), (38, true), (34, true), (36, false), (54, false), (1564, false)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c1132, c1140, c1121, c1127, c1161, c1157, c1128, c1143, c1123, c1134, c196] c1716 (by decide) p (sat_cons (step1132 p h) (sat_cons (step1140 p h) (sat_cons (step1121 p h) (sat_cons (step1127 p h) (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step1128 p h) (sat_cons (step1143 p h) (sat_cons (step1123 p h) (sat_cons (step1134 p h) (sat_cons (step196 p h) (sat_nil p))))))))))))
def c1717 : List Lit := [(3, false), (5, false), (33, false), (11, true), (4, true)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c750, c21, c2] c1717 (by decide) p (sat_cons (step750 p h) (sat_cons (step21 p h) (sat_cons (step2 p h) (sat_nil p))))
def c1718 : List Lit := [(1749, true), (87, true), (56, false)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c799, c1456, c1458, c1451, c1437, c1439, c1449, c1434, c1431, c721, c708] c1718 (by decide) p (sat_cons (step799 p h) (sat_cons (step1456 p h) (sat_cons (step1458 p h) (sat_cons (step1451 p h) (sat_cons (step1437 p h) (sat_cons (step1439 p h) (sat_cons (step1449 p h) (sat_cons (step1434 p h) (sat_cons (step1431 p h) (sat_cons (step721 p h) (sat_cons (step708 p h) (sat_nil p))))))))))))
def c1719 : List Lit := [(60, false), (1751, true), (54, false), (56, false), (40, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c778, c776, c366, c377, c388, c351, c349, c1704] c1719 (by decide) p (sat_cons (step778 p h) (sat_cons (step776 p h) (sat_cons (step366 p h) (sat_cons (step377 p h) (sat_cons (step388 p h) (sat_cons (step351 p h) (sat_cons (step349 p h) (sat_cons (step1704 p h) (sat_nil p)))))))))
def c1720 : List Lit := [(21, false), (5, false), (56, false)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c760, c106, c108] c1720 (by decide) p (sat_cons (step760 p h) (sat_cons (step106 p h) (sat_cons (step108 p h) (sat_nil p))))
def c1721 : List Lit := [(1544, true), (23, false), (29, false), (13, false)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c1609, c1069, c1652, c1608, c1056, c1059, c1078, c1080, c1073, c1060, c1650, c1058, c119] c1721 (by decide) p (sat_cons (step1609 p h) (sat_cons (step1069 p h) (sat_cons (step1652 p h) (sat_cons (step1608 p h) (sat_cons (step1056 p h) (sat_cons (step1059 p h) (sat_cons (step1078 p h) (sat_cons (step1080 p h) (sat_cons (step1073 p h) (sat_cons (step1060 p h) (sat_cons (step1650 p h) (sat_cons (step1058 p h) (sat_cons (step119 p h) (sat_nil p))))))))))))))
def c1722 : List Lit := [(21, false), (19, false), (6, false)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c760, c105, c113] c1722 (by decide) p (sat_cons (step760 p h) (sat_cons (step105 p h) (sat_cons (step113 p h) (sat_nil p))))
def c1723 : List Lit := [(1515, true), (11, true), (8, true), (14, false)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c754, c1026, c1036, c1034, c1027, c1029, c54, c51] c1723 (by decide) p (sat_cons (step754 p h) (sat_cons (step1026 p h) (sat_cons (step1036 p h) (sat_cons (step1034 p h) (sat_cons (step1027 p h) (sat_cons (step1029 p h) (sat_cons (step54 p h) (sat_cons (step51 p h) (sat_nil p)))))))))
def c1724 : List Lit := [(39, true), (19, false), (15, true), (6, false)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c752, c41, c43, c1554] c1724 (by decide) p (sat_cons (step752 p h) (sat_cons (step41 p h) (sat_cons (step43 p h) (sat_cons (step1554 p h) (sat_nil p)))))
def c1725 : List Lit := [(29, true), (31, true), (154, true), (1565, true)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c763, c1120, c142, c135] c1725 (by decide) p (sat_cons (step763 p h) (sat_cons (step1120 p h) (sat_cons (step142 p h) (sat_cons (step135 p h) (sat_nil p)))))
def c1726 : List Lit := [(30, true), (29, false), (6, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c764, c140, c139, c1557] c1726 (by decide) p (sat_cons (step764 p h) (sat_cons (step140 p h) (sat_cons (step139 p h) (sat_cons (step1557 p h) (sat_nil p)))))
def c1727 : List Lit := [(1531, true), (17, true), (20, true), (29, false), (6, false)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c764, c1053, c1056, c1065, c1063, c1055, c1058, c79, c114, c141] c1727 (by decide) p (sat_cons (step764 p h) (sat_cons (step1053 p h) (sat_cons (step1056 p h) (sat_cons (step1065 p h) (sat_cons (step1063 p h) (sat_cons (step1055 p h) (sat_cons (step1058 p h) (sat_cons (step79 p h) (sat_cons (step114 p h) (sat_cons (step141 p h) (sat_nil p)))))))))))
def c1728 : List Lit := [(21, false), (29, false), (6, false)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c760, c105, c116] c1728 (by decide) p (sat_cons (step760 p h) (sat_cons (step105 p h) (sat_cons (step116 p h) (sat_nil p))))
def c1729 : List Lit := [(71, false), (1681, true), (87, false), (33, false)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c474, c473, c1331] c1729 (by decide) p (sat_cons (step474 p h) (sat_cons (step473 p h) (sat_cons (step1331 p h) (sat_nil p))))
def c1730 : List Lit := [(1725, true), (87, true)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c794, c1408, c1412, c1400, c1402, c1386, c1398, c1394, c1383, c616, c621] c1730 (by decide) p (sat_cons (step794 p h) (sat_cons (step1408 p h) (sat_cons (step1412 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1386 p h) (sat_cons (step1398 p h) (sat_cons (step1394 p h) (sat_cons (step1383 p h) (sat_cons (step616 p h) (sat_cons (step621 p h) (sat_nil p))))))))))))
def c1731 : List Lit := [(87, true), (1758, true)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c799, c1730, c1471, c1456, c1458, c1451, c1437, c1439, c1449, c1434, c1431, c708, c722] c1731 (by decide) p (sat_cons (step799 p h) (sat_cons (step1730 p h) (sat_cons (step1471 p h) (sat_cons (step1456 p h) (sat_cons (step1458 p h) (sat_cons (step1451 p h) (sat_cons (step1437 p h) (sat_cons (step1439 p h) (sat_cons (step1449 p h) (sat_cons (step1434 p h) (sat_cons (step1431 p h) (sat_cons (step708 p h) (sat_cons (step722 p h) (sat_nil p))))))))))))))
def c1732 : List Lit := [(110, true), (1758, true)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c1469, c1461, c1442, c1431, c1433, c1439, c1458, c1459, c1471, c1451, c1408, c1448, c1400, c1397, c1688, c675] c1732 (by decide) p (sat_cons (step1469 p h) (sat_cons (step1461 p h) (sat_cons (step1442 p h) (sat_cons (step1431 p h) (sat_cons (step1433 p h) (sat_cons (step1439 p h) (sat_cons (step1458 p h) (sat_cons (step1459 p h) (sat_cons (step1471 p h) (sat_cons (step1451 p h) (sat_cons (step1408 p h) (sat_cons (step1448 p h) (sat_cons (step1400 p h) (sat_cons (step1397 p h) (sat_cons (step1688 p h) (sat_cons (step675 p h) (sat_nil p)))))))))))))))))
def c1733 : List Lit := [(1733, false), (1758, true)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c804, c1732, c1469, c1461, c1439, c1440, c1458, c1459, c1434, c1471, c1451, c1408, c1449, c1400, c722, c1397, c744, c1682] c1733 (by decide) p (sat_cons (step804 p h) (sat_cons (step1732 p h) (sat_cons (step1469 p h) (sat_cons (step1461 p h) (sat_cons (step1439 p h) (sat_cons (step1440 p h) (sat_cons (step1458 p h) (sat_cons (step1459 p h) (sat_cons (step1434 p h) (sat_cons (step1471 p h) (sat_cons (step1451 p h) (sat_cons (step1408 p h) (sat_cons (step1449 p h) (sat_cons (step1400 p h) (sat_cons (step722 p h) (sat_cons (step1397 p h) (sat_cons (step744 p h) (sat_cons (step1682 p h) (sat_nil p)))))))))))))))))))
def c1734 : List Lit := [(1713, true), (1758, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c1732, c1731, c1386, c1388, c1383, c1381, c507] c1734 (by decide) p (sat_cons (step1732 p h) (sat_cons (step1731 p h) (sat_cons (step1386 p h) (sat_cons (step1388 p h) (sat_cons (step1383 p h) (sat_cons (step1381 p h) (sat_cons (step507 p h) (sat_nil p))))))))
end B112E008
