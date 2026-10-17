import B112E158Part0001
namespace B112E158
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1698 : List Lit := [(1649, true), (1632, false), (117, false)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c711, c1423, c1449, c1446, c1424, c1437, c1418, c1429, c645, c659] c1698 (by decide) p (sat_cons (step711 p h) (sat_cons (step1423 p h) (sat_cons (step1449 p h) (sat_cons (step1446 p h) (sat_cons (step1424 p h) (sat_cons (step1437 p h) (sat_cons (step1418 p h) (sat_cons (step1429 p h) (sat_cons (step645 p h) (sat_cons (step659 p h) (sat_nil p)))))))))))
def c1699 : List Lit := [(110, false), (114, false), (117, false)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c711, c645, c659] c1699 (by decide) p (sat_cons (step711 p h) (sat_cons (step645 p h) (sat_cons (step659 p h) (sat_nil p))))
def c1700 : List Lit := [(1506, false), (50, true), (49, false), (1516, true), (54, true), (1495, false), (61, false)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c1143, c1148, c1180, c1153, c1163, c1166, c1184, c1155, c1149, c269, c1144] c1700 (by decide) p (sat_cons (step1143 p h) (sat_cons (step1148 p h) (sat_cons (step1180 p h) (sat_cons (step1153 p h) (sat_cons (step1163 p h) (sat_cons (step1166 p h) (sat_cons (step1184 p h) (sat_cons (step1155 p h) (sat_cons (step1149 p h) (sat_cons (step269 p h) (sat_cons (step1144 p h) (sat_nil p))))))))))))
def c1701 : List Lit := [(40, true), (1516, true), (54, true), (1495, false), (64, true), (58, true), (61, false), (59, false)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c690, c1156, c424, c423, c1549, c1700, c1158, c1613, c271, c1144, c1155, c1149, c1165, c1184] c1701 (by decide) p (sat_cons (step690 p h) (sat_cons (step1156 p h) (sat_cons (step424 p h) (sat_cons (step423 p h) (sat_cons (step1549 p h) (sat_cons (step1700 p h) (sat_cons (step1158 p h) (sat_cons (step1613 p h) (sat_cons (step271 p h) (sat_cons (step1144 p h) (sat_cons (step1155 p h) (sat_cons (step1149 p h) (sat_cons (step1165 p h) (sat_cons (step1184 p h) (sat_nil p)))))))))))))))
def c1702 : List Lit := [(51, false), (49, true), (63, false), (102, false)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c685, c326, c292] c1702 (by decide) p (sat_cons (step685 p h) (sat_cons (step326 p h) (sat_cons (step292 p h) (sat_nil p))))
def c1703 : List Lit := [(1649, true), (1632, false)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c1673, c1698, c1433] c1703 (by decide) p (sat_cons (step1673 p h) (sat_cons (step1698 p h) (sat_cons (step1433 p h) (sat_nil p))))
def c1704 : List Lit := [(1558, true), (69, false), (28, false)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1280, c507] c1704 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1280 p h) (sat_cons (step507 p h) (sat_nil p))))
def c1705 : List Lit := [(1477, false), (48, true), (1525, true), (39, true), (1497, false), (1508, false)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c680, c1139, c1148, c1178, c1213, c1110, c1117, c1128, c1129, c1207, c1120, c1118, c1183, c1111, c1112, c1113, c1151, c242, c1141, c239, c237, c1546] c1705 (by decide) p (sat_cons (step680 p h) (sat_cons (step1139 p h) (sat_cons (step1148 p h) (sat_cons (step1178 p h) (sat_cons (step1213 p h) (sat_cons (step1110 p h) (sat_cons (step1117 p h) (sat_cons (step1128 p h) (sat_cons (step1129 p h) (sat_cons (step1207 p h) (sat_cons (step1120 p h) (sat_cons (step1118 p h) (sat_cons (step1183 p h) (sat_cons (step1111 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step1151 p h) (sat_cons (step242 p h) (sat_cons (step1141 p h) (sat_cons (step239 p h) (sat_cons (step237 p h) (sat_cons (step1546 p h) (sat_nil p)))))))))))))))))))))))
def c1706 : List Lit := [(1477, true), (54, false), (30, false)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c676, c1104, c1106, c1101, c1102, c151, c175, c130, c142] c1706 (by decide) p (sat_cons (step676 p h) (sat_cons (step1104 p h) (sat_cons (step1106 p h) (sat_cons (step1101 p h) (sat_cons (step1102 p h) (sat_cons (step151 p h) (sat_cons (step175 p h) (sat_cons (step130 p h) (sat_cons (step142 p h) (sat_nil p))))))))))
def c1707 : List Lit := [(1524, true), (1477, false), (39, true), (1497, false), (1508, false)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c680, c1110, c1117, c1128, c1145, c1173, c1206, c1212, c1178, c1129, c1148, c1120, c1118, c1140, c1111, c1112, c1113, c227, c242, c239] c1707 (by decide) p (sat_cons (step680 p h) (sat_cons (step1110 p h) (sat_cons (step1117 p h) (sat_cons (step1128 p h) (sat_cons (step1145 p h) (sat_cons (step1173 p h) (sat_cons (step1206 p h) (sat_cons (step1212 p h) (sat_cons (step1178 p h) (sat_cons (step1129 p h) (sat_cons (step1148 p h) (sat_cons (step1120 p h) (sat_cons (step1118 p h) (sat_cons (step1140 p h) (sat_cons (step1111 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step227 p h) (sat_cons (step242 p h) (sat_cons (step239 p h) (sat_nil p)))))))))))))))))))))
def c1708 : List Lit := [(1643, false), (1650, true)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1447, c1684, c1423, c1416] c1708 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1447 p h) (sat_cons (step1684 p h) (sat_cons (step1423 p h) (sat_cons (step1416 p h) (sat_nil p))))))
def c1709 : List Lit := [(1485, true), (30, false), (1570, true), (1560, false), (39, true), (59, true), (54, false)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c680, c682, c1110, c1120, c1118, c1111, c1112, c1113, c242, c154, c239, c246, c228, c479, c480, c1273, c1280, c1278, c1288, c1309] c1709 (by decide) p (sat_cons (step680 p h) (sat_cons (step682 p h) (sat_cons (step1110 p h) (sat_cons (step1120 p h) (sat_cons (step1118 p h) (sat_cons (step1111 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step242 p h) (sat_cons (step154 p h) (sat_cons (step239 p h) (sat_cons (step246 p h) (sat_cons (step228 p h) (sat_cons (step479 p h) (sat_cons (step480 p h) (sat_cons (step1273 p h) (sat_cons (step1280 p h) (sat_cons (step1278 p h) (sat_cons (step1288 p h) (sat_cons (step1309 p h) (sat_nil p)))))))))))))))))))))
def c1710 : List Lit := [(41, false), (42, false), (40, false), (33, true), (44, false), (1570, true), (1560, false), (59, true), (54, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c682, c242, c228, c246, c479, c480, c1273, c1280, c1278, c1288, c1309] c1710 (by decide) p (sat_cons (step682 p h) (sat_cons (step242 p h) (sat_cons (step228 p h) (sat_cons (step246 p h) (sat_cons (step479 p h) (sat_cons (step480 p h) (sat_cons (step1273 p h) (sat_cons (step1280 p h) (sat_cons (step1278 p h) (sat_cons (step1288 p h) (sat_cons (step1309 p h) (sat_nil p))))))))))))
def c1711 : List Lit := [(1485, true), (39, true), (43, false), (44, false)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1120, c1118, c1111, c1113, c242] c1711 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1120 p h) (sat_cons (step1118 p h) (sat_cons (step1111 p h) (sat_cons (step1113 p h) (sat_cons (step242 p h) (sat_nil p)))))))
def c1712 : List Lit := [(41, false), (45, false), (64, true), (42, false), (1478, true), (53, false)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c680, c681, c227, c238, c241, c255, c143, c1101, c1107] c1712 (by decide) p (sat_cons (step680 p h) (sat_cons (step681 p h) (sat_cons (step227 p h) (sat_cons (step238 p h) (sat_cons (step241 p h) (sat_cons (step255 p h) (sat_cons (step143 p h) (sat_cons (step1101 p h) (sat_cons (step1107 p h) (sat_nil p))))))))))
def c1713 : List Lit := [(1463, true), (1444, false), (26, false), (28, false)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c1065, c1076, c1082, c1066, c1019, c1050, c1011, c1042, c1008, c119] c1713 (by decide) p (sat_cons (step1065 p h) (sat_cons (step1076 p h) (sat_cons (step1082 p h) (sat_cons (step1066 p h) (sat_cons (step1019 p h) (sat_cons (step1050 p h) (sat_cons (step1011 p h) (sat_cons (step1042 p h) (sat_cons (step1008 p h) (sat_cons (step119 p h) (sat_nil p)))))))))))
def c1714 : List Lit := [(1444, false), (1463, true), (28, false)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c675, c1076, c1065, c1713, c1066, c1082, c128, c1050, c1023, c1043, c1000, c95, c997] c1714 (by decide) p (sat_cons (step675 p h) (sat_cons (step1076 p h) (sat_cons (step1065 p h) (sat_cons (step1713 p h) (sat_cons (step1066 p h) (sat_cons (step1082 p h) (sat_cons (step128 p h) (sat_cons (step1050 p h) (sat_cons (step1023 p h) (sat_cons (step1043 p h) (sat_cons (step1000 p h) (sat_cons (step95 p h) (sat_cons (step997 p h) (sat_nil p))))))))))))))
def c1715 : List Lit := [(1463, true), (19, true), (55, false), (28, false)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c670, c1039, c1076, c1062, c1053, c1714, c1040, c1604, c1043, c1044, c1050, c1061, c1082, c1019, c1011, c1008, c119, c67, c73] c1715 (by decide) p (sat_cons (step670 p h) (sat_cons (step1039 p h) (sat_cons (step1076 p h) (sat_cons (step1062 p h) (sat_cons (step1053 p h) (sat_cons (step1714 p h) (sat_cons (step1040 p h) (sat_cons (step1604 p h) (sat_cons (step1043 p h) (sat_cons (step1044 p h) (sat_cons (step1050 p h) (sat_cons (step1061 p h) (sat_cons (step1082 p h) (sat_cons (step1019 p h) (sat_cons (step1011 p h) (sat_cons (step1008 p h) (sat_cons (step119 p h) (sat_cons (step67 p h) (sat_cons (step73 p h) (sat_nil p))))))))))))))))))))
def c1716 : List Lit := [(1512, true), (1505, false), (54, false)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c1159, c1168, c1172, c1162, c1145, c1154, c1655] c1716 (by decide) p (sat_cons (step1159 p h) (sat_cons (step1168 p h) (sat_cons (step1172 p h) (sat_cons (step1162 p h) (sat_cons (step1145 p h) (sat_cons (step1154 p h) (sat_cons (step1655 p h) (sat_nil p))))))))
def c1717 : List Lit := [(1497, true), (55, false), (54, false)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c685, c1142, c1143, c318, c263, c292] c1717 (by decide) p (sat_cons (step685 p h) (sat_cons (step1142 p h) (sat_cons (step1143 p h) (sat_cons (step318 p h) (sat_cons (step263 p h) (sat_cons (step292 p h) (sat_nil p)))))))
def c1718 : List Lit := [(51, false), (52, true), (55, false)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c685, c292, c290, c1550] c1718 (by decide) p (sat_cons (step685 p h) (sat_cons (step292 p h) (sat_cons (step290 p h) (sat_cons (step1550 p h) (sat_nil p)))))
def c1719 : List Lit := [(48, false), (37, false), (69, true), (1478, true), (58, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c684, c259, c201, c1541, c1107, c1102] c1719 (by decide) p (sat_cons (step684 p h) (sat_cons (step259 p h) (sat_cons (step201 p h) (sat_cons (step1541 p h) (sat_cons (step1107 p h) (sat_cons (step1102 p h) (sat_nil p)))))))
def c1720 : List Lit := [(48, true), (39, true), (1498, false), (1507, false), (1524, true)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c680, c1110, c1117, c1123, c1200, c1187, c1152, c1139, c1141, c1149, c1182, c1206, c1124, c1128, c1120, c1118, c1104, c1111, c1113, c1101, c227, c255, c238] c1720 (by decide) p (sat_cons (step680 p h) (sat_cons (step1110 p h) (sat_cons (step1117 p h) (sat_cons (step1123 p h) (sat_cons (step1200 p h) (sat_cons (step1187 p h) (sat_cons (step1152 p h) (sat_cons (step1139 p h) (sat_cons (step1141 p h) (sat_cons (step1149 p h) (sat_cons (step1182 p h) (sat_cons (step1206 p h) (sat_cons (step1124 p h) (sat_cons (step1128 p h) (sat_cons (step1120 p h) (sat_cons (step1118 p h) (sat_cons (step1104 p h) (sat_cons (step1111 p h) (sat_cons (step1113 p h) (sat_cons (step1101 p h) (sat_cons (step227 p h) (sat_cons (step255 p h) (sat_cons (step238 p h) (sat_nil p))))))))))))))))))))))))
def c1721 : List Lit := [(1434, true), (32, false), (37, true)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c667, c665, c664, c1019, c1023, c1013, c1000, c1002, c1005, c1006, c997, c998, c1, c38, c28, c18, c42] c1721 (by decide) p (sat_cons (step667 p h) (sat_cons (step665 p h) (sat_cons (step664 p h) (sat_cons (step1019 p h) (sat_cons (step1023 p h) (sat_cons (step1013 p h) (sat_cons (step1000 p h) (sat_cons (step1002 p h) (sat_cons (step1005 p h) (sat_cons (step1006 p h) (sat_cons (step997 p h) (sat_cons (step998 p h) (sat_cons (step1 p h) (sat_cons (step38 p h) (sat_cons (step28 p h) (sat_cons (step18 p h) (sat_cons (step42 p h) (sat_nil p))))))))))))))))))
def c1722 : List Lit := [(1615, true), (98, false), (93, true)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c1381, c1385, c1387, c1383, c1616] c1722 (by decide) p (sat_cons (step1381 p h) (sat_cons (step1385 p h) (sat_cons (step1387 p h) (sat_cons (step1383 p h) (sat_cons (step1616 p h) (sat_nil p))))))
def c1723 : List Lit := [(1659, true), (93, true), (44, false)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c1622, c1381, c1384, c1465, c1407, c1647, c1722, c1409, c1410, c1461, c1395, c1397, c1673, c1393, c1390, c1433, c1697] c1723 (by decide) p (sat_cons (step1622 p h) (sat_cons (step1381 p h) (sat_cons (step1384 p h) (sat_cons (step1465 p h) (sat_cons (step1407 p h) (sat_cons (step1647 p h) (sat_cons (step1722 p h) (sat_cons (step1409 p h) (sat_cons (step1410 p h) (sat_cons (step1461 p h) (sat_cons (step1395 p h) (sat_cons (step1397 p h) (sat_cons (step1673 p h) (sat_cons (step1393 p h) (sat_cons (step1390 p h) (sat_cons (step1433 p h) (sat_cons (step1697 p h) (sat_nil p))))))))))))))))))
def c1724 : List Lit := [(59, false), (36, true), (39, false), (33, true), (54, false), (35, false), (37, true)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c679, c403, c214, c221] c1724 (by decide) p (sat_cons (step679 p h) (sat_cons (step403 p h) (sat_cons (step214 p h) (sat_cons (step221 p h) (sat_nil p)))))
def c1725 : List Lit := [(1475, true), (59, false), (39, false), (33, true), (54, false), (37, true)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c1101, c1102, c1724, c178] c1725 (by decide) p (sat_cons (step1101 p h) (sat_cons (step1102 p h) (sat_cons (step1724 p h) (sat_cons (step178 p h) (sat_nil p)))))
def c1726 : List Lit := [(1590, true), (1583, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1334, c1337, c1330, c1317, c1322, c1602] c1726 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1334 p h) (sat_cons (step1337 p h) (sat_cons (step1330 p h) (sat_cons (step1317 p h) (sat_cons (step1322 p h) (sat_cons (step1602 p h) (sat_nil p))))))))
def c1727 : List Lit := [(58, false), (68, false), (60, true), (37, true)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c688, c377, c375, c1556] c1727 (by decide) p (sat_cons (step688 p h) (sat_cons (step377 p h) (sat_cons (step375 p h) (sat_cons (step1556 p h) (sat_nil p)))))
def c1728 : List Lit := [(1583, false), (1591, true), (1525, false), (1434, false), (1568, false), (1449, false), (1658, false)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c1527, c1668, c1726, c1043, c1361, c1052, c1494, c1058, c1523, c1083, c1249] c1728 (by decide) p (sat_cons (step1527 p h) (sat_cons (step1668 p h) (sat_cons (step1726 p h) (sat_cons (step1043 p h) (sat_cons (step1361 p h) (sat_cons (step1052 p h) (sat_cons (step1494 p h) (sat_cons (step1058 p h) (sat_cons (step1523 p h) (sat_cons (step1083 p h) (sat_cons (step1249 p h) (sat_nil p))))))))))))
def c1729 : List Lit := [(1650, true), (1632, false), (109, true), (117, false)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c1419, c1424, c1452, c1450, c1425, c1437, c1420, c1429, c1699] c1729 (by decide) p (sat_cons (step1419 p h) (sat_cons (step1424 p h) (sat_cons (step1452 p h) (sat_cons (step1450 p h) (sat_cons (step1425 p h) (sat_cons (step1437 p h) (sat_cons (step1420 p h) (sat_cons (step1429 p h) (sat_cons (step1699 p h) (sat_nil p))))))))))
def c1730 : List Lit := [(1514, true), (1495, false), (58, true), (50, true), (52, true)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c1143, c1148, c1156, c1159, c1182, c1178, c1149, c1160, c1144, c1158, c1718] c1730 (by decide) p (sat_cons (step1143 p h) (sat_cons (step1148 p h) (sat_cons (step1156 p h) (sat_cons (step1159 p h) (sat_cons (step1182 p h) (sat_cons (step1178 p h) (sat_cons (step1149 p h) (sat_cons (step1160 p h) (sat_cons (step1144 p h) (sat_cons (step1158 p h) (sat_cons (step1718 p h) (sat_nil p))))))))))))
def c1731 : List Lit := [(33, true), (39, false), (30, false), (1476, true), (52, true)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c676, c139, c141, c1537, c1103, c177] c1731 (by decide) p (sat_cons (step676 p h) (sat_cons (step139 p h) (sat_cons (step141 p h) (sat_cons (step1537 p h) (sat_cons (step1103 p h) (sat_cons (step177 p h) (sat_nil p)))))))
def c1732 : List Lit := [(1482, true), (45, false), (41, false)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c680, c1112, c1113, c242, c227, c239] c1732 (by decide) p (sat_cons (step680 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step242 p h) (sat_cons (step227 p h) (sat_cons (step239 p h) (sat_nil p)))))))
def c1733 : List Lit := [(1513, true), (50, true), (58, true), (52, true)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c1143, c1145, c1156, c1159, c1173, c1177, c1160, c1146, c1158, c1144, c1718] c1733 (by decide) p (sat_cons (step1143 p h) (sat_cons (step1145 p h) (sat_cons (step1156 p h) (sat_cons (step1159 p h) (sat_cons (step1173 p h) (sat_cons (step1177 p h) (sat_cons (step1160 p h) (sat_cons (step1146 p h) (sat_cons (step1158 p h) (sat_cons (step1144 p h) (sat_cons (step1718 p h) (sat_nil p))))))))))))
def c1734 : List Lit := [(1649, true), (39, false), (54, false)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c710, c1443, c1449, c1673, c1703, c1440, c1422, c1433, c1416, c1678, c1420, c405, c644, c630] c1734 (by decide) p (sat_cons (step710 p h) (sat_cons (step1443 p h) (sat_cons (step1449 p h) (sat_cons (step1673 p h) (sat_cons (step1703 p h) (sat_cons (step1440 p h) (sat_cons (step1422 p h) (sat_cons (step1433 p h) (sat_cons (step1416 p h) (sat_cons (step1678 p h) (sat_cons (step1420 p h) (sat_cons (step405 p h) (sat_cons (step644 p h) (sat_cons (step630 p h) (sat_nil p)))))))))))))))
def c1735 : List Lit := [(1621, true), (44, false), (117, false)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c1395, c1397, c1393, c1390, c1697] c1735 (by decide) p (sat_cons (step1395 p h) (sat_cons (step1397 p h) (sat_cons (step1393 p h) (sat_cons (step1390 p h) (sat_cons (step1697 p h) (sat_nil p))))))
def c1736 : List Lit := [(1626, true), (44, false), (117, false)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c1735, c1403, c1696, c1406, c1384, c1386, c1382, c1616] c1736 (by decide) p (sat_cons (step1735 p h) (sat_cons (step1403 p h) (sat_cons (step1696 p h) (sat_cons (step1406 p h) (sat_cons (step1384 p h) (sat_cons (step1386 p h) (sat_cons (step1382 p h) (sat_cons (step1616 p h) (sat_nil p)))))))))
def c1737 : List Lit := [(54, false), (1650, true), (105, false), (102, false), (117, false)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c629, c628, c1729, c1416] c1737 (by decide) p (sat_cons (step629 p h) (sat_cons (step628 p h) (sat_cons (step1729 p h) (sat_cons (step1416 p h) (sat_nil p)))))
def c1738 : List Lit := [(1509, false), (1477, false), (1526, true), (39, true), (48, true), (1497, false)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1117, c1128, c1208, c1139, c1148, c1179, c1184, c1214, c1151, c1129, c1141, c1120, c1118, c1732, c1111] c1738 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1117 p h) (sat_cons (step1128 p h) (sat_cons (step1208 p h) (sat_cons (step1139 p h) (sat_cons (step1148 p h) (sat_cons (step1179 p h) (sat_cons (step1184 p h) (sat_cons (step1214 p h) (sat_cons (step1151 p h) (sat_cons (step1129 p h) (sat_cons (step1141 p h) (sat_cons (step1120 p h) (sat_cons (step1118 p h) (sat_cons (step1732 p h) (sat_cons (step1111 p h) (sat_nil p)))))))))))))))))
def c1739 : List Lit := [(1477, true), (37, false), (92, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c1104, c1106, c1102, c197] c1739 (by decide) p (sat_cons (step1104 p h) (sat_cons (step1106 p h) (sat_cons (step1102 p h) (sat_cons (step197 p h) (sat_nil p)))))
def c1740 : List Lit := [(1526, true), (1478, false), (1497, false), (39, true), (48, true), (1508, false)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1117, c1133, c1139, c1148, c1178, c1219, c1214, c1134, c1183, c1120, c1118, c1151, c1111, c1141, c1732] c1740 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1117 p h) (sat_cons (step1133 p h) (sat_cons (step1139 p h) (sat_cons (step1148 p h) (sat_cons (step1178 p h) (sat_cons (step1219 p h) (sat_cons (step1214 p h) (sat_cons (step1134 p h) (sat_cons (step1183 p h) (sat_cons (step1120 p h) (sat_cons (step1118 p h) (sat_cons (step1151 p h) (sat_cons (step1111 p h) (sat_cons (step1141 p h) (sat_cons (step1732 p h) (sat_nil p)))))))))))))))))
def c1741 : List Lit := [(54, false), (13, false), (19, false), (51, false)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c669, c62, c302, c53] c1741 (by decide) p (sat_cons (step669 p h) (sat_cons (step62 p h) (sat_cons (step302 p h) (sat_cons (step53 p h) (sat_nil p)))))
def c1742 : List Lit := [(37, true), (92, false), (24, true), (74, true), (4, true), (7, false), (3, false), (32, true)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c702, c664, c1584, c1579, c698, c697, c700, c699, c598, c597, c18, c1566, c2, c585, c849, c850, c852, c854, c858, c846, c847, c840, c842, c845, c844, c837, c838, c834, c836, c835, c833, c1571, c556, c565, c561, c567, c559, c572, c569, c571] c1742 (by decide) p (sat_cons (step702 p h) (sat_cons (step664 p h) (sat_cons (step1584 p h) (sat_cons (step1579 p h) (sat_cons (step698 p h) (sat_cons (step697 p h) (sat_cons (step700 p h) (sat_cons (step699 p h) (sat_cons (step598 p h) (sat_cons (step597 p h) (sat_cons (step18 p h) (sat_cons (step1566 p h) (sat_cons (step2 p h) (sat_cons (step585 p h) (sat_cons (step849 p h) (sat_cons (step850 p h) (sat_cons (step852 p h) (sat_cons (step854 p h) (sat_cons (step858 p h) (sat_cons (step846 p h) (sat_cons (step847 p h) (sat_cons (step840 p h) (sat_cons (step842 p h) (sat_cons (step845 p h) (sat_cons (step844 p h) (sat_cons (step837 p h) (sat_cons (step838 p h) (sat_cons (step834 p h) (sat_cons (step836 p h) (sat_cons (step835 p h) (sat_cons (step833 p h) (sat_cons (step1571 p h) (sat_cons (step556 p h) (sat_cons (step565 p h) (sat_cons (step561 p h) (sat_cons (step567 p h) (sat_cons (step559 p h) (sat_cons (step572 p h) (sat_cons (step569 p h) (sat_cons (step571 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c1743 : List Lit := [(1507, true), (58, false), (37, true), (39, false)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c688, c1159, c1161, c1157, c1153, c1154, c359, c402, c377] c1743 (by decide) p (sat_cons (step688 p h) (sat_cons (step1159 p h) (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step359 p h) (sat_cons (step402 p h) (sat_cons (step377 p h) (sat_nil p))))))))))
def c1744 : List Lit := [(1497, true), (1428, true)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c669, c1009, c1008, c1142, c1143, c298, c47, c54] c1744 (by decide) p (sat_cons (step669 p h) (sat_cons (step1009 p h) (sat_cons (step1008 p h) (sat_cons (step1142 p h) (sat_cons (step1143 p h) (sat_cons (step298 p h) (sat_cons (step47 p h) (sat_cons (step54 p h) (sat_nil p)))))))))
def c1745 : List Lit := [(1507, true), (37, true), (39, false)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c1159, c1743, c1156] c1745 (by decide) p (sat_cons (step1159 p h) (sat_cons (step1743 p h) (sat_cons (step1156 p h) (sat_nil p))))
def c1746 : List Lit := [(50, false), (1428, true), (54, false)]
theorem step1746 (p : Nat → Bool) (h : Constraints p) : clause p c1746 = true :=
  Snake9.LocalRup.prove_clause [c669, c1009, c1008, c47, c299, c54] c1746 (by decide) p (sat_cons (step669 p h) (sat_cons (step1009 p h) (sat_cons (step1008 p h) (sat_cons (step47 p h) (sat_cons (step299 p h) (sat_cons (step54 p h) (sat_nil p)))))))
def c1747 : List Lit := [(30, false), (29, true), (52, true), (39, false), (54, false)]
theorem step1747 (p : Nat → Bool) (h : Constraints p) : clause p c1747 = true :=
  Snake9.LocalRup.prove_clause [c676, c153, c141] c1747 (by decide) p (sat_cons (step676 p h) (sat_cons (step153 p h) (sat_cons (step141 p h) (sat_nil p))))
def c1748 : List Lit := [(1484, true), (45, false)]
theorem step1748 (p : Nat → Bool) (h : Constraints p) : clause p c1748 = true :=
  Snake9.LocalRup.prove_clause [c1115, c1117, c1732, c1109] c1748 (by decide) p (sat_cons (step1115 p h) (sat_cons (step1117 p h) (sat_cons (step1732 p h) (sat_cons (step1109 p h) (sat_nil p)))))
def c1749 : List Lit := [(1678, true), (1568, false), (1567, false), (1614, false), (1649, false)]
theorem step1749 (p : Nat → Bool) (h : Constraints p) : clause p c1749 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1457, c1683, c1494, c1693, c1361, c1692, c1726] c1749 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1457 p h) (sat_cons (step1683 p h) (sat_cons (step1494 p h) (sat_cons (step1693 p h) (sat_cons (step1361 p h) (sat_cons (step1692 p h) (sat_cons (step1726 p h) (sat_nil p)))))))))
def c1750 : List Lit := [(4, true), (2, true), (37, true), (3, false)]
theorem step1750 (p : Nat → Bool) (h : Constraints p) : clause p c1750 = true :=
  Snake9.LocalRup.prove_clause [c664, c17] c1750 (by decide) p (sat_cons (step664 p h) (sat_cons (step17 p h) (sat_nil p)))
def c1751 : List Lit := [(1, true), (4, true), (3, false), (37, true)]
theorem step1751 (p : Nat → Bool) (h : Constraints p) : clause p c1751 = true :=
  Snake9.LocalRup.prove_clause [c664, c18] c1751 (by decide) p (sat_cons (step664 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1752 : List Lit := [(2, true), (1, true), (37, true), (3, false)]
theorem step1752 (p : Nat → Bool) (h : Constraints p) : clause p c1752 = true :=
  Snake9.LocalRup.prove_clause [c664, c19] c1752 (by decide) p (sat_cons (step664 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1753 : List Lit := [(6, false), (8, true)]
theorem step1753 (p : Nat → Bool) (h : Constraints p) : clause p c1753 = true :=
  Snake9.LocalRup.prove_clause [c665, c28] c1753 (by decide) p (sat_cons (step665 p h) (sat_cons (step28 p h) (sat_nil p)))
def c1754 : List Lit := [(6, false), (5, true)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c665, c29] c1754 (by decide) p (sat_cons (step665 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1755 : List Lit := [(5, true), (22, true), (7, false)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.LocalRup.prove_clause [c666, c31] c1755 (by decide) p (sat_cons (step666 p h) (sat_cons (step31 p h) (sat_nil p)))
def c1756 : List Lit := [(22, true), (1, true), (7, false)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c666, c32] c1756 (by decide) p (sat_cons (step666 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1757 : List Lit := [(5, true), (1, true), (7, false)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c666, c33] c1757 (by decide) p (sat_cons (step666 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1758 : List Lit := [(9, false), (10, true)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c667, c38] c1758 (by decide) p (sat_cons (step667 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1759 : List Lit := [(9, false), (2, true)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c667, c39] c1759 (by decide) p (sat_cons (step667 p h) (sat_cons (step39 p h) (sat_nil p)))
def c1760 : List Lit := [(10, true), (4, true), (11, false)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c668, c43] c1760 (by decide) p (sat_cons (step668 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1761 : List Lit := [(8, true), (4, true), (11, false)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c668, c44] c1761 (by decide) p (sat_cons (step668 p h) (sat_cons (step44 p h) (sat_nil p)))
end B112E158
