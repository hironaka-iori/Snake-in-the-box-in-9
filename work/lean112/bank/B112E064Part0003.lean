import B112E064Part0002
namespace B112E064
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1611 : List Lit := [(1540, true), (170, true), (1490, true), (72, false)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c1133, c1134, c1534, c334, c325, c1498, c253] c1611 (by decide) p (sat_cons (step1133 p h) (sat_cons (step1134 p h) (sat_cons (step1534 p h) (sat_cons (step334 p h) (sat_cons (step325 p h) (sat_cons (step1498 p h) (sat_cons (step253 p h) (sat_nil p))))))))
def c1612 : List Lit := [(1545, true), (1540, false), (72, false)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c1144, c1142, c1610] c1612 (by decide) p (sat_cons (step1144 p h) (sat_cons (step1142 p h) (sat_cons (step1610 p h) (sat_nil p))))
def c1613 : List Lit := [(1472, true), (1464, false)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c1000, c1013, c1590, c1467, c989] c1613 (by decide) p (sat_cons (step1000 p h) (sat_cons (step1013 p h) (sat_cons (step1590 p h) (sat_cons (step1467 p h) (sat_cons (step989 p h) (sat_nil p))))))
def c1614 : List Lit := [(1495, false), (1584, false), (1448, false), (1464, false), (108, true)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c1375, c1338, c1372, c1113, c1613, c1000, c1080, c1074, c1471, c1018, c1112, c1006, c1468, c1371, c1588, c1339, c1308] c1614 (by decide) p (sat_cons (step1375 p h) (sat_cons (step1338 p h) (sat_cons (step1372 p h) (sat_cons (step1113 p h) (sat_cons (step1613 p h) (sat_cons (step1000 p h) (sat_cons (step1080 p h) (sat_cons (step1074 p h) (sat_cons (step1471 p h) (sat_cons (step1018 p h) (sat_cons (step1112 p h) (sat_cons (step1006 p h) (sat_cons (step1468 p h) (sat_cons (step1371 p h) (sat_cons (step1588 p h) (sat_cons (step1339 p h) (sat_cons (step1308 p h) (sat_nil p))))))))))))))))))
def c1615 : List Lit := [(86, true), (72, false), (1417, false), (44, false), (108, true), (85, true), (116, false)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.TreeRup.prove_clause [c698, c1375, c667, c631, c634, c1393, c1025, c1554, c1030, c1054, c221, c215, c1454, c205, c948, c1589, c1370, c1350, c1456, c963, c979, c997, c1000, c1182, c1585, c1604, c1165, c1173, c1587, c1245, c1609, c1572, c1340, c1056, c1316, c1262, c1568, c804, c800, c798, c791, c790, c1611, c1612, c1163, c1614, c1058, c1055, c1031, c1041, c1043, c1602, c1026, c1038, c1035, c1125, c1563, c1132, c1131, c1127, c1158, c1575, c273, c1240, c1188, c242, c1200, c1204, c331, c1191, c1508, c1181] c1615 (by decide) p (sat_cons (step698 p h) (sat_cons (step1375 p h) (sat_cons (step667 p h) (sat_cons (step631 p h) (sat_cons (step634 p h) (sat_cons (step1393 p h) (sat_cons (step1025 p h) (sat_cons (step1554 p h) (sat_cons (step1030 p h) (sat_cons (step1054 p h) (sat_cons (step221 p h) (sat_cons (step215 p h) (sat_cons (step1454 p h) (sat_cons (step205 p h) (sat_cons (step948 p h) (sat_cons (step1589 p h) (sat_cons (step1370 p h) (sat_cons (step1350 p h) (sat_cons (step1456 p h) (sat_cons (step963 p h) (sat_cons (step979 p h) (sat_cons (step997 p h) (sat_cons (step1000 p h) (sat_cons (step1182 p h) (sat_cons (step1585 p h) (sat_cons (step1604 p h) (sat_cons (step1165 p h) (sat_cons (step1173 p h) (sat_cons (step1587 p h) (sat_cons (step1245 p h) (sat_cons (step1609 p h) (sat_cons (step1572 p h) (sat_cons (step1340 p h) (sat_cons (step1056 p h) (sat_cons (step1316 p h) (sat_cons (step1262 p h) (sat_cons (step1568 p h) (sat_cons (step804 p h) (sat_cons (step800 p h) (sat_cons (step798 p h) (sat_cons (step791 p h) (sat_cons (step790 p h) (sat_cons (step1611 p h) (sat_cons (step1612 p h) (sat_cons (step1163 p h) (sat_cons (step1614 p h) (sat_cons (step1058 p h) (sat_cons (step1055 p h) (sat_cons (step1031 p h) (sat_cons (step1041 p h) (sat_cons (step1043 p h) (sat_cons (step1602 p h) (sat_cons (step1026 p h) (sat_cons (step1038 p h) (sat_cons (step1035 p h) (sat_cons (step1125 p h) (sat_cons (step1563 p h) (sat_cons (step1132 p h) (sat_cons (step1131 p h) (sat_cons (step1127 p h) (sat_cons (step1158 p h) (sat_cons (step1575 p h) (sat_cons (step273 p h) (sat_cons (step1240 p h) (sat_cons (step1188 p h) (sat_cons (step242 p h) (sat_cons (step1200 p h) (sat_cons (step1204 p h) (sat_cons (step331 p h) (sat_cons (step1191 p h) (sat_cons (step1508 p h) (sat_cons (step1181 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1616 : List Lit := [(1495, true), (1585, true), (86, false), (72, false), (1417, false), (1425, false), (25, true), (41, true), (44, false), (1477, false), (46, true), (45, false), (108, true), (85, true)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c1477, c1475, c1244, c1025, c1030, c1029, c1058, c1055, c1052, c1031, c1041, c1043, c1517, c1602, c1026, c1038, c1039, c1035, c1125, c1563, c251, c1131, c1611, c1159, c1612, c1143, c1158, c1138, c1238, c1239, c1532, c1603, c1203, c429, c1165, c1174, c1169] c1616 (by decide) p (sat_cons (step1477 p h) (sat_cons (step1475 p h) (sat_cons (step1244 p h) (sat_cons (step1025 p h) (sat_cons (step1030 p h) (sat_cons (step1029 p h) (sat_cons (step1058 p h) (sat_cons (step1055 p h) (sat_cons (step1052 p h) (sat_cons (step1031 p h) (sat_cons (step1041 p h) (sat_cons (step1043 p h) (sat_cons (step1517 p h) (sat_cons (step1602 p h) (sat_cons (step1026 p h) (sat_cons (step1038 p h) (sat_cons (step1039 p h) (sat_cons (step1035 p h) (sat_cons (step1125 p h) (sat_cons (step1563 p h) (sat_cons (step251 p h) (sat_cons (step1131 p h) (sat_cons (step1611 p h) (sat_cons (step1159 p h) (sat_cons (step1612 p h) (sat_cons (step1143 p h) (sat_cons (step1158 p h) (sat_cons (step1138 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step1532 p h) (sat_cons (step1603 p h) (sat_cons (step1203 p h) (sat_cons (step429 p h) (sat_cons (step1165 p h) (sat_cons (step1174 p h) (sat_cons (step1169 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c1617 : List Lit := [(1550, false), (1559, false), (1659, true), (1584, true), (113, true), (72, false), (85, true)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c1477, c1475, c693, c1279, c1287, c1232, c1233, c1333, c1203, c1199, c1309, c1508, c1190, c1294, c1298, c1181, c1290, c1288, c1272, c1281, c1283, c1270, c626, c343, c585] c1617 (by decide) p (sat_cons (step1477 p h) (sat_cons (step1475 p h) (sat_cons (step693 p h) (sat_cons (step1279 p h) (sat_cons (step1287 p h) (sat_cons (step1232 p h) (sat_cons (step1233 p h) (sat_cons (step1333 p h) (sat_cons (step1203 p h) (sat_cons (step1199 p h) (sat_cons (step1309 p h) (sat_cons (step1508 p h) (sat_cons (step1190 p h) (sat_cons (step1294 p h) (sat_cons (step1298 p h) (sat_cons (step1181 p h) (sat_cons (step1290 p h) (sat_cons (step1288 p h) (sat_cons (step1272 p h) (sat_cons (step1281 p h) (sat_cons (step1283 p h) (sat_cons (step1270 p h) (sat_cons (step626 p h) (sat_cons (step343 p h) (sat_cons (step585 p h) (sat_nil p))))))))))))))))))))))))))
def c1618 : List Lit := [(1555, false), (1659, true), (1584, true), (113, true), (1537, false), (72, false), (108, true), (85, true), (116, false)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1279, c1287, c1173, c1617, c1153, c1144, c1562, c1606, c1610, c1298, c1174, c1139, c1309, c1203, c1152, c1333, c1227] c1618 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1279 p h) (sat_cons (step1287 p h) (sat_cons (step1173 p h) (sat_cons (step1617 p h) (sat_cons (step1153 p h) (sat_cons (step1144 p h) (sat_cons (step1562 p h) (sat_cons (step1606 p h) (sat_cons (step1610 p h) (sat_cons (step1298 p h) (sat_cons (step1174 p h) (sat_cons (step1139 p h) (sat_cons (step1309 p h) (sat_cons (step1203 p h) (sat_cons (step1152 p h) (sat_cons (step1333 p h) (sat_cons (step1227 p h) (sat_nil p)))))))))))))))))))
def c1619 : List Lit := [(72, false), (1417, false), (44, false), (108, true), (85, true), (116, false)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c698, c1375, c680, c631, c634, c1393, c1025, c1554, c1030, c1054, c221, c215, c1454, c205, c948, c1589, c1370, c1456, c963, c979, c997, c1613, c1615, c1552, c638, c1279, c1287, c1293, c1308, c1345, c1616, c1074, c1614, c1112, c1371, c1618, c1165, c1586, c1153, c1617, c1171, c1168, c1169, c390, c434, c403] c1619 (by decide) p (sat_cons (step698 p h) (sat_cons (step1375 p h) (sat_cons (step680 p h) (sat_cons (step631 p h) (sat_cons (step634 p h) (sat_cons (step1393 p h) (sat_cons (step1025 p h) (sat_cons (step1554 p h) (sat_cons (step1030 p h) (sat_cons (step1054 p h) (sat_cons (step221 p h) (sat_cons (step215 p h) (sat_cons (step1454 p h) (sat_cons (step205 p h) (sat_cons (step948 p h) (sat_cons (step1589 p h) (sat_cons (step1370 p h) (sat_cons (step1456 p h) (sat_cons (step963 p h) (sat_cons (step979 p h) (sat_cons (step997 p h) (sat_cons (step1613 p h) (sat_cons (step1615 p h) (sat_cons (step1552 p h) (sat_cons (step638 p h) (sat_cons (step1279 p h) (sat_cons (step1287 p h) (sat_cons (step1293 p h) (sat_cons (step1308 p h) (sat_cons (step1345 p h) (sat_cons (step1616 p h) (sat_cons (step1074 p h) (sat_cons (step1614 p h) (sat_cons (step1112 p h) (sat_cons (step1371 p h) (sat_cons (step1618 p h) (sat_cons (step1165 p h) (sat_cons (step1586 p h) (sat_cons (step1153 p h) (sat_cons (step1617 p h) (sat_cons (step1171 p h) (sat_cons (step1168 p h) (sat_cons (step1169 p h) (sat_cons (step390 p h) (sat_cons (step434 p h) (sat_cons (step403 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c1620 : List Lit := [(1573, true), (72, true), (85, true)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c1475, c680, c1166, c1173, c1203, c1587, c1176, c1174, c1183, c1167, c1168, c1169, c399, c390, c404] c1620 (by decide) p (sat_cons (step1475 p h) (sat_cons (step680 p h) (sat_cons (step1166 p h) (sat_cons (step1173 p h) (sat_cons (step1203 p h) (sat_cons (step1587 p h) (sat_cons (step1176 p h) (sat_cons (step1174 p h) (sat_cons (step1183 p h) (sat_cons (step1167 p h) (sat_cons (step1168 p h) (sat_cons (step1169 p h) (sat_cons (step399 p h) (sat_cons (step390 p h) (sat_cons (step404 p h) (sat_nil p))))))))))))))))
def c1621 : List Lit := [(74, false), (1557, true), (1584, true), (1559, false), (85, true)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c682, c680, c1169, c1168, c1580, c390, c1130, c483, c403, c404, c1179, c434, c428, c399, c1137, c1184, c1139, c1189, c1152, c1200, c1228] c1621 (by decide) p (sat_cons (step682 p h) (sat_cons (step680 p h) (sat_cons (step1169 p h) (sat_cons (step1168 p h) (sat_cons (step1580 p h) (sat_cons (step390 p h) (sat_cons (step1130 p h) (sat_cons (step483 p h) (sat_cons (step403 p h) (sat_cons (step404 p h) (sat_cons (step1179 p h) (sat_cons (step434 p h) (sat_cons (step428 p h) (sat_cons (step399 p h) (sat_cons (step1137 p h) (sat_cons (step1184 p h) (sat_cons (step1139 p h) (sat_cons (step1189 p h) (sat_cons (step1152 p h) (sat_cons (step1200 p h) (sat_cons (step1228 p h) (sat_nil p))))))))))))))))))))))
def c1622 : List Lit := [(75, true), (1560, false), (76, false), (78, false), (1584, true), (85, true)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c682, c680, c483, c403, c1179, c434, c425, c428, c1182, c1130, c1137, c1188, c1139, c1204, c1152, c1228] c1622 (by decide) p (sat_cons (step682 p h) (sat_cons (step680 p h) (sat_cons (step483 p h) (sat_cons (step403 p h) (sat_cons (step1179 p h) (sat_cons (step434 p h) (sat_cons (step425 p h) (sat_cons (step428 p h) (sat_cons (step1182 p h) (sat_cons (step1130 p h) (sat_cons (step1137 p h) (sat_cons (step1188 p h) (sat_cons (step1139 p h) (sat_cons (step1204 p h) (sat_cons (step1152 p h) (sat_cons (step1228 p h) (sat_nil p)))))))))))))))))
def c1623 : List Lit := [(1557, true), (1584, true), (72, true), (85, true), (116, false)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c1620, c1233, c1166, c1173, c1168, c1169, c1621, c1167, c1176, c1622, c388, c1411, c393, c1133, c1515, c1179, c1142, c1148, c1153, c1228, c1552, c1204, c1182, c1188] c1623 (by decide) p (sat_cons (step1620 p h) (sat_cons (step1233 p h) (sat_cons (step1166 p h) (sat_cons (step1173 p h) (sat_cons (step1168 p h) (sat_cons (step1169 p h) (sat_cons (step1621 p h) (sat_cons (step1167 p h) (sat_cons (step1176 p h) (sat_cons (step1622 p h) (sat_cons (step388 p h) (sat_cons (step1411 p h) (sat_cons (step393 p h) (sat_cons (step1133 p h) (sat_cons (step1515 p h) (sat_cons (step1179 p h) (sat_cons (step1142 p h) (sat_cons (step1148 p h) (sat_cons (step1153 p h) (sat_cons (step1228 p h) (sat_cons (step1552 p h) (sat_cons (step1204 p h) (sat_cons (step1182 p h) (sat_cons (step1188 p h) (sat_nil p)))))))))))))))))))))))))
def c1624 : List Lit := [(1574, true), (1542, false), (75, false), (76, false), (1557, false), (1550, true), (72, true), (116, false)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1166, c1174, c1207, c1204, c1177, c1167, c391, c385, c1179, c1133, c1188, c1142, c1182, c1153, c1552] c1624 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1166 p h) (sat_cons (step1174 p h) (sat_cons (step1207 p h) (sat_cons (step1204 p h) (sat_cons (step1177 p h) (sat_cons (step1167 p h) (sat_cons (step391 p h) (sat_cons (step385 p h) (sat_cons (step1179 p h) (sat_cons (step1133 p h) (sat_cons (step1188 p h) (sat_cons (step1142 p h) (sat_cons (step1182 p h) (sat_cons (step1153 p h) (sat_cons (step1552 p h) (sat_nil p)))))))))))))))))
def c1625 : List Lit := [(1542, false), (75, false), (76, false), (1557, false), (1550, true), (1584, true), (72, true), (116, false)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c1166, c1174, c1139, c1147, c1223, c1205, c1624, c1228, c1148, c1152, c1140, c1142, c1130, c1552, c1133, c1134, c1544, c1182, c389, c1534, c1138, c1191, c1181, c335] c1625 (by decide) p (sat_cons (step1166 p h) (sat_cons (step1174 p h) (sat_cons (step1139 p h) (sat_cons (step1147 p h) (sat_cons (step1223 p h) (sat_cons (step1205 p h) (sat_cons (step1624 p h) (sat_cons (step1228 p h) (sat_cons (step1148 p h) (sat_cons (step1152 p h) (sat_cons (step1140 p h) (sat_cons (step1142 p h) (sat_cons (step1130 p h) (sat_cons (step1552 p h) (sat_cons (step1133 p h) (sat_cons (step1134 p h) (sat_cons (step1544 p h) (sat_cons (step1182 p h) (sat_cons (step389 p h) (sat_cons (step1534 p h) (sat_cons (step1138 p h) (sat_cons (step1191 p h) (sat_cons (step1181 p h) (sat_cons (step335 p h) (sat_nil p)))))))))))))))))))))))))
def c1626 : List Lit := [(1542, true), (76, false), (1560, false), (1659, true), (1573, false), (85, true), (116, false)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c1136, c1137, c1515, c1584, c1506, c429, c430, c1130, c1182, c1279, c1151, c1287, c1298, c1309, c1333, c1227, c1222, c1156, c1204, c1131, c1188, c1126, c1575] c1626 (by decide) p (sat_cons (step1136 p h) (sat_cons (step1137 p h) (sat_cons (step1515 p h) (sat_cons (step1584 p h) (sat_cons (step1506 p h) (sat_cons (step429 p h) (sat_cons (step430 p h) (sat_cons (step1130 p h) (sat_cons (step1182 p h) (sat_cons (step1279 p h) (sat_cons (step1151 p h) (sat_cons (step1287 p h) (sat_cons (step1298 p h) (sat_cons (step1309 p h) (sat_cons (step1333 p h) (sat_cons (step1227 p h) (sat_cons (step1222 p h) (sat_cons (step1156 p h) (sat_cons (step1204 p h) (sat_cons (step1131 p h) (sat_cons (step1188 p h) (sat_cons (step1126 p h) (sat_cons (step1575 p h) (sat_nil p))))))))))))))))))))))))
def c1627 : List Lit := [(1549, true), (1566, true), (1542, false), (76, false), (1448, false), (25, true), (108, true), (85, true), (116, false)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c673, c1139, c1148, c1152, c1142, c1552, c1133, c1134, c1182, c1184, c298, c293, c1569, c289] c1627 (by decide) p (sat_cons (step673 p h) (sat_cons (step1139 p h) (sat_cons (step1148 p h) (sat_cons (step1152 p h) (sat_cons (step1142 p h) (sat_cons (step1552 p h) (sat_cons (step1133 p h) (sat_cons (step1134 p h) (sat_cons (step1182 p h) (sat_cons (step1184 p h) (sat_cons (step298 p h) (sat_cons (step293 p h) (sat_cons (step1569 p h) (sat_cons (step289 p h) (sat_nil p)))))))))))))))
def c1628 : List Lit := [(76, false), (1659, true), (1584, true), (72, true), (1448, false), (25, true), (108, true), (85, true), (116, false)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c682, c1475, c1166, c1623, c1174, c1620, c1233, c1626, c1139, c1625, c1147, c483, c1223, c1179, c1205, c1189, c1627, c1228, c1227, c1207, c1204, c1333, c1177, c1190, c1188, c1309, c1167, c1181, c1182, c1183, c460, c1552, c1546, c1153, c1298, c1562] c1628 (by decide) p (sat_cons (step682 p h) (sat_cons (step1475 p h) (sat_cons (step1166 p h) (sat_cons (step1623 p h) (sat_cons (step1174 p h) (sat_cons (step1620 p h) (sat_cons (step1233 p h) (sat_cons (step1626 p h) (sat_cons (step1139 p h) (sat_cons (step1625 p h) (sat_cons (step1147 p h) (sat_cons (step483 p h) (sat_cons (step1223 p h) (sat_cons (step1179 p h) (sat_cons (step1205 p h) (sat_cons (step1189 p h) (sat_cons (step1627 p h) (sat_cons (step1228 p h) (sat_cons (step1227 p h) (sat_cons (step1207 p h) (sat_cons (step1204 p h) (sat_cons (step1333 p h) (sat_cons (step1177 p h) (sat_cons (step1190 p h) (sat_cons (step1188 p h) (sat_cons (step1309 p h) (sat_cons (step1167 p h) (sat_cons (step1181 p h) (sat_cons (step1182 p h) (sat_cons (step1183 p h) (sat_cons (step460 p h) (sat_cons (step1552 p h) (sat_cons (step1546 p h) (sat_cons (step1153 p h) (sat_cons (step1298 p h) (sat_cons (step1562 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1629 : List Lit := [(86, false), (1631, true), (1550, true), (117, false), (108, true), (116, false)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c1552, c638, c1153, c1279, c1562, c1287, c1298] c1629 (by decide) p (sat_cons (step1552 p h) (sat_cons (step638 p h) (sat_cons (step1153 p h) (sat_cons (step1279 p h) (sat_cons (step1562 p h) (sat_cons (step1287 p h) (sat_cons (step1298 p h) (sat_nil p))))))))
def c1630 : List Lit := [(1549, false), (76, true), (1659, true), (1584, true), (72, true), (108, true), (85, true), (116, false)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c698, c1475, c680, c1166, c1623, c1174, c1620, c1233, c631, c1228, c1227, c1207, c1204, c1333, c1175, c1177, c1186, c1309, c1170, c1167, c1629, c1182, c1184, c1188, c399, c1179, c404, c392] c1630 (by decide) p (sat_cons (step698 p h) (sat_cons (step1475 p h) (sat_cons (step680 p h) (sat_cons (step1166 p h) (sat_cons (step1623 p h) (sat_cons (step1174 p h) (sat_cons (step1620 p h) (sat_cons (step1233 p h) (sat_cons (step631 p h) (sat_cons (step1228 p h) (sat_cons (step1227 p h) (sat_cons (step1207 p h) (sat_cons (step1204 p h) (sat_cons (step1333 p h) (sat_cons (step1175 p h) (sat_cons (step1177 p h) (sat_cons (step1186 p h) (sat_cons (step1309 p h) (sat_cons (step1170 p h) (sat_cons (step1167 p h) (sat_cons (step1629 p h) (sat_cons (step1182 p h) (sat_cons (step1184 p h) (sat_cons (step1188 p h) (sat_cons (step399 p h) (sat_cons (step1179 p h) (sat_cons (step404 p h) (sat_cons (step392 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1631 : List Lit := [(1544, false), (1549, true), (1560, false), (1448, false), (1472, false), (108, true), (85, true), (116, false)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c698, c672, c1375, c1148, c1562, c1297, c1308, c634, c1554, c631, c1393, c1147, c1152, c1128, c1130, c1552, c1125, c1126, c1182, c282, c1575, c1565, c1188, c1075, c1204, c1113, c1222, c1372, c1332] c1631 (by decide) p (sat_cons (step698 p h) (sat_cons (step672 p h) (sat_cons (step1375 p h) (sat_cons (step1148 p h) (sat_cons (step1562 p h) (sat_cons (step1297 p h) (sat_cons (step1308 p h) (sat_cons (step634 p h) (sat_cons (step1554 p h) (sat_cons (step631 p h) (sat_cons (step1393 p h) (sat_cons (step1147 p h) (sat_cons (step1152 p h) (sat_cons (step1128 p h) (sat_cons (step1130 p h) (sat_cons (step1552 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step1182 p h) (sat_cons (step282 p h) (sat_cons (step1575 p h) (sat_cons (step1565 p h) (sat_cons (step1188 p h) (sat_cons (step1075 p h) (sat_cons (step1204 p h) (sat_cons (step1113 p h) (sat_cons (step1222 p h) (sat_cons (step1372 p h) (sat_cons (step1332 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1632 : List Lit := [(1495, false), (1417, false), (44, false), (108, true), (85, true), (116, false)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c698, c1375, c675, c673, c694, c1619, c1166, c634, c205, c948, c215, c1454, c1456, c963, c979, c221, c997, c1613, c631, c1074, c1614, c1112, c1371, c1623, c1174, c1628, c1630, c1631, c1139, c1141, c1136, c1137, c1133, c1134, c297, c1534, c306, c307, c293, c335, c336, c543, c351, c289, c1180, c1182, c588, c1167, c1188, c1271, c1177, c1273, c1208, c1302, c1217, c1309, c1333] c1632 (by decide) p (sat_cons (step698 p h) (sat_cons (step1375 p h) (sat_cons (step675 p h) (sat_cons (step673 p h) (sat_cons (step694 p h) (sat_cons (step1619 p h) (sat_cons (step1166 p h) (sat_cons (step634 p h) (sat_cons (step205 p h) (sat_cons (step948 p h) (sat_cons (step215 p h) (sat_cons (step1454 p h) (sat_cons (step1456 p h) (sat_cons (step963 p h) (sat_cons (step979 p h) (sat_cons (step221 p h) (sat_cons (step997 p h) (sat_cons (step1613 p h) (sat_cons (step631 p h) (sat_cons (step1074 p h) (sat_cons (step1614 p h) (sat_cons (step1112 p h) (sat_cons (step1371 p h) (sat_cons (step1623 p h) (sat_cons (step1174 p h) (sat_cons (step1628 p h) (sat_cons (step1630 p h) (sat_cons (step1631 p h) (sat_cons (step1139 p h) (sat_cons (step1141 p h) (sat_cons (step1136 p h) (sat_cons (step1137 p h) (sat_cons (step1133 p h) (sat_cons (step1134 p h) (sat_cons (step297 p h) (sat_cons (step1534 p h) (sat_cons (step306 p h) (sat_cons (step307 p h) (sat_cons (step293 p h) (sat_cons (step335 p h) (sat_cons (step336 p h) (sat_cons (step543 p h) (sat_cons (step351 p h) (sat_cons (step289 p h) (sat_cons (step1180 p h) (sat_cons (step1182 p h) (sat_cons (step588 p h) (sat_cons (step1167 p h) (sat_cons (step1188 p h) (sat_cons (step1271 p h) (sat_cons (step1177 p h) (sat_cons (step1273 p h) (sat_cons (step1208 p h) (sat_cons (step1302 p h) (sat_cons (step1217 p h) (sat_cons (step1309 p h) (sat_cons (step1333 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1633 : List Lit := [(1574, false), (1550, false), (1538, false), (1660, true), (108, true), (116, false)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1240, c1234, c1158, c1345, c1562, c1308, c1297] c1633 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1240 p h) (sat_cons (step1234 p h) (sat_cons (step1158 p h) (sat_cons (step1345 p h) (sat_cons (step1562 p h) (sat_cons (step1308 p h) (sat_cons (step1297 p h) (sat_nil p)))))))))
def c1634 : List Lit := [(76, true), (1565, false), (1574, true), (72, true), (85, true)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c1475, c682, c1166, c1207, c1175, c1169, c1174, c1204, c1177, c1188, c1170, c1167, c1179, c483, c392] c1634 (by decide) p (sat_cons (step1475 p h) (sat_cons (step682 p h) (sat_cons (step1166 p h) (sat_cons (step1207 p h) (sat_cons (step1175 p h) (sat_cons (step1169 p h) (sat_cons (step1174 p h) (sat_cons (step1204 p h) (sat_cons (step1177 p h) (sat_cons (step1188 p h) (sat_cons (step1170 p h) (sat_cons (step1167 p h) (sat_cons (step1179 p h) (sat_cons (step483 p h) (sat_cons (step392 p h) (sat_nil p))))))))))))))))
def c1635 : List Lit := [(1568, true), (86, true), (85, true)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c682, c1182, c1186, c1188, c1184, c1179, c1180, c482, c465] c1635 (by decide) p (sat_cons (step682 p h) (sat_cons (step1182 p h) (sat_cons (step1186 p h) (sat_cons (step1188 p h) (sat_cons (step1184 p h) (sat_cons (step1179 p h) (sat_cons (step1180 p h) (sat_cons (step482 p h) (sat_cons (step465 p h) (sat_nil p))))))))))
def c1636 : List Lit := [(86, true), (1574, true), (1584, false), (70, true), (72, true), (1417, false), (1425, false), (25, true), (41, true), (44, false), (1477, false), (46, true), (45, false), (108, true), (85, true)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c1166, c1182, c1634, c1635, c1204, c1176, c1174, c1167, c1168, c1603, c1140, c1607, c1138] c1636 (by decide) p (sat_cons (step1166 p h) (sat_cons (step1182 p h) (sat_cons (step1634 p h) (sat_cons (step1635 p h) (sat_cons (step1204 p h) (sat_cons (step1176 p h) (sat_cons (step1174 p h) (sat_cons (step1167 p h) (sat_cons (step1168 p h) (sat_cons (step1603 p h) (sat_cons (step1140 p h) (sat_cons (step1607 p h) (sat_cons (step1138 p h) (sat_nil p))))))))))))))
def c1637 : List Lit := [(1417, false), (44, false), (108, true), (85, true), (116, false)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c698, c1375, c634, c205, c948, c215, c1454, c221, c631, c1393, c1025, c1554, c1030, c1054, c1589, c1370, c1619, c1620, c1632, c1058, c1055, c1031, c1041, c1517, c1602, c1026, c1038, c1136, c1125, c1563, c1139, c1131, c1157, c1233, c1340, c1309, c1633, c1636, c638, c1279, c1287, c1293, c1298, c1308, c1562, c1345, c1158, c1239] c1637 (by decide) p (sat_cons (step698 p h) (sat_cons (step1375 p h) (sat_cons (step634 p h) (sat_cons (step205 p h) (sat_cons (step948 p h) (sat_cons (step215 p h) (sat_cons (step1454 p h) (sat_cons (step221 p h) (sat_cons (step631 p h) (sat_cons (step1393 p h) (sat_cons (step1025 p h) (sat_cons (step1554 p h) (sat_cons (step1030 p h) (sat_cons (step1054 p h) (sat_cons (step1589 p h) (sat_cons (step1370 p h) (sat_cons (step1619 p h) (sat_cons (step1620 p h) (sat_cons (step1632 p h) (sat_cons (step1058 p h) (sat_cons (step1055 p h) (sat_cons (step1031 p h) (sat_cons (step1041 p h) (sat_cons (step1517 p h) (sat_cons (step1602 p h) (sat_cons (step1026 p h) (sat_cons (step1038 p h) (sat_cons (step1136 p h) (sat_cons (step1125 p h) (sat_cons (step1563 p h) (sat_cons (step1139 p h) (sat_cons (step1131 p h) (sat_cons (step1157 p h) (sat_cons (step1233 p h) (sat_cons (step1340 p h) (sat_cons (step1309 p h) (sat_cons (step1633 p h) (sat_cons (step1636 p h) (sat_cons (step638 p h) (sat_cons (step1279 p h) (sat_cons (step1287 p h) (sat_cons (step1293 p h) (sat_cons (step1298 p h) (sat_cons (step1308 p h) (sat_cons (step1562 p h) (sat_cons (step1345 p h) (sat_cons (step1158 p h) (sat_cons (step1239 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c1638 : List Lit := [(1545, true), (1573, true), (85, true)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1620, c1203, c1586, c1606, c1165, c1174] c1638 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1620 p h) (sat_cons (step1203 p h) (sat_cons (step1586 p h) (sat_cons (step1606 p h) (sat_cons (step1165 p h) (sat_cons (step1174 p h) (sat_nil p))))))))
def c1639 : List Lit := [(81, true), (1573, true), (86, false), (1574, true), (85, true)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c1475, c1203, c1508, c1509, c1181, c1476, c1190, c1199] c1639 (by decide) p (sat_cons (step1475 p h) (sat_cons (step1203 p h) (sat_cons (step1508 p h) (sat_cons (step1509 p h) (sat_cons (step1181 p h) (sat_cons (step1476 p h) (sat_cons (step1190 p h) (sat_cons (step1199 p h) (sat_nil p)))))))))
def c1640 : List Lit := [(81, false), (72, false), (1489, true)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c667, c1043, c1035, c1041, c1038, c331, c274, c242] c1640 (by decide) p (sat_cons (step667 p h) (sat_cons (step1043 p h) (sat_cons (step1035 p h) (sat_cons (step1041 p h) (sat_cons (step1038 p h) (sat_cons (step331 p h) (sat_cons (step274 p h) (sat_cons (step242 p h) (sat_nil p)))))))))
def c1641 : List Lit := [(1545, true), (70, true), (86, false), (117, false)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c675, c1136, c1140, c1142, c1138, c1133, c1134, c296, c306, c307, c543] c1641 (by decide) p (sat_cons (step675 p h) (sat_cons (step1136 p h) (sat_cons (step1140 p h) (sat_cons (step1142 p h) (sat_cons (step1138 p h) (sat_cons (step1133 p h) (sat_cons (step1134 p h) (sat_cons (step296 p h) (sat_cons (step306 p h) (sat_cons (step307 p h) (sat_cons (step543 p h) (sat_nil p))))))))))))
def c1642 : List Lit := [(11, true), (2, false), (32, true)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c641, c7] c1642 (by decide) p (sat_cons (step641 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1643 : List Lit := [(1, true), (2, false), (32, true)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c641, c8] c1643 (by decide) p (sat_cons (step641 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1644 : List Lit := [(1, true), (11, true), (2, false)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c641, c9] c1644 (by decide) p (sat_cons (step641 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1645 : List Lit := [(3, false), (8, true)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c642, c10] c1645 (by decide) p (sat_cons (step642 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1646 : List Lit := [(3, false), (1, true)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c642, c11] c1646 (by decide) p (sat_cons (step642 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1647 : List Lit := [(5, false), (14, true), (7, true), (69, true)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c643, c20] c1647 (by decide) p (sat_cons (step643 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1648 : List Lit := [(4, true), (5, false), (69, true), (14, true)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c643, c21] c1648 (by decide) p (sat_cons (step643 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1649 : List Lit := [(4, true), (5, false), (69, true), (7, true)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c643, c22] c1649 (by decide) p (sat_cons (step643 p h) (sat_cons (step22 p h) (sat_nil p)))
def c1650 : List Lit := [(8, true), (6, false), (4, true)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c644, c24] c1650 (by decide) p (sat_cons (step644 p h) (sat_cons (step24 p h) (sat_nil p)))
def c1651 : List Lit := [(6, false), (4, true), (7, true)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c644, c25] c1651 (by decide) p (sat_cons (step644 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1652 : List Lit := [(11, true), (12, false), (79, true)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c645, c51] c1652 (by decide) p (sat_cons (step645 p h) (sat_cons (step51 p h) (sat_nil p)))
def c1653 : List Lit := [(10, true), (12, false), (79, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c645, c52] c1653 (by decide) p (sat_cons (step645 p h) (sat_cons (step52 p h) (sat_nil p)))
def c1654 : List Lit := [(11, true), (10, true), (12, false)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c645, c53] c1654 (by decide) p (sat_cons (step645 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1655 : List Lit := [(14, true), (9, true), (42, true), (13, false), (80, true)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c646, c56] c1655 (by decide) p (sat_cons (step646 p h) (sat_cons (step56 p h) (sat_nil p)))
def c1656 : List Lit := [(4, true), (14, true), (42, true), (13, false), (80, true)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c646, c57] c1656 (by decide) p (sat_cons (step646 p h) (sat_cons (step57 p h) (sat_nil p)))
def c1657 : List Lit := [(4, true), (9, true), (42, true), (13, false), (80, true)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c646, c58] c1657 (by decide) p (sat_cons (step646 p h) (sat_cons (step58 p h) (sat_nil p)))
def c1658 : List Lit := [(4, true), (13, false), (9, true), (14, true), (80, true)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c646, c59] c1658 (by decide) p (sat_cons (step646 p h) (sat_cons (step59 p h) (sat_nil p)))
def c1659 : List Lit := [(14, true), (9, true), (4, true), (42, true), (13, false)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c646, c60] c1659 (by decide) p (sat_cons (step646 p h) (sat_cons (step60 p h) (sat_nil p)))
def c1660 : List Lit := [(14, true), (15, false), (84, true)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c647, c68] c1660 (by decide) p (sat_cons (step647 p h) (sat_cons (step68 p h) (sat_nil p)))
def c1661 : List Lit := [(11, true), (15, false), (84, true)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c647, c69] c1661 (by decide) p (sat_cons (step647 p h) (sat_cons (step69 p h) (sat_nil p)))
def c1662 : List Lit := [(11, true), (15, false), (14, true)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c647, c70] c1662 (by decide) p (sat_cons (step647 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1663 : List Lit := [(16, false), (45, true), (85, true)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c648, c72] c1663 (by decide) p (sat_cons (step648 p h) (sat_cons (step72 p h) (sat_nil p)))
def c1664 : List Lit := [(8, true), (16, false), (85, true)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c648, c73] c1664 (by decide) p (sat_cons (step648 p h) (sat_cons (step73 p h) (sat_nil p)))
def c1665 : List Lit := [(8, true), (16, false), (45, true)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c648, c74] c1665 (by decide) p (sat_cons (step648 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1666 : List Lit := [(23, true), (19, false), (32, true)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c649, c80] c1666 (by decide) p (sat_cons (step649 p h) (sat_cons (step80 p h) (sat_nil p)))
def c1667 : List Lit := [(18, true), (19, false), (32, true)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c649, c81] c1667 (by decide) p (sat_cons (step649 p h) (sat_cons (step81 p h) (sat_nil p)))
def c1668 : List Lit := [(18, true), (20, false), (21, true)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c650, c83] c1668 (by decide) p (sat_cons (step650 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1669 : List Lit := [(17, true), (20, false), (21, true)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c650, c84] c1669 (by decide) p (sat_cons (step650 p h) (sat_cons (step84 p h) (sat_nil p)))
def c1670 : List Lit := [(18, true), (17, true), (20, false)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c650, c85] c1670 (by decide) p (sat_cons (step650 p h) (sat_cons (step85 p h) (sat_nil p)))
def c1671 : List Lit := [(22, false), (38, true)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c651, c88] c1671 (by decide) p (sat_cons (step651 p h) (sat_cons (step88 p h) (sat_nil p)))
def c1672 : List Lit := [(22, false), (23, true)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c651, c89] c1672 (by decide) p (sat_cons (step651 p h) (sat_cons (step89 p h) (sat_nil p)))
def c1673 : List Lit := [(23, false), (22, true), (19, true)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c1421, c91] c1673 (by decide) p (sat_cons (step1421 p h) (sat_cons (step91 p h) (sat_nil p)))
def c1674 : List Lit := [(23, false), (22, true), (140, true)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c1421, c93] c1674 (by decide) p (sat_cons (step1421 p h) (sat_cons (step93 p h) (sat_nil p)))
end B112E064
