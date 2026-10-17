import B112E024Part0004
namespace B112E024
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1682 : List Lit := [(1674, false), (1707, true)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1255] c1682 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1255 p h) (sat_nil p)))
def c1683 : List Lit := [(1675, false), (1708, true)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1258] c1683 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1258 p h) (sat_nil p)))
def c1684 : List Lit := [(1644, false), (1725, true)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c1425, c1299] c1684 (by decide) p (sat_cons (step1425 p h) (sat_cons (step1299 p h) (sat_nil p)))
def c1685 : List Lit := [(1573, false), (1731, false)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1308] c1685 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1308 p h) (sat_nil p)))
def c1686 : List Lit := [(1574, false), (1730, false)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1309] c1686 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1309 p h) (sat_nil p)))
def c1687 : List Lit := [(1575, false), (1729, false)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1310] c1687 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1310 p h) (sat_nil p)))
def c1688 : List Lit := [(1576, false), (1728, false)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1311] c1688 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1311 p h) (sat_nil p)))
def c1689 : List Lit := [(1577, false), (1727, false)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1312] c1689 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1312 p h) (sat_nil p)))
def c1690 : List Lit := [(1578, false), (1726, false)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1313] c1690 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1313 p h) (sat_nil p)))
def c1691 : List Lit := [(1579, false), (1725, false)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1314] c1691 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1314 p h) (sat_nil p)))
def c1692 : List Lit := [(1580, false), (1724, false)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1315] c1692 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1315 p h) (sat_nil p)))
def c1693 : List Lit := [(1581, false), (1723, false)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1316] c1693 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1316 p h) (sat_nil p)))
def c1694 : List Lit := [(1536, true), (53, false), (85, false)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c941, c1472, c243] c1694 (by decide) p (sat_cons (step941 p h) (sat_cons (step1472 p h) (sat_cons (step243 p h) (sat_nil p))))
def c1695 : List Lit := [(1552, true), (1538, false)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c952, c977, c911, c1414, c1434, c910, c913, c972, c891, c957, c883, c1437] c1695 (by decide) p (sat_cons (step952 p h) (sat_cons (step977 p h) (sat_cons (step911 p h) (sat_cons (step1414 p h) (sat_cons (step1434 p h) (sat_cons (step910 p h) (sat_cons (step913 p h) (sat_cons (step972 p h) (sat_cons (step891 p h) (sat_cons (step957 p h) (sat_cons (step883 p h) (sat_cons (step1437 p h) (sat_nil p)))))))))))))
def c1696 : List Lit := [(1553, true), (1506, false), (1519, false), (16, true), (1538, false)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c952, c983, c914, c1414, c1434, c1471, c1477, c886] c1696 (by decide) p (sat_cons (step952 p h) (sat_cons (step983 p h) (sat_cons (step914 p h) (sat_cons (step1414 p h) (sat_cons (step1434 p h) (sat_cons (step1471 p h) (sat_cons (step1477 p h) (sat_cons (step886 p h) (sat_nil p)))))))))
def c1697 : List Lit := [(1640, true), (1593, false), (1625, false)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c1069, c1387, c1124, c1129, c1107, c1070, c1384, c1061, c1076, c1077, c1053, c1596, c304] c1697 (by decide) p (sat_cons (step1069 p h) (sat_cons (step1387 p h) (sat_cons (step1124 p h) (sat_cons (step1129 p h) (sat_cons (step1107 p h) (sat_cons (step1070 p h) (sat_cons (step1384 p h) (sat_cons (step1061 p h) (sat_cons (step1076 p h) (sat_cons (step1077 p h) (sat_cons (step1053 p h) (sat_cons (step1596 p h) (sat_cons (step304 p h) (sat_nil p))))))))))))))
def c1698 : List Lit := [(1673, true), (1654, false), (85, false), (99, true), (86, false)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c1508, c1156, c1158, c1166, c1191, c1187, c1157, c1169, c1167, c1160, c1162, c1430, c1149, c347, c489, c1612] c1698 (by decide) p (sat_cons (step1508 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1166 p h) (sat_cons (step1191 p h) (sat_cons (step1187 p h) (sat_cons (step1157 p h) (sat_cons (step1169 p h) (sat_cons (step1167 p h) (sat_cons (step1160 p h) (sat_cons (step1162 p h) (sat_cons (step1430 p h) (sat_cons (step1149 p h) (sat_cons (step347 p h) (sat_cons (step489 p h) (sat_cons (step1612 p h) (sat_nil p)))))))))))))))))
def c1699 : List Lit := [(1666, true), (1690, true), (93, false), (83, true), (99, true), (89, false), (86, false)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1169, c1167, c1160, c1162, c1486] c1699 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1169 p h) (sat_cons (step1167 p h) (sat_cons (step1160 p h) (sat_cons (step1162 p h) (sat_cons (step1486 p h) (sat_nil p)))))))
def c1700 : List Lit := [(1659, false), (93, false), (1708, true), (87, true), (1682, false), (83, true), (108, true), (99, true), (89, false), (86, false)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c453, c1222, c1256, c1158, c1166, c1186, c1188, c1249, c1168, c1224, c1699, c1187, c1253, c1225, c1223, c1447, c1413, c1216, c1211, c1212, c446, c1208, c1209, c1603, c576, c556, c509, c1640, c1163, c531, c1197, c1207, c1198, c551, c540, c1636] c1700 (by decide) p (sat_cons (step453 p h) (sat_cons (step1222 p h) (sat_cons (step1256 p h) (sat_cons (step1158 p h) (sat_cons (step1166 p h) (sat_cons (step1186 p h) (sat_cons (step1188 p h) (sat_cons (step1249 p h) (sat_cons (step1168 p h) (sat_cons (step1224 p h) (sat_cons (step1699 p h) (sat_cons (step1187 p h) (sat_cons (step1253 p h) (sat_cons (step1225 p h) (sat_cons (step1223 p h) (sat_cons (step1447 p h) (sat_cons (step1413 p h) (sat_cons (step1216 p h) (sat_cons (step1211 p h) (sat_cons (step1212 p h) (sat_cons (step446 p h) (sat_cons (step1208 p h) (sat_cons (step1209 p h) (sat_cons (step1603 p h) (sat_cons (step576 p h) (sat_cons (step556 p h) (sat_cons (step509 p h) (sat_cons (step1640 p h) (sat_cons (step1163 p h) (sat_cons (step531 p h) (sat_cons (step1197 p h) (sat_cons (step1207 p h) (sat_cons (step1198 p h) (sat_cons (step551 p h) (sat_cons (step540 p h) (sat_cons (step1636 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1701 : List Lit := [(1695, true), (96, false), (87, true), (1682, false), (108, true), (86, false)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c1223, c1447, c1216, c1410, c1208] c1701 (by decide) p (sat_cons (step1223 p h) (sat_cons (step1447 p h) (sat_cons (step1216 p h) (sat_cons (step1410 p h) (sat_cons (step1208 p h) (sat_nil p))))))
def c1702 : List Lit := [(96, false), (93, false), (1708, true), (87, true), (1658, false), (85, false), (83, true), (108, true), (99, true), (89, false), (86, false)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c453, c1490, c347, c1611, c1612, c489, c1160, c1169, c1182, c1249, c1224, c1215, c1701, c1253, c1183, c1170, c1162, c445, c1603, c509, c1212, c1213, c1217, c566, c1208] c1702 (by decide) p (sat_cons (step453 p h) (sat_cons (step1490 p h) (sat_cons (step347 p h) (sat_cons (step1611 p h) (sat_cons (step1612 p h) (sat_cons (step489 p h) (sat_cons (step1160 p h) (sat_cons (step1169 p h) (sat_cons (step1182 p h) (sat_cons (step1249 p h) (sat_cons (step1224 p h) (sat_cons (step1215 p h) (sat_cons (step1701 p h) (sat_cons (step1253 p h) (sat_cons (step1183 p h) (sat_cons (step1170 p h) (sat_cons (step1162 p h) (sat_cons (step445 p h) (sat_cons (step1603 p h) (sat_cons (step509 p h) (sat_cons (step1212 p h) (sat_cons (step1213 p h) (sat_cons (step1217 p h) (sat_cons (step566 p h) (sat_cons (step1208 p h) (sat_nil p))))))))))))))))))))))))))
def c1703 : List Lit := [(102, true), (115, false), (1667, true), (94, false), (99, true)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1168, c1162, c1163, c1170, c553, c1160, c1639, c481] c1703 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1168 p h) (sat_cons (step1162 p h) (sat_cons (step1163 p h) (sat_cons (step1170 p h) (sat_cons (step553 p h) (sat_cons (step1160 p h) (sat_cons (step1639 p h) (sat_cons (step481 p h) (sat_nil p))))))))))
def c1704 : List Lit := [(93, false), (1536, true), (89, false)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c942, c941, c261, c439, c1579] c1704 (by decide) p (sat_cons (step942 p h) (sat_cons (step941 p h) (sat_cons (step261 p h) (sat_cons (step439 p h) (sat_cons (step1579 p h) (sat_nil p))))))
def c1705 : List Lit := [(1640, true), (90, true), (55, false), (1625, false)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c1454, c1066, c1578, c1387, c1124, c1129, c1107, c1067, c1419, c1064] c1705 (by decide) p (sat_cons (step1454 p h) (sat_cons (step1066 p h) (sat_cons (step1578 p h) (sat_cons (step1387 p h) (sat_cons (step1124 p h) (sat_cons (step1129 p h) (sat_cons (step1107 p h) (sat_cons (step1067 p h) (sat_cons (step1419 p h) (sat_cons (step1064 p h) (sat_nil p)))))))))))
def c1706 : List Lit := [(1639, true), (1625, false)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c1387, c1118, c1123, c1107, c1066, c1384, c1061, c1076, c1077, c1053, c1596, c304] c1706 (by decide) p (sat_cons (step1387 p h) (sat_cons (step1118 p h) (sat_cons (step1123 p h) (sat_cons (step1107 p h) (sat_cons (step1066 p h) (sat_cons (step1384 p h) (sat_cons (step1061 p h) (sat_cons (step1076 p h) (sat_cons (step1077 p h) (sat_cons (step1053 p h) (sat_cons (step1596 p h) (sat_cons (step304 p h) (sat_nil p)))))))))))))
def c1707 : List Lit := [(1689, true), (1708, true), (85, false), (83, true), (91, true), (108, true), (99, true), (89, false), (86, false)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c1490, c1222, c1256, c1145, c1158, c1214, c1216, c1211, c1212, c1208, c1209, c576, c556, c1410, c1411, c1641, c1149, c509, c1154, c1162, c1188, c1167, c1170, c1192, c1160, c1157, c385, c1146, c1700] c1707 (by decide) p (sat_cons (step1490 p h) (sat_cons (step1222 p h) (sat_cons (step1256 p h) (sat_cons (step1145 p h) (sat_cons (step1158 p h) (sat_cons (step1214 p h) (sat_cons (step1216 p h) (sat_cons (step1211 p h) (sat_cons (step1212 p h) (sat_cons (step1208 p h) (sat_cons (step1209 p h) (sat_cons (step576 p h) (sat_cons (step556 p h) (sat_cons (step1410 p h) (sat_cons (step1411 p h) (sat_cons (step1641 p h) (sat_cons (step1149 p h) (sat_cons (step509 p h) (sat_cons (step1154 p h) (sat_cons (step1162 p h) (sat_cons (step1188 p h) (sat_cons (step1167 p h) (sat_cons (step1170 p h) (sat_cons (step1192 p h) (sat_cons (step1160 p h) (sat_cons (step1157 p h) (sat_cons (step385 p h) (sat_cons (step1146 p h) (sat_cons (step1700 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1708 : List Lit := [(1690, true), (96, false), (115, true), (1685, false)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c1218, c1217, c1210, c1410] c1708 (by decide) p (sat_cons (step1218 p h) (sat_cons (step1217 p h) (sat_cons (step1210 p h) (sat_cons (step1410 p h) (sat_nil p)))))
def c1709 : List Lit := [(1601, true), (53, false), (1537, true), (90, true), (93, false)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c1061, c1454, c1053, c943, c242, c260, c1581] c1709 (by decide) p (sat_cons (step1061 p h) (sat_cons (step1454 p h) (sat_cons (step1053 p h) (sat_cons (step943 p h) (sat_cons (step242 p h) (sat_cons (step260 p h) (sat_cons (step1581 p h) (sat_nil p))))))))
def c1710 : List Lit := [(110, false), (111, false), (105, false), (93, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c551, c540, c1636] c1710 (by decide) p (sat_cons (step551 p h) (sat_cons (step540 p h) (sat_cons (step1636 p h) (sat_nil p))))
def c1711 : List Lit := [(1672, true), (1653, false), (116, true), (99, true), (1657, false), (1663, false)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c1158, c1167, c1178, c1182, c1170, c1153, c1160, c1147, c1148, c1610, c490] c1711 (by decide) p (sat_cons (step1158 p h) (sat_cons (step1167 p h) (sat_cons (step1178 p h) (sat_cons (step1182 p h) (sat_cons (step1170 p h) (sat_cons (step1153 p h) (sat_cons (step1160 p h) (sat_cons (step1147 p h) (sat_cons (step1148 p h) (sat_cons (step1610 p h) (sat_cons (step490 p h) (sat_nil p))))))))))))
def c1712 : List Lit := [(1682, true), (110, true), (87, true), (93, false)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1202, c1204, c1200, c1196, c1628, c550] c1712 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1202 p h) (sat_cons (step1204 p h) (sat_cons (step1200 p h) (sat_cons (step1196 p h) (sat_cons (step1628 p h) (sat_cons (step550 p h) (sat_nil p))))))))
def c1713 : List Lit := [(1476, true), (12, true), (14, false), (13, false), (1473, false), (86, false)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c836, c838, c829, c1421, c1547, c124, c834, c92, c1553] c1713 (by decide) p (sat_cons (step836 p h) (sat_cons (step838 p h) (sat_cons (step829 p h) (sat_cons (step1421 p h) (sat_cons (step1547 p h) (sat_cons (step124 p h) (sat_cons (step834 p h) (sat_cons (step92 p h) (sat_cons (step1553 p h) (sat_nil p))))))))))
def c1714 : List Lit := [(22, false), (1522, true), (1555, true), (27, false), (1504, false), (31, true), (18, false)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c145, c146, c885, c924, c895, c1422, c920, c989, c1414, c919, c1434] c1714 (by decide) p (sat_cons (step145 p h) (sat_cons (step146 p h) (sat_cons (step885 p h) (sat_cons (step924 p h) (sat_cons (step895 p h) (sat_cons (step1422 p h) (sat_cons (step920 p h) (sat_cons (step989 p h) (sat_cons (step1414 p h) (sat_cons (step919 p h) (sat_cons (step1434 p h) (sat_nil p))))))))))))
def c1715 : List Lit := [(33, false), (47, false), (21, true), (19, false), (13, false)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c77, c191, c1540] c1715 (by decide) p (sat_cons (step77 p h) (sat_cons (step191 p h) (sat_cons (step1540 p h) (sat_nil p))))
def c1716 : List Lit := [(1505, false), (31, true), (1522, true), (1555, true), (27, false), (18, false)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c883, c893, c920, c1414, c1434, c919, c922, c989, c896, c1422, c885, c924, c148] c1716 (by decide) p (sat_cons (step883 p h) (sat_cons (step893 p h) (sat_cons (step920 p h) (sat_cons (step1414 p h) (sat_cons (step1434 p h) (sat_cons (step919 p h) (sat_cons (step922 p h) (sat_cons (step989 p h) (sat_cons (step896 p h) (sat_cons (step1422 p h) (sat_cons (step885 p h) (sat_cons (step924 p h) (sat_cons (step148 p h) (sat_nil p))))))))))))))
def c1717 : List Lit := [(1627, false), (1642, true), (1593, false)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c1069, c1126, c1389, c1109, c1131, c1384, c1070, c1076, c1077, c1061, c1596, c304, c1053] c1717 (by decide) p (sat_cons (step1069 p h) (sat_cons (step1126 p h) (sat_cons (step1389 p h) (sat_cons (step1109 p h) (sat_cons (step1131 p h) (sat_cons (step1384 p h) (sat_cons (step1070 p h) (sat_cons (step1076 p h) (sat_cons (step1077 p h) (sat_cons (step1061 p h) (sat_cons (step1596 p h) (sat_cons (step304 p h) (sat_cons (step1053 p h) (sat_nil p))))))))))))))
def c1718 : List Lit := [(85, false), (12, true), (15, true), (20, false), (13, false), (50, false)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c88, c322, c1529] c1718 (by decide) p (sat_cons (step88 p h) (sat_cons (step322 p h) (sat_cons (step1529 p h) (sat_nil p))))
def c1719 : List Lit := [(1508, false), (1521, true), (1522, true)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c920, c919, c1414, c1434] c1719 (by decide) p (sat_cons (step920 p h) (sat_cons (step919 p h) (sat_cons (step1414 p h) (sat_cons (step1434 p h) (sat_nil p)))))
def c1720 : List Lit := [(1514, true)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c903, c1434, c900] c1720 (by decide) p (sat_cons (step903 p h) (sat_cons (step1434 p h) (sat_cons (step900 p h) (sat_nil p))))
def c1721 : List Lit := [(44, false), (1515, true), (1508, true), (31, true), (27, false), (18, false), (33, false), (47, false)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c1414, c1473, c148, c906, c885, c901, c895, c1564, c886, c182] c1721 (by decide) p (sat_cons (step1414 p h) (sat_cons (step1473 p h) (sat_cons (step148 p h) (sat_cons (step906 p h) (sat_cons (step885 p h) (sat_cons (step901 p h) (sat_cons (step895 p h) (sat_cons (step1564 p h) (sat_cons (step886 p h) (sat_cons (step182 p h) (sat_nil p)))))))))))
def c1722 : List Lit := [(1515, true), (1508, true), (1527, true), (1540, false), (1556, true), (31, true), (27, false), (18, false), (33, false), (47, false)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c1720, c883, c1414, c1721, c924, c926, c932, c1567, c210, c959, c886, c986, c892, c916] c1722 (by decide) p (sat_cons (step1720 p h) (sat_cons (step883 p h) (sat_cons (step1414 p h) (sat_cons (step1721 p h) (sat_cons (step924 p h) (sat_cons (step926 p h) (sat_cons (step932 p h) (sat_cons (step1567 p h) (sat_cons (step210 p h) (sat_cons (step959 p h) (sat_cons (step886 p h) (sat_cons (step986 p h) (sat_cons (step892 p h) (sat_cons (step916 p h) (sat_nil p)))))))))))))))
def c1723 : List Lit := [(1540, false), (1522, true), (1546, true), (1556, true), (31, true), (27, false), (18, false), (33, false), (47, false)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c883, c891, c954, c964, c990, c935, c1719, c1722, c914, c917, c986, c894, c959, c885, c932, c148, c924] c1723 (by decide) p (sat_cons (step883 p h) (sat_cons (step891 p h) (sat_cons (step954 p h) (sat_cons (step964 p h) (sat_cons (step990 p h) (sat_cons (step935 p h) (sat_cons (step1719 p h) (sat_cons (step1722 p h) (sat_cons (step914 p h) (sat_cons (step917 p h) (sat_cons (step986 p h) (sat_cons (step894 p h) (sat_cons (step959 p h) (sat_cons (step885 p h) (sat_cons (step932 p h) (sat_cons (step148 p h) (sat_cons (step924 p h) (sat_nil p))))))))))))))))))
def c1724 : List Lit := [(1518, true)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c1720, c910] c1724 (by decide) p (sat_cons (step1720 p h) (sat_cons (step910 p h) (sat_nil p)))
def c1725 : List Lit := [(1593, false), (1641, true), (1626, false)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1130, c1069, c1070, c1125, c1059, c1061, c1108, c1056, c1053, c1384, c1593, c285, c1077] c1725 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1130 p h) (sat_cons (step1069 p h) (sat_cons (step1070 p h) (sat_cons (step1125 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1108 p h) (sat_cons (step1056 p h) (sat_cons (step1053 p h) (sat_cons (step1384 p h) (sat_cons (step1593 p h) (sat_cons (step285 p h) (sat_cons (step1077 p h) (sat_nil p)))))))))))))))
def c1726 : List Lit := [(1593, true), (81, true), (54, true), (50, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c1049, c1450, c1043, c231] c1726 (by decide) p (sat_cons (step1049 p h) (sat_cons (step1450 p h) (sat_cons (step1043 p h) (sat_cons (step231 p h) (sat_nil p)))))
def c1727 : List Lit := [(1708, true), (1682, false), (99, true), (1654, false), (1695, false), (1666, false), (102, true)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c1155, c1182, c1253, c1249, c1183, c1187, c1224, c1156, c1147, c1148, c1703, c1209, c1708] c1727 (by decide) p (sat_cons (step1155 p h) (sat_cons (step1182 p h) (sat_cons (step1253 p h) (sat_cons (step1249 p h) (sat_cons (step1183 p h) (sat_cons (step1187 p h) (sat_cons (step1224 p h) (sat_cons (step1156 p h) (sat_cons (step1147 p h) (sat_cons (step1148 p h) (sat_cons (step1703 p h) (sat_cons (step1209 p h) (sat_cons (step1708 p h) (sat_nil p))))))))))))))
def c1728 : List Lit := [(13, false), (15, true), (12, true), (1476, true), (82, true), (85, false), (50, false)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c840, c1718, c1528, c830, c831, c838, c124, c833] c1728 (by decide) p (sat_cons (step840 p h) (sat_cons (step1718 p h) (sat_cons (step1528 p h) (sat_cons (step830 p h) (sat_cons (step831 p h) (sat_cons (step838 p h) (sat_cons (step124 p h) (sat_cons (step833 p h) (sat_nil p)))))))))
def c1729 : List Lit := [(13, true), (1481, true), (86, false), (18, true)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c819, c857, c827, c816, c817, c824, c1510] c1729 (by decide) p (sat_cons (step819 p h) (sat_cons (step857 p h) (sat_cons (step827 p h) (sat_cons (step816 p h) (sat_cons (step817 p h) (sat_cons (step824 p h) (sat_cons (step1510 p h) (sat_nil p))))))))
def c1730 : List Lit := [(15, false), (13, false), (1481, true), (19, false), (1465, false)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c76, c73, c833, c815, c835, c824, c853] c1730 (by decide) p (sat_cons (step76 p h) (sat_cons (step73 p h) (sat_cons (step833 p h) (sat_cons (step815 p h) (sat_cons (step835 p h) (sat_cons (step824 p h) (sat_cons (step853 p h) (sat_nil p))))))))
def c1731 : List Lit := [(1475, true), (15, true), (13, false)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c835, c837, c832, c833, c829, c133, c124, c1550] c1731 (by decide) p (sat_cons (step835 p h) (sat_cons (step837 p h) (sat_cons (step832 p h) (sat_cons (step833 p h) (sat_cons (step829 p h) (sat_cons (step133 p h) (sat_cons (step124 p h) (sat_cons (step1550 p h) (sat_nil p)))))))))
def c1732 : List Lit := [(97, false), (98, false), (1656, true), (85, false)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c488, c489, c1149] c1732 (by decide) p (sat_cons (step488 p h) (sat_cons (step489 p h) (sat_cons (step1149 p h) (sat_nil p))))
def c1733 : List Lit := [(1473, true), (14, false), (86, false)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c832, c1456, c92] c1733 (by decide) p (sat_cons (step832 p h) (sat_cons (step1456 p h) (sat_cons (step92 p h) (sat_nil p))))
def c1734 : List Lit := [(1639, true), (1593, false)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c1069, c1393, c1123, c1070, c1106, c1059, c1061, c1384, c1056, c1053, c1077, c1593, c285] c1734 (by decide) p (sat_cons (step1069 p h) (sat_cons (step1393 p h) (sat_cons (step1123 p h) (sat_cons (step1070 p h) (sat_cons (step1106 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1384 p h) (sat_cons (step1056 p h) (sat_cons (step1053 p h) (sat_cons (step1077 p h) (sat_cons (step1593 p h) (sat_cons (step285 p h) (sat_nil p))))))))))))))
def c1735 : List Lit := [(1640, true), (74, true), (51, false), (1593, false)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c1077, c1384, c1106, c1069, c1124, c1129, c1111, c1070, c1385, c1059, c1061, c1078, c1056, c1053, c1596, c1593, c287] c1735 (by decide) p (sat_cons (step1077 p h) (sat_cons (step1384 p h) (sat_cons (step1106 p h) (sat_cons (step1069 p h) (sat_cons (step1124 p h) (sat_cons (step1129 p h) (sat_cons (step1111 p h) (sat_cons (step1070 p h) (sat_cons (step1385 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1078 p h) (sat_cons (step1056 p h) (sat_cons (step1053 p h) (sat_cons (step1596 p h) (sat_cons (step1593 p h) (sat_cons (step287 p h) (sat_nil p))))))))))))))))))
def c1736 : List Lit := [(50, true), (1515, false), (1555, true), (1539, false)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c911, c980, c963, c931, c927, c929, c930, c933, c958, c925, c985, c1440, c914, c883, c891] c1736 (by decide) p (sat_cons (step911 p h) (sat_cons (step980 p h) (sat_cons (step963 p h) (sat_cons (step931 p h) (sat_cons (step927 p h) (sat_cons (step929 p h) (sat_cons (step930 p h) (sat_cons (step933 p h) (sat_cons (step958 p h) (sat_cons (step925 p h) (sat_cons (step985 p h) (sat_cons (step1440 p h) (sat_cons (step914 p h) (sat_cons (step883 p h) (sat_cons (step891 p h) (sat_nil p))))))))))))))))
def c1737 : List Lit := [(18, false), (1481, true), (81, false), (89, false)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c398, c1500, c1535, c1462, c36, c829, c817, c837, c826, c853] c1737 (by decide) p (sat_cons (step398 p h) (sat_cons (step1500 p h) (sat_cons (step1535 p h) (sat_cons (step1462 p h) (sat_cons (step36 p h) (sat_cons (step829 p h) (sat_cons (step817 p h) (sat_cons (step837 p h) (sat_cons (step826 p h) (sat_cons (step853 p h) (sat_nil p)))))))))))
def c1738 : List Lit := [(14, false), (81, false), (85, false), (1476, true), (19, false), (13, false)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c1502, c34] c1738 (by decide) p (sat_cons (step1502 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1739 : List Lit := [(1555, true), (50, true), (1504, false), (1539, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c1720, c927, c930, c958, c889, c913, c980, c985, c963, c916, c931, c933, c892, c929, c925, c883, c1440] c1739 (by decide) p (sat_cons (step1720 p h) (sat_cons (step927 p h) (sat_cons (step930 p h) (sat_cons (step958 p h) (sat_cons (step889 p h) (sat_cons (step913 p h) (sat_cons (step980 p h) (sat_cons (step985 p h) (sat_cons (step963 p h) (sat_cons (step916 p h) (sat_cons (step931 p h) (sat_cons (step933 p h) (sat_cons (step892 p h) (sat_cons (step929 p h) (sat_cons (step925 p h) (sat_cons (step883 p h) (sat_cons (step1440 p h) (sat_nil p))))))))))))))))))
def c1740 : List Lit := [(1706, true), (88, true), (86, false), (83, true), (89, false), (85, false), (19, false), (81, false)]
theorem step1740 (p : Nat → Bool) (h : Constraints p) : clause p c1740 = true :=
  Snake9.LocalRup.prove_clause [c1488, c1497, c1156, c1185, c1681, c1698, c1187, c1492, c1494, c1242, c1223, c1214, c1216, c1211, c1212, c1208, c1209, c508, c576, c1641, c556] c1740 (by decide) p (sat_cons (step1488 p h) (sat_cons (step1497 p h) (sat_cons (step1156 p h) (sat_cons (step1185 p h) (sat_cons (step1681 p h) (sat_cons (step1698 p h) (sat_cons (step1187 p h) (sat_cons (step1492 p h) (sat_cons (step1494 p h) (sat_cons (step1242 p h) (sat_cons (step1223 p h) (sat_cons (step1214 p h) (sat_cons (step1216 p h) (sat_cons (step1211 p h) (sat_cons (step1212 p h) (sat_cons (step1208 p h) (sat_cons (step1209 p h) (sat_cons (step508 p h) (sat_cons (step576 p h) (sat_cons (step1641 p h) (sat_cons (step556 p h) (sat_nil p))))))))))))))))))))))
def c1741 : List Lit := [(1477, true), (86, false), (20, true), (23, false), (13, false), (14, false)]
theorem step1741 (p : Nat → Bool) (h : Constraints p) : clause p c1741 = true :=
  Snake9.LocalRup.prove_clause [c1733, c830, c839, c841, c831, c124, c1421, c834, c1553, c92] c1741 (by decide) p (sat_cons (step1733 p h) (sat_cons (step830 p h) (sat_cons (step839 p h) (sat_cons (step841 p h) (sat_cons (step831 p h) (sat_cons (step124 p h) (sat_cons (step1421 p h) (sat_cons (step834 p h) (sat_cons (step1553 p h) (sat_cons (step92 p h) (sat_nil p)))))))))))
def c1742 : List Lit := [(99, false), (1503, true), (1531, true), (27, false), (22, false)]
theorem step1742 (p : Nat → Bool) (h : Constraints p) : clause p c1742 = true :=
  Snake9.LocalRup.prove_clause [c935, c153, c152, c924, c926, c885, c933, c1440, c928] c1742 (by decide) p (sat_cons (step935 p h) (sat_cons (step153 p h) (sat_cons (step152 p h) (sat_cons (step924 p h) (sat_cons (step926 p h) (sat_cons (step885 p h) (sat_cons (step933 p h) (sat_cons (step1440 p h) (sat_cons (step928 p h) (sat_nil p))))))))))
def c1743 : List Lit := [(117, false), (119, false), (101, true), (115, false), (118, false)]
theorem step1743 (p : Nat → Bool) (h : Constraints p) : clause p c1743 = true :=
  Snake9.LocalRup.prove_clause [c556, c576, c1641] c1743 (by decide) p (sat_cons (step556 p h) (sat_cons (step576 p h) (sat_cons (step1641 p h) (sat_nil p))))
def c1744 : List Lit := [(1638, true)]
theorem step1744 (p : Nat → Bool) (h : Constraints p) : clause p c1744 = true :=
  Snake9.LocalRup.prove_clause [c1117, c1392, c1106, c1066, c1384, c1061, c1076, c1077, c1053, c1596, c304] c1744 (by decide) p (sat_cons (step1117 p h) (sat_cons (step1392 p h) (sat_cons (step1106 p h) (sat_cons (step1066 p h) (sat_cons (step1384 p h) (sat_cons (step1061 p h) (sat_cons (step1076 p h) (sat_cons (step1077 p h) (sat_cons (step1053 p h) (sat_cons (step1596 p h) (sat_cons (step304 p h) (sat_nil p))))))))))))
def c1745 : List Lit := [(108, true), (1695, true), (1708, true), (91, true), (86, false), (99, true), (83, true), (89, false), (85, false)]
theorem step1745 (p : Nat → Bool) (h : Constraints p) : clause p c1745 = true :=
  Snake9.LocalRup.prove_clause [c1490, c1707, c1223] c1745 (by decide) p (sat_cons (step1490 p h) (sat_cons (step1707 p h) (sat_cons (step1223 p h) (sat_nil p))))
end B112E024
