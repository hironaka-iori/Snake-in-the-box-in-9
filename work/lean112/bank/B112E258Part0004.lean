import B112E258Part0003
namespace B112E258
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1754 : List Lit := [(1735, true), (1755, true), (93, true), (81, true), (68, false), (65, false), (67, false)]
theorem step1754 (p : Nat → Bool) (h : Constraints p) : clause p c1754 = true :=
  Snake9.LocalRup.prove_clause [c1452, c674, c333, c1484, c326, c1532, c924, c332, c1658, c1714, c1731, c931, c1598, c1132, c1444, c1746, c1750, c319, c1286, c1288, c1192, c1752, c1296, c1299, c1724, c1725, c1193, c1197, c1291, c1629, c1172, c1170, c1753, c402, c1751, c410, c1294, c1553, c1302, c1603, c1313, c1373] c1754 (by decide) p (sat_cons (step1452 p h) (sat_cons (step674 p h) (sat_cons (step333 p h) (sat_cons (step1484 p h) (sat_cons (step326 p h) (sat_cons (step1532 p h) (sat_cons (step924 p h) (sat_cons (step332 p h) (sat_cons (step1658 p h) (sat_cons (step1714 p h) (sat_cons (step1731 p h) (sat_cons (step931 p h) (sat_cons (step1598 p h) (sat_cons (step1132 p h) (sat_cons (step1444 p h) (sat_cons (step1746 p h) (sat_cons (step1750 p h) (sat_cons (step319 p h) (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step1192 p h) (sat_cons (step1752 p h) (sat_cons (step1296 p h) (sat_cons (step1299 p h) (sat_cons (step1724 p h) (sat_cons (step1725 p h) (sat_cons (step1193 p h) (sat_cons (step1197 p h) (sat_cons (step1291 p h) (sat_cons (step1629 p h) (sat_cons (step1172 p h) (sat_cons (step1170 p h) (sat_cons (step1753 p h) (sat_cons (step402 p h) (sat_cons (step1751 p h) (sat_cons (step410 p h) (sat_cons (step1294 p h) (sat_cons (step1553 p h) (sat_cons (step1302 p h) (sat_cons (step1603 p h) (sat_cons (step1313 p h) (sat_cons (step1373 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
def c1755 : List Lit := [(1755, true), (93, true), (81, true), (68, false), (65, false), (67, false)]
theorem step1755 (p : Nat → Bool) (h : Constraints p) : clause p c1755 = true :=
  Snake9.TreeRup.prove_clause [c1452, c674, c677, c332, c1658, c1192, c333, c1217, c1225, c1210, c1212, c1236, c1258, c1714, c326, c1532, c924, c1484, c1731, c931, c933, c1598, c947, c1132, c1444, c1746, c1750, c319, c1754, c1418, c1411, c1259, c1265, c1446, c1241, c1237, c1193, c1145, c1213, c1215, c1228, c1226, c1629, c1011, c1211, c402, c1219, c1220, c1221, c404, c455, c466, c955, c493, c958, c966, c983, c969, c972, c987, c982, c963, c964, c961, c1017, c162, c1579] c1755 (by decide) p (sat_cons (step1452 p h) (sat_cons (step674 p h) (sat_cons (step677 p h) (sat_cons (step332 p h) (sat_cons (step1658 p h) (sat_cons (step1192 p h) (sat_cons (step333 p h) (sat_cons (step1217 p h) (sat_cons (step1225 p h) (sat_cons (step1210 p h) (sat_cons (step1212 p h) (sat_cons (step1236 p h) (sat_cons (step1258 p h) (sat_cons (step1714 p h) (sat_cons (step326 p h) (sat_cons (step1532 p h) (sat_cons (step924 p h) (sat_cons (step1484 p h) (sat_cons (step1731 p h) (sat_cons (step931 p h) (sat_cons (step933 p h) (sat_cons (step1598 p h) (sat_cons (step947 p h) (sat_cons (step1132 p h) (sat_cons (step1444 p h) (sat_cons (step1746 p h) (sat_cons (step1750 p h) (sat_cons (step319 p h) (sat_cons (step1754 p h) (sat_cons (step1418 p h) (sat_cons (step1411 p h) (sat_cons (step1259 p h) (sat_cons (step1265 p h) (sat_cons (step1446 p h) (sat_cons (step1241 p h) (sat_cons (step1237 p h) (sat_cons (step1193 p h) (sat_cons (step1145 p h) (sat_cons (step1213 p h) (sat_cons (step1215 p h) (sat_cons (step1228 p h) (sat_cons (step1226 p h) (sat_cons (step1629 p h) (sat_cons (step1011 p h) (sat_cons (step1211 p h) (sat_cons (step402 p h) (sat_cons (step1219 p h) (sat_cons (step1220 p h) (sat_cons (step1221 p h) (sat_cons (step404 p h) (sat_cons (step455 p h) (sat_cons (step466 p h) (sat_cons (step955 p h) (sat_cons (step493 p h) (sat_cons (step958 p h) (sat_cons (step966 p h) (sat_cons (step983 p h) (sat_cons (step969 p h) (sat_cons (step972 p h) (sat_cons (step987 p h) (sat_cons (step982 p h) (sat_cons (step963 p h) (sat_cons (step964 p h) (sat_cons (step961 p h) (sat_cons (step1017 p h) (sat_cons (step162 p h) (sat_cons (step1579 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1756 : List Lit := [(1508, false), (1523, false), (71, true), (1545, true), (1504, false)]
theorem step1756 (p : Nat → Bool) (h : Constraints p) : clause p c1756 = true :=
  Snake9.LocalRup.prove_clause [c642, c981, c1016, c948, c933, c936, c947, c928, c1010, c41, c40, c982, c1461, c969, c967] c1756 (by decide) p (sat_cons (step642 p h) (sat_cons (step981 p h) (sat_cons (step1016 p h) (sat_cons (step948 p h) (sat_cons (step933 p h) (sat_cons (step936 p h) (sat_cons (step947 p h) (sat_cons (step928 p h) (sat_cons (step1010 p h) (sat_cons (step41 p h) (sat_cons (step40 p h) (sat_cons (step982 p h) (sat_cons (step1461 p h) (sat_cons (step969 p h) (sat_cons (step967 p h) (sat_nil p))))))))))))))))
def c1757 : List Lit := [(1643, true), (79, false), (71, true), (75, true), (1545, true), (1504, false), (64, true), (69, true), (65, false)]
theorem step1757 (p : Nat → Bool) (h : Constraints p) : clause p c1757 = true :=
  Snake9.LocalRup.prove_clause [c674, c402, c1629, c404, c955, c958, c1756, c931, c1597, c1729, c1181, c1179, c1189] c1757 (by decide) p (sat_cons (step674 p h) (sat_cons (step402 p h) (sat_cons (step1629 p h) (sat_cons (step404 p h) (sat_cons (step955 p h) (sat_cons (step958 p h) (sat_cons (step1756 p h) (sat_cons (step931 p h) (sat_cons (step1597 p h) (sat_cons (step1729 p h) (sat_cons (step1181 p h) (sat_cons (step1179 p h) (sat_cons (step1189 p h) (sat_nil p))))))))))))))
def c1758 : List Lit := [(19, false), (14, false), (15, false), (64, true), (65, false)]
theorem step1758 (p : Nat → Bool) (h : Constraints p) : clause p c1758 = true :=
  Snake9.LocalRup.prove_clause [c667, c55, c64, c307] c1758 (by decide) p (sat_cons (step667 p h) (sat_cons (step55 p h) (sat_cons (step64 p h) (sat_cons (step307 p h) (sat_nil p)))))
def c1759 : List Lit := [(1535, true), (22, true), (1507, true), (1521, false), (19, true), (71, true)]
theorem step1759 (p : Nat → Bool) (h : Constraints p) : clause p c1759 = true :=
  Snake9.LocalRup.prove_clause [c647, c642, c958, c986, c982, c959, c961, c969, c957, c967, c96, c102, c929, c41, c40, c1461] c1759 (by decide) p (sat_cons (step647 p h) (sat_cons (step642 p h) (sat_cons (step958 p h) (sat_cons (step986 p h) (sat_cons (step982 p h) (sat_cons (step959 p h) (sat_cons (step961 p h) (sat_cons (step969 p h) (sat_cons (step957 p h) (sat_cons (step967 p h) (sat_cons (step96 p h) (sat_cons (step102 p h) (sat_cons (step929 p h) (sat_cons (step41 p h) (sat_cons (step40 p h) (sat_cons (step1461 p h) (sat_nil p)))))))))))))))))
def c1760 : List Lit := [(1535, false), (1529, true), (1735, false), (1647, false), (71, true), (1545, true), (81, true), (1600, false), (1504, false), (85, true)]
theorem step1760 (p : Nat → Bool) (h : Constraints p) : clause p c1760 = true :=
  Snake9.LocalRup.prove_clause [c1452, c642, c677, c1210, c1212, c946, c1217, c1225, c1003, c1010, c1132, c947, c1444, c935, c1425, c928, c1266, c41, c40, c1241, c1237, c1461, c1213, c1228, c1226, c968, c1211, c1219, c1220, c1221, c455, c466, c493] c1760 (by decide) p (sat_cons (step1452 p h) (sat_cons (step642 p h) (sat_cons (step677 p h) (sat_cons (step1210 p h) (sat_cons (step1212 p h) (sat_cons (step946 p h) (sat_cons (step1217 p h) (sat_cons (step1225 p h) (sat_cons (step1003 p h) (sat_cons (step1010 p h) (sat_cons (step1132 p h) (sat_cons (step947 p h) (sat_cons (step1444 p h) (sat_cons (step935 p h) (sat_cons (step1425 p h) (sat_cons (step928 p h) (sat_cons (step1266 p h) (sat_cons (step41 p h) (sat_cons (step40 p h) (sat_cons (step1241 p h) (sat_cons (step1237 p h) (sat_cons (step1461 p h) (sat_cons (step1213 p h) (sat_cons (step1228 p h) (sat_cons (step1226 p h) (sat_cons (step968 p h) (sat_cons (step1211 p h) (sat_cons (step1219 p h) (sat_cons (step1220 p h) (sat_cons (step1221 p h) (sat_cons (step455 p h) (sat_cons (step466 p h) (sat_cons (step493 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c1761 : List Lit := [(1521, false), (19, true), (1638, false), (77, true), (1678, true), (1735, false), (1647, false), (80, false), (79, false), (71, true), (1545, true), (81, true), (1600, false), (1504, false), (85, true)]
theorem step1761 (p : Nat → Bool) (h : Constraints p) : clause p c1761 = true :=
  Snake9.LocalRup.prove_clause [c677, c1210, c1212, c1267, c1238, c1217, c1225, c1236, c1278, c946, c1004, c958, c981, c983, c1016, c970, c948, c938, c1760, c982, c1759, c969, c971, c404, c966, c964, c1182, c1190, c1194, c1199, c1273, c1172, c1237, c1170, c1228, c1226, c1604, c1219, c1220, c466, c493] c1761 (by decide) p (sat_cons (step677 p h) (sat_cons (step1210 p h) (sat_cons (step1212 p h) (sat_cons (step1267 p h) (sat_cons (step1238 p h) (sat_cons (step1217 p h) (sat_cons (step1225 p h) (sat_cons (step1236 p h) (sat_cons (step1278 p h) (sat_cons (step946 p h) (sat_cons (step1004 p h) (sat_cons (step958 p h) (sat_cons (step981 p h) (sat_cons (step983 p h) (sat_cons (step1016 p h) (sat_cons (step970 p h) (sat_cons (step948 p h) (sat_cons (step938 p h) (sat_cons (step1760 p h) (sat_cons (step982 p h) (sat_cons (step1759 p h) (sat_cons (step969 p h) (sat_cons (step971 p h) (sat_cons (step404 p h) (sat_cons (step966 p h) (sat_cons (step964 p h) (sat_cons (step1182 p h) (sat_cons (step1190 p h) (sat_cons (step1194 p h) (sat_cons (step1199 p h) (sat_cons (step1273 p h) (sat_cons (step1172 p h) (sat_cons (step1237 p h) (sat_cons (step1170 p h) (sat_cons (step1228 p h) (sat_cons (step1226 p h) (sat_cons (step1604 p h) (sat_cons (step1219 p h) (sat_cons (step1220 p h) (sat_cons (step466 p h) (sat_cons (step493 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c1762 : List Lit := [(1508, true), (1735, false), (79, false), (71, true), (75, true), (1620, true), (81, true), (1600, false), (1504, false), (64, true), (85, true), (69, true), (65, false)]
theorem step1762 (p : Nat → Bool) (h : Constraints p) : clause p c1762 = true :=
  Snake9.LocalRup.prove_clause [c674, c1452, c645, c647, c656, c1607, c1125, c1443, c1430, c1138, c1757, c1193, c402, c1127, c930, c931, c78, c1597, c1729, c1179, c1758, c1761, c955, c956, c96, c97, c127, c128, c219, c1684, c1042, c1104, c1050, c1053] c1762 (by decide) p (sat_cons (step674 p h) (sat_cons (step1452 p h) (sat_cons (step645 p h) (sat_cons (step647 p h) (sat_cons (step656 p h) (sat_cons (step1607 p h) (sat_cons (step1125 p h) (sat_cons (step1443 p h) (sat_cons (step1430 p h) (sat_cons (step1138 p h) (sat_cons (step1757 p h) (sat_cons (step1193 p h) (sat_cons (step402 p h) (sat_cons (step1127 p h) (sat_cons (step930 p h) (sat_cons (step931 p h) (sat_cons (step78 p h) (sat_cons (step1597 p h) (sat_cons (step1729 p h) (sat_cons (step1179 p h) (sat_cons (step1758 p h) (sat_cons (step1761 p h) (sat_cons (step955 p h) (sat_cons (step956 p h) (sat_cons (step96 p h) (sat_cons (step97 p h) (sat_cons (step127 p h) (sat_cons (step128 p h) (sat_cons (step219 p h) (sat_cons (step1684 p h) (sat_cons (step1042 p h) (sat_cons (step1104 p h) (sat_cons (step1050 p h) (sat_cons (step1053 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c1763 : List Lit := [(1735, false), (79, false), (71, true), (75, true), (1620, true), (81, true), (1600, false), (64, true), (85, true), (69, true), (8, true), (65, false)]
theorem step1763 (p : Nat → Bool) (h : Constraints p) : clause p c1763 = true :=
  Snake9.LocalRup.prove_clause [c1452, c677, c1532, c924, c1138, c1757, c1193, c1210, c1212, c1217, c1225, c1762, c933, c1598, c1756, c947, c1132, c960, c1010, c1444, c978, c1425, c1266, c1241, c1237, c1213, c1228, c1226, c1211, c1219, c1220, c1221, c455, c466, c493, c966, c969, c972, c977, c963, c964, c1016, c1579, c162] c1763 (by decide) p (sat_cons (step1452 p h) (sat_cons (step677 p h) (sat_cons (step1532 p h) (sat_cons (step924 p h) (sat_cons (step1138 p h) (sat_cons (step1757 p h) (sat_cons (step1193 p h) (sat_cons (step1210 p h) (sat_cons (step1212 p h) (sat_cons (step1217 p h) (sat_cons (step1225 p h) (sat_cons (step1762 p h) (sat_cons (step933 p h) (sat_cons (step1598 p h) (sat_cons (step1756 p h) (sat_cons (step947 p h) (sat_cons (step1132 p h) (sat_cons (step960 p h) (sat_cons (step1010 p h) (sat_cons (step1444 p h) (sat_cons (step978 p h) (sat_cons (step1425 p h) (sat_cons (step1266 p h) (sat_cons (step1241 p h) (sat_cons (step1237 p h) (sat_cons (step1213 p h) (sat_cons (step1228 p h) (sat_cons (step1226 p h) (sat_cons (step1211 p h) (sat_cons (step1219 p h) (sat_cons (step1220 p h) (sat_cons (step1221 p h) (sat_cons (step455 p h) (sat_cons (step466 p h) (sat_cons (step493 p h) (sat_cons (step966 p h) (sat_cons (step969 p h) (sat_cons (step972 p h) (sat_cons (step977 p h) (sat_cons (step963 p h) (sat_cons (step964 p h) (sat_cons (step1016 p h) (sat_cons (step1579 p h) (sat_cons (step162 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c1764 : List Lit := [(1528, false), (86, false), (1531, true), (18, false), (1508, false), (1545, true)]
theorem step1764 (p : Nat → Bool) (h : Constraints p) : clause p c1764 = true :=
  Snake9.LocalRup.prove_clause [c969, c972, c977, c963, c964, c1016, c1579, c162] c1764 (by decide) p (sat_cons (step969 p h) (sat_cons (step972 p h) (sat_cons (step977 p h) (sat_cons (step963 p h) (sat_cons (step964 p h) (sat_cons (step1016 p h) (sat_cons (step1579 p h) (sat_cons (step162 p h) (sat_nil p)))))))))
def c1765 : List Lit := [(1659, true), (99, false), (1531, true), (18, false), (1508, false), (1545, true)]
theorem step1765 (p : Nat → Bool) (h : Constraints p) : clause p c1765 = true :=
  Snake9.LocalRup.prove_clause [c652, c1220, c1221, c1764, c966, c967, c185, c495, c190] c1765 (by decide) p (sat_cons (step652 p h) (sat_cons (step1220 p h) (sat_cons (step1221 p h) (sat_cons (step1764 p h) (sat_cons (step966 p h) (sat_cons (step967 p h) (sat_cons (step185 p h) (sat_cons (step495 p h) (sat_cons (step190 p h) (sat_nil p))))))))))
def c1766 : List Lit := [(83, true), (84, false), (99, false)]
theorem step1766 (p : Nat → Bool) (h : Constraints p) : clause p c1766 = true :=
  Snake9.LocalRup.prove_clause [c677, c465, c466, c1495] c1766 (by decide) p (sat_cons (step677 p h) (sat_cons (step465 p h) (sat_cons (step466 p h) (sat_cons (step1495 p h) (sat_nil p)))))
def c1767 : List Lit := [(1523, true), (19, true)]
theorem step1767 (p : Nat → Bool) (h : Constraints p) : clause p c1767 = true :=
  Snake9.LocalRup.prove_clause [c647, c958, c960, c955, c956, c117, c96] c1767 (by decide) p (sat_cons (step647 p h) (sat_cons (step958 p h) (sat_cons (step960 p h) (sat_cons (step955 p h) (sat_cons (step956 p h) (sat_cons (step117 p h) (sat_cons (step96 p h) (sat_nil p))))))))
def c1768 : List Lit := [(1662, false), (1678, true), (83, false), (84, false), (1643, false), (81, true)]
theorem step1768 (p : Nat → Bool) (h : Constraints p) : clause p c1768 = true :=
  Snake9.LocalRup.prove_clause [c1193, c1267, c1210, c1212, c1237, c1273, c1242, c1198, c1213, c1172, c1211, c1170, c447] c1768 (by decide) p (sat_cons (step1193 p h) (sat_cons (step1267 p h) (sat_cons (step1210 p h) (sat_cons (step1212 p h) (sat_cons (step1237 p h) (sat_cons (step1273 p h) (sat_cons (step1242 p h) (sat_cons (step1198 p h) (sat_cons (step1213 p h) (sat_cons (step1172 p h) (sat_cons (step1211 p h) (sat_cons (step1170 p h) (sat_cons (step447 p h) (sat_nil p))))))))))))))
def c1769 : List Lit := [(1724, true), (1694, true), (103, false), (64, true), (67, false)]
theorem step1769 (p : Nat → Bool) (h : Constraints p) : clause p c1769 = true :=
  Snake9.LocalRup.prove_clause [c1585, c1594, c563, c1298] c1769 (by decide) p (sat_cons (step1585 p h) (sat_cons (step1594 p h) (sat_cons (step563 p h) (sat_cons (step1298 p h) (sat_nil p)))))
def c1770 : List Lit := [(1693, false), (1701, true), (79, false), (71, true), (75, true), (1686, false)]
theorem step1770 (p : Nat → Bool) (h : Constraints p) : clause p c1770 = true :=
  Snake9.LocalRup.prove_clause [c1288, c1313, c1299, c1302, c1317, c1294, c1291, c1751] c1770 (by decide) p (sat_cons (step1288 p h) (sat_cons (step1313 p h) (sat_cons (step1299 p h) (sat_cons (step1302 p h) (sat_cons (step1317 p h) (sat_cons (step1294 p h) (sat_cons (step1291 p h) (sat_cons (step1751 p h) (sat_nil p)))))))))
def c1771 : List Lit := [(1693, true), (103, false), (67, false)]
theorem step1771 (p : Nat → Bool) (h : Constraints p) : clause p c1771 = true :=
  Snake9.LocalRup.prove_clause [c1296, c1297, c561] c1771 (by decide) p (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step561 p h) (sat_nil p))))
def c1772 : List Lit := [(79, false), (103, false), (93, true), (81, true), (68, false), (65, false), (67, false)]
theorem step1772 (p : Nat → Bool) (h : Constraints p) : clause p c1772 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1576, c1771, c1299, c319, c320, c1755, c1445, c1286, c1288, c1714, c1484, c333, c332, c326, c1763, c1377, c1314, c1770, c1373, c1585, c1769, c563, c1303, c1725, c1294, c1291, c1751] c1772 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1576 p h) (sat_cons (step1771 p h) (sat_cons (step1299 p h) (sat_cons (step319 p h) (sat_cons (step320 p h) (sat_cons (step1755 p h) (sat_cons (step1445 p h) (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step1714 p h) (sat_cons (step1484 p h) (sat_cons (step333 p h) (sat_cons (step332 p h) (sat_cons (step326 p h) (sat_cons (step1763 p h) (sat_cons (step1377 p h) (sat_cons (step1314 p h) (sat_cons (step1770 p h) (sat_cons (step1373 p h) (sat_cons (step1585 p h) (sat_cons (step1769 p h) (sat_cons (step563 p h) (sat_cons (step1303 p h) (sat_cons (step1725 p h) (sat_cons (step1294 p h) (sat_cons (step1291 p h) (sat_cons (step1751 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1773 : List Lit := [(86, false), (83, false), (1662, false), (94, false), (1679, true), (79, true), (81, true), (1642, false)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c457, c453, c1211, c1170, c1216, c1172, c1247, c1197, c1268] c1773 (by decide) p (sat_cons (step457 p h) (sat_cons (step453 p h) (sat_cons (step1211 p h) (sat_cons (step1170 p h) (sat_cons (step1216 p h) (sat_cons (step1172 p h) (sat_cons (step1247 p h) (sat_cons (step1197 p h) (sat_cons (step1268 p h) (sat_nil p))))))))))
def c1774 : List Lit := [(83, false), (1658, false), (94, false), (1679, true), (79, true), (81, true), (1642, false)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c1228, c1192, c1262, c1210, c1215, c1773, c1221, c1229, c1248, c1243, c1216, c1268, c1211, c1197, c449, c1172, c1170] c1774 (by decide) p (sat_cons (step1228 p h) (sat_cons (step1192 p h) (sat_cons (step1262 p h) (sat_cons (step1210 p h) (sat_cons (step1215 p h) (sat_cons (step1773 p h) (sat_cons (step1221 p h) (sat_cons (step1229 p h) (sat_cons (step1248 p h) (sat_cons (step1243 p h) (sat_cons (step1216 p h) (sat_cons (step1268 p h) (sat_cons (step1211 p h) (sat_cons (step1197 p h) (sat_cons (step449 p h) (sat_cons (step1172 p h) (sat_cons (step1170 p h) (sat_nil p))))))))))))))))))
def c1775 : List Lit := [(82, false), (83, true), (1724, true), (98, false), (90, false), (64, true)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c676, c1735, c484, c430] c1775 (by decide) p (sat_cons (step676 p h) (sat_cons (step1735 p h) (sat_cons (step484 p h) (sat_cons (step430 p h) (sat_nil p)))))
def c1776 : List Lit := [(1658, false), (1724, true), (94, false), (99, false), (98, false), (90, false), (1679, true), (1734, false), (79, true), (81, true), (1642, false), (1543, false), (64, true)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c683, c1452, c1563, c1192, c1262, c1228, c1774, c522, c523, c529, c1775, c1211, c1216, c1247, c1248, c1261, c1229, c1429, c1221, c1444, c537, c1126, c1034, c1103, c1036, c1059] c1776 (by decide) p (sat_cons (step683 p h) (sat_cons (step1452 p h) (sat_cons (step1563 p h) (sat_cons (step1192 p h) (sat_cons (step1262 p h) (sat_cons (step1228 p h) (sat_cons (step1774 p h) (sat_cons (step522 p h) (sat_cons (step523 p h) (sat_cons (step529 p h) (sat_cons (step1775 p h) (sat_cons (step1211 p h) (sat_cons (step1216 p h) (sat_cons (step1247 p h) (sat_cons (step1248 p h) (sat_cons (step1261 p h) (sat_cons (step1229 p h) (sat_cons (step1429 p h) (sat_cons (step1221 p h) (sat_cons (step1444 p h) (sat_cons (step537 p h) (sat_cons (step1126 p h) (sat_cons (step1034 p h) (sat_cons (step1103 p h) (sat_cons (step1036 p h) (sat_cons (step1059 p h) (sat_nil p)))))))))))))))))))))))))))
def c1777 : List Lit := [(84, false), (94, false), (99, false), (1670, true), (79, true), (81, true), (1657, false)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c685, c1766, c532, c460, c456, c548, c1211, c496, c1216, c1222, c1248, c1227] c1777 (by decide) p (sat_cons (step685 p h) (sat_cons (step1766 p h) (sat_cons (step532 p h) (sat_cons (step460 p h) (sat_cons (step456 p h) (sat_cons (step548 p h) (sat_cons (step1211 p h) (sat_cons (step496 p h) (sat_cons (step1216 p h) (sat_cons (step1222 p h) (sat_cons (step1248 p h) (sat_cons (step1227 p h) (sat_nil p)))))))))))))
def c1778 : List Lit := [(94, false), (99, false), (98, false), (90, false), (1701, false), (79, true), (81, true), (1757, true), (1642, false), (1543, false), (64, true), (85, true)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c1576, c683, c1452, c1563, c1192, c1372, c1436, c1262, c1210, c1215, c1217, c1777, c1219, c1228, c1774, c1776, c1242, c522, c523, c1373, c1260, c529, c1430, c1425, c1261, c1444, c1243, c1126, c1229, c1103, c1221, c1059, c537, c1036, c1034] c1778 (by decide) p (sat_cons (step1576 p h) (sat_cons (step683 p h) (sat_cons (step1452 p h) (sat_cons (step1563 p h) (sat_cons (step1192 p h) (sat_cons (step1372 p h) (sat_cons (step1436 p h) (sat_cons (step1262 p h) (sat_cons (step1210 p h) (sat_cons (step1215 p h) (sat_cons (step1217 p h) (sat_cons (step1777 p h) (sat_cons (step1219 p h) (sat_cons (step1228 p h) (sat_cons (step1774 p h) (sat_cons (step1776 p h) (sat_cons (step1242 p h) (sat_cons (step522 p h) (sat_cons (step523 p h) (sat_cons (step1373 p h) (sat_cons (step1260 p h) (sat_cons (step529 p h) (sat_cons (step1430 p h) (sat_cons (step1425 p h) (sat_cons (step1261 p h) (sat_cons (step1444 p h) (sat_cons (step1243 p h) (sat_cons (step1126 p h) (sat_cons (step1229 p h) (sat_cons (step1103 p h) (sat_cons (step1221 p h) (sat_cons (step1059 p h) (sat_cons (step537 p h) (sat_cons (step1036 p h) (sat_cons (step1034 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1779 : List Lit := [(2, false), (4, true)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c639, c3] c1779 (by decide) p (sat_cons (step639 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1780 : List Lit := [(2, false), (1, true)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c639, c4] c1780 (by decide) p (sat_cons (step639 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1781 : List Lit := [(4, false), (2, true)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c1498, c6] c1781 (by decide) p (sat_cons (step1498 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1782 : List Lit := [(4, false), (126, true)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c1498, c7] c1782 (by decide) p (sat_cons (step1498 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1783 : List Lit := [(26, true), (9, true), (8, false), (68, true)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c641, c18] c1783 (by decide) p (sat_cons (step641 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1784 : List Lit := [(26, true), (8, false), (6, true), (68, true)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c641, c19] c1784 (by decide) p (sat_cons (step641 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1785 : List Lit := [(6, true), (9, true), (8, false), (68, true)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c641, c20] c1785 (by decide) p (sat_cons (step641 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1786 : List Lit := [(9, true), (6, true), (8, false), (26, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c641, c21] c1786 (by decide) p (sat_cons (step641 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1787 : List Lit := [(32, true), (12, false), (71, true)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c642, c40] c1787 (by decide) p (sat_cons (step642 p h) (sat_cons (step40 p h) (sat_nil p)))
def c1788 : List Lit := [(10, true), (12, false), (71, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c642, c41] c1788 (by decide) p (sat_cons (step642 p h) (sat_cons (step41 p h) (sat_nil p)))
def c1789 : List Lit := [(10, true), (32, true), (12, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c642, c42] c1789 (by decide) p (sat_cons (step642 p h) (sat_cons (step42 p h) (sat_nil p)))
def c1790 : List Lit := [(11, true), (72, true), (23, true), (13, false)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c643, c47] c1790 (by decide) p (sat_cons (step643 p h) (sat_cons (step47 p h) (sat_nil p)))
def c1791 : List Lit := [(9, true), (72, true), (13, false), (23, true)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c643, c48] c1791 (by decide) p (sat_cons (step643 p h) (sat_cons (step48 p h) (sat_nil p)))
def c1792 : List Lit := [(11, true), (9, true), (72, true), (13, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c643, c49] c1792 (by decide) p (sat_cons (step643 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1793 : List Lit := [(11, true), (9, true), (13, false), (23, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c643, c50] c1793 (by decide) p (sat_cons (step643 p h) (sat_cons (step50 p h) (sat_nil p)))
def c1794 : List Lit := [(36, true), (17, false), (75, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c645, c77] c1794 (by decide) p (sat_cons (step645 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1795 : List Lit := [(17, false), (14, true), (75, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c645, c78] c1795 (by decide) p (sat_cons (step645 p h) (sat_cons (step78 p h) (sat_nil p)))
def c1796 : List Lit := [(36, true), (17, false), (14, true)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c645, c79] c1796 (by decide) p (sat_cons (step645 p h) (sat_cons (step79 p h) (sat_nil p)))
def c1797 : List Lit := [(76, true), (16, true), (23, true), (18, false)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c646, c82] c1797 (by decide) p (sat_cons (step646 p h) (sat_cons (step82 p h) (sat_nil p)))
def c1798 : List Lit := [(9, true), (76, true), (18, false), (23, true)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c646, c83] c1798 (by decide) p (sat_cons (step646 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1799 : List Lit := [(16, true), (9, true), (23, true), (18, false)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c646, c84] c1799 (by decide) p (sat_cons (step646 p h) (sat_cons (step84 p h) (sat_nil p)))
def c1800 : List Lit := [(40, true), (23, true), (21, false)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c647, c94] c1800 (by decide) p (sat_cons (step647 p h) (sat_cons (step94 p h) (sat_nil p)))
def c1801 : List Lit := [(40, true), (21, false), (19, true)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c647, c95] c1801 (by decide) p (sat_cons (step647 p h) (sat_cons (step95 p h) (sat_nil p)))
def c1802 : List Lit := [(23, true), (21, false), (19, true)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c647, c96] c1802 (by decide) p (sat_cons (step647 p h) (sat_cons (step96 p h) (sat_nil p)))
def c1803 : List Lit := [(23, true), (22, false), (80, true)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c648, c98] c1803 (by decide) p (sat_cons (step648 p h) (sat_cons (step98 p h) (sat_nil p)))
def c1804 : List Lit := [(20, true), (22, false), (80, true)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c648, c99] c1804 (by decide) p (sat_cons (step648 p h) (sat_cons (step99 p h) (sat_nil p)))
def c1805 : List Lit := [(20, true), (23, true), (22, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c648, c100] c1805 (by decide) p (sat_cons (step648 p h) (sat_cons (step100 p h) (sat_nil p)))
def c1806 : List Lit := [(54, true), (24, true), (83, true), (27, true), (25, false)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c649, c148] c1806 (by decide) p (sat_cons (step649 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1807 : List Lit := [(54, true), (7, true), (25, false), (27, true), (83, true)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c649, c149] c1807 (by decide) p (sat_cons (step649 p h) (sat_cons (step149 p h) (sat_nil p)))
def c1808 : List Lit := [(7, true), (24, true), (25, false), (83, true), (27, true)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c649, c150] c1808 (by decide) p (sat_cons (step649 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1809 : List Lit := [(54, true), (24, true), (7, true), (25, false), (27, true)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c649, c151] c1809 (by decide) p (sat_cons (step649 p h) (sat_cons (step151 p h) (sat_nil p)))
def c1810 : List Lit := [(27, true), (26, true), (28, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c650, c171] c1810 (by decide) p (sat_cons (step650 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1811 : List Lit := [(9, true), (27, true), (28, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c650, c172] c1811 (by decide) p (sat_cons (step650 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1812 : List Lit := [(9, true), (26, true), (28, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c650, c173] c1812 (by decide) p (sat_cons (step650 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1813 : List Lit := [(30, true), (89, true), (31, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c652, c190] c1813 (by decide) p (sat_cons (step652 p h) (sat_cons (step190 p h) (sat_nil p)))
def c1814 : List Lit := [(11, true), (89, true), (31, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c652, c191] c1814 (by decide) p (sat_cons (step652 p h) (sat_cons (step191 p h) (sat_nil p)))
def c1815 : List Lit := [(30, true), (11, true), (31, false)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c652, c192] c1815 (by decide) p (sat_cons (step652 p h) (sat_cons (step192 p h) (sat_nil p)))
def c1816 : List Lit := [(92, true), (32, true), (33, false)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c653, c200] c1816 (by decide) p (sat_cons (step653 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1817 : List Lit := [(92, true), (27, true), (33, false)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c653, c201] c1817 (by decide) p (sat_cons (step653 p h) (sat_cons (step201 p h) (sat_nil p)))
end B112E258
