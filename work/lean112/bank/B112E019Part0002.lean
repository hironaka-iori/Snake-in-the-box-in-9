import B112E019Part0001
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1934 : List Lit := [(1639, true), (96, true), (208, true), (106, true)]
theorem step1934 (p : Nat → Bool) (h : Constraints p) : clause p c1934 = true :=
  Snake9.LocalRup.prove_clause [c1482, c1484, c1479, c1480, c1476, c463, c465] c1934 (by decide) p (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1479 p h) (sat_cons (step1480 p h) (sat_cons (step1476 p h) (sat_cons (step463 p h) (sat_cons (step465 p h) (sat_nil p))))))))
def c1935 : List Lit := [(1629, true), (201, true), (100, true), (99, false)]
theorem step1935 (p : Nat → Bool) (h : Constraints p) : clause p c1935 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1895, c403] c1935 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1895 p h) (sat_cons (step403 p h) (sat_nil p))))
def c1936 : List Lit := [(1627, true), (77, true), (196, true), (116, false)]
theorem step1936 (p : Nat → Bool) (h : Constraints p) : clause p c1936 = true :=
  Snake9.LocalRup.prove_clause [c1462, c1463, c1932] c1936 (by decide) p (sat_cons (step1462 p h) (sat_cons (step1463 p h) (sat_cons (step1932 p h) (sat_nil p))))
def c1937 : List Lit := [(1566, true), (1551, false), (176, true), (117, true)]
theorem step1937 (p : Nat → Bool) (h : Constraints p) : clause p c1937 = true :=
  Snake9.LocalRup.prove_clause [c1322, c1346, c1343, c1325, c1335, c1317, c1876] c1937 (by decide) p (sat_cons (step1322 p h) (sat_cons (step1346 p h) (sat_cons (step1343 p h) (sat_cons (step1325 p h) (sat_cons (step1335 p h) (sat_cons (step1317 p h) (sat_cons (step1876 p h) (sat_nil p))))))))
def c1938 : List Lit := [(1557, true), (176, true), (118, false), (117, true)]
theorem step1938 (p : Nat → Bool) (h : Constraints p) : clause p c1938 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1331, c259, c265] c1938 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1331 p h) (sat_cons (step259 p h) (sat_cons (step265 p h) (sat_nil p)))))
def c1939 : List Lit := [(1627, true), (77, false), (118, false)]
theorem step1939 (p : Nat → Bool) (h : Constraints p) : clause p c1939 = true :=
  Snake9.LocalRup.prove_clause [c1462, c1463, c380] c1939 (by decide) p (sat_cons (step1462 p h) (sat_cons (step1463 p h) (sat_cons (step380 p h) (sat_nil p))))
def c1940 : List Lit := [(75, true), (76, true), (67, true), (1657, true), (1629, false), (63, true), (192, true), (193, true)]
theorem step1940 (p : Nat → Bool) (h : Constraints p) : clause p c1940 = true :=
  Snake9.LocalRup.prove_clause [c888, c383, c1464, c337, c1474, c1933, c1504, c1543] c1940 (by decide) p (sat_cons (step888 p h) (sat_cons (step383 p h) (sat_cons (step1464 p h) (sat_cons (step337 p h) (sat_cons (step1474 p h) (sat_cons (step1933 p h) (sat_cons (step1504 p h) (sat_cons (step1543 p h) (sat_nil p)))))))))
def c1941 : List Lit := [(1576, true), (1543, false), (1561, false), (55, true), (175, true), (56, true), (1531, false)]
theorem step1941 (p : Nat → Bool) (h : Constraints p) : clause p c1941 = true :=
  Snake9.LocalRup.prove_clause [c1339, c1364, c1369, c1340, c1343, c1308, c1337, c1324, c1332, c1317, c255, c194, c195, c1288, c1291, c1297] c1941 (by decide) p (sat_cons (step1339 p h) (sat_cons (step1364 p h) (sat_cons (step1369 p h) (sat_cons (step1340 p h) (sat_cons (step1343 p h) (sat_cons (step1308 p h) (sat_cons (step1337 p h) (sat_cons (step1324 p h) (sat_cons (step1332 p h) (sat_cons (step1317 p h) (sat_cons (step255 p h) (sat_cons (step194 p h) (sat_cons (step195 p h) (sat_cons (step1288 p h) (sat_cons (step1291 p h) (sat_cons (step1297 p h) (sat_nil p)))))))))))))))))
def c1942 : List Lit := [(107, false), (1699, true), (119, false), (116, false)]
theorem step1942 (p : Nat → Bool) (h : Constraints p) : clause p c1942 = true :=
  Snake9.LocalRup.prove_clause [c828, c830, c1609, c1611, c1617] c1942 (by decide) p (sat_cons (step828 p h) (sat_cons (step830 p h) (sat_cons (step1609 p h) (sat_cons (step1611 p h) (sat_cons (step1617 p h) (sat_nil p))))))
def c1943 : List Lit := [(67, false), (102, false), (75, false), (188, true), (118, false)]
theorem step1943 (p : Nat → Bool) (h : Constraints p) : clause p c1943 = true :=
  Snake9.LocalRup.prove_clause [c1910, c378] c1943 (by decide) p (sat_cons (step1910 p h) (sat_cons (step378 p h) (sat_nil p)))
def c1944 : List Lit := [(67, true), (190, true), (63, true), (1622, true)]
theorem step1944 (p : Nat → Bool) (h : Constraints p) : clause p c1944 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1450, c1441, c1431, c1432, c1438, c1439, c1454, c1433, c1428, c1422, c1423, c298, c316, c330] c1944 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1450 p h) (sat_cons (step1441 p h) (sat_cons (step1431 p h) (sat_cons (step1432 p h) (sat_cons (step1438 p h) (sat_cons (step1439 p h) (sat_cons (step1454 p h) (sat_cons (step1433 p h) (sat_cons (step1428 p h) (sat_cons (step1422 p h) (sat_cons (step1423 p h) (sat_cons (step298 p h) (sat_cons (step316 p h) (sat_cons (step330 p h) (sat_nil p))))))))))))))))
def c1945 : List Lit := [(1607, true), (69, false), (72, false), (190, true)]
theorem step1945 (p : Nat → Bool) (h : Constraints p) : clause p c1945 = true :=
  Snake9.LocalRup.prove_clause [c1422, c1423, c298, c316, c330] c1945 (by decide) p (sat_cons (step1422 p h) (sat_cons (step1423 p h) (sat_cons (step298 p h) (sat_cons (step316 p h) (sat_cons (step330 p h) (sat_nil p))))))
def c1946 : List Lit := [(77, false), (1628, true), (118, false), (67, false)]
theorem step1946 (p : Nat → Bool) (h : Constraints p) : clause p c1946 = true :=
  Snake9.LocalRup.prove_clause [c378, c379, c1464] c1946 (by decide) p (sat_cons (step378 p h) (sat_cons (step379 p h) (sat_cons (step1464 p h) (sat_nil p))))
def c1947 : List Lit := [(89, false), (84, true), (86, true), (82, false), (85, false), (210, true)]
theorem step1947 (p : Nat → Bool) (h : Constraints p) : clause p c1947 = true :=
  Snake9.LocalRup.prove_clause [c469, c487] c1947 (by decide) p (sat_cons (step469 p h) (sat_cons (step487 p h) (sat_nil p)))
def c1948 : List Lit := [(1621, true), (72, false), (190, true), (63, true)]
theorem step1948 (p : Nat → Bool) (h : Constraints p) : clause p c1948 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1453, c1449, c1428, c1438, c1945, c1430] c1948 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1453 p h) (sat_cons (step1449 p h) (sat_cons (step1428 p h) (sat_cons (step1438 p h) (sat_cons (step1945 p h) (sat_cons (step1430 p h) (sat_nil p))))))))
def c1949 : List Lit := [(1561, false), (1577, true), (1534, false), (357, true), (47, true), (44, true)]
theorem step1949 (p : Nat → Bool) (h : Constraints p) : clause p c1949 = true :=
  Snake9.LocalRup.prove_clause [c1027, c988, c971, c964, c963, c1874, c1291, c1297, c1308, c1370, c1025, c1022, c1002, c992, c991, c1339, c1343, c1374, c1322, c1324, c1309, c1319, c1316, c1298, c222, c1293, c172] c1949 (by decide) p (sat_cons (step1027 p h) (sat_cons (step988 p h) (sat_cons (step971 p h) (sat_cons (step964 p h) (sat_cons (step963 p h) (sat_cons (step1874 p h) (sat_cons (step1291 p h) (sat_cons (step1297 p h) (sat_cons (step1308 p h) (sat_cons (step1370 p h) (sat_cons (step1025 p h) (sat_cons (step1022 p h) (sat_cons (step1002 p h) (sat_cons (step992 p h) (sat_cons (step991 p h) (sat_cons (step1339 p h) (sat_cons (step1343 p h) (sat_cons (step1374 p h) (sat_cons (step1322 p h) (sat_cons (step1324 p h) (sat_cons (step1309 p h) (sat_cons (step1319 p h) (sat_cons (step1316 p h) (sat_cons (step1298 p h) (sat_cons (step222 p h) (sat_cons (step1293 p h) (sat_cons (step172 p h) (sat_nil p))))))))))))))))))))))))))))
def c1950 : List Lit := [(46, false), (1521, true), (29, false), (87, false), (1497, false), (12, false), (67, false)]
theorem step1950 (p : Nat → Bool) (h : Constraints p) : clause p c1950 = true :=
  Snake9.LocalRup.prove_clause [c127, c53, c52, c49, c124, c126, c1189, c1185, c1177, c1223, c1227, c1194, c1180, c1232, c1205, c1242, c1270] c1950 (by decide) p (sat_cons (step127 p h) (sat_cons (step53 p h) (sat_cons (step52 p h) (sat_cons (step49 p h) (sat_cons (step124 p h) (sat_cons (step126 p h) (sat_cons (step1189 p h) (sat_cons (step1185 p h) (sat_cons (step1177 p h) (sat_cons (step1223 p h) (sat_cons (step1227 p h) (sat_cons (step1194 p h) (sat_cons (step1180 p h) (sat_cons (step1232 p h) (sat_cons (step1205 p h) (sat_cons (step1242 p h) (sat_cons (step1270 p h) (sat_nil p))))))))))))))))))
def c1951 : List Lit := [(7, true), (1490, true), (137, true), (12, false), (67, false)]
theorem step1951 (p : Nat → Bool) (h : Constraints p) : clause p c1951 = true :=
  Snake9.LocalRup.prove_clause [c859, c76, c1177, c73, c1180, c1188, c1205, c1192, c1194, c1190, c1185, c51] c1951 (by decide) p (sat_cons (step859 p h) (sat_cons (step76 p h) (sat_cons (step1177 p h) (sat_cons (step73 p h) (sat_cons (step1180 p h) (sat_cons (step1188 p h) (sat_cons (step1205 p h) (sat_cons (step1192 p h) (sat_cons (step1194 p h) (sat_cons (step1190 p h) (sat_cons (step1185 p h) (sat_cons (step51 p h) (sat_nil p)))))))))))))
def c1952 : List Lit := [(1490, true), (130, true), (137, true), (12, false), (67, false)]
theorem step1952 (p : Nat → Bool) (h : Constraints p) : clause p c1952 = true :=
  Snake9.LocalRup.prove_clause [c857, c1201, c1951, c46, c48, c1185, c59, c1189, c1195, c1197, c1190, c1187, c73, c31, c21] c1952 (by decide) p (sat_cons (step857 p h) (sat_cons (step1201 p h) (sat_cons (step1951 p h) (sat_cons (step46 p h) (sat_cons (step48 p h) (sat_cons (step1185 p h) (sat_cons (step59 p h) (sat_cons (step1189 p h) (sat_cons (step1195 p h) (sat_cons (step1197 p h) (sat_cons (step1190 p h) (sat_cons (step1187 p h) (sat_cons (step73 p h) (sat_cons (step31 p h) (sat_cons (step21 p h) (sat_nil p))))))))))))))))
def c1953 : List Lit := [(39, false), (1669, true), (31, true), (96, false), (87, false), (212, true)]
theorem step1953 (p : Nat → Bool) (h : Constraints p) : clause p c1953 = true :=
  Snake9.LocalRup.prove_clause [c870, c159, c518, c533, c530, c1554, c496, c1560] c1953 (by decide) p (sat_cons (step870 p h) (sat_cons (step159 p h) (sat_cons (step518 p h) (sat_cons (step533 p h) (sat_cons (step530 p h) (sat_cons (step1554 p h) (sat_cons (step496 p h) (sat_cons (step1560 p h) (sat_nil p)))))))))
def c1954 : List Lit := [(1644, true), (1627, false), (94, true), (85, false)]
theorem step1954 (p : Nat → Bool) (h : Constraints p) : clause p c1954 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1470, c1499, c1495, c1471, c1482, c1484, c1465, c1466, c1479, c1477, c386, c431, c461, c469, c487, c443, c1088, c1083, c1091, c1086, c1096] c1954 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1470 p h) (sat_cons (step1499 p h) (sat_cons (step1495 p h) (sat_cons (step1471 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1465 p h) (sat_cons (step1466 p h) (sat_cons (step1479 p h) (sat_cons (step1477 p h) (sat_cons (step386 p h) (sat_cons (step431 p h) (sat_cons (step461 p h) (sat_cons (step469 p h) (sat_cons (step487 p h) (sat_cons (step443 p h) (sat_cons (step1088 p h) (sat_cons (step1083 p h) (sat_cons (step1091 p h) (sat_cons (step1086 p h) (sat_cons (step1096 p h) (sat_nil p)))))))))))))))))))))))
def c1955 : List Lit := [(1629, true), (1639, true), (94, true), (85, false)]
theorem step1955 (p : Nat → Bool) (h : Constraints p) : clause p c1955 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1482, c1480, c1479, c463, c1484, c1477, c469, c1465, c1466, c386, c431, c443, c487, c1083, c1088, c1086, c1091, c1096] c1955 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1482 p h) (sat_cons (step1480 p h) (sat_cons (step1479 p h) (sat_cons (step463 p h) (sat_cons (step1484 p h) (sat_cons (step1477 p h) (sat_cons (step469 p h) (sat_cons (step1465 p h) (sat_cons (step1466 p h) (sat_cons (step386 p h) (sat_cons (step431 p h) (sat_cons (step443 p h) (sat_cons (step487 p h) (sat_cons (step1083 p h) (sat_cons (step1088 p h) (sat_cons (step1086 p h) (sat_cons (step1091 p h) (sat_cons (step1096 p h) (sat_nil p))))))))))))))))))))
def c1956 : List Lit := [(1504, true), (29, false), (87, false)]
theorem step1956 (p : Nat → Bool) (h : Constraints p) : clause p c1956 = true :=
  Snake9.LocalRup.prove_clause [c1228, c1230, c1225, c1223, c123] c1956 (by decide) p (sat_cons (step1228 p h) (sat_cons (step1230 p h) (sat_cons (step1225 p h) (sat_cons (step1223 p h) (sat_cons (step123 p h) (sat_nil p))))))
def c1957 : List Lit := [(1497, true), (142, true)]
theorem step1957 (p : Nat → Bool) (h : Constraints p) : clause p c1957 = true :=
  Snake9.LocalRup.prove_clause [c1217, c1219, c1214, c1215, c85, c91] c1957 (by decide) p (sat_cons (step1217 p h) (sat_cons (step1219 p h) (sat_cons (step1214 p h) (sat_cons (step1215 p h) (sat_cons (step85 p h) (sat_cons (step91 p h) (sat_nil p)))))))
def c1958 : List Lit := [(41, false), (1677, true), (100, false), (80, false), (102, true)]
theorem step1958 (p : Nat → Bool) (h : Constraints p) : clause p c1958 = true :=
  Snake9.LocalRup.prove_clause [c567, c569, c1562, c1567, c1572] c1958 (by decide) p (sat_cons (step567 p h) (sat_cons (step569 p h) (sat_cons (step1562 p h) (sat_cons (step1567 p h) (sat_cons (step1572 p h) (sat_nil p))))))
def c1959 : List Lit := [(9, true), (12, false), (1489, true), (14, false)]
theorem step1959 (p : Nat → Bool) (h : Constraints p) : clause p c1959 = true :=
  Snake9.LocalRup.prove_clause [c1200, c1196, c1186, c1193, c1204, c1180, c1187, c1177, c44] c1959 (by decide) p (sat_cons (step1200 p h) (sat_cons (step1196 p h) (sat_cons (step1186 p h) (sat_cons (step1193 p h) (sat_cons (step1204 p h) (sat_cons (step1180 p h) (sat_cons (step1187 p h) (sat_cons (step1177 p h) (sat_cons (step44 p h) (sat_nil p))))))))))
def c1960 : List Lit := [(1704, true), (112, true), (98, false), (118, true), (110, false)]
theorem step1960 (p : Nat → Bool) (h : Constraints p) : clause p c1960 = true :=
  Snake9.LocalRup.prove_clause [c1598, c1600, c1612, c1614, c1632, c1628, c1601, c1603, c1615, c1617, c1599, c1595, c1613, c1608, c715, c1942, c844, c812, c836] c1960 (by decide) p (sat_cons (step1598 p h) (sat_cons (step1600 p h) (sat_cons (step1612 p h) (sat_cons (step1614 p h) (sat_cons (step1632 p h) (sat_cons (step1628 p h) (sat_cons (step1601 p h) (sat_cons (step1603 p h) (sat_cons (step1615 p h) (sat_cons (step1617 p h) (sat_cons (step1599 p h) (sat_cons (step1595 p h) (sat_cons (step1613 p h) (sat_cons (step1608 p h) (sat_cons (step715 p h) (sat_cons (step1942 p h) (sat_cons (step844 p h) (sat_cons (step812 p h) (sat_cons (step836 p h) (sat_nil p))))))))))))))))))))
def c1961 : List Lit := [(64, false), (66, false), (185, true), (69, false), (72, false), (99, false)]
theorem step1961 (p : Nat → Bool) (h : Constraints p) : clause p c1961 = true :=
  Snake9.LocalRup.prove_clause [c298, c286, c316, c297] c1961 (by decide) p (sat_cons (step298 p h) (sat_cons (step286 p h) (sat_cons (step316 p h) (sat_cons (step297 p h) (sat_nil p)))))
def c1962 : List Lit := [(1686, false), (1705, true), (69, false), (112, true), (98, false), (118, true), (110, false)]
theorem step1962 (p : Nat → Bool) (h : Constraints p) : clause p c1962 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1614, c1637, c1598, c1603, c1604, c1633, c1599, c1615, c1617, c1613, c1608, c844, c711, c812, c1916, c836] c1962 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1614 p h) (sat_cons (step1637 p h) (sat_cons (step1598 p h) (sat_cons (step1603 p h) (sat_cons (step1604 p h) (sat_cons (step1633 p h) (sat_cons (step1599 p h) (sat_cons (step1615 p h) (sat_cons (step1617 p h) (sat_cons (step1613 p h) (sat_cons (step1608 p h) (sat_cons (step844 p h) (sat_cons (step711 p h) (sat_cons (step812 p h) (sat_cons (step1916 p h) (sat_cons (step836 p h) (sat_nil p))))))))))))))))))
def c1963 : List Lit := [(66, false), (75, false), (109, true), (107, false), (44, false), (1700, true), (69, false), (99, false), (100, false), (118, true)]
theorem step1963 (p : Nat → Bool) (h : Constraints p) : clause p c1963 = true :=
  Snake9.LocalRup.prove_clause [c1819, c1810, c1612, c1620, c637, c319, c328, c1050, c1056, c1065, c1068, c1071, c1105, c1045, c1170, c1043, c1162, c1040, c1157, c306, c304, c1154, c554, c354, c1147, c1608, c1610, c1144, c1618, c775, c1613, c829] c1963 (by decide) p (sat_cons (step1819 p h) (sat_cons (step1810 p h) (sat_cons (step1612 p h) (sat_cons (step1620 p h) (sat_cons (step637 p h) (sat_cons (step319 p h) (sat_cons (step328 p h) (sat_cons (step1050 p h) (sat_cons (step1056 p h) (sat_cons (step1065 p h) (sat_cons (step1068 p h) (sat_cons (step1071 p h) (sat_cons (step1105 p h) (sat_cons (step1045 p h) (sat_cons (step1170 p h) (sat_cons (step1043 p h) (sat_cons (step1162 p h) (sat_cons (step1040 p h) (sat_cons (step1157 p h) (sat_cons (step306 p h) (sat_cons (step304 p h) (sat_cons (step1154 p h) (sat_cons (step554 p h) (sat_cons (step354 p h) (sat_cons (step1147 p h) (sat_cons (step1608 p h) (sat_cons (step1610 p h) (sat_cons (step1144 p h) (sat_cons (step1618 p h) (sat_cons (step775 p h) (sat_cons (step1613 p h) (sat_cons (step829 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1964 : List Lit := [(64, false), (109, true), (107, false), (69, false), (72, false)]
theorem step1964 (p : Nat → Bool) (h : Constraints p) : clause p c1964 = true :=
  Snake9.LocalRup.prove_clause [c298, c318, c324] c1964 (by decide) p (sat_cons (step298 p h) (sat_cons (step318 p h) (sat_cons (step324 p h) (sat_nil p))))
def c1965 : List Lit := [(69, false), (1607, true), (72, false), (99, false)]
theorem step1965 (p : Nat → Bool) (h : Constraints p) : clause p c1965 = true :=
  Snake9.LocalRup.prove_clause [c1819, c1423, c1422, c1945, c1961, c1050, c1035, c1056, c1038, c1065, c1047, c1071] c1965 (by decide) p (sat_cons (step1819 p h) (sat_cons (step1423 p h) (sat_cons (step1422 p h) (sat_cons (step1945 p h) (sat_cons (step1961 p h) (sat_cons (step1050 p h) (sat_cons (step1035 p h) (sat_cons (step1056 p h) (sat_cons (step1038 p h) (sat_cons (step1065 p h) (sat_cons (step1047 p h) (sat_cons (step1071 p h) (sat_nil p)))))))))))))
def c1966 : List Lit := [(187, true), (75, false), (105, true), (1705, true), (62, true), (1607, true), (1688, false), (1696, false)]
theorem step1966 (p : Nat → Bool) (h : Constraints p) : clause p c1966 = true :=
  Snake9.LocalRup.prove_clause [c1422, c1894, c305, c1595, c354, c1603, c1608, c1633, c1617] c1966 (by decide) p (sat_cons (step1422 p h) (sat_cons (step1894 p h) (sat_cons (step305 p h) (sat_cons (step1595 p h) (sat_cons (step354 p h) (sat_cons (step1603 p h) (sat_cons (step1608 p h) (sat_cons (step1633 p h) (sat_cons (step1617 p h) (sat_nil p))))))))))
def c1967 : List Lit := [(25, true), (2, false), (8, true), (123, true)]
theorem step1967 (p : Nat → Bool) (h : Constraints p) : clause p c1967 = true :=
  Snake9.LocalRup.prove_clause [c1809, c3] c1967 (by decide) p (sat_cons (step1809 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1968 : List Lit := [(4, true), (25, true), (123, true), (2, false)]
theorem step1968 (p : Nat → Bool) (h : Constraints p) : clause p c1968 = true :=
  Snake9.LocalRup.prove_clause [c1809, c4] c1968 (by decide) p (sat_cons (step1809 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1969 : List Lit := [(4, true), (2, false), (123, true), (8, true)]
theorem step1969 (p : Nat → Bool) (h : Constraints p) : clause p c1969 = true :=
  Snake9.LocalRup.prove_clause [c1809, c5] c1969 (by decide) p (sat_cons (step1809 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1970 : List Lit := [(11, true), (3, false), (58, true), (28, true)]
theorem step1970 (p : Nat → Bool) (h : Constraints p) : clause p c1970 = true :=
  Snake9.LocalRup.prove_clause [c851, c10] c1970 (by decide) p (sat_cons (step851 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1971 : List Lit := [(5, true), (28, true), (3, false), (58, true)]
theorem step1971 (p : Nat → Bool) (h : Constraints p) : clause p c1971 = true :=
  Snake9.LocalRup.prove_clause [c851, c11] c1971 (by decide) p (sat_cons (step851 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1972 : List Lit := [(5, true), (11, true), (3, false), (58, true)]
theorem step1972 (p : Nat → Bool) (h : Constraints p) : clause p c1972 = true :=
  Snake9.LocalRup.prove_clause [c851, c12] c1972 (by decide) p (sat_cons (step851 p h) (sat_cons (step12 p h) (sat_nil p)))
def c1973 : List Lit := [(4, false), (5, true)]
theorem step1973 (p : Nat → Bool) (h : Constraints p) : clause p c1973 = true :=
  Snake9.LocalRup.prove_clause [c852, c13] c1973 (by decide) p (sat_cons (step852 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1974 : List Lit := [(4, false), (2, true)]
theorem step1974 (p : Nat → Bool) (h : Constraints p) : clause p c1974 = true :=
  Snake9.LocalRup.prove_clause [c852, c14] c1974 (by decide) p (sat_cons (step852 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1975 : List Lit := [(6, false), (11, true)]
theorem step1975 (p : Nat → Bool) (h : Constraints p) : clause p c1975 = true :=
  Snake9.LocalRup.prove_clause [c853, c18] c1975 (by decide) p (sat_cons (step853 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1976 : List Lit := [(6, false), (7, true)]
theorem step1976 (p : Nat → Bool) (h : Constraints p) : clause p c1976 = true :=
  Snake9.LocalRup.prove_clause [c853, c19] c1976 (by decide) p (sat_cons (step853 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1977 : List Lit := [(2, true), (18, true), (8, false), (64, true)]
theorem step1977 (p : Nat → Bool) (h : Constraints p) : clause p c1977 = true :=
  Snake9.LocalRup.prove_clause [c854, c28] c1977 (by decide) p (sat_cons (step854 p h) (sat_cons (step28 p h) (sat_nil p)))
def c1978 : List Lit := [(10, false), (14, true), (7, true), (43, true)]
theorem step1978 (p : Nat → Bool) (h : Constraints p) : clause p c1978 = true :=
  Snake9.LocalRup.prove_clause [c855, c38] c1978 (by decide) p (sat_cons (step855 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1979 : List Lit := [(10, false), (9, true), (7, true), (14, true)]
theorem step1979 (p : Nat → Bool) (h : Constraints p) : clause p c1979 = true :=
  Snake9.LocalRup.prove_clause [c855, c39] c1979 (by decide) p (sat_cons (step855 p h) (sat_cons (step39 p h) (sat_nil p)))
def c1980 : List Lit := [(14, true), (11, true), (12, false), (46, true), (67, true)]
theorem step1980 (p : Nat → Bool) (h : Constraints p) : clause p c1980 = true :=
  Snake9.LocalRup.prove_clause [c856, c54] c1980 (by decide) p (sat_cons (step856 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1981 : List Lit := [(14, true), (7, true), (12, false), (46, true), (67, true)]
theorem step1981 (p : Nat → Bool) (h : Constraints p) : clause p c1981 = true :=
  Snake9.LocalRup.prove_clause [c856, c55] c1981 (by decide) p (sat_cons (step856 p h) (sat_cons (step55 p h) (sat_nil p)))
def c1982 : List Lit := [(11, true), (7, true), (67, true), (12, false), (46, true)]
theorem step1982 (p : Nat → Bool) (h : Constraints p) : clause p c1982 = true :=
  Snake9.LocalRup.prove_clause [c856, c56] c1982 (by decide) p (sat_cons (step856 p h) (sat_cons (step56 p h) (sat_nil p)))
def c1983 : List Lit := [(14, true), (11, true), (7, true), (12, false), (67, true)]
theorem step1983 (p : Nat → Bool) (h : Constraints p) : clause p c1983 = true :=
  Snake9.LocalRup.prove_clause [c856, c57] c1983 (by decide) p (sat_cons (step856 p h) (sat_cons (step57 p h) (sat_nil p)))
def c1984 : List Lit := [(14, true), (11, true), (7, true), (12, false), (46, true)]
theorem step1984 (p : Nat → Bool) (h : Constraints p) : clause p c1984 = true :=
  Snake9.LocalRup.prove_clause [c856, c58] c1984 (by decide) p (sat_cons (step856 p h) (sat_cons (step58 p h) (sat_nil p)))
def c1985 : List Lit := [(13, false), (14, true)]
theorem step1985 (p : Nat → Bool) (h : Constraints p) : clause p c1985 = true :=
  Snake9.LocalRup.prove_clause [c857, c59] c1985 (by decide) p (sat_cons (step857 p h) (sat_cons (step59 p h) (sat_nil p)))
def c1986 : List Lit := [(13, false), (9, true)]
theorem step1986 (p : Nat → Bool) (h : Constraints p) : clause p c1986 = true :=
  Snake9.LocalRup.prove_clause [c857, c60] c1986 (by decide) p (sat_cons (step857 p h) (sat_cons (step60 p h) (sat_nil p)))
def c1987 : List Lit := [(18, true), (15, false), (19, true)]
theorem step1987 (p : Nat → Bool) (h : Constraints p) : clause p c1987 = true :=
  Snake9.LocalRup.prove_clause [c858, c69] c1987 (by decide) p (sat_cons (step858 p h) (sat_cons (step69 p h) (sat_nil p)))
def c1988 : List Lit := [(15, false), (16, true), (18, true)]
theorem step1988 (p : Nat → Bool) (h : Constraints p) : clause p c1988 = true :=
  Snake9.LocalRup.prove_clause [c858, c70] c1988 (by decide) p (sat_cons (step858 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1989 : List Lit := [(17, false), (16, true)]
theorem step1989 (p : Nat → Bool) (h : Constraints p) : clause p c1989 = true :=
  Snake9.LocalRup.prove_clause [c859, c75] c1989 (by decide) p (sat_cons (step859 p h) (sat_cons (step75 p h) (sat_nil p)))
def c1990 : List Lit := [(17, false), (7, true)]
theorem step1990 (p : Nat → Bool) (h : Constraints p) : clause p c1990 = true :=
  Snake9.LocalRup.prove_clause [c859, c76] c1990 (by decide) p (sat_cons (step859 p h) (sat_cons (step76 p h) (sat_nil p)))
def c1991 : List Lit := [(20, false), (18, true), (21, true)]
theorem step1991 (p : Nat → Bool) (h : Constraints p) : clause p c1991 = true :=
  Snake9.LocalRup.prove_clause [c860, c86] c1991 (by decide) p (sat_cons (step860 p h) (sat_cons (step86 p h) (sat_nil p)))
def c1992 : List Lit := [(20, false), (18, true), (19, true)]
theorem step1992 (p : Nat → Bool) (h : Constraints p) : clause p c1992 = true :=
  Snake9.LocalRup.prove_clause [c860, c87] c1992 (by decide) p (sat_cons (step860 p h) (sat_cons (step87 p h) (sat_nil p)))
def c1993 : List Lit := [(22, false), (21, true)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c861, c92] c1993 (by decide) p (sat_cons (step861 p h) (sat_cons (step92 p h) (sat_nil p)))
def c1994 : List Lit := [(22, false), (14, true)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c861, c93] c1994 (by decide) p (sat_cons (step861 p h) (sat_cons (step93 p h) (sat_nil p)))
def c1995 : List Lit := [(23, false), (28, true), (81, true)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c862, c95] c1995 (by decide) p (sat_cons (step862 p h) (sat_cons (step95 p h) (sat_nil p)))
def c1996 : List Lit := [(24, true), (23, false), (28, true)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c862, c96] c1996 (by decide) p (sat_cons (step862 p h) (sat_cons (step96 p h) (sat_nil p)))
def c1997 : List Lit := [(27, false), (24, true), (43, true), (31, true)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c864, c115] c1997 (by decide) p (sat_cons (step864 p h) (sat_cons (step115 p h) (sat_nil p)))
end B112E019
