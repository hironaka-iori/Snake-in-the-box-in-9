import B112E089Part0000
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2076 : List Lit := [(1588, false), (1613, true)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c1512, c1498, c1469, c1470, c1493, c1494, c1464, c1465, c1517, c1483, c1441, c1476, c1433, c1435, c1430, c1427, c1428, c280, c380, c364, c361, c372] c2076 (by decide) p (sat_cons (step1512 p h) (sat_cons (step1498 p h) (sat_cons (step1469 p h) (sat_cons (step1470 p h) (sat_cons (step1493 p h) (sat_cons (step1494 p h) (sat_cons (step1464 p h) (sat_cons (step1465 p h) (sat_cons (step1517 p h) (sat_cons (step1483 p h) (sat_cons (step1441 p h) (sat_cons (step1476 p h) (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1430 p h) (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step280 p h) (sat_cons (step380 p h) (sat_cons (step364 p h) (sat_cons (step361 p h) (sat_cons (step372 p h) (sat_nil p)))))))))))))))))))))))
def c2077 : List Lit := [(1580, true), (48, true), (50, false), (47, false)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1445, c1433, c1419, c1431, c1416, c213, c332, c314] c2077 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1445 p h) (sat_cons (step1433 p h) (sat_cons (step1419 p h) (sat_cons (step1431 p h) (sat_cons (step1416 p h) (sat_cons (step213 p h) (sat_cons (step332 p h) (sat_cons (step314 p h) (sat_nil p))))))))))
def c2078 : List Lit := [(1518, true)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c1325, c1328, c1318, c1320, c1307, c1309, c1315, c1313, c1304, c1305, c10, c23, c18] c2078 (by decide) p (sat_cons (step1325 p h) (sat_cons (step1328 p h) (sat_cons (step1318 p h) (sat_cons (step1320 p h) (sat_cons (step1307 p h) (sat_cons (step1309 p h) (sat_cons (step1315 p h) (sat_cons (step1313 p h) (sat_cons (step1304 p h) (sat_cons (step1305 p h) (sat_cons (step10 p h) (sat_cons (step23 p h) (sat_cons (step18 p h) (sat_nil p))))))))))))))
def c2079 : List Lit := [(1576, true), (52, true), (54, false), (50, false), (51, false)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1435, c1430, c1427, c280, c380, c364, c372] c2079 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1430 p h) (sat_cons (step1427 p h) (sat_cons (step280 p h) (sat_cons (step380 p h) (sat_cons (step364 p h) (sat_cons (step372 p h) (sat_nil p)))))))))
def c2080 : List Lit := [(1590, true), (1613, true)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c1524, c1442, c1434, c2076, c1462, c1461, c1464, c1465, c318, c2077, c1517, c1489, c1483, c1476, c362, c2079, c1446, c1419, c1416, c332, c346, c314, c380, c213, c1432] c2080 (by decide) p (sat_cons (step1524 p h) (sat_cons (step1442 p h) (sat_cons (step1434 p h) (sat_cons (step2076 p h) (sat_cons (step1462 p h) (sat_cons (step1461 p h) (sat_cons (step1464 p h) (sat_cons (step1465 p h) (sat_cons (step318 p h) (sat_cons (step2077 p h) (sat_cons (step1517 p h) (sat_cons (step1489 p h) (sat_cons (step1483 p h) (sat_cons (step1476 p h) (sat_cons (step362 p h) (sat_cons (step2079 p h) (sat_cons (step1446 p h) (sat_cons (step1419 p h) (sat_cons (step1416 p h) (sat_cons (step332 p h) (sat_cons (step346 p h) (sat_cons (step314 p h) (sat_cons (step380 p h) (sat_cons (step213 p h) (sat_cons (step1432 p h) (sat_nil p))))))))))))))))))))))))))
def c2081 : List Lit := [(1613, true)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c2018, c1512, c2076, c1498, c1461, c1462, c1468, c2080, c1467, c1493, c1494, c1517, c1481, c1483, c1441, c1445, c1478, c1479, c1476, c1433, c1435, c1419, c1430, c1431, c1427, c1428, c1416, c280, c213, c208, c360, c447, c222, c218, c1103, c332, c1106, c1466, c1118, c364, c1121, c379, c1158, c1138, c1150, c1142, c1147] c2081 (by decide) p (sat_cons (step2018 p h) (sat_cons (step1512 p h) (sat_cons (step2076 p h) (sat_cons (step1498 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step1468 p h) (sat_cons (step2080 p h) (sat_cons (step1467 p h) (sat_cons (step1493 p h) (sat_cons (step1494 p h) (sat_cons (step1517 p h) (sat_cons (step1481 p h) (sat_cons (step1483 p h) (sat_cons (step1441 p h) (sat_cons (step1445 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step1476 p h) (sat_cons (step1433 p h) (sat_cons (step1435 p h) (sat_cons (step1419 p h) (sat_cons (step1430 p h) (sat_cons (step1431 p h) (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step1416 p h) (sat_cons (step280 p h) (sat_cons (step213 p h) (sat_cons (step208 p h) (sat_cons (step360 p h) (sat_cons (step447 p h) (sat_cons (step222 p h) (sat_cons (step218 p h) (sat_cons (step1103 p h) (sat_cons (step332 p h) (sat_cons (step1106 p h) (sat_cons (step1466 p h) (sat_cons (step1118 p h) (sat_cons (step364 p h) (sat_cons (step1121 p h) (sat_cons (step379 p h) (sat_cons (step1158 p h) (sat_cons (step1138 p h) (sat_cons (step1150 p h) (sat_cons (step1142 p h) (sat_cons (step1147 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c2082 : List Lit := [(51, false), (52, true), (54, false), (1576, true)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c2024, c1433, c1430, c1435, c1427, c1428, c270, c1431, c224, c364, c379, c358, c1138, c1129, c1142, c1132, c1147, c1134, c1153] c2082 (by decide) p (sat_cons (step2024 p h) (sat_cons (step1433 p h) (sat_cons (step1430 p h) (sat_cons (step1435 p h) (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step270 p h) (sat_cons (step1431 p h) (sat_cons (step224 p h) (sat_cons (step364 p h) (sat_cons (step379 p h) (sat_cons (step358 p h) (sat_cons (step1138 p h) (sat_cons (step1129 p h) (sat_cons (step1142 p h) (sat_cons (step1132 p h) (sat_cons (step1147 p h) (sat_cons (step1134 p h) (sat_cons (step1153 p h) (sat_nil p))))))))))))))))))))
def c2083 : List Lit := [(1598, true), (38, true), (39, false), (163, true), (42, false)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1479, c447, c208, c222] c2083 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step447 p h) (sat_cons (step208 p h) (sat_cons (step222 p h) (sat_nil p))))))
def c2084 : List Lit := [(33, true), (1568, true), (158, true)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1414, c1419, c1417, c201, c199, c1964] c2084 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1414 p h) (sat_cons (step1419 p h) (sat_cons (step1417 p h) (sat_cons (step201 p h) (sat_cons (step199 p h) (sat_cons (step1964 p h) (sat_nil p))))))))
def c2085 : List Lit := [(1538, true), (65, false), (24, true), (153, true)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c786, c1354, c1364, c1362, c1355, c1356, c140, c174] c2085 (by decide) p (sat_cons (step786 p h) (sat_cons (step1354 p h) (sat_cons (step1364 p h) (sat_cons (step1362 p h) (sat_cons (step1355 p h) (sat_cons (step1356 p h) (sat_cons (step140 p h) (sat_cons (step174 p h) (sat_nil p)))))))))
def c2086 : List Lit := [(30, true), (1568, true), (155, true)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1414, c1419, c1417, c182, c180, c1964] c2086 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1414 p h) (sat_cons (step1419 p h) (sat_cons (step1417 p h) (sat_cons (step182 p h) (sat_cons (step180 p h) (sat_cons (step1964 p h) (sat_nil p))))))))
def c2087 : List Lit := [(1746, true), (120, true), (116, false), (72, false)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1822, c1820, c1813, c1815, c920] c2087 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1822 p h) (sat_cons (step1820 p h) (sat_cons (step1813 p h) (sat_cons (step1815 p h) (sat_cons (step920 p h) (sat_nil p)))))))
def c2088 : List Lit := [(1737, true), (241, true), (107, false)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c1803, c1805, c1800, c1798, c927, c884] c2088 (by decide) p (sat_cons (step1803 p h) (sat_cons (step1805 p h) (sat_cons (step1800 p h) (sat_cons (step1798 p h) (sat_cons (step927 p h) (sat_cons (step884 p h) (sat_nil p)))))))
def c2089 : List Lit := [(112, false), (120, false), (90, false), (241, true), (1738, true), (107, false)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c897, c874, c1797, c927, c1806, c1800] c2089 (by decide) p (sat_cons (step897 p h) (sat_cons (step874 p h) (sat_cons (step1797 p h) (sat_cons (step927 p h) (sat_cons (step1806 p h) (sat_cons (step1800 p h) (sat_nil p)))))))
def c2090 : List Lit := [(113, true), (241, true), (1738, true), (107, false)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c1808, c1797, c1799, c1806, c1800, c927, c884] c2090 (by decide) p (sat_cons (step1808 p h) (sat_cons (step1797 p h) (sat_cons (step1799 p h) (sat_cons (step1806 p h) (sat_cons (step1800 p h) (sat_cons (step927 p h) (sat_cons (step884 p h) (sat_nil p))))))))
def c2091 : List Lit := [(244, true), (112, true), (120, false), (122, true)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c1029, c945, c947, c950, c2005] c2091 (by decide) p (sat_cons (step1029 p h) (sat_cons (step945 p h) (sat_cons (step947 p h) (sat_cons (step950 p h) (sat_cons (step2005 p h) (sat_nil p))))))
def c2092 : List Lit := [(455, true), (104, false), (1714, true), (44, false), (106, true)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c1015, c1250, c1252, c1248, c1236, c1242, c1227, c1240, c865, c831, c811, c1754, c816, c1759, c1751] c2092 (by decide) p (sat_cons (step1015 p h) (sat_cons (step1250 p h) (sat_cons (step1252 p h) (sat_cons (step1248 p h) (sat_cons (step1236 p h) (sat_cons (step1242 p h) (sat_cons (step1227 p h) (sat_cons (step1240 p h) (sat_cons (step865 p h) (sat_cons (step831 p h) (sat_cons (step811 p h) (sat_cons (step1754 p h) (sat_cons (step816 p h) (sat_cons (step1759 p h) (sat_cons (step1751 p h) (sat_nil p))))))))))))))))
def c2093 : List Lit := [(228, true), (98, false), (106, true), (104, false)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c864, c865, c2007] c2093 (by decide) p (sat_cons (step864 p h) (sat_cons (step865 p h) (sat_cons (step2007 p h) (sat_nil p))))
def c2094 : List Lit := [(47, false), (103, false), (39, false), (171, true), (44, false)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c213, c334, c316] c2094 (by decide) p (sat_cons (step213 p h) (sat_cons (step334 p h) (sat_cons (step316 p h) (sat_nil p))))
def c2095 : List Lit := [(98, true), (1714, true), (218, true)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c1015, c811, c1754, c816, c1759, c1751] c2095 (by decide) p (sat_cons (step1015 p h) (sat_cons (step811 p h) (sat_cons (step1754 p h) (sat_cons (step816 p h) (sat_cons (step1759 p h) (sat_cons (step1751 p h) (sat_nil p)))))))
def c2096 : List Lit := [(87, false), (85, false), (79, false)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c2047, c772, c783, c779, c1208, c1206, c1211] c2096 (by decide) p (sat_cons (step2047 p h) (sat_cons (step772 p h) (sat_cons (step783 p h) (sat_cons (step779 p h) (sat_cons (step1208 p h) (sat_cons (step1206 p h) (sat_cons (step1211 p h) (sat_nil p))))))))
def c2097 : List Lit := [(1678, true), (79, false)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c1661, c1662, c2096] c2097 (by decide) p (sat_cons (step1661 p h) (sat_cons (step1662 p h) (sat_cons (step2096 p h) (sat_nil p))))
def c2098 : List Lit := [(1572, true), (40, false), (44, false)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1428, c224] c2098 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1428 p h) (sat_cons (step224 p h) (sat_nil p))))
def c2099 : List Lit := [(1568, true), (158, true), (75, false)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c1419, c1421, c2084, c1417, c1413, c191] c2099 (by decide) p (sat_cons (step1419 p h) (sat_cons (step1421 p h) (sat_cons (step2084 p h) (sat_cons (step1417 p h) (sat_cons (step1413 p h) (sat_cons (step191 p h) (sat_nil p)))))))
def c2100 : List Lit := [(1606, true), (40, true), (50, true), (47, true), (175, true), (75, false)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c1461, c1465, c1470, c1503, c1499, c1471, c1473, c1483, c1466, c1463, c1476, c362, c358, c367] c2100 (by decide) p (sat_cons (step1461 p h) (sat_cons (step1465 p h) (sat_cons (step1470 p h) (sat_cons (step1503 p h) (sat_cons (step1499 p h) (sat_cons (step1471 p h) (sat_cons (step1473 p h) (sat_cons (step1483 p h) (sat_cons (step1466 p h) (sat_cons (step1463 p h) (sat_cons (step1476 p h) (sat_cons (step362 p h) (sat_cons (step358 p h) (sat_cons (step367 p h) (sat_nil p)))))))))))))))
def c2101 : List Lit := [(1569, true), (39, true), (158, true), (75, false)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1420, c1422, c1418, c1413, c1414, c191, c201, c199, c1964] c2101 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1420 p h) (sat_cons (step1422 p h) (sat_cons (step1418 p h) (sat_cons (step1413 p h) (sat_cons (step1414 p h) (sat_cons (step191 p h) (sat_cons (step201 p h) (sat_cons (step199 p h) (sat_cons (step1964 p h) (sat_nil p)))))))))))
def c2102 : List Lit := [(27, false), (26, true), (66, false), (45, false), (151, true)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c595, c162] c2102 (by decide) p (sat_cons (step595 p h) (sat_cons (step162 p h) (sat_nil p)))
def c2103 : List Lit := [(18, true), (1528, true), (21, true), (26, true), (146, true)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c979, c1344, c117, c114, c101, c1960] c2103 (by decide) p (sat_cons (step979 p h) (sat_cons (step1344 p h) (sat_cons (step117 p h) (sat_cons (step114 p h) (sat_cons (step101 p h) (sat_cons (step1960 p h) (sat_nil p)))))))
def c2104 : List Lit := [(14, false), (1593, true), (49, false), (103, false)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c328, c330, c1461, c1465, c1470] c2104 (by decide) p (sat_cons (step328 p h) (sat_cons (step330 p h) (sat_cons (step1461 p h) (sat_cons (step1465 p h) (sat_cons (step1470 p h) (sat_nil p))))))
def c2105 : List Lit := [(26, false), (14, true), (1536, true), (1544, true), (139, true), (153, true), (25, false)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c786, c977, c139, c174, c1356, c1358, c1359, c151, c148, c1381, c1342, c88, c1351, c82, c1341] c2105 (by decide) p (sat_cons (step786 p h) (sat_cons (step977 p h) (sat_cons (step139 p h) (sat_cons (step174 p h) (sat_cons (step1356 p h) (sat_cons (step1358 p h) (sat_cons (step1359 p h) (sat_cons (step151 p h) (sat_cons (step148 p h) (sat_cons (step1381 p h) (sat_cons (step1342 p h) (sat_cons (step88 p h) (sat_cons (step1351 p h) (sat_cons (step82 p h) (sat_cons (step1341 p h) (sat_nil p))))))))))))))))
def c2106 : List Lit := [(1600, true), (66, false), (45, false), (185, true)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c1481, c1483, c1478, c1479, c1475, c609, c416, c428, c473] c2106 (by decide) p (sat_cons (step1481 p h) (sat_cons (step1483 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step1475 p h) (sat_cons (step609 p h) (sat_cons (step416 p h) (sat_cons (step428 p h) (sat_cons (step473 p h) (sat_nil p))))))))))
def c2107 : List Lit := [(1544, true), (1536, false), (14, true), (65, true), (139, true), (149, true), (25, false)]
theorem step2107 (p : Nat → Bool) (h : Constraints p) : clause p c2107 = true :=
  Snake9.LocalRup.prove_clause [c977, c1360, c1340, c1347, c1374, c1378, c1363, c1350, c1348, c1354, c1341, c1342, c1343, c82, c103, c118, c88, c144, c145] c2107 (by decide) p (sat_cons (step977 p h) (sat_cons (step1360 p h) (sat_cons (step1340 p h) (sat_cons (step1347 p h) (sat_cons (step1374 p h) (sat_cons (step1378 p h) (sat_cons (step1363 p h) (sat_cons (step1350 p h) (sat_cons (step1348 p h) (sat_cons (step1354 p h) (sat_cons (step1341 p h) (sat_cons (step1342 p h) (sat_cons (step1343 p h) (sat_cons (step82 p h) (sat_cons (step103 p h) (sat_cons (step118 p h) (sat_cons (step88 p h) (sat_cons (step144 p h) (sat_cons (step145 p h) (sat_nil p))))))))))))))))))))
def c2108 : List Lit := [(1592, true), (49, false), (103, false)]
theorem step2108 (p : Nat → Bool) (h : Constraints p) : clause p c2108 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1469, c1465, c1461, c339] c2108 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step339 p h) (sat_nil p))))))
def c2109 : List Lit := [(40, false), (51, false), (1573, true), (44, false)]
theorem step2109 (p : Nat → Bool) (h : Constraints p) : clause p c2109 = true :=
  Snake9.LocalRup.prove_clause [c227, c230, c1429] c2109 (by decide) p (sat_cons (step227 p h) (sat_cons (step230 p h) (sat_cons (step1429 p h) (sat_nil p))))
def c2110 : List Lit := [(1505, true), (3, false), (79, false)]
theorem step2110 (p : Nat → Bool) (h : Constraints p) : clause p c2110 = true :=
  Snake9.LocalRup.prove_clause [c1304, c1305, c14] c2110 (by decide) p (sat_cons (step1304 p h) (sat_cons (step1305 p h) (sat_cons (step14 p h) (sat_nil p))))
def c2111 : List Lit := [(1508, true), (3, false), (79, false)]
theorem step2111 (p : Nat → Bool) (h : Constraints p) : clause p c2111 = true :=
  Snake9.LocalRup.prove_clause [c2110, c1308, c1310, c9, c11, c1306] c2111 (by decide) p (sat_cons (step2110 p h) (sat_cons (step1308 p h) (sat_cons (step1310 p h) (sat_cons (step9 p h) (sat_cons (step11 p h) (sat_cons (step1306 p h) (sat_nil p)))))))
def c2112 : List Lit := [(1520, true), (3, false), (79, false)]
theorem step2112 (p : Nat → Bool) (h : Constraints p) : clause p c2112 = true :=
  Snake9.LocalRup.prove_clause [c2111, c1336, c1333, c1318, c1315, c12, c15, c16, c1311, c1306] c2112 (by decide) p (sat_cons (step2111 p h) (sat_cons (step1336 p h) (sat_cons (step1333 p h) (sat_cons (step1318 p h) (sat_cons (step1315 p h) (sat_cons (step12 p h) (sat_cons (step15 p h) (sat_cons (step16 p h) (sat_cons (step1311 p h) (sat_cons (step1306 p h) (sat_nil p)))))))))))
def c2113 : List Lit := [(1541, true), (153, true), (25, false)]
theorem step2113 (p : Nat → Bool) (h : Constraints p) : clause p c2113 = true :=
  Snake9.LocalRup.prove_clause [c1367, c1371, c1359, c1345, c1356, c1342, c174, c106] c2113 (by decide) p (sat_cons (step1367 p h) (sat_cons (step1371 p h) (sat_cons (step1359 p h) (sat_cons (step1345 p h) (sat_cons (step1356 p h) (sat_cons (step1342 p h) (sat_cons (step174 p h) (sat_cons (step106 p h) (sat_nil p)))))))))
def c2114 : List Lit := [(1616, true), (1605, false), (1569, false), (50, true), (47, true), (44, false), (175, true), (75, false)]
theorem step2114 (p : Nat → Bool) (h : Constraints p) : clause p c2114 = true :=
  Snake9.LocalRup.prove_clause [c1450, c1534, c1527, c1451, c2100, c1435, c2098] c2114 (by decide) p (sat_cons (step1450 p h) (sat_cons (step1534 p h) (sat_cons (step1527 p h) (sat_cons (step1451 p h) (sat_cons (step2100 p h) (sat_cons (step1435 p h) (sat_cons (step2098 p h) (sat_nil p))))))))
def c2115 : List Lit := [(1760, true), (1713, false), (1717, false), (104, true), (241, true)]
theorem step2115 (p : Nat → Bool) (h : Constraints p) : clause p c2115 = true :=
  Snake9.LocalRup.prove_clause [c1768, c1773, c1784, c1862, c1857, c1785, c1827, c1774, c2088, c1769] c2115 (by decide) p (sat_cons (step1768 p h) (sat_cons (step1773 p h) (sat_cons (step1784 p h) (sat_cons (step1862 p h) (sat_cons (step1857 p h) (sat_cons (step1785 p h) (sat_cons (step1827 p h) (sat_cons (step1774 p h) (sat_cons (step2088 p h) (sat_cons (step1769 p h) (sat_nil p)))))))))))
def c2116 : List Lit := [(1733, false), (241, true), (1751, true), (115, true)]
theorem step2116 (p : Nat → Bool) (h : Constraints p) : clause p c2116 = true :=
  Snake9.LocalRup.prove_clause [c1835, c1801, c1806, c1807, c1832, c1802, c1817, c1819, c926, c1814, c1812, c928] c2116 (by decide) p (sat_cons (step1835 p h) (sat_cons (step1801 p h) (sat_cons (step1806 p h) (sat_cons (step1807 p h) (sat_cons (step1832 p h) (sat_cons (step1802 p h) (sat_cons (step1817 p h) (sat_cons (step1819 p h) (sat_cons (step926 p h) (sat_cons (step1814 p h) (sat_cons (step1812 p h) (sat_cons (step928 p h) (sat_nil p)))))))))))))
def c2117 : List Lit := [(1569, true), (39, true), (35, false), (27, false)]
theorem step2117 (p : Nat → Bool) (h : Constraints p) : clause p c2117 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1420, c1418, c1422, c202, c1414] c2117 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1420 p h) (sat_cons (step1418 p h) (sat_cons (step1422 p h) (sat_cons (step202 p h) (sat_cons (step1414 p h) (sat_nil p)))))))
def c2118 : List Lit := [(1570, true), (32, true), (35, false), (27, false), (39, true)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1416, c1425, c1423, c1415, c1418, c202] c2118 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1416 p h) (sat_cons (step1425 p h) (sat_cons (step1423 p h) (sat_cons (step1415 p h) (sat_cons (step1418 p h) (sat_cons (step202 p h) (sat_nil p))))))))
def c2119 : List Lit := [(2, true), (1508, true), (129, true), (9, true)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c972, c20, c1310, c24, c1305] c2119 (by decide) p (sat_cons (step972 p h) (sat_cons (step20 p h) (sat_cons (step1310 p h) (sat_cons (step24 p h) (sat_cons (step1305 p h) (sat_nil p))))))
def c2120 : List Lit := [(11, false), (2, false), (135, true), (18, false)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c1, c66] c2120 (by decide) p (sat_cons (step1 p h) (sat_cons (step66 p h) (sat_nil p)))
def c2121 : List Lit := [(1520, true), (135, true), (129, true), (18, false), (9, true)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1320, c1327, c1333, c1322, c2119, c2120, c1316, c1317, c1321, c1330, c1307, c1304, c1305, c10, c25] c2121 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1320 p h) (sat_cons (step1327 p h) (sat_cons (step1333 p h) (sat_cons (step1322 p h) (sat_cons (step2119 p h) (sat_cons (step2120 p h) (sat_cons (step1316 p h) (sat_cons (step1317 p h) (sat_cons (step1321 p h) (sat_cons (step1330 p h) (sat_cons (step1307 p h) (sat_cons (step1304 p h) (sat_cons (step1305 p h) (sat_cons (step10 p h) (sat_cons (step25 p h) (sat_nil p)))))))))))))))))
def c2122 : List Lit := [(5, false), (2, false), (129, true)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c24, c1953, c25] c2122 (by decide) p (sat_cons (step24 p h) (sat_cons (step1953 p h) (sat_cons (step25 p h) (sat_nil p))))
def c2123 : List Lit := [(1592, true), (55, true), (54, true), (42, true), (41, false)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c2061, c2036, c989, c995, c1467, c1469, c1464, c1465, c1461, c1462, c359, c318, c351, c346, c1130, c1131, c332, c1132, c1137, c1128, c1126, c317, c216, c227, c358, c357, c369, c1981] c2123 (by decide) p (sat_cons (step2061 p h) (sat_cons (step2036 p h) (sat_cons (step989 p h) (sat_cons (step995 p h) (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_cons (step1464 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step359 p h) (sat_cons (step318 p h) (sat_cons (step351 p h) (sat_cons (step346 p h) (sat_cons (step1130 p h) (sat_cons (step1131 p h) (sat_cons (step332 p h) (sat_cons (step1132 p h) (sat_cons (step1137 p h) (sat_cons (step1128 p h) (sat_cons (step1126 p h) (sat_cons (step317 p h) (sat_cons (step216 p h) (sat_cons (step227 p h) (sat_cons (step358 p h) (sat_cons (step357 p h) (sat_cons (step369 p h) (sat_cons (step1981 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2124 : List Lit := [(51, false), (44, false), (175, true), (46, false), (54, true), (42, true), (41, false)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c995, c359, c227, c358, c357, c369, c1981] c2124 (by decide) p (sat_cons (step995 p h) (sat_cons (step359 p h) (sat_cons (step227 p h) (sat_cons (step358 p h) (sat_cons (step357 p h) (sat_cons (step369 p h) (sat_cons (step1981 p h) (sat_nil p))))))))
def c2125 : List Lit := [(1665, true), (74, false), (75, false), (1657, false), (1650, false)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c1620, c1609, c1634, c1638, c1623, c1612, c1614, c706] c2125 (by decide) p (sat_cons (step1620 p h) (sat_cons (step1609 p h) (sat_cons (step1634 p h) (sat_cons (step1638 p h) (sat_cons (step1623 p h) (sat_cons (step1612 p h) (sat_cons (step1614 p h) (sat_cons (step706 p h) (sat_nil p)))))))))
def c2126 : List Lit := [(1653, true), (63, false), (64, true), (41, false)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c1607, c1610, c1612, c1608, c516] c2126 (by decide) p (sat_cons (step1607 p h) (sat_cons (step1610 p h) (sat_cons (step1612 p h) (sat_cons (step1608 p h) (sat_cons (step516 p h) (sat_nil p))))))
def c2127 : List Lit := [(1660, true), (70, false), (73, true), (46, false)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1621, c1623, c1619, c1614, c645] c2127 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1621 p h) (sat_cons (step1623 p h) (sat_cons (step1619 p h) (sat_cons (step1614 p h) (sat_cons (step645 p h) (sat_nil p)))))))
def c2128 : List Lit := [(1507, true), (129, true)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c1307, c1309, c1305, c2122] c2128 (by decide) p (sat_cons (step1307 p h) (sat_cons (step1309 p h) (sat_cons (step1305 p h) (sat_cons (step2122 p h) (sat_nil p)))))
def c2129 : List Lit := [(1534, false), (1544, true), (153, true), (1525, false)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c1347, c1374, c1364, c1365, c1378, c1356, c1348, c174, c1342, c1343, c104] c2129 (by decide) p (sat_cons (step1347 p h) (sat_cons (step1374 p h) (sat_cons (step1364 p h) (sat_cons (step1365 p h) (sat_cons (step1378 p h) (sat_cons (step1356 p h) (sat_cons (step1348 p h) (sat_cons (step174 p h) (sat_cons (step1342 p h) (sat_cons (step1343 p h) (sat_cons (step104 p h) (sat_nil p))))))))))))
def c2130 : List Lit := [(76, false), (200, true), (65, true), (67, false), (74, true), (75, false)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c756, c748] c2130 (by decide) p (sat_cons (step756 p h) (sat_cons (step748 p h) (sat_nil p)))
def c2131 : List Lit := [(29, false), (18, false), (25, false), (153, true)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c105, c174] c2131 (by decide) p (sat_cons (step105 p h) (sat_cons (step174 p h) (sat_nil p)))
def c2132 : List Lit := [(1520, true), (2, true), (9, true), (8, false)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c972, c1313, c1320, c20, c1309, c1330, c1333, c1321, c2119, c1315, c22, c13, c23] c2132 (by decide) p (sat_cons (step972 p h) (sat_cons (step1313 p h) (sat_cons (step1320 p h) (sat_cons (step20 p h) (sat_cons (step1309 p h) (sat_cons (step1330 p h) (sat_cons (step1333 p h) (sat_cons (step1321 p h) (sat_cons (step2119 p h) (sat_cons (step1315 p h) (sat_cons (step22 p h) (sat_cons (step13 p h) (sat_cons (step23 p h) (sat_nil p))))))))))))))
def c2133 : List Lit := [(1593, true), (51, true), (49, false), (14, false)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c1464, c1468, c1470, c1466, c1461, c326] c2133 (by decide) p (sat_cons (step1464 p h) (sat_cons (step1468 p h) (sat_cons (step1470 p h) (sat_cons (step1466 p h) (sat_cons (step1461 p h) (sat_cons (step326 p h) (sat_nil p)))))))
def c2134 : List Lit := [(60, false), (22, false), (1599, true), (67, false)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c438, c441, c1480] c2134 (by decide) p (sat_cons (step438 p h) (sat_cons (step441 p h) (sat_cons (step1480 p h) (sat_nil p))))
def c2135 : List Lit := [(27, false), (151, true), (61, false), (26, true), (67, false)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c162, c600] c2135 (by decide) p (sat_cons (step162 p h) (sat_cons (step600 p h) (sat_nil p)))
def c2136 : List Lit := [(1512, true), (135, true), (14, false)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c1315, c1316, c67, c65] c2136 (by decide) p (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step67 p h) (sat_cons (step65 p h) (sat_nil p)))))
def c2137 : List Lit := [(32, false), (34, true), (156, true), (23, true)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c985, c189, c190, c192, c1965] c2137 (by decide) p (sat_cons (step985 p h) (sat_cons (step189 p h) (sat_cons (step190 p h) (sat_cons (step192 p h) (sat_cons (step1965 p h) (sat_nil p))))))
def c2138 : List Lit := [(1745, true), (1735, true)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c2042, c1801, c1800, c1817, c1819, c1814, c1815, c1812, c967, c928, c937, c926, c1268, c1266, c1273] c2138 (by decide) p (sat_cons (step2042 p h) (sat_cons (step1801 p h) (sat_cons (step1800 p h) (sat_cons (step1817 p h) (sat_cons (step1819 p h) (sat_cons (step1814 p h) (sat_cons (step1815 p h) (sat_cons (step1812 p h) (sat_cons (step967 p h) (sat_cons (step928 p h) (sat_cons (step937 p h) (sat_cons (step926 p h) (sat_cons (step1268 p h) (sat_cons (step1266 p h) (sat_cons (step1273 p h) (sat_nil p))))))))))))))))
def c2139 : List Lit := [(123, false), (119, false), (243, true), (1735, true)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c1801, c1800, c966, c928, c937] c2139 (by decide) p (sat_cons (step1801 p h) (sat_cons (step1800 p h) (sat_cons (step966 p h) (sat_cons (step928 p h) (sat_cons (step937 p h) (sat_nil p))))))
end B112E089
