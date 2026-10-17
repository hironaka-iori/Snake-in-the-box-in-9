import B112E105Part0000
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1993 : List Lit := [(95, true), (1716, true), (225, true), (117, true)]
theorem step1993 (p : Nat → Bool) (h : Constraints p) : clause p c1993 = true :=
  Snake9.LocalRup.prove_clause [c990, c1652, c1642, c528, c1643, c1650, c1644, c1645, c572, c545] c1993 (by decide) p (sat_cons (step990 p h) (sat_cons (step1652 p h) (sat_cons (step1642 p h) (sat_cons (step528 p h) (sat_cons (step1643 p h) (sat_cons (step1650 p h) (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step572 p h) (sat_cons (step545 p h) (sat_nil p)))))))))))
def c1994 : List Lit := [(89, true), (95, false), (1686, true), (217, true), (91, true)]
theorem step1994 (p : Nat → Bool) (h : Constraints p) : clause p c1994 = true :=
  Snake9.LocalRup.prove_clause [c1573, c1581, c1569, c1571, c1579, c1574, c525, c539] c1994 (by decide) p (sat_cons (step1573 p h) (sat_cons (step1581 p h) (sat_cons (step1569 p h) (sat_cons (step1571 p h) (sat_cons (step1579 p h) (sat_cons (step1574 p h) (sat_cons (step525 p h) (sat_cons (step539 p h) (sat_nil p)))))))))
def c1995 : List Lit := [(1719, true), (116, false), (113, false), (115, false), (108, false)]
theorem step1995 (p : Nat → Bool) (h : Constraints p) : clause p c1995 = true :=
  Snake9.LocalRup.prove_clause [c1655, c1656, c600, c688, c638, c649] c1995 (by decide) p (sat_cons (step1655 p h) (sat_cons (step1656 p h) (sat_cons (step600 p h) (sat_cons (step688 p h) (sat_cons (step638 p h) (sat_cons (step649 p h) (sat_nil p)))))))
def c1996 : List Lit := [(1715, true), (89, false), (213, true), (108, false)]
theorem step1996 (p : Nat → Bool) (h : Constraints p) : clause p c1996 = true :=
  Snake9.LocalRup.prove_clause [c1647, c1649, c1644, c1645, c1641, c544, c511, c505] c1996 (by decide) p (sat_cons (step1647 p h) (sat_cons (step1649 p h) (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step1641 p h) (sat_cons (step544 p h) (sat_cons (step511 p h) (sat_cons (step505 p h) (sat_nil p)))))))))
def c1997 : List Lit := [(84, true), (213, true), (89, false), (1716, true), (108, false)]
theorem step1997 (p : Nat → Bool) (h : Constraints p) : clause p c1997 = true :=
  Snake9.LocalRup.prove_clause [c506, c507, c511, c1641, c1650, c1644, c1645, c544] c1997 (by decide) p (sat_cons (step506 p h) (sat_cons (step507 p h) (sat_cons (step511 p h) (sat_cons (step1641 p h) (sat_cons (step1650 p h) (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step544 p h) (sat_nil p)))))))))
def c1998 : List Lit := [(1596, true), (51, true), (104, true)]
theorem step1998 (p : Nat → Bool) (h : Constraints p) : clause p c1998 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1410, c1405, c1406, c1402, c1403, c191, c255, c199] c1998 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1405 p h) (sat_cons (step1406 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step191 p h) (sat_cons (step255 p h) (sat_cons (step199 p h) (sat_nil p))))))))))
def c1999 : List Lit := [(1602, false), (1596, false), (1620, true), (56, true), (58, false), (115, false), (1574, false)]
theorem step1999 (p : Nat → Bool) (h : Constraints p) : clause p c1999 = true :=
  Snake9.LocalRup.prove_clause [c1392, c1457, c1437, c1417, c1425, c1436, c1428, c1461, c1418, c1393, c332, c1382, c1375] c1999 (by decide) p (sat_cons (step1392 p h) (sat_cons (step1457 p h) (sat_cons (step1437 p h) (sat_cons (step1417 p h) (sat_cons (step1425 p h) (sat_cons (step1436 p h) (sat_cons (step1428 p h) (sat_cons (step1461 p h) (sat_cons (step1418 p h) (sat_cons (step1393 p h) (sat_cons (step332 p h) (sat_cons (step1382 p h) (sat_cons (step1375 p h) (sat_nil p))))))))))))))
def c2000 : List Lit := [(1527, true), (1520, false)]
theorem step2000 (p : Nat → Bool) (h : Constraints p) : clause p c2000 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1283, c1286, c1280, c1268, c1273, c1265, c1266, c17, c19] c2000 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1283 p h) (sat_cons (step1286 p h) (sat_cons (step1280 p h) (sat_cons (step1268 p h) (sat_cons (step1273 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step17 p h) (sat_cons (step19 p h) (sat_nil p)))))))))))
def c2001 : List Lit := [(1550, true), (1535, false)]
theorem step2001 (p : Nat → Bool) (h : Constraints p) : clause p c2001 = true :=
  Snake9.LocalRup.prove_clause [c1301, c1332, c1328, c1304, c1315, c1317, c1295, c1296, c1313, c1309, c121, c57, c114] c2001 (by decide) p (sat_cons (step1301 p h) (sat_cons (step1332 p h) (sat_cons (step1328 p h) (sat_cons (step1304 p h) (sat_cons (step1315 p h) (sat_cons (step1317 p h) (sat_cons (step1295 p h) (sat_cons (step1296 p h) (sat_cons (step1313 p h) (sat_cons (step1309 p h) (sat_cons (step121 p h) (sat_cons (step57 p h) (sat_cons (step114 p h) (sat_nil p))))))))))))))
def c2002 : List Lit := [(33, false), (38, false), (44, false), (1573, true)]
theorem step2002 (p : Nat → Bool) (h : Constraints p) : clause p c2002 = true :=
  Snake9.LocalRup.prove_clause [c162, c163, c1368] c2002 (by decide) p (sat_cons (step162 p h) (sat_cons (step163 p h) (sat_cons (step1368 p h) (sat_nil p))))
def c2003 : List Lit := [(1587, true), (1574, false), (61, false), (40, true)]
theorem step2003 (p : Nat → Bool) (h : Constraints p) : clause p c2003 = true :=
  Snake9.LocalRup.prove_clause [c962, c1957, c1375, c1382, c168, c1394, c1397, c1385, c1383, c1370, c1376, c1377, c1378, c177, c176, c1070, c1071, c1079, c1076, c1073, c184, c2002, c1372, c1366, c1367, c164] c2003 (by decide) p (sat_cons (step962 p h) (sat_cons (step1957 p h) (sat_cons (step1375 p h) (sat_cons (step1382 p h) (sat_cons (step168 p h) (sat_cons (step1394 p h) (sat_cons (step1397 p h) (sat_cons (step1385 p h) (sat_cons (step1383 p h) (sat_cons (step1370 p h) (sat_cons (step1376 p h) (sat_cons (step1377 p h) (sat_cons (step1378 p h) (sat_cons (step177 p h) (sat_cons (step176 p h) (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step1079 p h) (sat_cons (step1076 p h) (sat_cons (step1073 p h) (sat_cons (step184 p h) (sat_cons (step2002 p h) (sat_cons (step1372 p h) (sat_cons (step1366 p h) (sat_cons (step1367 p h) (sat_cons (step164 p h) (sat_nil p)))))))))))))))))))))))))))
def c2004 : List Lit := [(41, false), (165, true), (45, false), (61, false), (39, true)]
theorem step2004 (p : Nat → Bool) (h : Constraints p) : clause p c2004 = true :=
  Snake9.LocalRup.prove_clause [c177, c176] c2004 (by decide) p (sat_cons (step177 p h) (sat_cons (step176 p h) (sat_nil p)))
def c2005 : List Lit := [(18, true), (1551, true), (2, false), (303, true), (1535, false)]
theorem step2005 (p : Nat → Bool) (h : Constraints p) : clause p c2005 = true :=
  Snake9.LocalRup.prove_clause [c1301, c1329, c1320, c1051, c1049, c1042, c1041, c1053, c1039, c1029, c116, c1309, c1311, c1317, c1318, c1333, c1313, c1304, c1295, c1296, c62, c53, c36] c2005 (by decide) p (sat_cons (step1301 p h) (sat_cons (step1329 p h) (sat_cons (step1320 p h) (sat_cons (step1051 p h) (sat_cons (step1049 p h) (sat_cons (step1042 p h) (sat_cons (step1041 p h) (sat_cons (step1053 p h) (sat_cons (step1039 p h) (sat_cons (step1029 p h) (sat_cons (step116 p h) (sat_cons (step1309 p h) (sat_cons (step1311 p h) (sat_cons (step1317 p h) (sat_cons (step1318 p h) (sat_cons (step1333 p h) (sat_cons (step1313 p h) (sat_cons (step1304 p h) (sat_cons (step1295 p h) (sat_cons (step1296 p h) (sat_cons (step62 p h) (sat_cons (step53 p h) (sat_cons (step36 p h) (sat_nil p))))))))))))))))))))))))
def c2006 : List Lit := [(1533, true), (18, false), (16, false)]
theorem step2006 (p : Nat → Bool) (h : Constraints p) : clause p c2006 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1296, c54] c2006 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1296 p h) (sat_cons (step54 p h) (sat_nil p))))
def c2007 : List Lit := [(1551, true), (16, false), (2, false), (303, true), (1535, false)]
theorem step2007 (p : Nat → Bool) (h : Constraints p) : clause p c2007 = true :=
  Snake9.LocalRup.prove_clause [c1336, c1307, c2005, c2006, c1304, c1333, c1317, c1309, c55, c56, c1297] c2007 (by decide) p (sat_cons (step1336 p h) (sat_cons (step1307 p h) (sat_cons (step2005 p h) (sat_cons (step2006 p h) (sat_cons (step1304 p h) (sat_cons (step1333 p h) (sat_cons (step1317 p h) (sat_cons (step1309 p h) (sat_cons (step55 p h) (sat_cons (step56 p h) (sat_cons (step1297 p h) (sat_nil p))))))))))))
def c2008 : List Lit := [(34, true), (31, false), (155, true), (35, false)]
theorem step2008 (p : Nat → Bool) (h : Constraints p) : clause p c2008 = true :=
  Snake9.LocalRup.prove_clause [c128, c130, c1872] c2008 (by decide) p (sat_cons (step128 p h) (sat_cons (step130 p h) (sat_cons (step1872 p h) (sat_nil p))))
def c2009 : List Lit := [(8, false), (34, false), (11, false), (4, false), (6, false), (13, false), (137, true)]
theorem step2009 (p : Nat → Bool) (h : Constraints p) : clause p c2009 = true :=
  Snake9.LocalRup.prove_clause [c14, c9, c33] c2009 (by decide) p (sat_cons (step14 p h) (sat_cons (step9 p h) (sat_cons (step33 p h) (sat_nil p))))
def c2010 : List Lit := [(1676, true), (77, false), (25, false)]
theorem step2010 (p : Nat → Bool) (h : Constraints p) : clause p c2010 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1563, c1559, c1556, c441] c2010 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1563 p h) (sat_cons (step1559 p h) (sat_cons (step1556 p h) (sat_cons (step441 p h) (sat_nil p))))))
def c2011 : List Lit := [(1748, true), (117, true), (119, false), (61, false)]
theorem step2011 (p : Nat → Bool) (h : Constraints p) : clause p c2011 = true :=
  Snake9.LocalRup.prove_clause [c1705, c1716, c1714, c1707, c1708, c862] c2011 (by decide) p (sat_cons (step1705 p h) (sat_cons (step1716 p h) (sat_cons (step1714 p h) (sat_cons (step1707 p h) (sat_cons (step1708 p h) (sat_cons (step862 p h) (sat_nil p)))))))
def c2012 : List Lit := [(1684, true), (95, false), (217, true)]
theorem step2012 (p : Nat → Bool) (h : Constraints p) : clause p c2012 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1577, c1572, c1570, c539, c525] c2012 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1577 p h) (sat_cons (step1572 p h) (sat_cons (step1570 p h) (sat_cons (step539 p h) (sat_cons (step525 p h) (sat_nil p)))))))
def c2013 : List Lit := [(1597, true), (49, true), (172, true), (51, true), (104, true)]
theorem step2013 (p : Nat → Bool) (h : Constraints p) : clause p c2013 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1413, c1411, c1404, c1405, c1406, c255, c204] c2013 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1413 p h) (sat_cons (step1411 p h) (sat_cons (step1404 p h) (sat_cons (step1405 p h) (sat_cons (step1406 p h) (sat_cons (step255 p h) (sat_cons (step204 p h) (sat_nil p)))))))))
def c2014 : List Lit := [(1667, true), (66, true), (192, true), (64, true), (104, true)]
theorem step2014 (p : Nat → Bool) (h : Constraints p) : clause p c2014 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1524, c1552, c1549, c1525, c1532, c1534, c1520, c1530, c1527, c403, c398] c2014 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1524 p h) (sat_cons (step1552 p h) (sat_cons (step1549 p h) (sat_cons (step1525 p h) (sat_cons (step1532 p h) (sat_cons (step1534 p h) (sat_cons (step1520 p h) (sat_cons (step1530 p h) (sat_cons (step1527 p h) (sat_cons (step403 p h) (sat_cons (step398 p h) (sat_nil p)))))))))))))
def c2015 : List Lit := [(1688, true), (209, true), (104, true)]
theorem step2015 (p : Nat → Bool) (h : Constraints p) : clause p c2015 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1587, c1575, c1577, c1561, c1573, c1570, c1558, c493, c486] c2015 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1587 p h) (sat_cons (step1575 p h) (sat_cons (step1577 p h) (sat_cons (step1561 p h) (sat_cons (step1573 p h) (sat_cons (step1570 p h) (sat_cons (step1558 p h) (sat_cons (step493 p h) (sat_cons (step486 p h) (sat_nil p)))))))))))
def c2016 : List Lit := [(1560, true), (1535, false), (17, true)]
theorem step2016 (p : Nat → Bool) (h : Constraints p) : clause p c2016 = true :=
  Snake9.LocalRup.prove_clause [c1978, c1296, c1304, c2001, c1346, c1350, c1336, c1333, c2000, c1307, c1315, c1317, c1274, c1297, c1313, c1309, c121, c56, c114] c2016 (by decide) p (sat_cons (step1978 p h) (sat_cons (step1296 p h) (sat_cons (step1304 p h) (sat_cons (step2001 p h) (sat_cons (step1346 p h) (sat_cons (step1350 p h) (sat_cons (step1336 p h) (sat_cons (step1333 p h) (sat_cons (step2000 p h) (sat_cons (step1307 p h) (sat_cons (step1315 p h) (sat_cons (step1317 p h) (sat_cons (step1274 p h) (sat_cons (step1297 p h) (sat_cons (step1313 p h) (sat_cons (step1309 p h) (sat_cons (step121 p h) (sat_cons (step56 p h) (sat_cons (step114 p h) (sat_nil p))))))))))))))))))))
def c2017 : List Lit := [(1545, true), (20, false), (16, false)]
theorem step2017 (p : Nat → Bool) (h : Constraints p) : clause p c2017 = true :=
  Snake9.LocalRup.prove_clause [c1315, c1317, c1313, c1309, c56, c121, c114] c2017 (by decide) p (sat_cons (step1315 p h) (sat_cons (step1317 p h) (sat_cons (step1313 p h) (sat_cons (step1309 p h) (sat_cons (step56 p h) (sat_cons (step121 p h) (sat_cons (step114 p h) (sat_nil p))))))))
def c2018 : List Lit := [(1596, true), (53, false), (54, false)]
theorem step2018 (p : Nat → Bool) (h : Constraints p) : clause p c2018 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1410, c1406, c1403, c255] c2018 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1406 p h) (sat_cons (step1403 p h) (sat_cons (step255 p h) (sat_nil p))))))
def c2019 : List Lit := [(1596, false), (1621, true), (1601, false), (40, true), (1574, false)]
theorem step2019 (p : Nat → Bool) (h : Constraints p) : clause p c2019 = true :=
  Snake9.LocalRup.prove_clause [c1375, c1382, c1393, c1462, c1427, c1436, c1437, c1468, c1428, c2003, c1419] c2019 (by decide) p (sat_cons (step1375 p h) (sat_cons (step1382 p h) (sat_cons (step1393 p h) (sat_cons (step1462 p h) (sat_cons (step1427 p h) (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step1468 p h) (sat_cons (step1428 p h) (sat_cons (step2003 p h) (sat_cons (step1419 p h) (sat_nil p))))))))))))
def c2020 : List Lit := [(53, true), (1596, true), (176, true), (64, true)]
theorem step2020 (p : Nat → Bool) (h : Constraints p) : clause p c2020 = true :=
  Snake9.LocalRup.prove_clause [c974, c1408, c1406, c1410, c1403, c1402, c191, c253, c254, c1886, c367] c2020 (by decide) p (sat_cons (step974 p h) (sat_cons (step1408 p h) (sat_cons (step1406 p h) (sat_cons (step1410 p h) (sat_cons (step1403 p h) (sat_cons (step1402 p h) (sat_cons (step191 p h) (sat_cons (step253 p h) (sat_cons (step254 p h) (sat_cons (step1886 p h) (sat_cons (step367 p h) (sat_nil p))))))))))))
def c2021 : List Lit := [(1596, true), (176, true), (64, true)]
theorem step2021 (p : Nat → Bool) (h : Constraints p) : clause p c2021 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1410, c1406, c1403, c2020, c1405, c255] c2021 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1406 p h) (sat_cons (step1403 p h) (sat_cons (step2020 p h) (sat_cons (step1405 p h) (sat_cons (step255 p h) (sat_nil p))))))))
def c2022 : List Lit := [(49, false), (2, false), (1576, true), (25, false), (126, true), (35, true)]
theorem step2022 (p : Nat → Bool) (h : Constraints p) : clause p c2022 = true :=
  Snake9.LocalRup.prove_clause [c1932, c38, c2, c132, c1373, c133, c1368] c2022 (by decide) p (sat_cons (step1932 p h) (sat_cons (step38 p h) (sat_cons (step2 p h) (sat_cons (step132 p h) (sat_cons (step1373 p h) (sat_cons (step133 p h) (sat_cons (step1368 p h) (sat_nil p))))))))
def c2023 : List Lit := [(1597, false), (1601, false), (1622, true), (40, true), (1574, false)]
theorem step2023 (p : Nat → Bool) (h : Constraints p) : clause p c2023 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1375, c1382, c1393, c1463, c1441, c1442, c1469, c1428, c2003, c1419] c2023 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1375 p h) (sat_cons (step1382 p h) (sat_cons (step1393 p h) (sat_cons (step1463 p h) (sat_cons (step1441 p h) (sat_cons (step1442 p h) (sat_cons (step1469 p h) (sat_cons (step1428 p h) (sat_cons (step2003 p h) (sat_cons (step1419 p h) (sat_nil p))))))))))))
def c2024 : List Lit := [(1587, true), (2, false), (161, true), (1577, false), (35, true), (1572, false)]
theorem step2024 (p : Nat → Bool) (h : Constraints p) : clause p c2024 = true :=
  Snake9.LocalRup.prove_clause [c1382, c1369, c1397, c1394, c1370, c1372, c1383, c1368, c131, c1378, c160, c2002] c2024 (by decide) p (sat_cons (step1382 p h) (sat_cons (step1369 p h) (sat_cons (step1397 p h) (sat_cons (step1394 p h) (sat_cons (step1370 p h) (sat_cons (step1372 p h) (sat_cons (step1383 p h) (sat_cons (step1368 p h) (sat_cons (step131 p h) (sat_cons (step1378 p h) (sat_cons (step160 p h) (sat_cons (step2002 p h) (sat_nil p)))))))))))))
def c2025 : List Lit := [(1748, true), (119, false), (61, false)]
theorem step2025 (p : Nat → Bool) (h : Constraints p) : clause p c2025 = true :=
  Snake9.LocalRup.prove_clause [c2011, c863, c861, c1708, c1706, c1714] c2025 (by decide) p (sat_cons (step2011 p h) (sat_cons (step863 p h) (sat_cons (step861 p h) (sat_cons (step1708 p h) (sat_cons (step1706 p h) (sat_cons (step1714 p h) (sat_nil p)))))))
def c2026 : List Lit := [(1596, true), (37, false), (33, false)]
theorem step2026 (p : Nat → Bool) (h : Constraints p) : clause p c2026 = true :=
  Snake9.LocalRup.prove_clause [c1937, c1408, c1410, c1405, c1406, c1402, c1403, c2018, c191, c134, c285, c159, c254, c1064, c1089, c1065, c1092, c1067, c1093, c1082, c1113, c1119] c2026 (by decide) p (sat_cons (step1937 p h) (sat_cons (step1408 p h) (sat_cons (step1410 p h) (sat_cons (step1405 p h) (sat_cons (step1406 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step2018 p h) (sat_cons (step191 p h) (sat_cons (step134 p h) (sat_cons (step285 p h) (sat_cons (step159 p h) (sat_cons (step254 p h) (sat_cons (step1064 p h) (sat_cons (step1089 p h) (sat_cons (step1065 p h) (sat_cons (step1092 p h) (sat_cons (step1067 p h) (sat_cons (step1093 p h) (sat_cons (step1082 p h) (sat_cons (step1113 p h) (sat_cons (step1119 p h) (sat_nil p)))))))))))))))))))))))
def c2027 : List Lit := [(44, true), (169, true), (1580, true), (61, true)]
theorem step2027 (p : Nat → Bool) (h : Constraints p) : clause p c2027 = true :=
  Snake9.LocalRup.prove_clause [c965, c963, c190, c1379, c187, c186, c179, c1875] c2027 (by decide) p (sat_cons (step965 p h) (sat_cons (step963 p h) (sat_cons (step190 p h) (sat_cons (step1379 p h) (sat_cons (step187 p h) (sat_cons (step186 p h) (sat_cons (step179 p h) (sat_cons (step1875 p h) (sat_nil p)))))))))
def c2028 : List Lit := [(329, true), (37, false), (1580, true), (33, false), (61, true)]
theorem step2028 (p : Nat → Bool) (h : Constraints p) : clause p c2028 = true :=
  Snake9.LocalRup.prove_clause [c1075, c1076, c1074, c1073, c2027, c184, c163] c2028 (by decide) p (sat_cons (step1075 p h) (sat_cons (step1076 p h) (sat_cons (step1074 p h) (sat_cons (step1073 p h) (sat_cons (step2027 p h) (sat_cons (step184 p h) (sat_cons (step163 p h) (sat_nil p))))))))
def c2029 : List Lit := [(44, true), (165, true), (1583, true), (40, true)]
theorem step2029 (p : Nat → Bool) (h : Constraints p) : clause p c2029 = true :=
  Snake9.LocalRup.prove_clause [c962, c1375, c1384, c168, c1378, c1379, c1386, c1376, c175, c176, c1875] c2029 (by decide) p (sat_cons (step962 p h) (sat_cons (step1375 p h) (sat_cons (step1384 p h) (sat_cons (step168 p h) (sat_cons (step1378 p h) (sat_cons (step1379 p h) (sat_cons (step1386 p h) (sat_cons (step1376 p h) (sat_cons (step175 p h) (sat_cons (step176 p h) (sat_cons (step1875 p h) (sat_nil p))))))))))))
def c2030 : List Lit := [(42, false), (46, false), (165, true), (39, true), (61, true)]
theorem step2030 (p : Nat → Bool) (h : Constraints p) : clause p c2030 = true :=
  Snake9.LocalRup.prove_clause [c965, c963, c189, c179, c185, c175] c2030 (by decide) p (sat_cons (step965 p h) (sat_cons (step963 p h) (sat_cons (step189 p h) (sat_cons (step179 p h) (sat_cons (step185 p h) (sat_cons (step175 p h) (sat_nil p)))))))
def c2031 : List Lit := [(1545, true), (20, false), (19, true), (152, true)]
theorem step2031 (p : Nat → Bool) (h : Constraints p) : clause p c2031 = true :=
  Snake9.LocalRup.prove_clause [c1315, c1317, c1313, c1309, c119, c121] c2031 (by decide) p (sat_cons (step1315 p h) (sat_cons (step1317 p h) (sat_cons (step1313 p h) (sat_cons (step1309 p h) (sat_cons (step119 p h) (sat_cons (step121 p h) (sat_nil p)))))))
def c2032 : List Lit := [(116, false), (1720, true), (104, false), (48, false)]
theorem step2032 (p : Nat → Bool) (h : Constraints p) : clause p c2032 = true :=
  Snake9.LocalRup.prove_clause [c617, c619, c1657] c2032 (by decide) p (sat_cons (step617 p h) (sat_cons (step619 p h) (sat_cons (step1657 p h) (sat_nil p))))
def c2033 : List Lit := [(118, true), (50, true), (60, false), (59, false), (184, true)]
theorem step2033 (p : Nat → Bool) (h : Constraints p) : clause p c2033 = true :=
  Snake9.LocalRup.prove_clause [c354, c355, c1890] c2033 (by decide) p (sat_cons (step354 p h) (sat_cons (step355 p h) (sat_cons (step1890 p h) (sat_nil p))))
def c2034 : List Lit := [(47, false), (104, false), (48, false), (52, true), (49, true)]
theorem step2034 (p : Nat → Bool) (h : Constraints p) : clause p c2034 = true :=
  Snake9.LocalRup.prove_clause [c966, c195, c1878] c2034 (by decide) p (sat_cons (step966 p h) (sat_cons (step195 p h) (sat_cons (step1878 p h) (sat_nil p))))
def c2035 : List Lit := [(51, true), (53, true), (48, false), (52, true), (49, true), (172, true)]
theorem step2035 (p : Nat → Bool) (h : Constraints p) : clause p c2035 = true :=
  Snake9.LocalRup.prove_clause [c204, c207, c2034] c2035 (by decide) p (sat_cons (step204 p h) (sat_cons (step207 p h) (sat_cons (step2034 p h) (sat_nil p))))
def c2036 : List Lit := [(1721, false), (1715, false), (1737, false), (1764, true), (102, true), (104, true), (110, true), (229, true)]
theorem step2036 (p : Nat → Bool) (h : Constraints p) : clause p c2036 = true :=
  Snake9.LocalRup.prove_clause [c1691, c1700, c1728, c1767, c1676, c1656, c1664, c1667, c1675, c1657, c1760, c652, c650, c1733, c1915, c1703, c1693] c2036 (by decide) p (sat_cons (step1691 p h) (sat_cons (step1700 p h) (sat_cons (step1728 p h) (sat_cons (step1767 p h) (sat_cons (step1676 p h) (sat_cons (step1656 p h) (sat_cons (step1664 p h) (sat_cons (step1667 p h) (sat_cons (step1675 p h) (sat_cons (step1657 p h) (sat_cons (step1760 p h) (sat_cons (step652 p h) (sat_cons (step650 p h) (sat_cons (step1733 p h) (sat_cons (step1915 p h) (sat_cons (step1703 p h) (sat_cons (step1693 p h) (sat_nil p))))))))))))))))))
def c2037 : List Lit := [(116, false), (119, true), (123, false), (104, true), (99, false), (240, true)]
theorem step2037 (p : Nat → Bool) (h : Constraints p) : clause p c2037 = true :=
  Snake9.LocalRup.prove_clause [c871, c799] c2037 (by decide) p (sat_cons (step871 p h) (sat_cons (step799 p h) (sat_nil p)))
def c2038 : List Lit := [(78, false), (1716, true), (118, false), (60, false), (225, true)]
theorem step2038 (p : Nat → Bool) (h : Constraints p) : clause p c2038 = true :=
  Snake9.LocalRup.prove_clause [c822, c825, c1993] c2038 (by decide) p (sat_cons (step822 p h) (sat_cons (step825 p h) (sat_cons (step1993 p h) (sat_nil p))))
def c2039 : List Lit := [(105, false), (1741, true), (104, true), (54, false), (110, true), (229, true)]
theorem step2039 (p : Nat → Bool) (h : Constraints p) : clause p c2039 = true :=
  Snake9.LocalRup.prove_clause [c652, c650, c1915, c686, c1693, c1695, c1703] c2039 (by decide) p (sat_cons (step652 p h) (sat_cons (step650 p h) (sat_cons (step1915 p h) (sat_cons (step686 p h) (sat_cons (step1693 p h) (sat_cons (step1695 p h) (sat_cons (step1703 p h) (sat_nil p))))))))
def c2040 : List Lit := [(64, false), (54, false), (60, false), (59, false), (188, true)]
theorem step2040 (p : Nat → Bool) (h : Constraints p) : clause p c2040 = true :=
  Snake9.LocalRup.prove_clause [c336, c374, c376] c2040 (by decide) p (sat_cons (step336 p h) (sat_cons (step374 p h) (sat_cons (step376 p h) (sat_nil p))))
def c2041 : List Lit := [(105, false), (109, false), (1742, true), (102, false), (110, true), (48, false), (54, false), (229, true)]
theorem step2041 (p : Nat → Bool) (h : Constraints p) : clause p c2041 = true :=
  Snake9.LocalRup.prove_clause [c615, c685, c686, c652, c1693, c594, c1704, c1696] c2041 (by decide) p (sat_cons (step615 p h) (sat_cons (step685 p h) (sat_cons (step686 p h) (sat_cons (step652 p h) (sat_cons (step1693 p h) (sat_cons (step594 p h) (sat_cons (step1704 p h) (sat_cons (step1696 p h) (sat_nil p)))))))))
def c2042 : List Lit := [(1763, true), (1725, false), (1739, false), (225, true)]
theorem step2042 (p : Nat → Bool) (h : Constraints p) : clause p c2042 = true :=
  Snake9.LocalRup.prove_clause [c1671, c1723, c1766, c1759, c1676, c1724, c1647, c1649, c1711, c1713, c1644, c1642, c1708, c1705, c526, c904, c571] c2042 (by decide) p (sat_cons (step1671 p h) (sat_cons (step1723 p h) (sat_cons (step1766 p h) (sat_cons (step1759 p h) (sat_cons (step1676 p h) (sat_cons (step1724 p h) (sat_cons (step1647 p h) (sat_cons (step1649 p h) (sat_cons (step1711 p h) (sat_cons (step1713 p h) (sat_cons (step1644 p h) (sat_cons (step1642 p h) (sat_cons (step1708 p h) (sat_cons (step1705 p h) (sat_cons (step526 p h) (sat_cons (step904 p h) (sat_cons (step571 p h) (sat_nil p))))))))))))))))))
def c2043 : List Lit := [(1752, true), (110, true), (246, true)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c1691, c1699, c1728, c1724, c1702, c1700, c1711, c1713, c1693, c1694, c1695, c1708, c1709, c1705, c709, c856, c909, c926] c2043 (by decide) p (sat_cons (step1691 p h) (sat_cons (step1699 p h) (sat_cons (step1728 p h) (sat_cons (step1724 p h) (sat_cons (step1702 p h) (sat_cons (step1700 p h) (sat_cons (step1711 p h) (sat_cons (step1713 p h) (sat_cons (step1693 p h) (sat_cons (step1694 p h) (sat_cons (step1695 p h) (sat_cons (step1708 p h) (sat_cons (step1709 p h) (sat_cons (step1705 p h) (sat_cons (step709 p h) (sat_cons (step856 p h) (sat_cons (step909 p h) (sat_cons (step926 p h) (sat_nil p)))))))))))))))))))
def c2044 : List Lit := [(116, false), (104, false), (1725, true), (48, false)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c620, c2032, c1658, c1667] c2044 (by decide) p (sat_cons (step620 p h) (sat_cons (step2032 p h) (sat_cons (step1658 p h) (sat_cons (step1667 p h) (sat_nil p)))))
def c2045 : List Lit := [(85, true), (1677, true), (121, true), (117, false), (207, true)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c1562, c1558, c1560, c1564, c474, c1556, c444] c2045 (by decide) p (sat_cons (step1562 p h) (sat_cons (step1558 p h) (sat_cons (step1560 p h) (sat_cons (step1564 p h) (sat_cons (step474 p h) (sat_cons (step1556 p h) (sat_cons (step444 p h) (sat_nil p))))))))
def c2046 : List Lit := [(85, false), (104, false), (1725, true), (102, true), (48, false)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c612, c613, c1657, c1658, c1667] c2046 (by decide) p (sat_cons (step612 p h) (sat_cons (step613 p h) (sat_cons (step1657 p h) (sat_cons (step1658 p h) (sat_cons (step1667 p h) (sat_nil p))))))
def c2047 : List Lit := [(1654, true), (63, false), (52, false)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1523, c1519, c366] c2047 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1523 p h) (sat_cons (step1519 p h) (sat_cons (step366 p h) (sat_nil p)))))
def c2048 : List Lit := [(104, true), (64, true), (1698, true), (1654, false), (427, true)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c1187, c1152, c1133, c1130, c1129, c1185, c1182, c1164, c1161, c1160, c2015, c1620, c1548, c1545, c1524, c1532, c1534, c1518, c1530, c1527, c398, c403] c2048 (by decide) p (sat_cons (step1187 p h) (sat_cons (step1152 p h) (sat_cons (step1133 p h) (sat_cons (step1130 p h) (sat_cons (step1129 p h) (sat_cons (step1185 p h) (sat_cons (step1182 p h) (sat_cons (step1164 p h) (sat_cons (step1161 p h) (sat_cons (step1160 p h) (sat_cons (step2015 p h) (sat_cons (step1620 p h) (sat_cons (step1548 p h) (sat_cons (step1545 p h) (sat_cons (step1524 p h) (sat_cons (step1532 p h) (sat_cons (step1534 p h) (sat_cons (step1518 p h) (sat_cons (step1530 p h) (sat_cons (step1527 p h) (sat_cons (step398 p h) (sat_cons (step403 p h) (sat_nil p)))))))))))))))))))))))
def c2049 : List Lit := [(123, true), (121, false), (1738, false), (1754, true)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c1698, c1730, c1712, c1708, c1710, c1711, c1714, c1734, c1705, c1701, c906, c1691] c2049 (by decide) p (sat_cons (step1698 p h) (sat_cons (step1730 p h) (sat_cons (step1712 p h) (sat_cons (step1708 p h) (sat_cons (step1710 p h) (sat_cons (step1711 p h) (sat_cons (step1714 p h) (sat_cons (step1734 p h) (sat_cons (step1705 p h) (sat_cons (step1701 p h) (sat_cons (step906 p h) (sat_cons (step1691 p h) (sat_nil p)))))))))))))
def c2050 : List Lit := [(1739, true), (55, true), (234, true), (56, false)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c1697, c1699, c1695, c1691, c1692, c707, c728, c700] c2050 (by decide) p (sat_cons (step1697 p h) (sat_cons (step1699 p h) (sat_cons (step1695 p h) (sat_cons (step1691 p h) (sat_cons (step1692 p h) (sat_cons (step707 p h) (sat_cons (step728 p h) (sat_cons (step700 p h) (sat_nil p)))))))))
def c2051 : List Lit := [(105, false), (108, false), (1722, true), (229, true), (54, false), (48, false)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c685, c650, c651, c618, c598, c1660] c2051 (by decide) p (sat_cons (step685 p h) (sat_cons (step650 p h) (sat_cons (step651 p h) (sat_cons (step618 p h) (sat_cons (step598 p h) (sat_cons (step1660 p h) (sat_nil p)))))))
def c2052 : List Lit := [(104, true), (1698, true), (63, false), (427, true), (52, false)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c2047, c1187, c1152, c1133, c1130, c1129, c1185, c1182, c1164, c1161, c1160, c2015, c2048, c1620, c366, c1548, c1545, c1522, c1532, c1534, c1520, c1530, c1527, c398, c403] c2052 (by decide) p (sat_cons (step2047 p h) (sat_cons (step1187 p h) (sat_cons (step1152 p h) (sat_cons (step1133 p h) (sat_cons (step1130 p h) (sat_cons (step1129 p h) (sat_cons (step1185 p h) (sat_cons (step1182 p h) (sat_cons (step1164 p h) (sat_cons (step1161 p h) (sat_cons (step1160 p h) (sat_cons (step2015 p h) (sat_cons (step2048 p h) (sat_cons (step1620 p h) (sat_cons (step366 p h) (sat_cons (step1548 p h) (sat_cons (step1545 p h) (sat_cons (step1522 p h) (sat_cons (step1532 p h) (sat_cons (step1534 p h) (sat_cons (step1520 p h) (sat_cons (step1530 p h) (sat_cons (step1527 p h) (sat_cons (step398 p h) (sat_cons (step403 p h) (sat_nil p))))))))))))))))))))))))))
def c2053 : List Lit := [(1741, true), (109, false), (115, true), (110, true), (54, false)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c1694, c1691, c1701, c1703, c1696, c1693, c687] c2053 (by decide) p (sat_cons (step1694 p h) (sat_cons (step1691 p h) (sat_cons (step1701 p h) (sat_cons (step1703 p h) (sat_cons (step1696 p h) (sat_cons (step1693 p h) (sat_cons (step687 p h) (sat_nil p))))))))
def c2054 : List Lit := [(331, true), (44, false), (41, false), (39, true), (61, true)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c1077, c1078, c1076, c1071, c1073, c1070, c183, c176, c2030] c2054 (by decide) p (sat_cons (step1077 p h) (sat_cons (step1078 p h) (sat_cons (step1076 p h) (sat_cons (step1071 p h) (sat_cons (step1073 p h) (sat_cons (step1070 p h) (sat_cons (step183 p h) (sat_cons (step176 p h) (sat_cons (step2030 p h) (sat_nil p))))))))))
def c2055 : List Lit := [(1747, true), (112, true), (113, false), (247, true)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c1711, c1713, c1708, c1709, c1705, c1706, c867, c909, c939, c936] c2055 (by decide) p (sat_cons (step1711 p h) (sat_cons (step1713 p h) (sat_cons (step1708 p h) (sat_cons (step1709 p h) (sat_cons (step1705 p h) (sat_cons (step1706 p h) (sat_cons (step867 p h) (sat_cons (step909 p h) (sat_cons (step939 p h) (sat_cons (step936 p h) (sat_nil p)))))))))))
def c2056 : List Lit := [(117, false), (121, false), (1746, true), (110, false)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c906, c907, c1710] c2056 (by decide) p (sat_cons (step906 p h) (sat_cons (step907 p h) (sat_cons (step1710 p h) (sat_nil p))))
end B112E105
