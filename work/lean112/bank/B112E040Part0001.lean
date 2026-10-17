import B112E040Part0000
namespace B112E040
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1589 : List Lit := [(1594, true), (63, true)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c1227, c1230, c1256, c1253, c1231, c1558, c1229] c1589 (by decide) p (sat_cons (step1227 p h) (sat_cons (step1230 p h) (sat_cons (step1256 p h) (sat_cons (step1253 p h) (sat_cons (step1231 p h) (sat_cons (step1558 p h) (sat_cons (step1229 p h) (sat_nil p))))))))
def c1590 : List Lit := [(111, true), (1657, false), (1711, true), (1600, false), (1594, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1550, c1300, c1443, c1411, c1362, c1364, c1383, c1410, c1451, c1301, c1290, c1269, c1566, c1263] c1590 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1550 p h) (sat_cons (step1300 p h) (sat_cons (step1443 p h) (sat_cons (step1411 p h) (sat_cons (step1362 p h) (sat_cons (step1364 p h) (sat_cons (step1383 p h) (sat_cons (step1410 p h) (sat_cons (step1451 p h) (sat_cons (step1301 p h) (sat_cons (step1290 p h) (sat_cons (step1269 p h) (sat_cons (step1566 p h) (sat_cons (step1263 p h) (sat_nil p))))))))))))))))
def c1591 : List Lit := [(1658, false), (1711, true), (1600, false), (1594, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1550, c720, c1300, c1443, c1415, c1416, c1451, c1381, c1383, c1301, c1377, c1364, c1290, c1373, c1361, c1269, c654, c643, c1263] c1591 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1550 p h) (sat_cons (step720 p h) (sat_cons (step1300 p h) (sat_cons (step1443 p h) (sat_cons (step1415 p h) (sat_cons (step1416 p h) (sat_cons (step1451 p h) (sat_cons (step1381 p h) (sat_cons (step1383 p h) (sat_cons (step1301 p h) (sat_cons (step1377 p h) (sat_cons (step1364 p h) (sat_cons (step1290 p h) (sat_cons (step1373 p h) (sat_cons (step1361 p h) (sat_cons (step1269 p h) (sat_cons (step654 p h) (sat_cons (step643 p h) (sat_cons (step1263 p h) (sat_nil p)))))))))))))))))))))
def c1592 : List Lit := [(80, true), (1605, true)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c701, c1267, c1263, c1265, c1269, c1260, c1261, c477, c480] c1592 (by decide) p (sat_cons (step701 p h) (sat_cons (step1267 p h) (sat_cons (step1263 p h) (sat_cons (step1265 p h) (sat_cons (step1269 p h) (sat_cons (step1260 p h) (sat_cons (step1261 p h) (sat_cons (step477 p h) (sat_cons (step480 p h) (sat_nil p))))))))))
def c1593 : List Lit := [(105, false), (1642, true), (96, false), (79, false)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c539, c538, c1316] c1593 (by decide) p (sat_cons (step539 p h) (sat_cons (step538 p h) (sat_cons (step1316 p h) (sat_nil p))))
def c1594 : List Lit := [(88, false), (85, false), (77, false), (109, false)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c707, c511, c501, c510] c1594 (by decide) p (sat_cons (step707 p h) (sat_cons (step511 p h) (sat_cons (step501 p h) (sat_cons (step510 p h) (sat_nil p)))))
def c1595 : List Lit := [(77, false), (1613, true), (109, false)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c706, c1280, c1555, c1282, c1273, c1594, c1278, c507, c500] c1595 (by decide) p (sat_cons (step706 p h) (sat_cons (step1280 p h) (sat_cons (step1555 p h) (sat_cons (step1282 p h) (sat_cons (step1273 p h) (sat_cons (step1594 p h) (sat_cons (step1278 p h) (sat_cons (step507 p h) (sat_cons (step500 p h) (sat_nil p))))))))))
def c1596 : List Lit := [(1618, true), (1667, true), (111, false)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c719, c1549, c1550, c701, c705, c706, c707, c1527, c1364, c1361, c650, c649, c1366, c1359, c1358, c1288, c1290, c1284, c1271, c1592, c1595, c1260, c1262, c1269, c477, c478, c1264, c481, c488, c1273, c1275, c498, c1282, c517, c1276, c1277, c616, c506, c508, c505, c514, c820, c652, c823, c857, c824, c858, c826, c864, c829, c867, c878, c870] c1596 (by decide) p (sat_cons (step719 p h) (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step701 p h) (sat_cons (step705 p h) (sat_cons (step706 p h) (sat_cons (step707 p h) (sat_cons (step1527 p h) (sat_cons (step1364 p h) (sat_cons (step1361 p h) (sat_cons (step650 p h) (sat_cons (step649 p h) (sat_cons (step1366 p h) (sat_cons (step1359 p h) (sat_cons (step1358 p h) (sat_cons (step1288 p h) (sat_cons (step1290 p h) (sat_cons (step1284 p h) (sat_cons (step1271 p h) (sat_cons (step1592 p h) (sat_cons (step1595 p h) (sat_cons (step1260 p h) (sat_cons (step1262 p h) (sat_cons (step1269 p h) (sat_cons (step477 p h) (sat_cons (step478 p h) (sat_cons (step1264 p h) (sat_cons (step481 p h) (sat_cons (step488 p h) (sat_cons (step1273 p h) (sat_cons (step1275 p h) (sat_cons (step498 p h) (sat_cons (step1282 p h) (sat_cons (step517 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step616 p h) (sat_cons (step506 p h) (sat_cons (step508 p h) (sat_cons (step505 p h) (sat_cons (step514 p h) (sat_cons (step820 p h) (sat_cons (step652 p h) (sat_cons (step823 p h) (sat_cons (step857 p h) (sat_cons (step824 p h) (sat_cons (step858 p h) (sat_cons (step826 p h) (sat_cons (step864 p h) (sat_cons (step829 p h) (sat_cons (step867 p h) (sat_cons (step878 p h) (sat_cons (step870 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1597 : List Lit := [(37, true), (1503, true), (35, false), (105, false)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c1057, c1053, c1055, c1059, c251] c1597 (by decide) p (sat_cons (step1057 p h) (sat_cons (step1053 p h) (sat_cons (step1055 p h) (sat_cons (step1059 p h) (sat_cons (step251 p h) (sat_nil p))))))
def c1598 : List Lit := [(1510, true), (39, true), (41, false), (111, false)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c1061, c1072, c1070, c1063, c1065, c347] c1598 (by decide) p (sat_cons (step1061 p h) (sat_cons (step1072 p h) (sat_cons (step1070 p h) (sat_cons (step1063 p h) (sat_cons (step1065 p h) (sat_cons (step347 p h) (sat_nil p)))))))
def c1599 : List Lit := [(73, true), (1596, true), (64, true), (367, true)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c695, c1236, c803, c802, c800, c804, c799, c1238, c447, c1244, c436, c1258, c1557] c1599 (by decide) p (sat_cons (step695 p h) (sat_cons (step1236 p h) (sat_cons (step803 p h) (sat_cons (step802 p h) (sat_cons (step800 p h) (sat_cons (step804 p h) (sat_cons (step799 p h) (sat_cons (step1238 p h) (sat_cons (step447 p h) (sat_cons (step1244 p h) (sat_cons (step436 p h) (sat_cons (step1258 p h) (sat_cons (step1557 p h) (sat_nil p))))))))))))))
def c1600 : List Lit := [(1667, true), (88, false), (111, false), (234, true)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c719, c707, c1364, c1366, c1361, c1359, c649, c616, c652, c508, c514] c1600 (by decide) p (sat_cons (step719 p h) (sat_cons (step707 p h) (sat_cons (step1364 p h) (sat_cons (step1366 p h) (sat_cons (step1361 p h) (sat_cons (step1359 p h) (sat_cons (step649 p h) (sat_cons (step616 p h) (sat_cons (step652 p h) (sat_cons (step508 p h) (sat_cons (step514 p h) (sat_nil p))))))))))))
def c1601 : List Lit := [(75, false), (80, false), (112, false), (110, false), (90, false), (92, false), (1619, true), (85, true)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c708, c475, c488, c474, c516, c1262, c517, c1271, c1275, c1291, c1284] c1601 (by decide) p (sat_cons (step708 p h) (sat_cons (step475 p h) (sat_cons (step488 p h) (sat_cons (step474 p h) (sat_cons (step516 p h) (sat_cons (step1262 p h) (sat_cons (step517 p h) (sat_cons (step1271 p h) (sat_cons (step1275 p h) (sat_cons (step1291 p h) (sat_cons (step1284 p h) (sat_nil p))))))))))))
def c1602 : List Lit := [(82, false), (80, false), (110, false), (90, false)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c705, c517, c496, c498] c1602 (by decide) p (sat_cons (step705 p h) (sat_cons (step517 p h) (sat_cons (step496 p h) (sat_cons (step498 p h) (sat_nil p)))))
def c1603 : List Lit := [(1455, true), (1446, false)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c946, c953, c957, c947, c935, c1565] c1603 (by decide) p (sat_cons (step946 p h) (sat_cons (step953 p h) (sat_cons (step957 p h) (sat_cons (step947 p h) (sat_cons (step935 p h) (sat_cons (step1565 p h) (sat_nil p)))))))
def c1604 : List Lit := [(1643, true), (104, true)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c710, c1317, c1319, c1314, c1315, c1311, c523, c526] c1604 (by decide) p (sat_cons (step710 p h) (sat_cons (step1317 p h) (sat_cons (step1319 p h) (sat_cons (step1314 p h) (sat_cons (step1315 p h) (sat_cons (step1311 p h) (sat_cons (step523 p h) (sat_cons (step526 p h) (sat_nil p)))))))))
def c1605 : List Lit := [(1609, false), (1619, true), (76, true)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1289, c1284, c1285, c1291, c1555, c1271, c1262] c1605 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1289 p h) (sat_cons (step1284 p h) (sat_cons (step1285 p h) (sat_cons (step1291 p h) (sat_cons (step1555 p h) (sat_cons (step1271 p h) (sat_cons (step1262 p h) (sat_nil p)))))))))
def c1606 : List Lit := [(1681, true), (111, true), (116, true), (112, false), (80, false)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c1362, c1364, c1372, c1377, c1388, c1385, c1365, c1379, c1363, c1374, c643] c1606 (by decide) p (sat_cons (step1362 p h) (sat_cons (step1364 p h) (sat_cons (step1372 p h) (sat_cons (step1377 p h) (sat_cons (step1388 p h) (sat_cons (step1385 p h) (sat_cons (step1365 p h) (sat_cons (step1379 p h) (sat_cons (step1363 p h) (sat_cons (step1374 p h) (sat_cons (step643 p h) (sat_nil p))))))))))))
def c1607 : List Lit := [(63, false), (1480, true), (1470, false), (25, false), (98, false)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c153, c144, c986, c972, c994, c974, c1003] c1607 (by decide) p (sat_cons (step153 p h) (sat_cons (step144 p h) (sat_cons (step986 p h) (sat_cons (step972 p h) (sat_cons (step994 p h) (sat_cons (step974 p h) (sat_cons (step1003 p h) (sat_nil p))))))))
def c1608 : List Lit := [(1619, true), (1602, false), (76, true), (109, false)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1261, c1269, c1293, c1291, c1272, c1595, c1262] c1608 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1261 p h) (sat_cons (step1269 p h) (sat_cons (step1293 p h) (sat_cons (step1291 p h) (sat_cons (step1272 p h) (sat_cons (step1595 p h) (sat_cons (step1262 p h) (sat_nil p)))))))))
def c1609 : List Lit := [(103, false), (105, false), (1613, true), (100, false), (109, false)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c707, c576, c624, c621, c1273, c508, c1282, c1276] c1609 (by decide) p (sat_cons (step707 p h) (sat_cons (step576 p h) (sat_cons (step624 p h) (sat_cons (step621 p h) (sat_cons (step1273 p h) (sat_cons (step508 p h) (sat_cons (step1282 p h) (sat_cons (step1276 p h) (sat_nil p)))))))))
def c1610 : List Lit := [(1680, true), (1663, false), (80, false)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c719, c1366, c1387, c1384, c1367, c1377, c1361, c1373, c650, c643] c1610 (by decide) p (sat_cons (step719 p h) (sat_cons (step1366 p h) (sat_cons (step1387 p h) (sat_cons (step1384 p h) (sat_cons (step1367 p h) (sat_cons (step1377 p h) (sat_cons (step1361 p h) (sat_cons (step1373 p h) (sat_cons (step650 p h) (sat_cons (step643 p h) (sat_nil p)))))))))))
def c1611 : List Lit := [(1510, true), (41, false), (111, false)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c1598, c350, c345, c1065, c1062, c1070] c1611 (by decide) p (sat_cons (step1598 p h) (sat_cons (step350 p h) (sat_cons (step345 p h) (sat_cons (step1065 p h) (sat_cons (step1062 p h) (sat_cons (step1070 p h) (sat_nil p)))))))
def c1612 : List Lit := [(115, true), (1676, true), (119, false), (109, false)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c1379, c1373, c1378, c1374, c1375, c664] c1612 (by decide) p (sat_cons (step1379 p h) (sat_cons (step1373 p h) (sat_cons (step1378 p h) (sat_cons (step1374 p h) (sat_cons (step1375 p h) (sat_cons (step664 p h) (sat_nil p)))))))
def c1613 : List Lit := [(1488, true), (1474, false), (25, false), (98, false)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c1546, c997, c1023, c1029, c1002, c1586, c974, c930, c972, c124] c1613 (by decide) p (sat_cons (step1546 p h) (sat_cons (step997 p h) (sat_cons (step1023 p h) (sat_cons (step1029 p h) (sat_cons (step1002 p h) (sat_cons (step1586 p h) (sat_cons (step974 p h) (sat_cons (step930 p h) (sat_cons (step972 p h) (sat_cons (step124 p h) (sat_nil p)))))))))))
def c1614 : List Lit := [(1455, true), (1464, true), (18, false), (25, false), (98, false)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c667, c1586, c1603, c930, c931, c939, c124, c55, c973, c10, c1] c1614 (by decide) p (sat_cons (step667 p h) (sat_cons (step1586 p h) (sat_cons (step1603 p h) (sat_cons (step930 p h) (sat_cons (step931 p h) (sat_cons (step939 p h) (sat_cons (step124 p h) (sat_cons (step55 p h) (sat_cons (step973 p h) (sat_cons (step10 p h) (sat_cons (step1 p h) (sat_nil p))))))))))))
def c1615 : List Lit := [(1479, true), (1470, false), (25, false), (98, false)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c993, c998, c1002, c994, c974, c986, c972, c141] c1615 (by decide) p (sat_cons (step993 p h) (sat_cons (step998 p h) (sat_cons (step1002 p h) (sat_cons (step994 p h) (sat_cons (step974 p h) (sat_cons (step986 p h) (sat_cons (step972 p h) (sat_cons (step141 p h) (sat_nil p)))))))))
def c1616 : List Lit := [(1655, true)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c710, c1339, c1343, c1331, c1317, c1319, c1604, c1329, c1314, c1315, c1311, c1518, c527, c523] c1616 (by decide) p (sat_cons (step710 p h) (sat_cons (step1339 p h) (sat_cons (step1343 p h) (sat_cons (step1331 p h) (sat_cons (step1317 p h) (sat_cons (step1319 p h) (sat_cons (step1604 p h) (sat_cons (step1329 p h) (sat_cons (step1314 p h) (sat_cons (step1315 p h) (sat_cons (step1311 p h) (sat_cons (step1518 p h) (sat_cons (step527 p h) (sat_cons (step523 p h) (sat_nil p)))))))))))))))
def c1617 : List Lit := [(1687, true)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1396] c1617 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1396 p h) (sat_nil p)))
def c1618 : List Lit := [(1706, true)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1554, c1431] c1618 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1554 p h) (sat_cons (step1431 p h) (sat_nil p))))
def c1619 : List Lit := [(1575, false)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c1618, c1475, c1474] c1619 (by decide) p (sat_cons (step1618 p h) (sat_cons (step1475 p h) (sat_cons (step1474 p h) (sat_nil p))))
def c1620 : List Lit := [(1456, true), (22, false), (18, false), (6, true), (1441, false)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c667, c965, c1588, c1565, c937, c936, c932, c962, c946, c938, c939, c56, c1, c10] c1620 (by decide) p (sat_cons (step667 p h) (sat_cons (step965 p h) (sat_cons (step1588 p h) (sat_cons (step1565 p h) (sat_cons (step937 p h) (sat_cons (step936 p h) (sat_cons (step932 p h) (sat_cons (step962 p h) (sat_cons (step946 p h) (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step56 p h) (sat_cons (step1 p h) (sat_cons (step10 p h) (sat_nil p)))))))))))))))
def c1621 : List Lit := [(44, false), (50, false), (47, false)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c686, c369, c365] c1621 (by decide) p (sat_cons (step686 p h) (sat_cons (step369 p h) (sat_cons (step365 p h) (sat_nil p))))
def c1622 : List Lit := [(44, true), (1515, true), (1505, false), (22, false), (41, true)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c681, c1077, c1071, c1064, c1066, c1070, c1081, c1056, c1058, c1054, c249, c228, c214] c1622 (by decide) p (sat_cons (step681 p h) (sat_cons (step1077 p h) (sat_cons (step1071 p h) (sat_cons (step1064 p h) (sat_cons (step1066 p h) (sat_cons (step1070 p h) (sat_cons (step1081 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1054 p h) (sat_cons (step249 p h) (sat_cons (step228 p h) (sat_cons (step214 p h) (sat_nil p))))))))))))))
def c1623 : List Lit := [(1514, true), (1505, false), (22, false), (41, true)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c681, c1069, c1076, c1080, c1070, c1056, c1058, c1065, c1054, c249, c228, c214] c1623 (by decide) p (sat_cons (step681 p h) (sat_cons (step1069 p h) (sat_cons (step1076 p h) (sat_cons (step1080 p h) (sat_cons (step1070 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1065 p h) (sat_cons (step1054 p h) (sat_cons (step249 p h) (sat_cons (step228 p h) (sat_cons (step214 p h) (sat_nil p)))))))))))))
def c1624 : List Lit := [(1657, true), (106, true), (1647, false)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c711, c1328, c1334, c1341, c1345, c1335, c1317, c1319, c1330, c1314, c1315, c1311, c1604, c1518, c523, c530] c1624 (by decide) p (sat_cons (step711 p h) (sat_cons (step1328 p h) (sat_cons (step1334 p h) (sat_cons (step1341 p h) (sat_cons (step1345 p h) (sat_cons (step1335 p h) (sat_cons (step1317 p h) (sat_cons (step1319 p h) (sat_cons (step1330 p h) (sat_cons (step1314 p h) (sat_cons (step1315 p h) (sat_cons (step1311 p h) (sat_cons (step1604 p h) (sat_cons (step1518 p h) (sat_cons (step523 p h) (sat_cons (step530 p h) (sat_nil p)))))))))))))))))
def c1625 : List Lit := [(115, false), (1505, false), (1550, true), (22, false), (41, true), (16, false)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c720, c687, c1623, c1147, c654, c655, c1512, c409, c407, c404, c1094, c1113, c1097, c1115, c1103, c1135, c1133, c1132, c1106, c1118, c1153, c1096, c1109, c1622, c373, c370] c1625 (by decide) p (sat_cons (step720 p h) (sat_cons (step687 p h) (sat_cons (step1623 p h) (sat_cons (step1147 p h) (sat_cons (step654 p h) (sat_cons (step655 p h) (sat_cons (step1512 p h) (sat_cons (step409 p h) (sat_cons (step407 p h) (sat_cons (step404 p h) (sat_cons (step1094 p h) (sat_cons (step1113 p h) (sat_cons (step1097 p h) (sat_cons (step1115 p h) (sat_cons (step1103 p h) (sat_cons (step1135 p h) (sat_cons (step1133 p h) (sat_cons (step1132 p h) (sat_cons (step1106 p h) (sat_cons (step1118 p h) (sat_cons (step1153 p h) (sat_cons (step1096 p h) (sat_cons (step1109 p h) (sat_cons (step1622 p h) (sat_cons (step373 p h) (sat_cons (step370 p h) (sat_nil p)))))))))))))))))))))))))))
def c1626 : List Lit := [(1690, true), (1675, false), (109, true), (1647, false)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1359, c1366, c1384, c1333, c1399, c1405, c1388, c1340, c1344, c1369, c1334, c1317, c1604, c1360, c1329, c1315, c578] c1626 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1359 p h) (sat_cons (step1366 p h) (sat_cons (step1384 p h) (sat_cons (step1333 p h) (sat_cons (step1399 p h) (sat_cons (step1405 p h) (sat_cons (step1388 p h) (sat_cons (step1340 p h) (sat_cons (step1344 p h) (sat_cons (step1369 p h) (sat_cons (step1334 p h) (sat_cons (step1317 p h) (sat_cons (step1604 p h) (sat_cons (step1360 p h) (sat_cons (step1329 p h) (sat_cons (step1315 p h) (sat_cons (step578 p h) (sat_nil p)))))))))))))))))))
def c1627 : List Lit := [(115, false), (1539, true), (16, false)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c720, c654, c655, c1512, c409, c407, c404, c1094, c1113, c1097, c1115, c1103, c1132] c1627 (by decide) p (sat_cons (step720 p h) (sat_cons (step654 p h) (sat_cons (step655 p h) (sat_cons (step1512 p h) (sat_cons (step409 p h) (sat_cons (step407 p h) (sat_cons (step404 p h) (sat_cons (step1094 p h) (sat_cons (step1113 p h) (sat_cons (step1097 p h) (sat_cons (step1115 p h) (sat_cons (step1103 p h) (sat_cons (step1132 p h) (sat_nil p))))))))))))))
def c1628 : List Lit := [(36, false), (1515, true), (106, false), (38, true), (16, false)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c266, c261, c1063, c1053, c1072, c1056, c1081] c1628 (by decide) p (sat_cons (step266 p h) (sat_cons (step261 p h) (sat_cons (step1063 p h) (sat_cons (step1053 p h) (sat_cons (step1072 p h) (sat_cons (step1056 p h) (sat_cons (step1081 p h) (sat_nil p))))))))
def c1629 : List Lit := [(34, false), (42, false), (32, false), (31, true), (41, true)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c681, c228, c249] c1629 (by decide) p (sat_cons (step681 p h) (sat_cons (step228 p h) (sat_cons (step249 p h) (sat_nil p))))
def c1630 : List Lit := [(26, false), (64, false), (63, false)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c697, c443, c442] c1630 (by decide) p (sat_cons (step697 p h) (sat_cons (step443 p h) (sat_cons (step442 p h) (sat_nil p))))
def c1631 : List Lit := [(26, false), (37, false), (1594, true)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c696, c1589, c1583, c148, c1239, c439, c461] c1631 (by decide) p (sat_cons (step696 p h) (sat_cons (step1589 p h) (sat_cons (step1583 p h) (sat_cons (step148 p h) (sat_cons (step1239 p h) (sat_cons (step439 p h) (sat_cons (step461 p h) (sat_nil p))))))))
def c1632 : List Lit := [(71, false), (37, false), (36, true), (55, true), (63, false)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c699, c459, c461] c1632 (by decide) p (sat_cons (step699 p h) (sat_cons (step459 p h) (sat_cons (step461 p h) (sat_nil p))))
def c1633 : List Lit := [(71, true), (1594, true), (41, true)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c700, c1250, c1242, c1239, c1240, c1241, c1244, c467, c1253, c1236, c1230, c446, c1228] c1633 (by decide) p (sat_cons (step700 p h) (sat_cons (step1250 p h) (sat_cons (step1242 p h) (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step1241 p h) (sat_cons (step1244 p h) (sat_cons (step467 p h) (sat_cons (step1253 p h) (sat_cons (step1236 p h) (sat_cons (step1230 p h) (sat_cons (step446 p h) (sat_cons (step1228 p h) (sat_nil p))))))))))))))
def c1634 : List Lit := [(1515, true), (1505, false), (37, true), (22, false), (41, true)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c1069, c1053, c1056, c1085, c1081, c1057, c1059, c1070, c1055, c1065, c214, c1629] c1634 (by decide) p (sat_cons (step1069 p h) (sat_cons (step1053 p h) (sat_cons (step1056 p h) (sat_cons (step1085 p h) (sat_cons (step1081 p h) (sat_cons (step1057 p h) (sat_cons (step1059 p h) (sat_cons (step1070 p h) (sat_cons (step1055 p h) (sat_cons (step1065 p h) (sat_cons (step214 p h) (sat_cons (step1629 p h) (sat_nil p)))))))))))))
def c1635 : List Lit := [(70, true), (1594, true)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c697, c1250, c1246, c1235, c1237, c1243, c1244, c441, c1253, c1238, c1230, c446, c1228] c1635 (by decide) p (sat_cons (step697 p h) (sat_cons (step1250 p h) (sat_cons (step1246 p h) (sat_cons (step1235 p h) (sat_cons (step1237 p h) (sat_cons (step1243 p h) (sat_cons (step1244 p h) (sat_cons (step441 p h) (sat_cons (step1253 p h) (sat_cons (step1238 p h) (sat_cons (step1230 p h) (sat_cons (step446 p h) (sat_cons (step1228 p h) (sat_nil p))))))))))))))
def c1636 : List Lit := [(32, false), (34, false), (70, false), (22, false), (41, true)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c681, c214, c250, c228] c1636 (by decide) p (sat_cons (step681 p h) (sat_cons (step214 p h) (sat_cons (step250 p h) (sat_cons (step228 p h) (sat_nil p)))))
def c1637 : List Lit := [(1691, true), (1648, false), (1675, false), (109, true)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c1336, c1340, c1359, c1366, c1384, c1411, c1406, c1341, c1345, c1388, c1337, c1317, c1604, c1369, c1329, c1315, c1360, c578] c1637 (by decide) p (sat_cons (step1336 p h) (sat_cons (step1340 p h) (sat_cons (step1359 p h) (sat_cons (step1366 p h) (sat_cons (step1384 p h) (sat_cons (step1411 p h) (sat_cons (step1406 p h) (sat_cons (step1341 p h) (sat_cons (step1345 p h) (sat_cons (step1388 p h) (sat_cons (step1337 p h) (sat_cons (step1317 p h) (sat_cons (step1604 p h) (sat_cons (step1369 p h) (sat_cons (step1329 p h) (sat_cons (step1315 p h) (sat_cons (step1360 p h) (sat_cons (step578 p h) (sat_nil p)))))))))))))))))))
def c1638 : List Lit := [(1503, true), (37, true), (70, false), (22, false), (41, true)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c1053, c1057, c1059, c1055, c1636] c1638 (by decide) p (sat_cons (step1053 p h) (sat_cons (step1057 p h) (sat_cons (step1059 p h) (sat_cons (step1055 p h) (sat_cons (step1636 p h) (sat_nil p))))))
def c1639 : List Lit := [(36, false), (1506, true), (71, false), (16, false)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c263, c265, c1063] c1639 (by decide) p (sat_cons (step263 p h) (sat_cons (step265 p h) (sat_cons (step1063 p h) (sat_nil p))))
def c1640 : List Lit := [(1514, true), (36, true), (22, false), (41, true)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c683, c1084, c1623, c1062, c300, c215, c216, c1059, c1054] c1640 (by decide) p (sat_cons (step683 p h) (sat_cons (step1084 p h) (sat_cons (step1623 p h) (sat_cons (step1062 p h) (sat_cons (step300 p h) (sat_cons (step215 p h) (sat_cons (step216 p h) (sat_cons (step1059 p h) (sat_cons (step1054 p h) (sat_nil p))))))))))
def c1641 : List Lit := [(1709, true), (1663, false), (1594, false)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1616, c1550, c1366, c1383, c1397, c1300, c1441, c1449, c1398, c1301, c1610, c1290, c1592] c1641 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1616 p h) (sat_cons (step1550 p h) (sat_cons (step1366 p h) (sat_cons (step1383 p h) (sat_cons (step1397 p h) (sat_cons (step1300 p h) (sat_cons (step1441 p h) (sat_cons (step1449 p h) (sat_cons (step1398 p h) (sat_cons (step1301 p h) (sat_cons (step1610 p h) (sat_cons (step1290 p h) (sat_cons (step1592 p h) (sat_nil p)))))))))))))))
def c1642 : List Lit := [(88, true), (1618, true)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1550, c706, c701, c1290, c1271, c1288, c1280, c1276, c1278, c1282, c507, c1273, c500, c1260, c1262, c1269, c477, c1264, c481] c1642 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step706 p h) (sat_cons (step701 p h) (sat_cons (step1290 p h) (sat_cons (step1271 p h) (sat_cons (step1288 p h) (sat_cons (step1280 p h) (sat_cons (step1276 p h) (sat_cons (step1278 p h) (sat_cons (step1282 p h) (sat_cons (step507 p h) (sat_cons (step1273 p h) (sat_cons (step500 p h) (sat_cons (step1260 p h) (sat_cons (step1262 p h) (sat_cons (step1269 p h) (sat_cons (step477 p h) (sat_cons (step1264 p h) (sat_cons (step481 p h) (sat_nil p)))))))))))))))))))))
def c1643 : List Lit := [(1618, true), (1663, false), (1691, true), (108, false), (38, false)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1290, c1592, c1610, c1411, c1642, c601, c602, c1325, c1624] c1643 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1290 p h) (sat_cons (step1592 p h) (sat_cons (step1610 p h) (sat_cons (step1411 p h) (sat_cons (step1642 p h) (sat_cons (step601 p h) (sat_cons (step602 p h) (sat_cons (step1325 p h) (sat_cons (step1624 p h) (sat_nil p)))))))))))
def c1644 : List Lit := [(1667, true), (108, false), (38, false)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c1364, c1366, c1362, c1359, c610] c1644 (by decide) p (sat_cons (step1364 p h) (sat_cons (step1366 p h) (sat_cons (step1362 p h) (sat_cons (step1359 p h) (sat_cons (step610 p h) (sat_nil p))))))
def c1645 : List Lit := [(109, false), (1657, true), (108, false), (38, false)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c608, c606, c1624, c1325] c1645 (by decide) p (sat_cons (step608 p h) (sat_cons (step606 p h) (sat_cons (step1624 p h) (sat_cons (step1325 p h) (sat_nil p)))))
def c1646 : List Lit := [(1538, true), (1522, false), (71, false), (55, false)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1100, c1131, c1127, c1103, c1115, c1094, c416, c415, c1113] c1646 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1100 p h) (sat_cons (step1131 p h) (sat_cons (step1127 p h) (sat_cons (step1103 p h) (sat_cons (step1115 p h) (sat_cons (step1094 p h) (sat_cons (step416 p h) (sat_cons (step415 p h) (sat_cons (step1113 p h) (sat_nil p)))))))))))
def c1647 : List Lit := [(99, false), (1690, true), (108, false), (38, false)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1644, c1383, c1410, c1645, c1359, c1399, c1390, c605, c607, c1328, c1362, c1331, c1370, c1367, c1360, c1387, c1405, c1340, c1344, c1332, c1317, c1604, c1330, c1315, c578] c1647 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1644 p h) (sat_cons (step1383 p h) (sat_cons (step1410 p h) (sat_cons (step1645 p h) (sat_cons (step1359 p h) (sat_cons (step1399 p h) (sat_cons (step1390 p h) (sat_cons (step605 p h) (sat_cons (step607 p h) (sat_cons (step1328 p h) (sat_cons (step1362 p h) (sat_cons (step1331 p h) (sat_cons (step1370 p h) (sat_cons (step1367 p h) (sat_cons (step1360 p h) (sat_cons (step1387 p h) (sat_cons (step1405 p h) (sat_cons (step1340 p h) (sat_cons (step1344 p h) (sat_cons (step1332 p h) (sat_cons (step1317 p h) (sat_cons (step1604 p h) (sat_cons (step1330 p h) (sat_cons (step1315 p h) (sat_cons (step578 p h) (sat_nil p)))))))))))))))))))))))))))
def c1648 : List Lit := [(1690, true), (108, false), (38, false)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1644, c1383, c1399, c1410, c1390, c1645, c1359, c1647, c1325, c1333, c1624, c609, c1362, c1370, c1367, c1360, c1387, c1405, c1340, c1344, c1334, c1317, c1604, c1329, c1315, c578] c1648 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1644 p h) (sat_cons (step1383 p h) (sat_cons (step1399 p h) (sat_cons (step1410 p h) (sat_cons (step1390 p h) (sat_cons (step1645 p h) (sat_cons (step1359 p h) (sat_cons (step1647 p h) (sat_cons (step1325 p h) (sat_cons (step1333 p h) (sat_cons (step1624 p h) (sat_cons (step609 p h) (sat_cons (step1362 p h) (sat_cons (step1370 p h) (sat_cons (step1367 p h) (sat_cons (step1360 p h) (sat_cons (step1387 p h) (sat_cons (step1405 p h) (sat_cons (step1340 p h) (sat_cons (step1344 p h) (sat_cons (step1334 p h) (sat_cons (step1317 p h) (sat_cons (step1604 p h) (sat_cons (step1329 p h) (sat_cons (step1315 p h) (sat_cons (step578 p h) (sat_nil p))))))))))))))))))))))))))))
def c1649 : List Lit := [(1710, true), (108, false), (38, false)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1547, c1648, c1435, c1442, c1297, c1642, c1643, c603, c1359] c1649 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1547 p h) (sat_cons (step1648 p h) (sat_cons (step1435 p h) (sat_cons (step1442 p h) (sat_cons (step1297 p h) (sat_cons (step1642 p h) (sat_cons (step1643 p h) (sat_cons (step603 p h) (sat_cons (step1359 p h) (sat_nil p)))))))))))
def c1650 : List Lit := [(1474, true), (63, false), (39, false), (30, true)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c679, c985, c989, c991, c987, c982, c983, c146, c184, c181, c183, c1501] c1650 (by decide) p (sat_cons (step679 p h) (sat_cons (step985 p h) (sat_cons (step989 p h) (sat_cons (step991 p h) (sat_cons (step987 p h) (sat_cons (step982 p h) (sat_cons (step983 p h) (sat_cons (step146 p h) (sat_cons (step184 p h) (sat_cons (step181 p h) (sat_cons (step183 p h) (sat_cons (step1501 p h) (sat_nil p)))))))))))))
def c1651 : List Lit := [(73, false), (120, false), (70, false), (41, true)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c700, c466, c471] c1651 (by decide) p (sat_cons (step700 p h) (sat_cons (step466 p h) (sat_cons (step471 p h) (sat_nil p))))
def c1652 : List Lit := [(21, false), (25, true), (22, false)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c675, c100, c1489, c99] c1652 (by decide) p (sat_cons (step675 p h) (sat_cons (step100 p h) (sat_cons (step1489 p h) (sat_cons (step99 p h) (sat_nil p)))))
end B112E040
