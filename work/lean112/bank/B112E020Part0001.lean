import B112E020Part0000
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1676 : List Lit := [(1580, true), (44, false), (9, false)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c1152, c1153, c218] c1676 (by decide) p (sat_cons (step1152 p h) (sat_cons (step1153 p h) (sat_cons (step218 p h) (sat_nil p))))
def c1677 : List Lit := [(1683, true), (82, false), (76, false)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c1338, c1341, c1333, c1318, c1326, c1316, c464] c1677 (by decide) p (sat_cons (step1338 p h) (sat_cons (step1341 p h) (sat_cons (step1333 p h) (sat_cons (step1318 p h) (sat_cons (step1326 p h) (sat_cons (step1316 p h) (sat_cons (step464 p h) (sat_nil p))))))))
def c1678 : List Lit := [(104, false), (1731, true), (103, false)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c816, c1424, c1423, c541, c523, c539] c1678 (by decide) p (sat_cons (step816 p h) (sat_cons (step1424 p h) (sat_cons (step1423 p h) (sat_cons (step541 p h) (sat_cons (step523 p h) (sat_cons (step539 p h) (sat_nil p)))))))
def c1679 : List Lit := [(104, true), (1758, true), (1711, false)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c1673, c1437, c1445, c1397, c1668, c1399, c1486, c1412] c1679 (by decide) p (sat_cons (step1673 p h) (sat_cons (step1437 p h) (sat_cons (step1445 p h) (sat_cons (step1397 p h) (sat_cons (step1668 p h) (sat_cons (step1399 p h) (sat_cons (step1486 p h) (sat_cons (step1412 p h) (sat_nil p)))))))))
def c1680 : List Lit := [(1758, true), (103, false), (1711, false)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1673, c1480, c1437, c1445, c1461, c1679, c1665, c1678, c1431, c1432, c1457, c1426, c1448, c657, c1439] c1680 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1673 p h) (sat_cons (step1480 p h) (sat_cons (step1437 p h) (sat_cons (step1445 p h) (sat_cons (step1461 p h) (sat_cons (step1679 p h) (sat_cons (step1665 p h) (sat_cons (step1678 p h) (sat_cons (step1431 p h) (sat_cons (step1432 p h) (sat_cons (step1457 p h) (sat_cons (step1426 p h) (sat_cons (step1448 p h) (sat_cons (step657 p h) (sat_cons (step1439 p h) (sat_nil p)))))))))))))))))
def c1681 : List Lit := [(115, true), (104, false), (103, false)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c816, c537, c538, c1597] c1681 (by decide) p (sat_cons (step816 p h) (sat_cons (step537 p h) (sat_cons (step538 p h) (sat_cons (step1597 p h) (sat_nil p)))))
def c1682 : List Lit := [(113, false), (116, false), (1731, false), (1759, true), (1739, false), (115, false)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c817, c1445, c1431, c1456, c1493, c657, c654, c1397, c1380, c1399, c1388, c1412, c1413, c1487, c1400, c1402, c1457, c1461, c1398, c1393, c1446, c1432, c544, c1440, c1427, c552, c611] c1682 (by decide) p (sat_cons (step817 p h) (sat_cons (step1445 p h) (sat_cons (step1431 p h) (sat_cons (step1456 p h) (sat_cons (step1493 p h) (sat_cons (step657 p h) (sat_cons (step654 p h) (sat_cons (step1397 p h) (sat_cons (step1380 p h) (sat_cons (step1399 p h) (sat_cons (step1388 p h) (sat_cons (step1412 p h) (sat_cons (step1413 p h) (sat_cons (step1487 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1457 p h) (sat_cons (step1461 p h) (sat_cons (step1398 p h) (sat_cons (step1393 p h) (sat_cons (step1446 p h) (sat_cons (step1432 p h) (sat_cons (step544 p h) (sat_cons (step1440 p h) (sat_cons (step1427 p h) (sat_cons (step552 p h) (sat_cons (step611 p h) (sat_nil p))))))))))))))))))))))))))))
def c1683 : List Lit := [(1711, false), (113, true), (1731, false), (1759, true), (1739, false)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c817, c1445, c1426, c1432, c1461, c1487, c1411, c1412, c1481, c1399, c1401, c1466, c1462, c1396, c1397, c1393, c1433, c1446, c540, c1428, c1440, c552, c611] c1683 (by decide) p (sat_cons (step817 p h) (sat_cons (step1445 p h) (sat_cons (step1426 p h) (sat_cons (step1432 p h) (sat_cons (step1461 p h) (sat_cons (step1487 p h) (sat_cons (step1411 p h) (sat_cons (step1412 p h) (sat_cons (step1481 p h) (sat_cons (step1399 p h) (sat_cons (step1401 p h) (sat_cons (step1466 p h) (sat_cons (step1462 p h) (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step1393 p h) (sat_cons (step1433 p h) (sat_cons (step1446 p h) (sat_cons (step540 p h) (sat_cons (step1428 p h) (sat_cons (step1440 p h) (sat_cons (step552 p h) (sat_cons (step611 p h) (sat_nil p))))))))))))))))))))))))
def c1684 : List Lit := [(116, false), (99, false), (1731, false), (1759, true), (1739, false), (115, false)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c812, c1682, c1683, c1388, c1380, c1381, c1595, c513, c500] c1684 (by decide) p (sat_cons (step812 p h) (sat_cons (step1682 p h) (sat_cons (step1683 p h) (sat_cons (step1388 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step1595 p h) (sat_cons (step513 p h) (sat_cons (step500 p h) (sat_nil p))))))))))
def c1685 : List Lit := [(113, true), (1740, false), (1731, false), (1759, true), (1739, false)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c815, c1476, c1448, c1467, c1433, c1426, c1683, c1428, c1432, c1386, c1463, c1462, c1383, c1449, c1481, c1440, c1441, c1407, c745, c1401, c1394, c521, c519] c1685 (by decide) p (sat_cons (step815 p h) (sat_cons (step1476 p h) (sat_cons (step1448 p h) (sat_cons (step1467 p h) (sat_cons (step1433 p h) (sat_cons (step1426 p h) (sat_cons (step1683 p h) (sat_cons (step1428 p h) (sat_cons (step1432 p h) (sat_cons (step1386 p h) (sat_cons (step1463 p h) (sat_cons (step1462 p h) (sat_cons (step1383 p h) (sat_cons (step1449 p h) (sat_cons (step1481 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1407 p h) (sat_cons (step745 p h) (sat_cons (step1401 p h) (sat_cons (step1394 p h) (sat_cons (step521 p h) (sat_cons (step519 p h) (sat_nil p))))))))))))))))))))))))
def c1686 : List Lit := [(1711, true), (113, false), (1740, false), (1731, false), (1759, true), (115, false)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c815, c1431, c1448, c1457, c1487, c1408, c1386, c1388, c1383, c1380, c651, c1397, c1399, c1402, c1407, c1394, c1481, c1458, c1462, c1449, c1432, c1440, c1427, c743, c521, c519] c1686 (by decide) p (sat_cons (step815 p h) (sat_cons (step1431 p h) (sat_cons (step1448 p h) (sat_cons (step1457 p h) (sat_cons (step1487 p h) (sat_cons (step1408 p h) (sat_cons (step1386 p h) (sat_cons (step1388 p h) (sat_cons (step1383 p h) (sat_cons (step1380 p h) (sat_cons (step651 p h) (sat_cons (step1397 p h) (sat_cons (step1399 p h) (sat_cons (step1402 p h) (sat_cons (step1407 p h) (sat_cons (step1394 p h) (sat_cons (step1481 p h) (sat_cons (step1458 p h) (sat_cons (step1462 p h) (sat_cons (step1449 p h) (sat_cons (step1432 p h) (sat_cons (step1440 p h) (sat_cons (step1427 p h) (sat_cons (step743 p h) (sat_cons (step521 p h) (sat_cons (step519 p h) (sat_nil p)))))))))))))))))))))))))))
def c1687 : List Lit := [(1740, false), (1731, false), (1759, true), (1739, false), (115, false)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c816, c1431, c1448, c1457, c1487, c1685, c1686, c1412, c1399, c1401, c1396, c1397, c1393, c540, c1599, c539] c1687 (by decide) p (sat_cons (step816 p h) (sat_cons (step1431 p h) (sat_cons (step1448 p h) (sat_cons (step1457 p h) (sat_cons (step1487 p h) (sat_cons (step1685 p h) (sat_cons (step1686 p h) (sat_cons (step1412 p h) (sat_cons (step1399 p h) (sat_cons (step1401 p h) (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step1393 p h) (sat_cons (step540 p h) (sat_cons (step1599 p h) (sat_cons (step539 p h) (sat_nil p)))))))))))))))))
def c1688 : List Lit := [(116, false), (1731, false), (115, false), (1759, true), (1739, false)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c1682, c1684, c1683, c1383, c1386] c1688 (by decide) p (sat_cons (step1682 p h) (sat_cons (step1684 p h) (sat_cons (step1683 p h) (sat_cons (step1383 p h) (sat_cons (step1386 p h) (sat_nil p))))))
def c1689 : List Lit := [(1731, false), (1759, true), (118, true), (115, false)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c1437, c1687, c1439, c1688] c1689 (by decide) p (sat_cons (step1437 p h) (sat_cons (step1687 p h) (sat_cons (step1439 p h) (sat_cons (step1688 p h) (sat_nil p)))))
def c1690 : List Lit := [(1711, true), (115, false), (116, false), (109, false)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c814, c1386, c1388, c1383, c1380, c1381, c713, c1595, c513, c517] c1690 (by decide) p (sat_cons (step814 p h) (sat_cons (step1386 p h) (sat_cons (step1388 p h) (sat_cons (step1383 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step713 p h) (sat_cons (step1595 p h) (sat_cons (step513 p h) (sat_cons (step517 p h) (sat_nil p)))))))))))
def c1691 : List Lit := [(1707, true), (99, false), (115, false), (116, false)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c812, c1380, c1381, c1595, c513, c500] c1691 (by decide) p (sat_cons (step812 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step1595 p h) (sat_cons (step513 p h) (sat_cons (step500 p h) (sat_nil p)))))))
def c1692 : List Lit := [(103, false), (1718, true), (124, false), (1731, true), (109, false), (116, false)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c817, c1678, c545, c1398, c552, c610] c1692 (by decide) p (sat_cons (step817 p h) (sat_cons (step1678 p h) (sat_cons (step545 p h) (sat_cons (step1398 p h) (sat_cons (step552 p h) (sat_cons (step610 p h) (sat_nil p)))))))
def c1693 : List Lit := [(124, false), (1721, true), (1731, true), (101, false), (109, false), (99, false), (116, false)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c817, c521, c1394, c1403, c1692, c1395, c1405, c1396, c1397, c547, c610, c552] c1693 (by decide) p (sat_cons (step817 p h) (sat_cons (step521 p h) (sat_cons (step1394 p h) (sat_cons (step1403 p h) (sat_cons (step1692 p h) (sat_cons (step1395 p h) (sat_cons (step1405 p h) (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step547 p h) (sat_cons (step610 p h) (sat_cons (step552 p h) (sat_nil p)))))))))))))
def c1694 : List Lit := [(1536, true), (1527, false), (1518, false)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c1064, c1055, c1080, c1076, c1056, c1067, c1049, c1649] c1694 (by decide) p (sat_cons (step1064 p h) (sat_cons (step1055 p h) (sat_cons (step1080 p h) (sat_cons (step1076 p h) (sat_cons (step1056 p h) (sat_cons (step1067 p h) (sat_cons (step1049 p h) (sat_cons (step1649 p h) (sat_nil p)))))))))
def c1695 : List Lit := [(87, false), (93, false), (89, false)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c1630, c485, c497, c484, c948, c944, c949, c946, c953] c1695 (by decide) p (sat_cons (step1630 p h) (sat_cons (step485 p h) (sat_cons (step497 p h) (sat_cons (step484 p h) (sat_cons (step948 p h) (sat_cons (step944 p h) (sat_cons (step949 p h) (sat_cons (step946 p h) (sat_cons (step953 p h) (sat_nil p))))))))))
def c1696 : List Lit := [(50, false), (46, false), (49, true), (174, true), (11, false)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c264, c250] c1696 (by decide) p (sat_cons (step264 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1697 : List Lit := [(1711, false), (1724, true), (1758, true)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1680, c1401, c1393] c1697 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1680 p h) (sat_cons (step1401 p h) (sat_cons (step1393 p h) (sat_nil p)))))
def c1698 : List Lit := [(1749, true), (1740, false)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c819, c1448, c1453, c1457, c1449, c1429, c1431, c1440, c1441, c1427, c1423, c1424, c590, c601, c745, c607] c1698 (by decide) p (sat_cons (step819 p h) (sat_cons (step1448 p h) (sat_cons (step1453 p h) (sat_cons (step1457 p h) (sat_cons (step1449 p h) (sat_cons (step1429 p h) (sat_cons (step1431 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1427 p h) (sat_cons (step1423 p h) (sat_cons (step1424 p h) (sat_cons (step590 p h) (sat_cons (step601 p h) (sat_cons (step745 p h) (sat_cons (step607 p h) (sat_nil p)))))))))))))))))
def c1699 : List Lit := [(1758, true), (1711, true)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c812, c1388, c1386, c1383, c1380, c1381, c513, c498, c1691, c1475, c1673, c1439, c1448, c1462, c1698, c1480, c1407, c1399, c1401, c1397, c1393, c651, c1678, c1426, c1432] c1699 (by decide) p (sat_cons (step812 p h) (sat_cons (step1388 p h) (sat_cons (step1386 p h) (sat_cons (step1383 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step513 p h) (sat_cons (step498 p h) (sat_cons (step1691 p h) (sat_cons (step1475 p h) (sat_cons (step1673 p h) (sat_cons (step1439 p h) (sat_cons (step1448 p h) (sat_cons (step1462 p h) (sat_cons (step1698 p h) (sat_cons (step1480 p h) (sat_cons (step1407 p h) (sat_cons (step1399 p h) (sat_cons (step1401 p h) (sat_cons (step1397 p h) (sat_cons (step1393 p h) (sat_cons (step651 p h) (sat_cons (step1678 p h) (sat_cons (step1426 p h) (sat_cons (step1432 p h) (sat_nil p))))))))))))))))))))))))))
def c1700 : List Lit := [(124, false), (121, false), (100, false), (99, false)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c815, c521, c744, c519] c1700 (by decide) p (sat_cons (step815 p h) (sat_cons (step521 p h) (sat_cons (step744 p h) (sat_cons (step519 p h) (sat_nil p)))))
def c1701 : List Lit := [(1586, true), (48, true), (45, true), (46, false), (66, false)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c1155, c1152, c1162, c1164, c1157, c1154, c234] c1701 (by decide) p (sat_cons (step1155 p h) (sat_cons (step1152 p h) (sat_cons (step1162 p h) (sat_cons (step1164 p h) (sat_cons (step1157 p h) (sat_cons (step1154 p h) (sat_cons (step234 p h) (sat_nil p))))))))
def c1702 : List Lit := [(1594, true), (56, true), (58, false), (59, true), (49, true)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c795, c1169, c1167, c1176, c1178, c1171, c1168, c280, c270] c1702 (by decide) p (sat_cons (step795 p h) (sat_cons (step1169 p h) (sat_cons (step1167 p h) (sat_cons (step1176 p h) (sat_cons (step1178 p h) (sat_cons (step1171 p h) (sat_cons (step1168 p h) (sat_cons (step280 p h) (sat_cons (step270 p h) (sat_nil p))))))))))
def c1703 : List Lit := [(1502, true), (12, false), (1583, true)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c774, c48, c47, c1021, c1022, c34, c42, c1157] c1703 (by decide) p (sat_cons (step774 p h) (sat_cons (step48 p h) (sat_cons (step47 p h) (sat_cons (step1021 p h) (sat_cons (step1022 p h) (sat_cons (step34 p h) (sat_cons (step42 p h) (sat_cons (step1157 p h) (sat_nil p)))))))))
def c1704 : List Lit := [(1758, true)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c1673, c1699, c1437, c1411, c1679, c1697, c1445, c1480, c1665, c1486, c1698, c1456, c1439, c1429, c657, c1426] c1704 (by decide) p (sat_cons (step1673 p h) (sat_cons (step1699 p h) (sat_cons (step1437 p h) (sat_cons (step1411 p h) (sat_cons (step1679 p h) (sat_cons (step1697 p h) (sat_cons (step1445 p h) (sat_cons (step1480 p h) (sat_cons (step1665 p h) (sat_cons (step1486 p h) (sat_cons (step1698 p h) (sat_cons (step1456 p h) (sat_cons (step1439 p h) (sat_cons (step1429 p h) (sat_cons (step657 p h) (sat_cons (step1426 p h) (sat_nil p)))))))))))))))))
def c1705 : List Lit := [(1512, true), (6, true), (1506, false), (1504, true)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c774, c5, c1612, c1025, c1, c1017, c1019, c1024, c48, c1039, c1043, c1032, c1020, c1023, c1018, c27] c1705 (by decide) p (sat_cons (step774 p h) (sat_cons (step5 p h) (sat_cons (step1612 p h) (sat_cons (step1025 p h) (sat_cons (step1 p h) (sat_cons (step1017 p h) (sat_cons (step1019 p h) (sat_cons (step1024 p h) (sat_cons (step48 p h) (sat_cons (step1039 p h) (sat_cons (step1043 p h) (sat_cons (step1032 p h) (sat_cons (step1020 p h) (sat_cons (step1023 p h) (sat_cons (step1018 p h) (sat_cons (step27 p h) (sat_nil p)))))))))))))))))
def c1706 : List Lit := [(1580, true), (34, false), (48, false), (1504, true)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c774, c790, c789, c1024, c47, c1025, c1152, c1153, c1676, c231, c250, c207, c206, c1571] c1706 (by decide) p (sat_cons (step774 p h) (sat_cons (step790 p h) (sat_cons (step789 p h) (sat_cons (step1024 p h) (sat_cons (step47 p h) (sat_cons (step1025 p h) (sat_cons (step1152 p h) (sat_cons (step1153 p h) (sat_cons (step1676 p h) (sat_cons (step231 p h) (sat_cons (step250 p h) (sat_cons (step207 p h) (sat_cons (step206 p h) (sat_cons (step1571 p h) (sat_nil p)))))))))))))))
def c1707 : List Lit := [(1526, false), (1536, true)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c777, c1647, c1069, c1070, c1076, c1061, c1644, c1049, c1050, c69, c65] c1707 (by decide) p (sat_cons (step777 p h) (sat_cons (step1647 p h) (sat_cons (step1069 p h) (sat_cons (step1070 p h) (sat_cons (step1076 p h) (sat_cons (step1061 p h) (sat_cons (step1644 p h) (sat_cons (step1049 p h) (sat_cons (step1050 p h) (sat_cons (step69 p h) (sat_cons (step65 p h) (sat_nil p))))))))))))
def c1708 : List Lit := [(21, false), (58, false), (1536, true), (31, false), (5, false), (9, false)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c783, c778, c82, c178, c90, c156, c70, c1062, c1642, c1694] c1708 (by decide) p (sat_cons (step783 p h) (sat_cons (step778 p h) (sat_cons (step82 p h) (sat_cons (step178 p h) (sat_cons (step90 p h) (sat_cons (step156 p h) (sat_cons (step70 p h) (sat_cons (step1062 p h) (sat_cons (step1642 p h) (sat_cons (step1694 p h) (sat_nil p)))))))))))
def c1709 : List Lit := [(58, false), (1536, true), (31, false), (5, false), (9, false)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c783, c777, c1707, c1647, c1708, c1059, c1060, c1068, c83, c178, c156, c1062, c1067, c1076, c1644, c1049, c1050, c69, c65, c1063] c1709 (by decide) p (sat_cons (step783 p h) (sat_cons (step777 p h) (sat_cons (step1707 p h) (sat_cons (step1647 p h) (sat_cons (step1708 p h) (sat_cons (step1059 p h) (sat_cons (step1060 p h) (sat_cons (step1068 p h) (sat_cons (step83 p h) (sat_cons (step178 p h) (sat_cons (step156 p h) (sat_cons (step1062 p h) (sat_cons (step1067 p h) (sat_cons (step1076 p h) (sat_cons (step1644 p h) (sat_cons (step1049 p h) (sat_cons (step1050 p h) (sat_cons (step69 p h) (sat_cons (step65 p h) (sat_cons (step1063 p h) (sat_nil p)))))))))))))))))))))
def c1710 : List Lit := [(65, false), (60, false), (67, true), (68, false), (69, false)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c802, c424, c365, c422] c1710 (by decide) p (sat_cons (step802 p h) (sat_cons (step424 p h) (sat_cons (step365 p h) (sat_cons (step422 p h) (sat_nil p)))))
def c1711 : List Lit := [(1525, false), (1536, true), (24, true)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c777, c1647, c1062, c1068, c1067, c1063, c1076, c1644, c1049, c1050, c69, c65] c1711 (by decide) p (sat_cons (step777 p h) (sat_cons (step1647 p h) (sat_cons (step1062 p h) (sat_cons (step1068 p h) (sat_cons (step1067 p h) (sat_cons (step1063 p h) (sat_cons (step1076 p h) (sat_cons (step1644 p h) (sat_cons (step1049 p h) (sat_cons (step1050 p h) (sat_cons (step69 p h) (sat_cons (step65 p h) (sat_nil p)))))))))))))
def c1712 : List Lit := [(1536, true), (24, true), (5, false), (31, false)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c778, c1062, c1694, c1642, c1711, c1058, c1059, c80, c70, c90] c1712 (by decide) p (sat_cons (step778 p h) (sat_cons (step1062 p h) (sat_cons (step1694 p h) (sat_cons (step1642 p h) (sat_cons (step1711 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step80 p h) (sat_cons (step70 p h) (sat_cons (step90 p h) (sat_nil p)))))))))))
def c1713 : List Lit := [(1685, true), (77, true), (75, true), (80, true)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c805, c1315, c1313, c1321, c1348, c1346, c1324, c1322, c1333, c1314, c1317, c1326, c442, c464] c1713 (by decide) p (sat_cons (step805 p h) (sat_cons (step1315 p h) (sat_cons (step1313 p h) (sat_cons (step1321 p h) (sat_cons (step1348 p h) (sat_cons (step1346 p h) (sat_cons (step1324 p h) (sat_cons (step1322 p h) (sat_cons (step1333 p h) (sat_cons (step1314 p h) (sat_cons (step1317 p h) (sat_cons (step1326 p h) (sat_cons (step442 p h) (sat_cons (step464 p h) (sat_nil p)))))))))))))))
def c1714 : List Lit := [(76, false), (78, false), (83, false), (77, true)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c805, c442, c464] c1714 (by decide) p (sat_cons (step805 p h) (sat_cons (step442 p h) (sat_cons (step464 p h) (sat_nil p))))
def c1715 : List Lit := [(48, false), (46, false), (1586, true), (45, true), (66, false)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c236, c239, c1154, c1156, c1164] c1715 (by decide) p (sat_cons (step236 p h) (sat_cons (step239 p h) (sat_cons (step1154 p h) (sat_cons (step1156 p h) (sat_cons (step1164 p h) (sat_nil p))))))
def c1716 : List Lit := [(46, false), (1586, true), (66, false), (45, true)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c1715, c1701] c1716 (by decide) p (sat_cons (step1715 p h) (sat_cons (step1701 p h) (sat_nil p)))
def c1717 : List Lit := [(1599, true), (45, true), (46, false), (66, false)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c1716, c1197, c1194, c1174, c1167, c241, c240, c237, c1157, c1154, c1165] c1717 (by decide) p (sat_cons (step1716 p h) (sat_cons (step1197 p h) (sat_cons (step1194 p h) (sat_cons (step1174 p h) (sat_cons (step1167 p h) (sat_cons (step241 p h) (sat_cons (step240 p h) (sat_cons (step237 p h) (sat_cons (step1157 p h) (sat_cons (step1154 p h) (sat_cons (step1165 p h) (sat_nil p))))))))))))
def c1718 : List Lit := [(84, false), (1752, true), (1732, false), (124, true), (122, false), (1739, false), (69, false)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c727, c728, c1427, c1442, c1435, c1447, c1468] c1718 (by decide) p (sat_cons (step727 p h) (sat_cons (step728 p h) (sat_cons (step1427 p h) (sat_cons (step1442 p h) (sat_cons (step1435 p h) (sat_cons (step1447 p h) (sat_cons (step1468 p h) (sat_nil p))))))))
def c1719 : List Lit := [(78, false), (1537, true), (26, false), (1518, false), (61, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c143, c152, c149, c1050, c1063, c1056, c1065, c1081] c1719 (by decide) p (sat_cons (step143 p h) (sat_cons (step152 p h) (sat_cons (step149 p h) (sat_cons (step1050 p h) (sat_cons (step1063 p h) (sat_cons (step1056 p h) (sat_cons (step1065 p h) (sat_cons (step1081 p h) (sat_nil p)))))))))
def c1720 : List Lit := [(1511, true), (3, true)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c774, c1017, c1019, c1042, c1038, c1020, c1027, c1029, c1018, c1024, c1021, c48, c27] c1720 (by decide) p (sat_cons (step774 p h) (sat_cons (step1017 p h) (sat_cons (step1019 p h) (sat_cons (step1042 p h) (sat_cons (step1038 p h) (sat_cons (step1020 p h) (sat_cons (step1027 p h) (sat_cons (step1029 p h) (sat_cons (step1018 p h) (sat_cons (step1024 p h) (sat_cons (step1021 p h) (sat_cons (step48 p h) (sat_cons (step27 p h) (sat_nil p))))))))))))))
def c1721 : List Lit := [(1527, true), (26, false), (61, false)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c1061, c1062, c145] c1721 (by decide) p (sat_cons (step1061 p h) (sat_cons (step1062 p h) (sat_cons (step145 p h) (sat_nil p))))
def c1722 : List Lit := [(1561, true), (32, false), (22, false), (34, true)]
theorem step1722 (p : Nat → Bool) (h : Constraints p) : clause p c1722 = true :=
  Snake9.LocalRup.prove_clause [c1112, c1116, c1118, c1114, c1109, c179] c1722 (by decide) p (sat_cons (step1112 p h) (sat_cons (step1116 p h) (sat_cons (step1118 p h) (sat_cons (step1114 p h) (sat_cons (step1109 p h) (sat_cons (step179 p h) (sat_nil p)))))))
def c1723 : List Lit := [(1740, false), (1752, true), (1732, false), (124, true), (122, false), (69, false)]
theorem step1723 (p : Nat → Bool) (h : Constraints p) : clause p c1723 = true :=
  Snake9.LocalRup.prove_clause [c1434, c1464, c1440, c1450, c1449, c1442, c1468, c733, c1435, c1427] c1723 (by decide) p (sat_cons (step1434 p h) (sat_cons (step1464 p h) (sat_cons (step1440 p h) (sat_cons (step1450 p h) (sat_cons (step1449 p h) (sat_cons (step1442 p h) (sat_cons (step1468 p h) (sat_cons (step733 p h) (sat_cons (step1435 p h) (sat_cons (step1427 p h) (sat_nil p)))))))))))
def c1724 : List Lit := [(1584, true), (60, false), (66, false), (67, true)]
theorem step1724 (p : Nat → Bool) (h : Constraints p) : clause p c1724 = true :=
  Snake9.LocalRup.prove_clause [c791, c1158, c1160, c1155, c1156, c1153, c239, c246, c217] c1724 (by decide) p (sat_cons (step791 p h) (sat_cons (step1158 p h) (sat_cons (step1160 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1153 p h) (sat_cons (step239 p h) (sat_cons (step246 p h) (sat_cons (step217 p h) (sat_nil p))))))))))
def c1725 : List Lit := [(47, false), (46, true), (42, false), (60, false), (67, true)]
theorem step1725 (p : Nat → Bool) (h : Constraints p) : clause p c1725 = true :=
  Snake9.LocalRup.prove_clause [c791, c246, c217] c1725 (by decide) p (sat_cons (step791 p h) (sat_cons (step246 p h) (sat_cons (step217 p h) (sat_nil p))))
def c1726 : List Lit := [(1593, true), (63, true), (56, true), (58, false)]
theorem step1726 (p : Nat → Bool) (h : Constraints p) : clause p c1726 = true :=
  Snake9.LocalRup.prove_clause [c794, c1169, c1173, c1175, c1171, c1166, c274, c270] c1726 (by decide) p (sat_cons (step794 p h) (sat_cons (step1169 p h) (sat_cons (step1173 p h) (sat_cons (step1175 p h) (sat_cons (step1171 p h) (sat_cons (step1166 p h) (sat_cons (step274 p h) (sat_cons (step270 p h) (sat_nil p)))))))))
def c1727 : List Lit := [(1511, true), (1502, false)]
theorem step1727 (p : Nat → Bool) (h : Constraints p) : clause p c1727 = true :=
  Snake9.LocalRup.prove_clause [c1612, c5, c1035, c1720, c1030, c1, c1025] c1727 (by decide) p (sat_cons (step1612 p h) (sat_cons (step5 p h) (sat_cons (step1035 p h) (sat_cons (step1720 p h) (sat_cons (step1030 p h) (sat_cons (step1 p h) (sat_cons (step1025 p h) (sat_nil p))))))))
def c1728 : List Lit := [(1546, true), (8, true), (9, true), (1502, false)]
theorem step1728 (p : Nat → Bool) (h : Constraints p) : clause p c1728 = true :=
  Snake9.LocalRup.prove_clause [c1651, c774, c769, c770, c777, c1025, c1030, c1727, c1095, c1090, c1036, c1039, c1707, c1031, c1033, c1019, c1026, c1023, c1016, c1017, c47, c6, c17, c13, c1058, c1060, c11, c1066, c70, c1080, c1642, c1056, c1694, c1049, c1050, c1061, c69, c65] c1728 (by decide) p (sat_cons (step1651 p h) (sat_cons (step774 p h) (sat_cons (step769 p h) (sat_cons (step770 p h) (sat_cons (step777 p h) (sat_cons (step1025 p h) (sat_cons (step1030 p h) (sat_cons (step1727 p h) (sat_cons (step1095 p h) (sat_cons (step1090 p h) (sat_cons (step1036 p h) (sat_cons (step1039 p h) (sat_cons (step1707 p h) (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1019 p h) (sat_cons (step1026 p h) (sat_cons (step1023 p h) (sat_cons (step1016 p h) (sat_cons (step1017 p h) (sat_cons (step47 p h) (sat_cons (step6 p h) (sat_cons (step17 p h) (sat_cons (step13 p h) (sat_cons (step1058 p h) (sat_cons (step1060 p h) (sat_cons (step11 p h) (sat_cons (step1066 p h) (sat_cons (step70 p h) (sat_cons (step1080 p h) (sat_cons (step1642 p h) (sat_cons (step1056 p h) (sat_cons (step1694 p h) (sat_cons (step1049 p h) (sat_cons (step1050 p h) (sat_cons (step1061 p h) (sat_cons (step69 p h) (sat_cons (step65 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1729 : List Lit := [(1519, true), (27, false)]
theorem step1729 (p : Nat → Bool) (h : Constraints p) : clause p c1729 = true :=
  Snake9.LocalRup.prove_clause [c777, c1049, c1050, c69, c65] c1729 (by decide) p (sat_cons (step777 p h) (sat_cons (step1049 p h) (sat_cons (step1050 p h) (sat_cons (step69 p h) (sat_cons (step65 p h) (sat_nil p))))))
def c1730 : List Lit := [(16, false), (15, false), (27, false), (24, false)]
theorem step1730 (p : Nat → Bool) (h : Constraints p) : clause p c1730 = true :=
  Snake9.LocalRup.prove_clause [c776, c134, c60, c50] c1730 (by decide) p (sat_cons (step776 p h) (sat_cons (step134 p h) (sat_cons (step60 p h) (sat_cons (step50 p h) (sat_nil p)))))
def c1731 : List Lit := [(27, false), (1523, true), (24, false)]
theorem step1731 (p : Nat → Bool) (h : Constraints p) : clause p c1731 = true :=
  Snake9.LocalRup.prove_clause [c777, c1645, c1729, c1056, c1642, c1730, c1051, c69, c64] c1731 (by decide) p (sat_cons (step777 p h) (sat_cons (step1645 p h) (sat_cons (step1729 p h) (sat_cons (step1056 p h) (sat_cons (step1642 p h) (sat_cons (step1730 p h) (sat_cons (step1051 p h) (sat_cons (step69 p h) (sat_cons (step64 p h) (sat_nil p))))))))))
def c1732 : List Lit := [(1525, false), (1536, true)]
theorem step1732 (p : Nat → Bool) (h : Constraints p) : clause p c1732 = true :=
  Snake9.LocalRup.prove_clause [c777, c1066, c1711, c1080, c1731, c1061, c1694, c1067, c1642, c1076, c1644, c1049, c1050, c69, c62] c1732 (by decide) p (sat_cons (step777 p h) (sat_cons (step1066 p h) (sat_cons (step1711 p h) (sat_cons (step1080 p h) (sat_cons (step1731 p h) (sat_cons (step1061 p h) (sat_cons (step1694 p h) (sat_cons (step1067 p h) (sat_cons (step1642 p h) (sat_cons (step1076 p h) (sat_cons (step1644 p h) (sat_cons (step1049 p h) (sat_cons (step1050 p h) (sat_cons (step69 p h) (sat_cons (step62 p h) (sat_nil p))))))))))))))))
def c1733 : List Lit := [(19, true), (7, false), (1525, true)]
theorem step1733 (p : Nat → Bool) (h : Constraints p) : clause p c1733 = true :=
  Snake9.LocalRup.prove_clause [c778, c1059, c1058, c89, c90, c91] c1733 (by decide) p (sat_cons (step778 p h) (sat_cons (step1059 p h) (sat_cons (step1058 p h) (sat_cons (step89 p h) (sat_cons (step90 p h) (sat_cons (step91 p h) (sat_nil p)))))))
def c1734 : List Lit := [(67, false), (60, false), (47, false), (1652, true)]
theorem step1734 (p : Nat → Bool) (h : Constraints p) : clause p c1734 = true :=
  Snake9.LocalRup.prove_clause [c398, c399, c1278] c1734 (by decide) p (sat_cons (step398 p h) (sat_cons (step399 p h) (sat_cons (step1278 p h) (sat_nil p))))
def c1735 : List Lit := [(66, true), (67, false), (60, false), (1657, true), (73, true)]
theorem step1735 (p : Nat → Bool) (h : Constraints p) : clause p c1735 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1288, c1277, c1278, c1286, c406, c1281] c1735 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1288 p h) (sat_cons (step1277 p h) (sat_cons (step1278 p h) (sat_cons (step1286 p h) (sat_cons (step406 p h) (sat_cons (step1281 p h) (sat_nil p))))))))
def c1736 : List Lit := [(67, false), (60, false), (73, true), (1657, true)]
theorem step1736 (p : Nat → Bool) (h : Constraints p) : clause p c1736 = true :=
  Snake9.LocalRup.prove_clause [c1735, c404, c405, c1276, c1281, c1286] c1736 (by decide) p (sat_cons (step1735 p h) (sat_cons (step404 p h) (sat_cons (step405 p h) (sat_cons (step1276 p h) (sat_cons (step1281 p h) (sat_cons (step1286 p h) (sat_nil p)))))))
def c1737 : List Lit := [(53, false), (60, false), (52, false), (54, false), (1663, true), (73, true), (51, true), (61, true)]
theorem step1737 (p : Nat → Bool) (h : Constraints p) : clause p c1737 = true :=
  Snake9.LocalRup.prove_clause [c794, c275, c270, c362, c363, c1263, c1267, c1281, c1272, c1283, c1306] c1737 (by decide) p (sat_cons (step794 p h) (sat_cons (step275 p h) (sat_cons (step270 p h) (sat_cons (step362 p h) (sat_cons (step363 p h) (sat_cons (step1263 p h) (sat_cons (step1267 p h) (sat_cons (step1281 p h) (sat_cons (step1272 p h) (sat_cons (step1283 p h) (sat_cons (step1306 p h) (sat_nil p))))))))))))
def c1738 : List Lit := [(1643, false), (1662, true), (67, true), (60, false), (73, true), (61, true)]
theorem step1738 (p : Nat → Bool) (h : Constraints p) : clause p c1738 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1282, c1305, c1266, c1271, c1272, c1301, c1267, c1283, c1285, c1281, c1276, c1710] c1738 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1282 p h) (sat_cons (step1305 p h) (sat_cons (step1266 p h) (sat_cons (step1271 p h) (sat_cons (step1272 p h) (sat_cons (step1301 p h) (sat_cons (step1267 p h) (sat_cons (step1283 p h) (sat_cons (step1285 p h) (sat_cons (step1281 p h) (sat_cons (step1276 p h) (sat_cons (step1710 p h) (sat_nil p))))))))))))))
def c1739 : List Lit := [(84, false), (69, false), (1752, true), (1732, false), (122, false), (1739, false)]
theorem step1739 (p : Nat → Bool) (h : Constraints p) : clause p c1739 = true :=
  Snake9.LocalRup.prove_clause [c1718, c729] c1739 (by decide) p (sat_cons (step1718 p h) (sat_cons (step729 p h) (sat_nil p)))
end B112E020
