import B112E203Part0003
namespace B112E203
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1529 : List Lit := [(116, false), (115, true)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c568, c515] c1529 (by decide) p (sat_cons (step568 p h) (sat_cons (step515 p h) (sat_nil p)))
def c1530 : List Lit := [(116, false), (108, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c568, c516] c1530 (by decide) p (sat_cons (step568 p h) (sat_cons (step516 p h) (sat_nil p)))
def c1531 : List Lit := [(114, true), (115, true), (117, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c569, c518] c1531 (by decide) p (sat_cons (step569 p h) (sat_cons (step518 p h) (sat_nil p)))
def c1532 : List Lit := [(113, true), (115, true), (117, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c569, c519] c1532 (by decide) p (sat_cons (step569 p h) (sat_cons (step519 p h) (sat_nil p)))
def c1533 : List Lit := [(121, false), (122, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1300, c574] c1533 (by decide) p (sat_cons (step1300 p h) (sat_cons (step574 p h) (sat_nil p)))
def c1534 : List Lit := [(239, false), (241, false)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1297, c578] c1534 (by decide) p (sat_cons (step1297 p h) (sat_cons (step578 p h) (sat_nil p)))
def c1535 : List Lit := [(237, false), (243, false)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1293, c583] c1535 (by decide) p (sat_cons (step1293 p h) (sat_cons (step583 p h) (sat_nil p)))
def c1536 : List Lit := [(245, false), (257, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1288, c593] c1536 (by decide) p (sat_cons (step1288 p h) (sat_cons (step593 p h) (sat_nil p)))
def c1537 : List Lit := [(273, false), (275, false)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1296, c599] c1537 (by decide) p (sat_cons (step1296 p h) (sat_cons (step599 p h) (sat_nil p)))
def c1538 : List Lit := [(259, false), (287, false)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1282, c610] c1538 (by decide) p (sat_cons (step1282 p h) (sat_cons (step610 p h) (sat_nil p)))
def c1539 : List Lit := [(301, false), (313, false)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1286, c627] c1539 (by decide) p (sat_cons (step1286 p h) (sat_cons (step627 p h) (sat_nil p)))
def c1540 : List Lit := [(289, false), (345, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1279, c647] c1540 (by decide) p (sat_cons (step1279 p h) (sat_cons (step647 p h) (sat_nil p)))
def c1541 : List Lit := [(351, false), (357, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1291, c656] c1541 (by decide) p (sat_cons (step1291 p h) (sat_cons (step656 p h) (sat_nil p)))
def c1542 : List Lit := [(188, false), (189, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1299, c661] c1542 (by decide) p (sat_cons (step1299 p h) (sat_cons (step661 p h) (sat_nil p)))
def c1543 : List Lit := [(365, false), (367, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1295, c664] c1543 (by decide) p (sat_cons (step1295 p h) (sat_cons (step664 p h) (sat_nil p)))
def c1544 : List Lit := [(359, false), (371, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1284, c671] c1544 (by decide) p (sat_cons (step1284 p h) (sat_cons (step671 p h) (sat_nil p)))
def c1545 : List Lit := [(373, false), (401, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1280, c692] c1545 (by decide) p (sat_cons (step1280 p h) (sat_cons (step692 p h) (sat_nil p)))
def c1546 : List Lit := [(403, false), (459, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1278, c726] c1546 (by decide) p (sat_cons (step1278 p h) (sat_cons (step726 p h) (sat_nil p)))
def c1547 : List Lit := [(347, false), (461, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c731, c729] c1547 (by decide) p (sat_cons (step731 p h) (sat_cons (step729 p h) (sat_nil p)))
def c1548 : List Lit := [(812, false), (840, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1334, c817] c1548 (by decide) p (sat_cons (step1334 p h) (sat_cons (step817 p h) (sat_nil p)))
def c1549 : List Lit := [(813, false), (841, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1334, c823] c1549 (by decide) p (sat_cons (step1334 p h) (sat_cons (step823 p h) (sat_nil p)))
def c1550 : List Lit := [(815, false), (843, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1334, c826] c1550 (by decide) p (sat_cons (step1334 p h) (sat_cons (step826 p h) (sat_nil p)))
def c1551 : List Lit := [(865, false), (899, true)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1339, c894] c1551 (by decide) p (sat_cons (step1339 p h) (sat_cons (step894 p h) (sat_nil p)))
def c1552 : List Lit := [(866, false), (900, true)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1339, c900] c1552 (by decide) p (sat_cons (step1339 p h) (sat_cons (step900 p h) (sat_nil p)))
def c1553 : List Lit := [(867, false), (901, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1339, c906] c1553 (by decide) p (sat_cons (step1339 p h) (sat_cons (step906 p h) (sat_nil p)))
def c1554 : List Lit := [(868, false), (902, true)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1339, c909] c1554 (by decide) p (sat_cons (step1339 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1555 : List Lit := [(918, true), (841, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1340, c924] c1555 (by decide) p (sat_cons (step1340 p h) (sat_cons (step924 p h) (sat_nil p)))
def c1556 : List Lit := [(919, true), (842, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1340, c931] c1556 (by decide) p (sat_cons (step1340 p h) (sat_cons (step931 p h) (sat_nil p)))
def c1557 : List Lit := [(920, true), (843, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1340, c937] c1557 (by decide) p (sat_cons (step1340 p h) (sat_cons (step937 p h) (sat_nil p)))
def c1558 : List Lit := [(921, true), (844, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1340, c942] c1558 (by decide) p (sat_cons (step1340 p h) (sat_cons (step942 p h) (sat_nil p)))
def c1559 : List Lit := [(966, true), (953, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1018] c1559 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1018 p h) (sat_nil p)))
def c1560 : List Lit := [(967, true), (954, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1021] c1560 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1021 p h) (sat_nil p)))
def c1561 : List Lit := [(955, false), (968, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1023] c1561 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1023 p h) (sat_nil p)))
def c1562 : List Lit := [(956, false), (969, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1024] c1562 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1024 p h) (sat_nil p)))
def c1563 : List Lit := [(974, true), (942, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1028] c1563 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1028 p h) (sat_nil p)))
def c1564 : List Lit := [(975, true), (943, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1033] c1564 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1033 p h) (sat_nil p)))
def c1565 : List Lit := [(976, true), (944, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1038] c1565 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1038 p h) (sat_nil p)))
def c1566 : List Lit := [(945, false), (977, true)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1043] c1566 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1043 p h) (sat_nil p)))
def c1567 : List Lit := [(946, false), (978, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1047] c1567 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1047 p h) (sat_nil p)))
def c1568 : List Lit := [(947, false), (979, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1051] c1568 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1051 p h) (sat_nil p)))
def c1569 : List Lit := [(1034, false), (1050, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1332, c1104] c1569 (by decide) p (sat_cons (step1332 p h) (sat_cons (step1104 p h) (sat_nil p)))
def c1570 : List Lit := [(980, false), (1034, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1130] c1570 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1130 p h) (sat_nil p)))
def c1571 : List Lit := [(981, false), (1033, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1132] c1571 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1132 p h) (sat_nil p)))
def c1572 : List Lit := [(918, false), (1056, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1134] c1572 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c1573 : List Lit := [(919, false), (1055, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1135] c1573 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1135 p h) (sat_nil p)))
def c1574 : List Lit := [(920, false), (1054, false)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1136] c1574 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1136 p h) (sat_nil p)))
def c1575 : List Lit := [(921, false), (1053, false)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1137] c1575 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1137 p h) (sat_nil p)))
def c1576 : List Lit := [(922, false), (1052, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1138] c1576 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1138 p h) (sat_nil p)))
def c1577 : List Lit := [(923, false), (1051, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1139] c1577 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1139 p h) (sat_nil p)))
def c1578 : List Lit := [(924, false), (1050, false)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1140] c1578 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1140 p h) (sat_nil p)))
def c1579 : List Lit := [(1480, false), (1513, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1328, c1185] c1579 (by decide) p (sat_cons (step1328 p h) (sat_cons (step1185 p h) (sat_nil p)))
def c1580 : List Lit := [(1642, false), (1659, true)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1324, c1234] c1580 (by decide) p (sat_cons (step1324 p h) (sat_cons (step1234 p h) (sat_nil p)))
def c1581 : List Lit := [(1536, false), (1659, false)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1235] c1581 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1235 p h) (sat_nil p)))
def c1582 : List Lit := [(810, true)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c752, c755, c1345, c735, c733] c1582 (by decide) p (sat_cons (step752 p h) (sat_cons (step755 p h) (sat_cons (step1345 p h) (sat_cons (step735 p h) (sat_cons (step733 p h) (sat_nil p))))))
def c1583 : List Lit := [(839, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c1582, c1376] c1583 (by decide) p (sat_cons (step1582 p h) (sat_cons (step1376 p h) (sat_nil p)))
def c1584 : List Lit := [(890, true), (51, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c858, c866, c1313, c877, c869, c867, c1310, c860, c861, c862, c852, c853, c163, c265, c1461] c1584 (by decide) p (sat_cons (step858 p h) (sat_cons (step866 p h) (sat_cons (step1313 p h) (sat_cons (step877 p h) (sat_cons (step869 p h) (sat_cons (step867 p h) (sat_cons (step1310 p h) (sat_cons (step860 p h) (sat_cons (step861 p h) (sat_cons (step862 p h) (sat_cons (step852 p h) (sat_cons (step853 p h) (sat_cons (step163 p h) (sat_cons (step265 p h) (sat_cons (step1461 p h) (sat_nil p))))))))))))))))
def c1585 : List Lit := [(945, true), (935, false), (56, true), (57, true)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c966, c952, c976, c980, c967, c953, c959, c947, c1482, c372, c948] c1585 (by decide) p (sat_cons (step966 p h) (sat_cons (step952 p h) (sat_cons (step976 p h) (sat_cons (step980 p h) (sat_cons (step967 p h) (sat_cons (step953 p h) (sat_cons (step959 p h) (sat_cons (step947 p h) (sat_cons (step1482 p h) (sat_cons (step372 p h) (sat_cons (step948 p h) (sat_nil p))))))))))))
def c1586 : List Lit := [(88, true), (90, true), (45, true), (46, false), (1002, true)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c1079, c1059, c1056, c1057, c1417, c1061, c455] c1586 (by decide) p (sat_cons (step1079 p h) (sat_cons (step1059 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1417 p h) (sat_cons (step1061 p h) (sat_cons (step455 p h) (sat_nil p))))))))
def c1587 : List Lit := [(88, true), (1002, true), (873, true), (52, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c1079, c1059, c853, c852, c160, c1056, c1057, c1586, c1061, c467] c1587 (by decide) p (sat_cons (step1079 p h) (sat_cons (step1059 p h) (sat_cons (step853 p h) (sat_cons (step852 p h) (sat_cons (step160 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1586 p h) (sat_cons (step1061 p h) (sat_cons (step467 p h) (sat_nil p)))))))))))
def c1588 : List Lit := [(88, false), (880, true), (50, false), (47, false)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c228, c225, c860] c1588 (by decide) p (sat_cons (step228 p h) (sat_cons (step225 p h) (sat_cons (step860 p h) (sat_nil p))))
def c1589 : List Lit := [(873, true), (52, false), (980, false), (885, true), (865, false)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c1583, c852, c853, c160, c1461, c1462, c265, c861, c870, c1588, c1587, c1099, c1129, c1572, c911, c895, c1313, c1584, c867, c222, c859] c1589 (by decide) p (sat_cons (step1583 p h) (sat_cons (step852 p h) (sat_cons (step853 p h) (sat_cons (step160 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step265 p h) (sat_cons (step861 p h) (sat_cons (step870 p h) (sat_cons (step1588 p h) (sat_cons (step1587 p h) (sat_cons (step1099 p h) (sat_cons (step1129 p h) (sat_cons (step1572 p h) (sat_cons (step911 p h) (sat_cons (step895 p h) (sat_cons (step1313 p h) (sat_cons (step1584 p h) (sat_cons (step867 p h) (sat_cons (step222 p h) (sat_cons (step859 p h) (sat_nil p))))))))))))))))))))))
def c1590 : List Lit := [(945, false), (46, false), (797, false), (70, true), (891, false), (1033, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c1582, c1583, c989, c996, c1559, c1318, c1044, c1120, c1574, c926, c808, c1401, c896, c912, c919, c1573, c1373, c1125, c748, c1045, c741, c1560, c997, c1420, c991, c330] c1590 (by decide) p (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step989 p h) (sat_cons (step996 p h) (sat_cons (step1559 p h) (sat_cons (step1318 p h) (sat_cons (step1044 p h) (sat_cons (step1120 p h) (sat_cons (step1574 p h) (sat_cons (step926 p h) (sat_cons (step808 p h) (sat_cons (step1401 p h) (sat_cons (step896 p h) (sat_cons (step912 p h) (sat_cons (step919 p h) (sat_cons (step1573 p h) (sat_cons (step1373 p h) (sat_cons (step1125 p h) (sat_cons (step748 p h) (sat_cons (step1045 p h) (sat_cons (step741 p h) (sat_cons (step1560 p h) (sat_cons (step997 p h) (sat_cons (step1420 p h) (sat_cons (step991 p h) (sat_cons (step330 p h) (sat_nil p)))))))))))))))))))))))))))
def c1591 : List Lit := [(802, true), (58, false), (930, true), (46, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c740, c741, c1436, c34, c328, c949] c1591 (by decide) p (sat_cons (step740 p h) (sat_cons (step741 p h) (sat_cons (step1436 p h) (sat_cons (step34 p h) (sat_cons (step328 p h) (sat_cons (step949 p h) (sat_nil p)))))))
def c1592 : List Lit := [(8, false), (58, false), (930, true), (46, false)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c327, c328, c949] c1592 (by decide) p (sat_cons (step327 p h) (sat_cons (step328 p h) (sat_cons (step949 p h) (sat_nil p))))
end B112E203
