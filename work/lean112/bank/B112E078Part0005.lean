import B112E078Part0004
namespace B112E078
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1532 : List Lit := [(1483, false), (1491, true)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c1349, c814] c1532 (by decide) p (sat_cons (step1349 p h) (sat_cons (step814 p h) (sat_nil p)))
def c1533 : List Lit := [(1518, false), (1550, true)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1237, c957] c1533 (by decide) p (sat_cons (step1237 p h) (sat_cons (step957 p h) (sat_nil p)))
def c1534 : List Lit := [(1568, true), (1552, false)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1375, c963] c1534 (by decide) p (sat_cons (step1375 p h) (sat_cons (step963 p h) (sat_nil p)))
def c1535 : List Lit := [(1553, false), (1569, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1375, c964] c1535 (by decide) p (sat_cons (step1375 p h) (sat_cons (step964 p h) (sat_nil p)))
def c1536 : List Lit := [(1554, false), (1570, true)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1375, c965] c1536 (by decide) p (sat_cons (step1375 p h) (sat_cons (step965 p h) (sat_nil p)))
def c1537 : List Lit := [(1612, false), (1620, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1233, c1050] c1537 (by decide) p (sat_cons (step1233 p h) (sat_cons (step1050 p h) (sat_nil p)))
def c1538 : List Lit := [(1613, false), (1621, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1233, c1051] c1538 (by decide) p (sat_cons (step1233 p h) (sat_cons (step1051 p h) (sat_nil p)))
def c1539 : List Lit := [(1592, false), (1620, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1052] c1539 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1052 p h) (sat_nil p)))
def c1540 : List Lit := [(1593, false), (1621, true)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1055] c1540 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1055 p h) (sat_nil p)))
def c1541 : List Lit := [(1634, false), (1646, true)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1250, c1080] c1541 (by decide) p (sat_cons (step1250 p h) (sat_cons (step1080 p h) (sat_nil p)))
def c1542 : List Lit := [(1635, false), (1647, true)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1250, c1084] c1542 (by decide) p (sat_cons (step1250 p h) (sat_cons (step1084 p h) (sat_nil p)))
def c1543 : List Lit := [(1677, true), (1668, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1129] c1543 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1129 p h) (sat_nil p)))
def c1544 : List Lit := [(1678, true), (1669, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1130] c1544 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1130 p h) (sat_nil p)))
def c1545 : List Lit := [(1670, false), (1679, true)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1131] c1545 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1131 p h) (sat_nil p)))
def c1546 : List Lit := [(1671, false), (1680, true)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1132] c1546 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1132 p h) (sat_nil p)))
def c1547 : List Lit := [(1672, false), (1681, true)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1133] c1547 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1133 p h) (sat_nil p)))
def c1548 : List Lit := [(1679, false), (1695, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1234, c1146] c1548 (by decide) p (sat_cons (step1234 p h) (sat_cons (step1146 p h) (sat_nil p)))
def c1549 : List Lit := [(1680, false), (1696, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1234, c1147] c1549 (by decide) p (sat_cons (step1234 p h) (sat_cons (step1147 p h) (sat_nil p)))
def c1550 : List Lit := [(1681, false), (1697, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1234, c1148] c1550 (by decide) p (sat_cons (step1234 p h) (sat_cons (step1148 p h) (sat_nil p)))
def c1551 : List Lit := [(1677, false), (1694, true)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1149] c1551 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1149 p h) (sat_nil p)))
def c1552 : List Lit := [(1678, false), (1695, true)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1150] c1552 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1150 p h) (sat_nil p)))
def c1553 : List Lit := [(1679, false), (1696, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1151] c1553 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1151 p h) (sat_nil p)))
def c1554 : List Lit := [(1680, false), (1697, true)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1152] c1554 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1152 p h) (sat_nil p)))
def c1555 : List Lit := [(1681, false), (1698, true)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1153] c1555 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1153 p h) (sat_nil p)))
def c1556 : List Lit := [(1682, false), (1699, true)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1154] c1556 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1154 p h) (sat_nil p)))
def c1557 : List Lit := [(1568, false), (1699, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1171, c1165] c1557 (by decide) p (sat_cons (step1171 p h) (sat_cons (step1165 p h) (sat_nil p)))
def c1558 : List Lit := [(1569, false), (1698, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1171, c1166] c1558 (by decide) p (sat_cons (step1171 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c1559 : List Lit := [(1570, false), (1697, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1171, c1167] c1559 (by decide) p (sat_cons (step1171 p h) (sat_cons (step1167 p h) (sat_nil p)))
def c1560 : List Lit := [(1571, false), (1696, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1171, c1168] c1560 (by decide) p (sat_cons (step1171 p h) (sat_cons (step1168 p h) (sat_nil p)))
def c1561 : List Lit := [(1572, false), (1695, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1171, c1169] c1561 (by decide) p (sat_cons (step1171 p h) (sat_cons (step1169 p h) (sat_nil p)))
def c1562 : List Lit := [(1573, false), (1694, false)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1171, c1170] c1562 (by decide) p (sat_cons (step1171 p h) (sat_cons (step1170 p h) (sat_nil p)))
def c1563 : List Lit := [(1656, true), (1665, true), (45, true)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1093, c1095, c1090, c1091, c1087, c1088, c1505, c1295, c483, c1110, c1102] c1563 (by decide) p (sat_cons (step1093 p h) (sat_cons (step1095 p h) (sat_cons (step1090 p h) (sat_cons (step1091 p h) (sat_cons (step1087 p h) (sat_cons (step1088 p h) (sat_cons (step1505 p h) (sat_cons (step1295 p h) (sat_cons (step483 p h) (sat_cons (step1110 p h) (sat_cons (step1102 p h) (sat_nil p))))))))))))
def c1564 : List Lit := [(1634, true), (23, true), (22, false), (1620, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1537, c1257, c1036, c1035, c1539, c1059, c1061, c1057, c1289, c441, c445, c1483] c1564 (by decide) p (sat_cons (step1537 p h) (sat_cons (step1257 p h) (sat_cons (step1036 p h) (sat_cons (step1035 p h) (sat_cons (step1539 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1057 p h) (sat_cons (step1289 p h) (sat_cons (step441 p h) (sat_cons (step445 p h) (sat_cons (step1483 p h) (sat_nil p)))))))))))))
def c1565 : List Lit := [(90, false), (23, true), (22, false), (1633, true), (86, false), (89, false), (1592, true), (1474, true)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c782, c781, c121, c451, c1289, c1484, c445, c1483, c438, c441, c1488, c1058] c1565 (by decide) p (sat_cons (step782 p h) (sat_cons (step781 p h) (sat_cons (step121 p h) (sat_cons (step451 p h) (sat_cons (step1289 p h) (sat_cons (step1484 p h) (sat_cons (step445 p h) (sat_cons (step1483 p h) (sat_cons (step438 p h) (sat_cons (step441 p h) (sat_cons (step1488 p h) (sat_cons (step1058 p h) (sat_nil p)))))))))))))
def c1566 : List Lit := [(61, true), (1581, true)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1009, c1003, c1004, c1471, c1469, c406, c405, c669, c668, c1525] c1566 (by decide) p (sat_cons (step1009 p h) (sat_cons (step1003 p h) (sat_cons (step1004 p h) (sat_cons (step1471 p h) (sat_cons (step1469 p h) (sat_cons (step406 p h) (sat_cons (step405 p h) (sat_cons (step669 p h) (sat_cons (step668 p h) (sat_cons (step1525 p h) (sat_nil p)))))))))))
def c1567 : List Lit := [(49, false), (1664, true), (14, false)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1109, c1102, c1107, c1105, c349, c510, c1512] c1567 (by decide) p (sat_cons (step1109 p h) (sat_cons (step1102 p h) (sat_cons (step1107 p h) (sat_cons (step1105 p h) (sat_cons (step349 p h) (sat_cons (step510 p h) (sat_cons (step1512 p h) (sat_nil p))))))))
def c1568 : List Lit := [(106, true), (112, false), (115, false), (86, false), (89, false), (1657, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1098, c1087, c1089, c1096, c442, c513, c1090, c1494, c483] c1568 (by decide) p (sat_cons (step1098 p h) (sat_cons (step1087 p h) (sat_cons (step1089 p h) (sat_cons (step1096 p h) (sat_cons (step442 p h) (sat_cons (step513 p h) (sat_cons (step1090 p h) (sat_cons (step1494 p h) (sat_cons (step483 p h) (sat_nil p))))))))))
def c1569 : List Lit := [(1646, false), (1696, true), (45, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1553, c1135, c1385, c1115, c1121, c1156, c1094, c1537, c1257, c1035, c1036, c1563, c1118, c1107, c1109, c1101, c1102, c1568, c1295, c1091, c1092, c1096, c1505, c1088, c483] c1569 (by decide) p (sat_cons (step1553 p h) (sat_cons (step1135 p h) (sat_cons (step1385 p h) (sat_cons (step1115 p h) (sat_cons (step1121 p h) (sat_cons (step1156 p h) (sat_cons (step1094 p h) (sat_cons (step1537 p h) (sat_cons (step1257 p h) (sat_cons (step1035 p h) (sat_cons (step1036 p h) (sat_cons (step1563 p h) (sat_cons (step1118 p h) (sat_cons (step1107 p h) (sat_cons (step1109 p h) (sat_cons (step1101 p h) (sat_cons (step1102 p h) (sat_cons (step1568 p h) (sat_cons (step1295 p h) (sat_cons (step1091 p h) (sat_cons (step1092 p h) (sat_cons (step1096 p h) (sat_cons (step1505 p h) (sat_cons (step1088 p h) (sat_cons (step483 p h) (sat_nil p))))))))))))))))))))))))))
def c1570 : List Lit := [(106, false), (1662, true), (103, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1105, c1104, c529, c496, c1514] c1570 (by decide) p (sat_cons (step1105 p h) (sat_cons (step1104 p h) (sat_cons (step529 p h) (sat_cons (step496 p h) (sat_cons (step1514 p h) (sat_nil p))))))
def c1571 : List Lit := [(1669, true), (103, false), (45, true)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1115, c1121, c1563, c1098, c1118, c1107, c1109, c1102, c1570, c1087, c1089, c1096, c1090, c483, c1505] c1571 (by decide) p (sat_cons (step1115 p h) (sat_cons (step1121 p h) (sat_cons (step1563 p h) (sat_cons (step1098 p h) (sat_cons (step1118 p h) (sat_cons (step1107 p h) (sat_cons (step1109 p h) (sat_cons (step1102 p h) (sat_cons (step1570 p h) (sat_cons (step1087 p h) (sat_cons (step1089 p h) (sat_cons (step1096 p h) (sat_cons (step1090 p h) (sat_cons (step483 p h) (sat_cons (step1505 p h) (sat_nil p))))))))))))))))
def c1572 : List Lit := [(1476, false), (1490, true), (1481, true), (81, false), (5, true)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c732, c735, c792, c797, c823, c773, c770, c771, c760, c751, c1298, c742, c65, c1415, c78] c1572 (by decide) p (sat_cons (step732 p h) (sat_cons (step735 p h) (sat_cons (step792 p h) (sat_cons (step797 p h) (sat_cons (step823 p h) (sat_cons (step773 p h) (sat_cons (step770 p h) (sat_cons (step771 p h) (sat_cons (step760 p h) (sat_cons (step751 p h) (sat_cons (step1298 p h) (sat_cons (step742 p h) (sat_cons (step65 p h) (sat_cons (step1415 p h) (sat_cons (step78 p h) (sat_nil p))))))))))))))))
def c1573 : List Lit := [(1481, true), (1572, true), (1620, true), (20, true), (1634, true), (1540, false), (27, true), (1512, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c779, c786, c1537, c1061, c1539, c1289, c1265, c1474, c414, c1026, c1029, c1045, c1040, c1034, c1257, c1035, c1268, c793, c789, c780, c1564, c117, c839, c845, c873, c960, c980, c1572] c1573 (by decide) p (sat_cons (step779 p h) (sat_cons (step786 p h) (sat_cons (step1537 p h) (sat_cons (step1061 p h) (sat_cons (step1539 p h) (sat_cons (step1289 p h) (sat_cons (step1265 p h) (sat_cons (step1474 p h) (sat_cons (step414 p h) (sat_cons (step1026 p h) (sat_cons (step1029 p h) (sat_cons (step1045 p h) (sat_cons (step1040 p h) (sat_cons (step1034 p h) (sat_cons (step1257 p h) (sat_cons (step1035 p h) (sat_cons (step1268 p h) (sat_cons (step793 p h) (sat_cons (step789 p h) (sat_cons (step780 p h) (sat_cons (step1564 p h) (sat_cons (step117 p h) (sat_cons (step839 p h) (sat_cons (step845 p h) (sat_cons (step873 p h) (sat_cons (step960 p h) (sat_cons (step980 p h) (sat_cons (step1572 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1574 : List Lit := [(1696, true), (1540, false), (27, true), (1512, false), (2, false), (45, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.TreeRup.prove_clause [c844, c868, c953, c1337, c1388, c1569, c1078, c1541, c1242, c1059, c1061, c190, c1057, c1571, c1544, c1552, c1156, c1561, c1537, c1539, c985, c1047, c1257, c1024, c1268, c1265, c1289, c1030, c1035, c1036, c1007, c732, c1474, c414, c441, c735, c1026, c1028, c1029, c1477, c1045, c1040, c1033, c1034, c1479, c431, c819, c1573, c1296, c818, c824, c1483, c980, c760, c960, c751, c873, c845, c839, c117, c780, c789, c798, c773, c1298, c770, c771, c742, c1415, c65] c1574 (by decide) p (sat_cons (step844 p h) (sat_cons (step868 p h) (sat_cons (step953 p h) (sat_cons (step1337 p h) (sat_cons (step1388 p h) (sat_cons (step1569 p h) (sat_cons (step1078 p h) (sat_cons (step1541 p h) (sat_cons (step1242 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step190 p h) (sat_cons (step1057 p h) (sat_cons (step1571 p h) (sat_cons (step1544 p h) (sat_cons (step1552 p h) (sat_cons (step1156 p h) (sat_cons (step1561 p h) (sat_cons (step1537 p h) (sat_cons (step1539 p h) (sat_cons (step985 p h) (sat_cons (step1047 p h) (sat_cons (step1257 p h) (sat_cons (step1024 p h) (sat_cons (step1268 p h) (sat_cons (step1265 p h) (sat_cons (step1289 p h) (sat_cons (step1030 p h) (sat_cons (step1035 p h) (sat_cons (step1036 p h) (sat_cons (step1007 p h) (sat_cons (step732 p h) (sat_cons (step1474 p h) (sat_cons (step414 p h) (sat_cons (step441 p h) (sat_cons (step735 p h) (sat_cons (step1026 p h) (sat_cons (step1028 p h) (sat_cons (step1029 p h) (sat_cons (step1477 p h) (sat_cons (step1045 p h) (sat_cons (step1040 p h) (sat_cons (step1033 p h) (sat_cons (step1034 p h) (sat_cons (step1479 p h) (sat_cons (step431 p h) (sat_cons (step819 p h) (sat_cons (step1573 p h) (sat_cons (step1296 p h) (sat_cons (step818 p h) (sat_cons (step824 p h) (sat_cons (step1483 p h) (sat_cons (step980 p h) (sat_cons (step760 p h) (sat_cons (step960 p h) (sat_cons (step751 p h) (sat_cons (step873 p h) (sat_cons (step845 p h) (sat_cons (step839 p h) (sat_cons (step117 p h) (sat_cons (step780 p h) (sat_cons (step789 p h) (sat_cons (step798 p h) (sat_cons (step773 p h) (sat_cons (step1298 p h) (sat_cons (step770 p h) (sat_cons (step771 p h) (sat_cons (step742 p h) (sat_cons (step1415 p h) (sat_cons (step65 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1575 : List Lit := [(1489, true), (5, true), (1461, false), (45, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c732, c735, c822, c817, c760, c796, c1298, c740, c748, c749, c764, c1334, c736] c1575 (by decide) p (sat_cons (step732 p h) (sat_cons (step735 p h) (sat_cons (step822 p h) (sat_cons (step817 p h) (sat_cons (step760 p h) (sat_cons (step796 p h) (sat_cons (step1298 p h) (sat_cons (step740 p h) (sat_cons (step748 p h) (sat_cons (step749 p h) (sat_cons (step764 p h) (sat_cons (step1334 p h) (sat_cons (step736 p h) (sat_nil p))))))))))))))
def c1576 : List Lit := [(1476, false), (5, true), (1481, true), (1490, true), (45, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c732, c735, c792, c797, c823, c760, c1298, c740, c748, c749, c764, c1334, c736] c1576 (by decide) p (sat_cons (step732 p h) (sat_cons (step735 p h) (sat_cons (step792 p h) (sat_cons (step797 p h) (sat_cons (step823 p h) (sat_cons (step760 p h) (sat_cons (step1298 p h) (sat_cons (step740 p h) (sat_cons (step748 p h) (sat_cons (step749 p h) (sat_cons (step764 p h) (sat_cons (step1334 p h) (sat_cons (step736 p h) (sat_nil p))))))))))))))
def c1577 : List Lit := [(22, false), (20, false), (26, false), (32, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c87, c111, c1418] c1577 (by decide) p (sat_cons (step87 p h) (sat_cons (step111 p h) (sat_cons (step1418 p h) (sat_nil p))))
def c1578 : List Lit := [(5, true), (1571, true), (1540, false), (27, true), (1512, false), (1461, false), (45, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c844, c868, c953, c979, c818, c1575, c974, c960, c873, c845, c839, c1576, c784, c786, c781, c779, c1577, c778] c1578 (by decide) p (sat_cons (step844 p h) (sat_cons (step868 p h) (sat_cons (step953 p h) (sat_cons (step979 p h) (sat_cons (step818 p h) (sat_cons (step1575 p h) (sat_cons (step974 p h) (sat_cons (step960 p h) (sat_cons (step873 p h) (sat_cons (step845 p h) (sat_cons (step839 p h) (sat_cons (step1576 p h) (sat_cons (step784 p h) (sat_cons (step786 p h) (sat_cons (step781 p h) (sat_cons (step779 p h) (sat_cons (step1577 p h) (sat_cons (step778 p h) (sat_nil p)))))))))))))))))))
def c1579 : List Lit := [(1476, false), (1452, false), (5, false), (1481, true), (1490, true), (45, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c748, c792, c797, c823, c775, c756, c764, c1409, c750, c736, c1334, c749, c760, c735, c733, c54, c1292, c745, c1404] c1579 (by decide) p (sat_cons (step748 p h) (sat_cons (step792 p h) (sat_cons (step797 p h) (sat_cons (step823 p h) (sat_cons (step775 p h) (sat_cons (step756 p h) (sat_cons (step764 p h) (sat_cons (step1409 p h) (sat_cons (step750 p h) (sat_cons (step736 p h) (sat_cons (step1334 p h) (sat_cons (step749 p h) (sat_cons (step760 p h) (sat_cons (step735 p h) (sat_cons (step733 p h) (sat_cons (step54 p h) (sat_cons (step1292 p h) (sat_cons (step745 p h) (sat_cons (step1404 p h) (sat_nil p))))))))))))))))))))
def c1580 : List Lit := [(1472, true), (1540, false), (27, true), (1512, false), (2, false), (45, true)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c844, c868, c953, c1574, c1560, c979, c1337, c818, c1578, c1389, c1, c740, c1579, c784, c781, c816, c1388, c778, c779, c190, c1242, c1078, c1385, c1387, c1577, c1035, c839, c1257, c845, c1537, c873, c960, c968, c1559, c1161, c1157, c1053, c1135, c1268, c1115, c1061, c1563, c1081, c1117, c1138] c1580 (by decide) p (sat_cons (step844 p h) (sat_cons (step868 p h) (sat_cons (step953 p h) (sat_cons (step1574 p h) (sat_cons (step1560 p h) (sat_cons (step979 p h) (sat_cons (step1337 p h) (sat_cons (step818 p h) (sat_cons (step1578 p h) (sat_cons (step1389 p h) (sat_cons (step1 p h) (sat_cons (step740 p h) (sat_cons (step1579 p h) (sat_cons (step784 p h) (sat_cons (step781 p h) (sat_cons (step816 p h) (sat_cons (step1388 p h) (sat_cons (step778 p h) (sat_cons (step779 p h) (sat_cons (step190 p h) (sat_cons (step1242 p h) (sat_cons (step1078 p h) (sat_cons (step1385 p h) (sat_cons (step1387 p h) (sat_cons (step1577 p h) (sat_cons (step1035 p h) (sat_cons (step839 p h) (sat_cons (step1257 p h) (sat_cons (step845 p h) (sat_cons (step1537 p h) (sat_cons (step873 p h) (sat_cons (step960 p h) (sat_cons (step968 p h) (sat_cons (step1559 p h) (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step1053 p h) (sat_cons (step1135 p h) (sat_cons (step1268 p h) (sat_cons (step1115 p h) (sat_cons (step1061 p h) (sat_cons (step1563 p h) (sat_cons (step1081 p h) (sat_cons (step1117 p h) (sat_cons (step1138 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c1581 : List Lit := [(1540, false), (27, true), (1512, false), (2, false), (45, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c844, c868, c1337, c1389, c953, c1574, c1560, c979, c818, c1578, c1, c740, c1579, c1580, c786] c1581 (by decide) p (sat_cons (step844 p h) (sat_cons (step868 p h) (sat_cons (step1337 p h) (sat_cons (step1389 p h) (sat_cons (step953 p h) (sat_cons (step1574 p h) (sat_cons (step1560 p h) (sat_cons (step979 p h) (sat_cons (step818 p h) (sat_cons (step1578 p h) (sat_cons (step1 p h) (sat_cons (step740 p h) (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step786 p h) (sat_nil p))))))))))))))))
def c1582 : List Lit := [(1664, true), (1539, true), (52, true), (14, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c881, c884, c912, c899, c1107, c1567, c1255, c883, c892, c885, c900, c916] c1582 (by decide) p (sat_cons (step881 p h) (sat_cons (step884 p h) (sat_cons (step912 p h) (sat_cons (step899 p h) (sat_cons (step1107 p h) (sat_cons (step1567 p h) (sat_cons (step1255 p h) (sat_cons (step883 p h) (sat_cons (step892 p h) (sat_cons (step885 p h) (sat_cons (step900 p h) (sat_cons (step916 p h) (sat_nil p)))))))))))))
def c1583 : List Lit := [(1669, true), (1664, false), (45, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c1115, c1118, c1563] c1583 (by decide) p (sat_cons (step1115 p h) (sat_cons (step1118 p h) (sat_cons (step1563 p h) (sat_nil p))))
def c1584 : List Lit := [(20, false), (22, false), (14, false), (26, false), (1552, true), (1490, false), (5, false), (27, true), (1512, false), (2, false), (45, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c1388, c190, c189, c1387, c1577, c1242, c1035, c839, c1078, c1257, c845, c1537, c873, c1533, c959, c977, c1558, c1158, c1582, c1583, c1139, c1135, c1267, c1081, c1162, c1474, c1061, c1053, c413, c1289] c1584 (by decide) p (sat_cons (step1388 p h) (sat_cons (step190 p h) (sat_cons (step189 p h) (sat_cons (step1387 p h) (sat_cons (step1577 p h) (sat_cons (step1242 p h) (sat_cons (step1035 p h) (sat_cons (step839 p h) (sat_cons (step1078 p h) (sat_cons (step1257 p h) (sat_cons (step845 p h) (sat_cons (step1537 p h) (sat_cons (step873 p h) (sat_cons (step1533 p h) (sat_cons (step959 p h) (sat_cons (step977 p h) (sat_cons (step1558 p h) (sat_cons (step1158 p h) (sat_cons (step1582 p h) (sat_cons (step1583 p h) (sat_cons (step1139 p h) (sat_cons (step1135 p h) (sat_cons (step1267 p h) (sat_cons (step1081 p h) (sat_cons (step1162 p h) (sat_cons (step1474 p h) (sat_cons (step1061 p h) (sat_cons (step1053 p h) (sat_cons (step413 p h) (sat_cons (step1289 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1585 : List Lit := [(1612, false), (1642, false), (1698, true), (1669, false), (5, false)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1135, c1162, c1267, c1053, c1474, c1024, c413, c1566] c1585 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1135 p h) (sat_cons (step1162 p h) (sat_cons (step1267 p h) (sat_cons (step1053 p h) (sat_cons (step1474 p h) (sat_cons (step1024 p h) (sat_cons (step413 p h) (sat_cons (step1566 p h) (sat_nil p))))))))))
def c1586 : List Lit := [(1538, true), (1523, false)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c915, c1343, c887, c879] c1586 (by decide) p (sat_cons (step915 p h) (sat_cons (step1343 p h) (sat_cons (step887 p h) (sat_cons (step879 p h) (sat_nil p)))))
def c1587 : List Lit := [(1463, true), (1453, false), (13, false), (5, false), (45, true)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c751, c1409, c757, c765, c753, c736, c1334, c752, c761, c735, c733, c54, c1292, c745, c1404] c1587 (by decide) p (sat_cons (step751 p h) (sat_cons (step1409 p h) (sat_cons (step757 p h) (sat_cons (step765 p h) (sat_cons (step753 p h) (sat_cons (step736 p h) (sat_cons (step1334 p h) (sat_cons (step752 p h) (sat_cons (step761 p h) (sat_cons (step735 p h) (sat_cons (step733 p h) (sat_cons (step54 p h) (sat_cons (step1292 p h) (sat_cons (step745 p h) (sat_cons (step1404 p h) (sat_nil p))))))))))))))))
def c1588 : List Lit := [(8, false), (4, false), (5, false), (45, true)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c9, c1404] c1588 (by decide) p (sat_cons (step9 p h) (sat_cons (step1404 p h) (sat_nil p)))
def c1589 : List Lit := [(1697, true), (1669, false), (1642, false), (5, false)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1135, c1554, c1157, c1139, c1539, c1081, c1268, c1061] c1589 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1135 p h) (sat_cons (step1554 p h) (sat_cons (step1157 p h) (sat_cons (step1139 p h) (sat_cons (step1539 p h) (sat_cons (step1081 p h) (sat_cons (step1268 p h) (sat_cons (step1061 p h) (sat_nil p))))))))))
def c1590 : List Lit := [(1523, false), (1539, true), (1570, true), (1469, true), (1480, false), (7, true), (5, false), (1517, false), (45, true)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c775, c773, c1586, c1300, c951, c742, c983, c1587, c829] c1590 (by decide) p (sat_cons (step775 p h) (sat_cons (step773 p h) (sat_cons (step1586 p h) (sat_cons (step1300 p h) (sat_cons (step951 p h) (sat_cons (step742 p h) (sat_cons (step983 p h) (sat_cons (step1587 p h) (sat_cons (step829 p h) (sat_nil p))))))))))
def c1591 : List Lit := [(1570, true), (1469, true), (1490, false), (1480, false), (7, true), (5, false), (1517, false), (45, true)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c773, c771, c770, c775, c978, c952, c1590, c1304, c907, c951, c983, c829, c1587, c742, c65, c1308, c1398] c1591 (by decide) p (sat_cons (step773 p h) (sat_cons (step771 p h) (sat_cons (step770 p h) (sat_cons (step775 p h) (sat_cons (step978 p h) (sat_cons (step952 p h) (sat_cons (step1590 p h) (sat_cons (step1304 p h) (sat_cons (step907 p h) (sat_cons (step951 p h) (sat_cons (step983 p h) (sat_cons (step829 p h) (sat_cons (step1587 p h) (sat_cons (step742 p h) (sat_cons (step65 p h) (sat_cons (step1308 p h) (sat_cons (step1398 p h) (sat_nil p))))))))))))))))))
def c1592 : List Lit := [(1462, true), (13, false), (1452, false), (5, false), (45, true)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c1409, c748, c756, c764, c750, c736, c1334, c749, c760, c735, c733, c54, c1588, c745] c1592 (by decide) p (sat_cons (step1409 p h) (sat_cons (step748 p h) (sat_cons (step756 p h) (sat_cons (step764 p h) (sat_cons (step750 p h) (sat_cons (step736 p h) (sat_cons (step1334 p h) (sat_cons (step749 p h) (sat_cons (step760 p h) (sat_cons (step735 p h) (sat_cons (step733 p h) (sat_cons (step54 p h) (sat_cons (step1588 p h) (sat_cons (step745 p h) (sat_nil p)))))))))))))))
def c1593 : List Lit := [(1523, true), (1697, true), (5, false), (2, false), (45, true)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c1388, c881, c882, c198, c1242, c1589, c1121, c1583, c1098, c1107, c1109, c1104, c1105, c1101, c1102, c510, c1510, c529, c1087, c1089, c1096, c513, c1090, c1506, c483] c1593 (by decide) p (sat_cons (step1388 p h) (sat_cons (step881 p h) (sat_cons (step882 p h) (sat_cons (step198 p h) (sat_cons (step1242 p h) (sat_cons (step1589 p h) (sat_cons (step1121 p h) (sat_cons (step1583 p h) (sat_cons (step1098 p h) (sat_cons (step1107 p h) (sat_cons (step1109 p h) (sat_cons (step1104 p h) (sat_cons (step1105 p h) (sat_cons (step1101 p h) (sat_cons (step1102 p h) (sat_cons (step510 p h) (sat_cons (step1510 p h) (sat_cons (step529 p h) (sat_cons (step1087 p h) (sat_cons (step1089 p h) (sat_cons (step1096 p h) (sat_cons (step513 p h) (sat_cons (step1090 p h) (sat_cons (step1506 p h) (sat_cons (step483 p h) (sat_nil p))))))))))))))))))))))))))
def c1594 : List Lit := [(49, false), (1664, true), (1535, true)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c1109, c1102, c1107, c1105, c1371, c510, c892, c1512, c902, c361, c360, c897] c1594 (by decide) p (sat_cons (step1109 p h) (sat_cons (step1102 p h) (sat_cons (step1107 p h) (sat_cons (step1105 p h) (sat_cons (step1371 p h) (sat_cons (step510 p h) (sat_cons (step892 p h) (sat_cons (step1512 p h) (sat_cons (step902 p h) (sat_cons (step361 p h) (sat_cons (step360 p h) (sat_cons (step897 p h) (sat_nil p)))))))))))))
def c1595 : List Lit := [(111, true), (112, false), (115, false), (116, false), (118, false), (1657, true)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c1098, c1510, c529, c1087, c1089, c1096, c513, c1090, c1506, c483] c1595 (by decide) p (sat_cons (step1098 p h) (sat_cons (step1510 p h) (sat_cons (step529 p h) (sat_cons (step1087 p h) (sat_cons (step1089 p h) (sat_cons (step1096 p h) (sat_cons (step513 p h) (sat_cons (step1090 p h) (sat_cons (step1506 p h) (sat_cons (step483 p h) (sat_nil p)))))))))))
end B112E078
