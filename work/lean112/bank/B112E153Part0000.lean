import B112E153Inputs
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1547 : List Lit := [(9, true)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c14, c13] c1547 (by decide) p (sat_cons (step14 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1548 : List Lit := [(3, false), (11, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1547, c14, c15] c1548 (by decide) p (sat_cons (step1547 p h) (sat_cons (step14 p h) (sat_cons (step15 p h) (sat_nil p))))
def c1549 : List Lit := [(133, true), (3, true), (11, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1547, c16] c1549 (by decide) p (sat_cons (step1547 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1550 : List Lit := [(1, false)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c650, c1] c1550 (by decide) p (sat_cons (step650 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1551 : List Lit := [(490, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c867, c864] c1551 (by decide) p (sat_cons (step867 p h) (sat_cons (step864 p h) (sat_nil p)))
def c1552 : List Lit := [(368, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c867, c866] c1552 (by decide) p (sat_cons (step867 p h) (sat_cons (step866 p h) (sat_nil p)))
def c1553 : List Lit := [(488, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1551, c860] c1553 (by decide) p (sat_cons (step1551 p h) (sat_cons (step860 p h) (sat_nil p)))
def c1554 : List Lit := [(428, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1551, c863] c1554 (by decide) p (sat_cons (step1551 p h) (sat_cons (step863 p h) (sat_nil p)))
def c1555 : List Lit := [(366, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1552, c767] c1555 (by decide) p (sat_cons (step1552 p h) (sat_cons (step767 p h) (sat_nil p)))
def c1556 : List Lit := [(306, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1552, c770] c1556 (by decide) p (sat_cons (step1552 p h) (sat_cons (step770 p h) (sat_nil p)))
def c1557 : List Lit := [(486, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1553, c855] c1557 (by decide) p (sat_cons (step1553 p h) (sat_cons (step855 p h) (sat_nil p)))
def c1558 : List Lit := [(456, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1553, c858] c1558 (by decide) p (sat_cons (step1553 p h) (sat_cons (step858 p h) (sat_nil p)))
def c1559 : List Lit := [(426, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1554, c815] c1559 (by decide) p (sat_cons (step1554 p h) (sat_cons (step815 p h) (sat_nil p)))
def c1560 : List Lit := [(396, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1554, c818] c1560 (by decide) p (sat_cons (step1554 p h) (sat_cons (step818 p h) (sat_nil p)))
def c1561 : List Lit := [(276, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1556, c737] c1561 (by decide) p (sat_cons (step1556 p h) (sat_cons (step737 p h) (sat_nil p)))
def c1562 : List Lit := [(484, false)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1557, c851] c1562 (by decide) p (sat_cons (step1557 p h) (sat_cons (step851 p h) (sat_nil p)))
def c1563 : List Lit := [(440, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1558, c838] c1563 (by decide) p (sat_cons (step1558 p h) (sat_cons (step838 p h) (sat_nil p)))
def c1564 : List Lit := [(410, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1559, c813] c1564 (by decide) p (sat_cons (step1559 p h) (sat_cons (step813 p h) (sat_nil p)))
def c1565 : List Lit := [(394, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1560, c793] c1565 (by decide) p (sat_cons (step1560 p h) (sat_cons (step793 p h) (sat_nil p)))
def c1566 : List Lit := [(380, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1560, c796] c1566 (by decide) p (sat_cons (step1560 p h) (sat_cons (step796 p h) (sat_nil p)))
def c1567 : List Lit := [(274, false)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1561, c718] c1567 (by decide) p (sat_cons (step1561 p h) (sat_cons (step718 p h) (sat_nil p)))
def c1568 : List Lit := [(438, false)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1563, c827] c1568 (by decide) p (sat_cons (step1563 p h) (sat_cons (step827 p h) (sat_nil p)))
def c1569 : List Lit := [(378, false)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1566, c781] c1569 (by decide) p (sat_cons (step1566 p h) (sat_cons (step781 p h) (sat_nil p)))
def c1570 : List Lit := [(434, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1568, c825] c1570 (by decide) p (sat_cons (step1568 p h) (sat_cons (step825 p h) (sat_nil p)))
def c1571 : List Lit := [(374, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1569, c779] c1571 (by decide) p (sat_cons (step1569 p h) (sat_cons (step779 p h) (sat_nil p)))
def c1572 : List Lit := [(845, true)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1550, c871] c1572 (by decide) p (sat_cons (step1550 p h) (sat_cons (step871 p h) (sat_nil p)))
def c1573 : List Lit := [(843, false), (846, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1550, c872] c1573 (by decide) p (sat_cons (step1550 p h) (sat_cons (step872 p h) (sat_nil p)))
def c1574 : List Lit := [(844, false), (847, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1550, c873] c1574 (by decide) p (sat_cons (step1550 p h) (sat_cons (step873 p h) (sat_nil p)))
def c1575 : List Lit := [(852, false), (857, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c1572, c883] c1575 (by decide) p (sat_cons (step1572 p h) (sat_cons (step883 p h) (sat_nil p)))
def c1576 : List Lit := [(853, false), (858, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1572, c884] c1576 (by decide) p (sat_cons (step1572 p h) (sat_cons (step884 p h) (sat_nil p)))
def c1577 : List Lit := [(854, false), (859, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c1572, c885] c1577 (by decide) p (sat_cons (step1572 p h) (sat_cons (step885 p h) (sat_nil p)))
def c1578 : List Lit := [(1663, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1571, c1455, c1457, c1451, c1453, c1445, c1449, c1446, c1447, c1443, c1444, c213, c200, c210, c207, c775] c1578 (by decide) p (sat_cons (step1571 p h) (sat_cons (step1455 p h) (sat_cons (step1457 p h) (sat_cons (step1451 p h) (sat_cons (step1453 p h) (sat_cons (step1445 p h) (sat_cons (step1449 p h) (sat_cons (step1446 p h) (sat_cons (step1447 p h) (sat_cons (step1443 p h) (sat_cons (step1444 p h) (sat_cons (step213 p h) (sat_cons (step200 p h) (sat_cons (step210 p h) (sat_cons (step207 p h) (sat_cons (step775 p h) (sat_nil p)))))))))))))))))
def c1579 : List Lit := [(76, true), (1664, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1571, c1456, c1452, c1448, c1450, c1451, c1454, c1458, c1446, c1447, c1445, c1443, c1444, c213, c200, c210, c207, c775] c1579 (by decide) p (sat_cons (step1571 p h) (sat_cons (step1456 p h) (sat_cons (step1452 p h) (sat_cons (step1448 p h) (sat_cons (step1450 p h) (sat_cons (step1451 p h) (sat_cons (step1454 p h) (sat_cons (step1458 p h) (sat_cons (step1446 p h) (sat_cons (step1447 p h) (sat_cons (step1445 p h) (sat_cons (step1443 p h) (sat_cons (step1444 p h) (sat_cons (step213 p h) (sat_cons (step200 p h) (sat_cons (step210 p h) (sat_cons (step207 p h) (sat_cons (step775 p h) (sat_nil p)))))))))))))))))))
def c1580 : List Lit := [(1001, true), (94, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c681, c1088, c1092, c1080, c1069, c1071, c1077, c1066, c1067, c181, c205, c244] c1580 (by decide) p (sat_cons (step681 p h) (sat_cons (step1088 p h) (sat_cons (step1092 p h) (sat_cons (step1080 p h) (sat_cons (step1069 p h) (sat_cons (step1071 p h) (sat_cons (step1077 p h) (sat_cons (step1066 p h) (sat_cons (step1067 p h) (sat_cons (step181 p h) (sat_cons (step205 p h) (sat_cons (step244 p h) (sat_nil p)))))))))))))
def c1581 : List Lit := [(1008, false), (105, false), (1026, true), (86, true), (94, false)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c684, c1148, c1109, c1115, c1144, c1116, c1126, c1128, c1111, c1123, c1120, c1121, c280, c275, c366, c273] c1581 (by decide) p (sat_cons (step684 p h) (sat_cons (step1148 p h) (sat_cons (step1109 p h) (sat_cons (step1115 p h) (sat_cons (step1144 p h) (sat_cons (step1116 p h) (sat_cons (step1126 p h) (sat_cons (step1128 p h) (sat_cons (step1111 p h) (sat_cons (step1123 p h) (sat_cons (step1120 p h) (sat_cons (step1121 p h) (sat_cons (step280 p h) (sat_cons (step275 p h) (sat_cons (step366 p h) (sat_cons (step273 p h) (sat_nil p)))))))))))))))))
def c1582 : List Lit := [(82, false), (92, true), (1016, true), (105, false), (94, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c684, c1121, c1120, c280, c275, c273] c1582 (by decide) p (sat_cons (step684 p h) (sat_cons (step1121 p h) (sat_cons (step1120 p h) (sat_cons (step280 p h) (sat_cons (step275 p h) (sat_cons (step273 p h) (sat_nil p)))))))
def c1583 : List Lit := [(997, true), (80, false), (109, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c678, c1080, c1082, c1078, c1075, c254, c224] c1583 (by decide) p (sat_cons (step678 p h) (sat_cons (step1080 p h) (sat_cons (step1082 p h) (sat_cons (step1078 p h) (sat_cons (step1075 p h) (sat_cons (step254 p h) (sat_cons (step224 p h) (sat_nil p))))))))
def c1584 : List Lit := [(75, true), (998, true), (80, false), (109, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c678, c1081, c1077, c1079, c1083, c1075, c224, c254] c1584 (by decide) p (sat_cons (step678 p h) (sat_cons (step1081 p h) (sat_cons (step1077 p h) (sat_cons (step1079 p h) (sat_cons (step1083 p h) (sat_cons (step1075 p h) (sat_cons (step224 p h) (sat_cons (step254 p h) (sat_nil p)))))))))
def c1585 : List Lit := [(1002, true), (80, false), (109, true), (94, false)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c681, c1583, c1089, c1093, c1069, c1071, c1066, c1067, c1584, c205, c181, c244] c1585 (by decide) p (sat_cons (step681 p h) (sat_cons (step1583 p h) (sat_cons (step1089 p h) (sat_cons (step1093 p h) (sat_cons (step1069 p h) (sat_cons (step1071 p h) (sat_cons (step1066 p h) (sat_cons (step1067 p h) (sat_cons (step1584 p h) (sat_cons (step205 p h) (sat_cons (step181 p h) (sat_cons (step244 p h) (sat_nil p)))))))))))))
def c1586 : List Lit := [(1020, true), (82, false), (105, false), (94, false)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c684, c1126, c1128, c1123, c1120, c1121, c280, c275, c366, c273] c1586 (by decide) p (sat_cons (step684 p h) (sat_cons (step1126 p h) (sat_cons (step1128 p h) (sat_cons (step1123 p h) (sat_cons (step1120 p h) (sat_cons (step1121 p h) (sat_cons (step280 p h) (sat_cons (step275 p h) (sat_cons (step366 p h) (sat_cons (step273 p h) (sat_nil p)))))))))))
def c1587 : List Lit := [(105, false), (86, true), (109, true), (1035, true), (1026, true), (94, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c1109, c1112, c1581, c1107, c1585, c1172, c1143, c1113, c1111, c1586, c1139] c1587 (by decide) p (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1581 p h) (sat_cons (step1107 p h) (sat_cons (step1585 p h) (sat_cons (step1172 p h) (sat_cons (step1143 p h) (sat_cons (step1113 p h) (sat_cons (step1111 p h) (sat_cons (step1586 p h) (sat_cons (step1139 p h) (sat_nil p))))))))))))
def c1588 : List Lit := [(988, true), (66, false), (75, false)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c1066, c1067, c205] c1588 (by decide) p (sat_cons (step1066 p h) (sat_cons (step1067 p h) (sat_cons (step205 p h) (sat_nil p))))
def c1589 : List Lit := [(57, true), (55, true), (941, true), (183, true), (61, true), (77, true)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c674, c183, c994, c185, c1005, c997] c1589 (by decide) p (sat_cons (step674 p h) (sat_cons (step183 p h) (sat_cons (step994 p h) (sat_cons (step185 p h) (sat_cons (step1005 p h) (sat_cons (step997 p h) (sat_nil p)))))))
def c1590 : List Lit := [(1081, true), (124, false), (118, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c1265, c1266, c649] c1590 (by decide) p (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step649 p h) (sat_nil p))))
def c1591 : List Lit := [(43, false), (38, false), (39, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c664, c111, c107] c1591 (by decide) p (sat_cons (step664 p h) (sat_cons (step111 p h) (sat_cons (step107 p h) (sat_nil p))))
def c1592 : List Lit := [(38, false), (916, true), (41, false), (117, false), (46, true)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c116, c957, c962, c952, c953, c1591] c1592 (by decide) p (sat_cons (step116 p h) (sat_cons (step957 p h) (sat_cons (step962 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step1591 p h) (sat_nil p)))))))
def c1593 : List Lit := [(938, true), (927, true)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c674, c998, c1000, c995, c996, c992, c993, c182, c187, c139, c138, c983] c1593 (by decide) p (sat_cons (step674 p h) (sat_cons (step998 p h) (sat_cons (step1000 p h) (sat_cons (step995 p h) (sat_cons (step996 p h) (sat_cons (step992 p h) (sat_cons (step993 p h) (sat_cons (step182 p h) (sat_cons (step187 p h) (sat_cons (step139 p h) (sat_cons (step138 p h) (sat_cons (step983 p h) (sat_nil p)))))))))))))
def c1594 : List Lit := [(926, true)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c668, c981, c982, c131, c132, c1509] c1594 (by decide) p (sat_cons (step668 p h) (sat_cons (step981 p h) (sat_cons (step982 p h) (sat_cons (step131 p h) (sat_cons (step132 p h) (sat_cons (step1509 p h) (sat_nil p)))))))
def c1595 : List Lit := [(930, true)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c1594, c987] c1595 (by decide) p (sat_cons (step1594 p h) (sat_cons (step987 p h) (sat_nil p)))
def c1596 : List Lit := [(942, true)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1006] c1596 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1006 p h) (sat_nil p)))
def c1597 : List Lit := [(1071, true), (109, false), (35, false)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c1248, c1249, c486] c1597 (by decide) p (sat_cons (step1248 p h) (sat_cons (step1249 p h) (sat_cons (step486 p h) (sat_nil p))))
def c1598 : List Lit := [(93, false), (94, false), (96, false), (92, true)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c688, c372, c374] c1598 (by decide) p (sat_cons (step688 p h) (sat_cons (step372 p h) (sat_cons (step374 p h) (sat_nil p))))
def c1599 : List Lit := [(63, false), (58, true), (52, false), (57, false)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c676, c197, c191] c1599 (by decide) p (sat_cons (step676 p h) (sat_cons (step197 p h) (sat_cons (step191 p h) (sat_nil p))))
def c1600 : List Lit := [(71, false), (1074, false), (1102, true), (1057, false), (109, false), (35, false), (1051, false), (1083, false)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c475, c473, c476, c1213, c1250, c1221, c1261, c1232, c1294, c1318] c1600 (by decide) p (sat_cons (step475 p h) (sat_cons (step473 p h) (sat_cons (step476 p h) (sat_cons (step1213 p h) (sat_cons (step1250 p h) (sat_cons (step1221 p h) (sat_cons (step1261 p h) (sat_cons (step1232 p h) (sat_cons (step1294 p h) (sat_cons (step1318 p h) (sat_nil p)))))))))))
def c1601 : List Lit := [(78, false), (70, false), (80, true), (202, true), (109, false)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c223, c256] c1601 (by decide) p (sat_cons (step223 p h) (sat_cons (step256 p h) (sat_nil p)))
def c1602 : List Lit := [(20, false), (12, false), (3, false)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c653, c27, c19] c1602 (by decide) p (sat_cons (step653 p h) (sat_cons (step27 p h) (sat_cons (step19 p h) (sat_nil p))))
def c1603 : List Lit := [(1079, true), (116, false), (115, false)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1263, c584] c1603 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step584 p h) (sat_nil p))))
def c1604 : List Lit := [(1047, true), (93, false), (92, true)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c1198, c1199, c1598] c1604 (by decide) p (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step1598 p h) (sat_nil p))))
def c1605 : List Lit := [(919, true), (902, false)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c946, c972, c969, c947, c960, c941, c952, c953, c1591] c1605 (by decide) p (sat_cons (step946 p h) (sat_cons (step972 p h) (sat_cons (step969 p h) (sat_cons (step947 p h) (sat_cons (step960 p h) (sat_cons (step941 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step1591 p h) (sat_nil p))))))))))
def c1606 : List Lit := [(910, true), (35, true), (905, true), (908, true), (91, false), (73, false)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c664, c662, c952, c953, c1591, c108, c941, c943, c950, c540, c103, c102, c940, c83] c1606 (by decide) p (sat_cons (step664 p h) (sat_cons (step662 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step1591 p h) (sat_cons (step108 p h) (sat_cons (step941 p h) (sat_cons (step943 p h) (sat_cons (step950 p h) (sat_cons (step540 p h) (sat_cons (step103 p h) (sat_cons (step102 p h) (sat_cons (step940 p h) (sat_cons (step83 p h) (sat_nil p)))))))))))))))
def c1607 : List Lit := [(35, true), (920, true), (91, false), (73, false), (902, false)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c662, c976, c948, c946, c970, c1606, c960, c961, c973, c955, c949, c947, c940, c942, c96, c540, c102] c1607 (by decide) p (sat_cons (step662 p h) (sat_cons (step976 p h) (sat_cons (step948 p h) (sat_cons (step946 p h) (sat_cons (step970 p h) (sat_cons (step1606 p h) (sat_cons (step960 p h) (sat_cons (step961 p h) (sat_cons (step973 p h) (sat_cons (step955 p h) (sat_cons (step949 p h) (sat_cons (step947 p h) (sat_cons (step940 p h) (sat_cons (step942 p h) (sat_cons (step96 p h) (sat_cons (step540 p h) (sat_cons (step102 p h) (sat_nil p))))))))))))))))))
def c1608 : List Lit := [(37, false), (90, true), (89, true), (53, false), (91, false), (73, false)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c671, c662, c679, c687, c1554, c166, c152, c540, c103, c347, c236, c235, c349, c459, c144, c1515, c1524, c217, c285, c776, c801, c777, c803, c780, c805, c794, c812, c817] c1608 (by decide) p (sat_cons (step671 p h) (sat_cons (step662 p h) (sat_cons (step679 p h) (sat_cons (step687 p h) (sat_cons (step1554 p h) (sat_cons (step166 p h) (sat_cons (step152 p h) (sat_cons (step540 p h) (sat_cons (step103 p h) (sat_cons (step347 p h) (sat_cons (step236 p h) (sat_cons (step235 p h) (sat_cons (step349 p h) (sat_cons (step459 p h) (sat_cons (step144 p h) (sat_cons (step1515 p h) (sat_cons (step1524 p h) (sat_cons (step217 p h) (sat_cons (step285 p h) (sat_cons (step776 p h) (sat_cons (step801 p h) (sat_cons (step777 p h) (sat_cons (step803 p h) (sat_cons (step780 p h) (sat_cons (step805 p h) (sat_cons (step794 p h) (sat_cons (step812 p h) (sat_cons (step817 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1609 : List Lit := [(37, true), (920, true), (902, false)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c976, c948, c942, c943, c947, c973, c960, c952, c953, c1591] c1609 (by decide) p (sat_cons (step976 p h) (sat_cons (step948 p h) (sat_cons (step942 p h) (sat_cons (step943 p h) (sat_cons (step947 p h) (sat_cons (step973 p h) (sat_cons (step960 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step1591 p h) (sat_nil p)))))))))))
def c1610 : List Lit := [(1052, true), (98, true), (100, true), (89, true), (91, false)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c690, c1201, c1205, c1207, c1203, c1198, c398, c391] c1610 (by decide) p (sat_cons (step690 p h) (sat_cons (step1201 p h) (sat_cons (step1205 p h) (sat_cons (step1207 p h) (sat_cons (step1203 p h) (sat_cons (step1198 p h) (sat_cons (step398 p h) (sat_cons (step391 p h) (sat_nil p)))))))))
end B112E153
