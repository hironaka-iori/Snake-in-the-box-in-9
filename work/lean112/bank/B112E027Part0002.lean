import B112E027Part0001
namespace B112E027
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1578 : List Lit := [(17, true), (142, true), (1471, true), (15, false)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c969, c1546, c989, c972, c980] c1578 (by decide) p (sat_cons (step969 p h) (sat_cons (step1546 p h) (sat_cons (step989 p h) (sat_cons (step972 p h) (sat_cons (step980 p h) (sat_nil p))))))
def c1579 : List Lit := [(1531, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1495, c1093, c1099, c1082, c1045, c1059, c1061, c1040, c1057, c1037, c1038, c1511, c198, c210, c207, c759] c1579 (by decide) p (sat_cons (step1495 p h) (sat_cons (step1093 p h) (sat_cons (step1099 p h) (sat_cons (step1082 p h) (sat_cons (step1045 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1040 p h) (sat_cons (step1057 p h) (sat_cons (step1037 p h) (sat_cons (step1038 p h) (sat_cons (step1511 p h) (sat_cons (step198 p h) (sat_cons (step210 p h) (sat_cons (step207 p h) (sat_cons (step759 p h) (sat_nil p)))))))))))))))))
def c1580 : List Lit := [(1513, true), (1603, true), (83, true), (1534, true)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1502, c1461, c1229, c1173, c1155, c1559, c1222, c1207, c1197, c1189, c1059, c1061, c1056, c1057, c233, c231, c767, c224, c223, c770, c1068, c1066, c780, c1076, c786, c1080, c762, c1102, c760, c1045, c757, c1040, c210, c1037, c214] c1580 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1502 p h) (sat_cons (step1461 p h) (sat_cons (step1229 p h) (sat_cons (step1173 p h) (sat_cons (step1155 p h) (sat_cons (step1559 p h) (sat_cons (step1222 p h) (sat_cons (step1207 p h) (sat_cons (step1197 p h) (sat_cons (step1189 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step233 p h) (sat_cons (step231 p h) (sat_cons (step767 p h) (sat_cons (step224 p h) (sat_cons (step223 p h) (sat_cons (step770 p h) (sat_cons (step1068 p h) (sat_cons (step1066 p h) (sat_cons (step780 p h) (sat_cons (step1076 p h) (sat_cons (step786 p h) (sat_cons (step1080 p h) (sat_cons (step762 p h) (sat_cons (step1102 p h) (sat_cons (step760 p h) (sat_cons (step1045 p h) (sat_cons (step757 p h) (sat_cons (step1040 p h) (sat_cons (step210 p h) (sat_cons (step1037 p h) (sat_cons (step214 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1581 : List Lit := [(1603, true), (83, true), (1534, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1501, c1096, c1222, c1229, c1207, c1173, c1197, c1155, c1189, c1504, c1559, c1089, c1580, c1085, c1084, c1102, c1045, c1040, c1566, c231, c224, c223, c1068, c1066, c1076] c1581 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1501 p h) (sat_cons (step1096 p h) (sat_cons (step1222 p h) (sat_cons (step1229 p h) (sat_cons (step1207 p h) (sat_cons (step1173 p h) (sat_cons (step1197 p h) (sat_cons (step1155 p h) (sat_cons (step1189 p h) (sat_cons (step1504 p h) (sat_cons (step1559 p h) (sat_cons (step1089 p h) (sat_cons (step1580 p h) (sat_cons (step1085 p h) (sat_cons (step1084 p h) (sat_cons (step1102 p h) (sat_cons (step1045 p h) (sat_cons (step1040 p h) (sat_cons (step1566 p h) (sat_cons (step231 p h) (sat_cons (step224 p h) (sat_cons (step223 p h) (sat_cons (step1068 p h) (sat_cons (step1066 p h) (sat_cons (step1076 p h) (sat_nil p)))))))))))))))))))))))))))
def c1582 : List Lit := [(82, false), (51, false), (52, false), (1521, true)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c224, c223, c1068, c1064, c1073] c1582 (by decide) p (sat_cons (step224 p h) (sat_cons (step223 p h) (sat_cons (step1068 p h) (sat_cons (step1064 p h) (sat_cons (step1073 p h) (sat_nil p))))))
def c1583 : List Lit := [(1524, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c1487, c1078, c1082, c1070, c1072, c1059, c1067, c1068, c1064, c1065, c1056, c269, c235, c222, c268, c260, c774, c772, c777] c1583 (by decide) p (sat_cons (step1487 p h) (sat_cons (step1078 p h) (sat_cons (step1082 p h) (sat_cons (step1070 p h) (sat_cons (step1072 p h) (sat_cons (step1059 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_cons (step1064 p h) (sat_cons (step1065 p h) (sat_cons (step1056 p h) (sat_cons (step269 p h) (sat_cons (step235 p h) (sat_cons (step222 p h) (sat_cons (step268 p h) (sat_cons (step260 p h) (sat_cons (step774 p h) (sat_cons (step772 p h) (sat_cons (step777 p h) (sat_nil p))))))))))))))))))))
def c1584 : List Lit := [(90, false), (94, false), (100, false), (82, true), (98, false), (92, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c666, c546, c545, c519] c1584 (by decide) p (sat_cons (step666 p h) (sat_cons (step546 p h) (sat_cons (step545 p h) (sat_cons (step519 p h) (sat_nil p)))))
def c1585 : List Lit := [(7, true), (261, true), (15, true), (1454, true), (3, true)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c618, c621, c699, c686, c681, c679, c697, c695, c689, c2, c937, c34, c1520, c40, c963, c935, c943] c1585 (by decide) p (sat_cons (step618 p h) (sat_cons (step621 p h) (sat_cons (step699 p h) (sat_cons (step686 p h) (sat_cons (step681 p h) (sat_cons (step679 p h) (sat_cons (step697 p h) (sat_cons (step695 p h) (sat_cons (step689 p h) (sat_cons (step2 p h) (sat_cons (step937 p h) (sat_cons (step34 p h) (sat_cons (step1520 p h) (sat_cons (step40 p h) (sat_cons (step963 p h) (sat_cons (step935 p h) (sat_cons (step943 p h) (sat_nil p))))))))))))))))))
def c1586 : List Lit := [(1460, false), (1481, true), (21, false), (39, false)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c1513, c1006, c1523, c980, c994, c993, c983, c1011, c1519, c1516, c937] c1586 (by decide) p (sat_cons (step1513 p h) (sat_cons (step1006 p h) (sat_cons (step1523 p h) (sat_cons (step980 p h) (sat_cons (step994 p h) (sat_cons (step993 p h) (sat_cons (step983 p h) (sat_cons (step1011 p h) (sat_cons (step1519 p h) (sat_cons (step1516 p h) (sat_cons (step937 p h) (sat_nil p))))))))))))
def c1587 : List Lit := [(1520, true), (53, false), (54, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c1070, c1072, c1067, c1064, c235] c1587 (by decide) p (sat_cons (step1070 p h) (sat_cons (step1072 p h) (sat_cons (step1067 p h) (sat_cons (step1064 p h) (sat_cons (step235 p h) (sat_nil p))))))
def c1588 : List Lit := [(1532, true), (1520, false)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c1583, c1495, c1094, c1100, c1045, c1040, c1037, c1038, c1083, c1059, c1061, c1511, c1057, c198, c210, c207, c759] c1588 (by decide) p (sat_cons (step1583 p h) (sat_cons (step1495 p h) (sat_cons (step1094 p h) (sat_cons (step1100 p h) (sat_cons (step1045 p h) (sat_cons (step1040 p h) (sat_cons (step1037 p h) (sat_cons (step1038 p h) (sat_cons (step1083 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1511 p h) (sat_cons (step1057 p h) (sat_cons (step198 p h) (sat_cons (step210 p h) (sat_cons (step207 p h) (sat_cons (step759 p h) (sat_nil p))))))))))))))))))
def c1589 : List Lit := [(11, true), (20, true), (19, false), (17, false), (1452, true)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c1456, c1526, c1550, c77, c697, c92, c732, c702, c726, c703, c708] c1589 (by decide) p (sat_cons (step1456 p h) (sat_cons (step1526 p h) (sat_cons (step1550 p h) (sat_cons (step77 p h) (sat_cons (step697 p h) (sat_cons (step92 p h) (sat_cons (step732 p h) (sat_cons (step702 p h) (sat_cons (step726 p h) (sat_cons (step703 p h) (sat_cons (step708 p h) (sat_nil p))))))))))))
def c1590 : List Lit := [(1481, true), (22, true), (21, false), (39, false), (36, true), (38, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c1452, c1523, c980, c964, c967, c989, c1016, c1586, c968, c970, c966, c103, c1589, c176, c180, c741, c742, c746, c748, c790, c796, c729, c731, c726, c697, c699, c708, c694, c695, c685, c686, c703, c692, c689, c684, c681, c702, c691, c683, c679, c90, c92, c1417, c77, c71, c1525] c1590 (by decide) p (sat_cons (step1452 p h) (sat_cons (step1523 p h) (sat_cons (step980 p h) (sat_cons (step964 p h) (sat_cons (step967 p h) (sat_cons (step989 p h) (sat_cons (step1016 p h) (sat_cons (step1586 p h) (sat_cons (step968 p h) (sat_cons (step970 p h) (sat_cons (step966 p h) (sat_cons (step103 p h) (sat_cons (step1589 p h) (sat_cons (step176 p h) (sat_cons (step180 p h) (sat_cons (step741 p h) (sat_cons (step742 p h) (sat_cons (step746 p h) (sat_cons (step748 p h) (sat_cons (step790 p h) (sat_cons (step796 p h) (sat_cons (step729 p h) (sat_cons (step731 p h) (sat_cons (step726 p h) (sat_cons (step697 p h) (sat_cons (step699 p h) (sat_cons (step708 p h) (sat_cons (step694 p h) (sat_cons (step695 p h) (sat_cons (step685 p h) (sat_cons (step686 p h) (sat_cons (step703 p h) (sat_cons (step692 p h) (sat_cons (step689 p h) (sat_cons (step684 p h) (sat_cons (step681 p h) (sat_cons (step702 p h) (sat_cons (step691 p h) (sat_cons (step683 p h) (sat_cons (step679 p h) (sat_cons (step90 p h) (sat_cons (step92 p h) (sat_cons (step1417 p h) (sat_cons (step77 p h) (sat_cons (step71 p h) (sat_cons (step1525 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c1591 : List Lit := [(289, true), (261, true), (129, true), (182, true), (186, true), (188, true), (193, true), (194, true), (195, true), (199, true), (200, true), (203, true), (208, true), (210, true), (213, true), (214, true), (215, true), (220, true), (226, true), (229, true), (232, true), (233, true), (235, true), (185, true), (192, true), (207, true), (150, true), (153, true), (156, true), (157, true), (159, true), (163, true), (164, true), (165, true), (166, true), (170, true), (173, true), (174, true), (175, true), (172, true), (437, true), (179, true), (141, true), (140, true), (216, true), (177, true)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c699, c686, c681, c679, c678, c685, c684, c683, c697, c694, c692, c691, c695, c689, c884, c883, c882, c885, c724, c726, c720, c721, c707, c708, c718, c719, c713, c706, c703, c704, c717, c716, c712, c705, c702, c1498] c1591 (by decide) p (sat_cons (step699 p h) (sat_cons (step686 p h) (sat_cons (step681 p h) (sat_cons (step679 p h) (sat_cons (step678 p h) (sat_cons (step685 p h) (sat_cons (step684 p h) (sat_cons (step683 p h) (sat_cons (step697 p h) (sat_cons (step694 p h) (sat_cons (step692 p h) (sat_cons (step691 p h) (sat_cons (step695 p h) (sat_cons (step689 p h) (sat_cons (step884 p h) (sat_cons (step883 p h) (sat_cons (step882 p h) (sat_cons (step885 p h) (sat_cons (step724 p h) (sat_cons (step726 p h) (sat_cons (step720 p h) (sat_cons (step721 p h) (sat_cons (step707 p h) (sat_cons (step708 p h) (sat_cons (step718 p h) (sat_cons (step719 p h) (sat_cons (step713 p h) (sat_cons (step706 p h) (sat_cons (step703 p h) (sat_cons (step704 p h) (sat_cons (step717 p h) (sat_cons (step716 p h) (sat_cons (step712 p h) (sat_cons (step705 p h) (sat_cons (step702 p h) (sat_cons (step1498 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1592 : List Lit := [(1505, true), (50, false), (46, true), (150, true), (163, true), (30, true)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c644, c1037, c1040, c215, c1046, c1049, c1041, c1033, c1039, c164, c201, c206] c1592 (by decide) p (sat_cons (step644 p h) (sat_cons (step1037 p h) (sat_cons (step1040 p h) (sat_cons (step215 p h) (sat_cons (step1046 p h) (sat_cons (step1049 p h) (sat_cons (step1041 p h) (sat_cons (step1033 p h) (sat_cons (step1039 p h) (sat_cons (step164 p h) (sat_cons (step201 p h) (sat_cons (step206 p h) (sat_nil p)))))))))))))
def c1593 : List Lit := [(52, false), (1593, true), (170, true), (17, false)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c1549, c233, c376, c1201, c1193] c1593 (by decide) p (sat_cons (step1549 p h) (sat_cons (step233 p h) (sat_cons (step376 p h) (sat_cons (step1201 p h) (sat_cons (step1193 p h) (sat_nil p))))))
def c1594 : List Lit := [(1652, true), (457, true)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c899, c896, c898, c897, c1319, c1321, c1507, c1314, c1302, c1311, c1312, c1294, c1448, c608] c1594 (by decide) p (sat_cons (step899 p h) (sat_cons (step896 p h) (sat_cons (step898 p h) (sat_cons (step897 p h) (sat_cons (step1319 p h) (sat_cons (step1321 p h) (sat_cons (step1507 p h) (sat_cons (step1314 p h) (sat_cons (step1302 p h) (sat_cons (step1311 p h) (sat_cons (step1312 p h) (sat_cons (step1294 p h) (sat_cons (step1448 p h) (sat_cons (step608 p h) (sat_nil p)))))))))))))))
def c1595 : List Lit := [(104, false), (1644, true), (84, true), (222, true), (65, true), (36, true)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c1309, c1308, c568, c597] c1595 (by decide) p (sat_cons (step1309 p h) (sat_cons (step1308 p h) (sat_cons (step568 p h) (sat_cons (step597 p h) (sat_nil p)))))
def c1596 : List Lit := [(1648, true), (84, true), (222, true), (1641, true), (65, true), (36, true)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c1480, c1305, c1314, c1316, c1311, c1312, c1595, c1295, c1296, c1303, c610, c1298, c608, c579, c896, c1508, c900, c897] c1596 (by decide) p (sat_cons (step1480 p h) (sat_cons (step1305 p h) (sat_cons (step1314 p h) (sat_cons (step1316 p h) (sat_cons (step1311 p h) (sat_cons (step1312 p h) (sat_cons (step1595 p h) (sat_cons (step1295 p h) (sat_cons (step1296 p h) (sat_cons (step1303 p h) (sat_cons (step610 p h) (sat_cons (step1298 p h) (sat_cons (step608 p h) (sat_cons (step579 p h) (sat_cons (step896 p h) (sat_cons (step1508 p h) (sat_cons (step900 p h) (sat_cons (step897 p h) (sat_nil p)))))))))))))))))))
def c1597 : List Lit := [(84, true), (222, true), (1653, true), (65, true), (36, true)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c1480, c1324, c1320, c1596, c1322, c1300, c1302, c1298, c1294, c1295, c1595, c1317, c1311, c1312, c579, c610, c1508, c608, c897, c896, c900] c1597 (by decide) p (sat_cons (step1480 p h) (sat_cons (step1324 p h) (sat_cons (step1320 p h) (sat_cons (step1596 p h) (sat_cons (step1322 p h) (sat_cons (step1300 p h) (sat_cons (step1302 p h) (sat_cons (step1298 p h) (sat_cons (step1294 p h) (sat_cons (step1295 p h) (sat_cons (step1595 p h) (sat_cons (step1317 p h) (sat_cons (step1311 p h) (sat_cons (step1312 p h) (sat_cons (step579 p h) (sat_cons (step610 p h) (sat_cons (step1508 p h) (sat_cons (step608 p h) (sat_cons (step897 p h) (sat_cons (step896 p h) (sat_cons (step900 p h) (sat_nil p))))))))))))))))))))))
def c1598 : List Lit := [(104, true), (235, true), (1653, true)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c1324, c1305, c1295, c1296, c1302, c1303, c1322, c1298, c1314, c1311, c1508, c579] c1598 (by decide) p (sat_cons (step1324 p h) (sat_cons (step1305 p h) (sat_cons (step1295 p h) (sat_cons (step1296 p h) (sat_cons (step1302 p h) (sat_cons (step1303 p h) (sat_cons (step1322 p h) (sat_cons (step1298 p h) (sat_cons (step1314 p h) (sat_cons (step1311 p h) (sat_cons (step1508 p h) (sat_cons (step579 p h) (sat_nil p)))))))))))))
def c1599 : List Lit := [(1, false), (15, true), (3, true)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c618, c2] c1599 (by decide) p (sat_cons (step618 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1600 : List Lit := [(4, false), (8, true), (55, true), (11, true), (19, true)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c619, c28] c1600 (by decide) p (sat_cons (step619 p h) (sat_cons (step28 p h) (sat_nil p)))
def c1601 : List Lit := [(5, false), (7, true)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c620, c29] c1601 (by decide) p (sat_cons (step620 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1602 : List Lit := [(5, false), (2, true)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c620, c30] c1602 (by decide) p (sat_cons (step620 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1603 : List Lit := [(6, false), (7, true), (8, true)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c621, c32] c1603 (by decide) p (sat_cons (step621 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1604 : List Lit := [(6, false), (8, true), (3, true)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c621, c33] c1604 (by decide) p (sat_cons (step621 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1605 : List Lit := [(9, false), (64, true), (35, true)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c622, c43] c1605 (by decide) p (sat_cons (step622 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1606 : List Lit := [(64, true), (2, true), (9, false)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c622, c44] c1606 (by decide) p (sat_cons (step622 p h) (sat_cons (step44 p h) (sat_nil p)))
def c1607 : List Lit := [(10, false), (11, true)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c623, c45] c1607 (by decide) p (sat_cons (step623 p h) (sat_cons (step45 p h) (sat_nil p)))
def c1608 : List Lit := [(68, true), (39, true), (12, false)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c624, c54] c1608 (by decide) p (sat_cons (step624 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1609 : List Lit := [(13, true), (39, true), (12, false)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c624, c55] c1609 (by decide) p (sat_cons (step624 p h) (sat_cons (step55 p h) (sat_nil p)))
def c1610 : List Lit := [(14, false), (11, true)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c625, c60] c1610 (by decide) p (sat_cons (step625 p h) (sat_cons (step60 p h) (sat_nil p)))
def c1611 : List Lit := [(23, true), (3, true), (82, true), (15, true), (19, true), (16, false)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c626, c84] c1611 (by decide) p (sat_cons (step626 p h) (sat_cons (step84 p h) (sat_nil p)))
def c1612 : List Lit := [(29, true), (20, false), (19, true), (85, true), (17, true)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c628, c112] c1612 (by decide) p (sat_cons (step628 p h) (sat_cons (step112 p h) (sat_nil p)))
def c1613 : List Lit := [(25, false), (24, true), (90, true), (23, true)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c630, c143] c1613 (by decide) p (sat_cons (step630 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1614 : List Lit := [(25, false), (24, true), (90, true), (19, true)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c630, c144] c1614 (by decide) p (sat_cons (step630 p h) (sat_cons (step144 p h) (sat_nil p)))
def c1615 : List Lit := [(25, false), (23, true), (19, true), (90, true)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c630, c145] c1615 (by decide) p (sat_cons (step630 p h) (sat_cons (step145 p h) (sat_nil p)))
def c1616 : List Lit := [(28, false), (29, true)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c632, c150] c1616 (by decide) p (sat_cons (step632 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1617 : List Lit := [(28, false), (27, true)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c632, c151] c1617 (by decide) p (sat_cons (step632 p h) (sat_cons (step151 p h) (sat_nil p)))
def c1618 : List Lit := [(30, false), (32, true)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c633, c155] c1618 (by decide) p (sat_cons (step633 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1619 : List Lit := [(30, false), (22, true)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c633, c156] c1619 (by decide) p (sat_cons (step633 p h) (sat_cons (step156 p h) (sat_nil p)))
def c1620 : List Lit := [(33, false), (32, true)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c635, c165] c1620 (by decide) p (sat_cons (step635 p h) (sat_cons (step165 p h) (sat_nil p)))
def c1621 : List Lit := [(33, false), (29, true)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c635, c166] c1621 (by decide) p (sat_cons (step635 p h) (sat_cons (step166 p h) (sat_nil p)))
def c1622 : List Lit := [(34, false), (35, true), (15, true)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c636, c168] c1622 (by decide) p (sat_cons (step636 p h) (sat_cons (step168 p h) (sat_nil p)))
def c1623 : List Lit := [(42, false), (41, true)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c640, c195] c1623 (by decide) p (sat_cons (step640 p h) (sat_cons (step195 p h) (sat_nil p)))
def c1624 : List Lit := [(43, false), (35, true)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c641, c197] c1624 (by decide) p (sat_cons (step641 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1625 : List Lit := [(49, false), (48, true)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c643, c212] c1625 (by decide) p (sat_cons (step643 p h) (sat_cons (step212 p h) (sat_nil p)))
def c1626 : List Lit := [(49, false), (41, true)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c643, c213] c1626 (by decide) p (sat_cons (step643 p h) (sat_cons (step213 p h) (sat_nil p)))
def c1627 : List Lit := [(47, true), (46, true), (50, false)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c644, c215] c1627 (by decide) p (sat_cons (step644 p h) (sat_cons (step215 p h) (sat_nil p)))
def c1628 : List Lit := [(56, true), (55, true), (82, true), (51, false), (52, true)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c645, c226] c1628 (by decide) p (sat_cons (step645 p h) (sat_cons (step226 p h) (sat_nil p)))
def c1629 : List Lit := [(56, true), (51, false), (55, true), (3, true), (82, true)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c645, c227] c1629 (by decide) p (sat_cons (step645 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1630 : List Lit := [(56, true), (51, false), (3, true), (52, true), (82, true)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c645, c228] c1630 (by decide) p (sat_cons (step645 p h) (sat_cons (step228 p h) (sat_nil p)))
def c1631 : List Lit := [(51, false), (55, true), (3, true), (82, true), (52, true)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c645, c229] c1631 (by decide) p (sat_cons (step645 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1632 : List Lit := [(57, true), (55, true), (59, true), (53, false)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c646, c237] c1632 (by decide) p (sat_cons (step646 p h) (sat_cons (step237 p h) (sat_nil p)))
def c1633 : List Lit := [(53, false), (57, true), (54, true), (59, true)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c646, c238] c1633 (by decide) p (sat_cons (step646 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1634 : List Lit := [(57, true), (55, true), (53, false), (54, true)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c646, c239] c1634 (by decide) p (sat_cons (step646 p h) (sat_cons (step239 p h) (sat_nil p)))
def c1635 : List Lit := [(58, false), (57, true), (56, true), (90, true)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c647, c273] c1635 (by decide) p (sat_cons (step647 p h) (sat_cons (step273 p h) (sat_nil p)))
def c1636 : List Lit := [(58, false), (57, true), (55, true), (90, true)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c647, c274] c1636 (by decide) p (sat_cons (step647 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1637 : List Lit := [(56, true), (58, false), (55, true), (90, true)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c647, c275] c1637 (by decide) p (sat_cons (step647 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1638 : List Lit := [(54, true), (60, false), (59, true)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c648, c281] c1638 (by decide) p (sat_cons (step648 p h) (sat_cons (step281 p h) (sat_nil p)))
def c1639 : List Lit := [(179, true), (60, true)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c1450, c282] c1639 (by decide) p (sat_cons (step1450 p h) (sat_cons (step282 p h) (sat_nil p)))
def c1640 : List Lit := [(63, false), (68, true)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c649, c285] c1640 (by decide) p (sat_cons (step649 p h) (sat_cons (step285 p h) (sat_nil p)))
def c1641 : List Lit := [(63, false), (64, true)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c649, c286] c1641 (by decide) p (sat_cons (step649 p h) (sat_cons (step286 p h) (sat_nil p)))
end B112E027
