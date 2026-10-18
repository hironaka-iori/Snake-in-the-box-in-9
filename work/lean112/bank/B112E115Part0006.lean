import B112E115Part0005
namespace B112E115
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1623 : List Lit := [(945, false), (977, true)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c1294, c1113] c1623 (by decide) p (sat_cons (step1294 p h) (sat_cons (step1113 p h) (sat_nil p)))
def c1624 : List Lit := [(946, false), (978, true)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c1294, c1117] c1624 (by decide) p (sat_cons (step1294 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c1625 : List Lit := [(947, false), (979, true)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c1294, c1120] c1625 (by decide) p (sat_cons (step1294 p h) (sat_cons (step1120 p h) (sat_nil p)))
def c1626 : List Lit := [(1036, false), (1052, true)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1164] c1626 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1164 p h) (sat_nil p)))
def c1627 : List Lit := [(1037, false), (1053, true)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1165] c1627 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1165 p h) (sat_nil p)))
def c1628 : List Lit := [(1038, false), (1054, true)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1166] c1628 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c1629 : List Lit := [(915, false), (1059, false)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1198] c1629 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1198 p h) (sat_nil p)))
def c1630 : List Lit := [(916, false), (1058, false)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1199] c1630 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1199 p h) (sat_nil p)))
def c1631 : List Lit := [(917, false), (1057, false)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1200] c1631 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1200 p h) (sat_nil p)))
def c1632 : List Lit := [(918, false), (1056, false)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1201] c1632 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1201 p h) (sat_nil p)))
def c1633 : List Lit := [(919, false), (1055, false)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1202] c1633 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1202 p h) (sat_nil p)))
def c1634 : List Lit := [(920, false), (1054, false)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1203] c1634 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1203 p h) (sat_nil p)))
def c1635 : List Lit := [(921, false), (1053, false)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1204] c1635 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1204 p h) (sat_nil p)))
def c1636 : List Lit := [(922, false), (1052, false)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1205] c1636 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1205 p h) (sat_nil p)))
def c1637 : List Lit := [(899, false), (7, true), (945, false), (1035, false), (2, false), (24, false)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c1375, c1373] c1637 (by decide) p (sat_cons (step1375 p h) (sat_cons (step1373 p h) (sat_nil p)))
def c1638 : List Lit := [(11, false), (21, false), (7, false), (19, false)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c1336, c194] c1638 (by decide) p (sat_cons (step1336 p h) (sat_cons (step194 p h) (sat_nil p)))
def c1639 : List Lit := [(9, false), (6, true), (22, false), (18, false)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c1494, c175] c1639 (by decide) p (sat_cons (step1494 p h) (sat_cons (step175 p h) (sat_nil p)))
def c1640 : List Lit := [(12, false), (819, true), (805, true), (18, false)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c775, c1318, c115, c742] c1640 (by decide) p (sat_cons (step775 p h) (sat_cons (step1318 p h) (sat_cons (step115 p h) (sat_cons (step742 p h) (sat_nil p)))))
def c1641 : List Lit := [(803, false), (799, false), (843, true), (827, false), (22, false), (2, true), (18, false)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c793, c836, c759, c1317, c750, c749, c758, c831, c797, c775, c178, c1640, c1507, c1502, c163, c742] c1641 (by decide) p (sat_cons (step793 p h) (sat_cons (step836 p h) (sat_cons (step759 p h) (sat_cons (step1317 p h) (sat_cons (step750 p h) (sat_cons (step749 p h) (sat_cons (step758 p h) (sat_cons (step831 p h) (sat_cons (step797 p h) (sat_cons (step775 p h) (sat_cons (step178 p h) (sat_cons (step1640 p h) (sat_cons (step1507 p h) (sat_cons (step1502 p h) (sat_cons (step163 p h) (sat_cons (step742 p h) (sat_nil p)))))))))))))))))
def c1642 : List Lit := [(9, false), (22, false), (18, false), (7, false)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c66, c1494, c175] c1642 (by decide) p (sat_cons (step66 p h) (sat_cons (step1494 p h) (sat_cons (step175 p h) (sat_nil p))))
def c1643 : List Lit := [(898, true), (853, false), (875, false), (858, false), (19, false)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c860, c873, c914, c944, c939, c874, c915, c863, c904, c854, c1452] c1643 (by decide) p (sat_cons (step860 p h) (sat_cons (step873 p h) (sat_cons (step914 p h) (sat_cons (step944 p h) (sat_cons (step939 p h) (sat_cons (step874 p h) (sat_cons (step915 p h) (sat_cons (step863 p h) (sat_cons (step904 p h) (sat_cons (step854 p h) (sat_cons (step1452 p h) (sat_nil p))))))))))))
def c1644 : List Lit := [(879, true), (22, false), (19, false)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c896, c1300, c214] c1644 (by decide) p (sat_cons (step896 p h) (sat_cons (step1300 p h) (sat_cons (step214 p h) (sat_nil p))))
def c1645 : List Lit := [(36, true), (33, false), (38, false), (23, true)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c1524, c1522, c1230] c1645 (by decide) p (sat_cons (step1524 p h) (sat_cons (step1522 p h) (sat_cons (step1230 p h) (sat_nil p))))
def c1646 : List Lit := [(799, true), (12, true), (6, true), (7, false)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c732, c734, c730, c1487, c5] c1646 (by decide) p (sat_cons (step732 p h) (sat_cons (step734 p h) (sat_cons (step730 p h) (sat_cons (step1487 p h) (sat_cons (step5 p h) (sat_nil p))))))
def c1647 : List Lit := [(1052, true), (1001, false)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c1280, c1626, c1168, c1160, c1620, c1277, c1297, c1269, c1131] c1647 (by decide) p (sat_cons (step1280 p h) (sat_cons (step1626 p h) (sat_cons (step1168 p h) (sat_cons (step1160 p h) (sat_cons (step1620 p h) (sat_cons (step1277 p h) (sat_cons (step1297 p h) (sat_cons (step1269 p h) (sat_cons (step1131 p h) (sat_nil p))))))))))
def c1648 : List Lit := [(881, true), (939, true), (39, false)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c1033, c899, c900, c1465, c355, c1549, c375, c1022, c1024, c1031, c422, c1026] c1648 (by decide) p (sat_cons (step1033 p h) (sat_cons (step899 p h) (sat_cons (step900 p h) (sat_cons (step1465 p h) (sat_cons (step355 p h) (sat_cons (step1549 p h) (sat_cons (step375 p h) (sat_cons (step1022 p h) (sat_cons (step1024 p h) (sat_cons (step1031 p h) (sat_cons (step422 p h) (sat_cons (step1026 p h) (sat_nil p)))))))))))))
def c1649 : List Lit := [(934, true), (57, true), (59, false)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c1022, c1023, c446, c1560] c1649 (by decide) p (sat_cons (step1022 p h) (sat_cons (step1023 p h) (sat_cons (step446 p h) (sat_cons (step1560 p h) (sat_nil p)))))
def c1650 : List Lit := [(59, false), (934, true), (39, false)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c1023, c1649, c360] c1650 (by decide) p (sat_cons (step1023 p h) (sat_cons (step1649 p h) (sat_cons (step360 p h) (sat_nil p))))
def c1651 : List Lit := [(61, true), (59, true), (30, false), (943, true)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c1044, c1019, c1481, c1020, c1040, c385, c1015, c1028, c403, c1025, c1026, c1563, c455] c1651 (by decide) p (sat_cons (step1044 p h) (sat_cons (step1019 p h) (sat_cons (step1481 p h) (sat_cons (step1020 p h) (sat_cons (step1040 p h) (sat_cons (step385 p h) (sat_cons (step1015 p h) (sat_cons (step1028 p h) (sat_cons (step403 p h) (sat_cons (step1025 p h) (sat_cons (step1026 p h) (sat_cons (step1563 p h) (sat_cons (step455 p h) (sat_nil p))))))))))))))
def c1652 : List Lit := [(64, true), (865, false), (875, false), (70, false), (73, false), (882, false), (824, false), (106, true), (59, true), (68, false), (930, true)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.TreeRup.prove_clause [c1131, c1269, c1379, c1564, c1563, c454, c451, c455, c897, c1015, c1016, c906, c1017, c1558, c917, c1039, c387, c941, c1620, c655, c656, c660, c670, c686, c1610, c716, c712, c714, c709, c700, c704, c699, c701, c697, c698, c1590, c516, c1592, c517, c1140, c1589, c1273, c1267, c1150, c1137, c1157, c1153, c1170, c1158, c1634, c979, c1363, c1474, c1468, c1407, c813, c1053, c964, c1292, c1632, c1099, c1175] c1652 (by decide) p (sat_cons (step1131 p h) (sat_cons (step1269 p h) (sat_cons (step1379 p h) (sat_cons (step1564 p h) (sat_cons (step1563 p h) (sat_cons (step454 p h) (sat_cons (step451 p h) (sat_cons (step455 p h) (sat_cons (step897 p h) (sat_cons (step1015 p h) (sat_cons (step1016 p h) (sat_cons (step906 p h) (sat_cons (step1017 p h) (sat_cons (step1558 p h) (sat_cons (step917 p h) (sat_cons (step1039 p h) (sat_cons (step387 p h) (sat_cons (step941 p h) (sat_cons (step1620 p h) (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step660 p h) (sat_cons (step670 p h) (sat_cons (step686 p h) (sat_cons (step1610 p h) (sat_cons (step716 p h) (sat_cons (step712 p h) (sat_cons (step714 p h) (sat_cons (step709 p h) (sat_cons (step700 p h) (sat_cons (step704 p h) (sat_cons (step699 p h) (sat_cons (step701 p h) (sat_cons (step697 p h) (sat_cons (step698 p h) (sat_cons (step1590 p h) (sat_cons (step516 p h) (sat_cons (step1592 p h) (sat_cons (step517 p h) (sat_cons (step1140 p h) (sat_cons (step1589 p h) (sat_cons (step1273 p h) (sat_cons (step1267 p h) (sat_cons (step1150 p h) (sat_cons (step1137 p h) (sat_cons (step1157 p h) (sat_cons (step1153 p h) (sat_cons (step1170 p h) (sat_cons (step1158 p h) (sat_cons (step1634 p h) (sat_cons (step979 p h) (sat_cons (step1363 p h) (sat_cons (step1474 p h) (sat_cons (step1468 p h) (sat_cons (step1407 p h) (sat_cons (step813 p h) (sat_cons (step1053 p h) (sat_cons (step964 p h) (sat_cons (step1292 p h) (sat_cons (step1632 p h) (sat_cons (step1099 p h) (sat_cons (step1175 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1653 : List Lit := [(936, true), (860, false), (882, false), (824, false), (106, true), (59, true), (30, false), (934, true), (930, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c1023, c1022, c1025, c1026, c424, c1559, c442, c445, c846, c887, c849, c889, c873, c1652, c406, c404, c1016] c1653 (by decide) p (sat_cons (step1023 p h) (sat_cons (step1022 p h) (sat_cons (step1025 p h) (sat_cons (step1026 p h) (sat_cons (step424 p h) (sat_cons (step1559 p h) (sat_cons (step442 p h) (sat_cons (step445 p h) (sat_cons (step846 p h) (sat_cons (step887 p h) (sat_cons (step849 p h) (sat_cons (step889 p h) (sat_cons (step873 p h) (sat_cons (step1652 p h) (sat_cons (step406 p h) (sat_cons (step404 p h) (sat_cons (step1016 p h) (sat_nil p))))))))))))))))))
def c1654 : List Lit := [(929, true), (61, false), (30, false)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c1014, c1015, c1315, c403, c1556] c1654 (by decide) p (sat_cons (step1014 p h) (sat_cons (step1015 p h) (sat_cons (step1315 p h) (sat_cons (step403 p h) (sat_cons (step1556 p h) (sat_nil p))))))
def c1655 : List Lit := [(59, true), (30, false), (934, true), (943, true)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c1023, c1022, c1044, c1018, c1651, c1654, c1017, c1040, c1028, c1026, c424, c1561, c352, c368, c362, c374, c782, c901, c858, c1653, c860] c1655 (by decide) p (sat_cons (step1023 p h) (sat_cons (step1022 p h) (sat_cons (step1044 p h) (sat_cons (step1018 p h) (sat_cons (step1651 p h) (sat_cons (step1654 p h) (sat_cons (step1017 p h) (sat_cons (step1040 p h) (sat_cons (step1028 p h) (sat_cons (step1026 p h) (sat_cons (step424 p h) (sat_cons (step1561 p h) (sat_cons (step352 p h) (sat_cons (step368 p h) (sat_cons (step362 p h) (sat_cons (step374 p h) (sat_cons (step782 p h) (sat_cons (step901 p h) (sat_cons (step858 p h) (sat_cons (step1653 p h) (sat_cons (step860 p h) (sat_nil p))))))))))))))))))))))
def c1656 : List Lit := [(59, false), (934, true), (943, true)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c1023, c1022, c1649, c446, c371, c1559, c1019, c424, c1040, c1026, c1028] c1656 (by decide) p (sat_cons (step1023 p h) (sat_cons (step1022 p h) (sat_cons (step1649 p h) (sat_cons (step446 p h) (sat_cons (step371 p h) (sat_cons (step1559 p h) (sat_cons (step1019 p h) (sat_cons (step424 p h) (sat_cons (step1040 p h) (sat_cons (step1026 p h) (sat_cons (step1028 p h) (sat_nil p))))))))))))
def c1657 : List Lit := [(943, true), (61, true)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c1019, c1044, c1040, c1020, c1028, c1014, c1015, c1025, c1026, c415, c455, c1563] c1657 (by decide) p (sat_cons (step1019 p h) (sat_cons (step1044 p h) (sat_cons (step1040 p h) (sat_cons (step1020 p h) (sat_cons (step1028 p h) (sat_cons (step1014 p h) (sat_cons (step1015 p h) (sat_cons (step1025 p h) (sat_cons (step1026 p h) (sat_cons (step415 p h) (sat_cons (step455 p h) (sat_cons (step1563 p h) (sat_nil p)))))))))))))
def c1658 : List Lit := [(929, true), (936, true)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c1026, c1025, c1014, c1015, c415, c455, c1563] c1658 (by decide) p (sat_cons (step1026 p h) (sat_cons (step1025 p h) (sat_cons (step1014 p h) (sat_cons (step1015 p h) (sat_cons (step415 p h) (sat_cons (step455 p h) (sat_cons (step1563 p h) (sat_nil p))))))))
def c1659 : List Lit := [(65, false), (62, true), (64, true), (61, true), (59, true)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1557, c387, c398, c655, c657, c656, c658, c1604] c1659 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1557 p h) (sat_cons (step387 p h) (sat_cons (step398 p h) (sat_cons (step655 p h) (sat_cons (step657 p h) (sat_cons (step656 p h) (sat_cons (step658 p h) (sat_cons (step1604 p h) (sat_nil p))))))))))
def c1660 : List Lit := [(25, true), (840, true), (841, true)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c781, c1363, c1474, c1468, c1410, c814, c783, c1356] c1660 (by decide) p (sat_cons (step781 p h) (sat_cons (step1363 p h) (sat_cons (step1474 p h) (sat_cons (step1468 p h) (sat_cons (step1410 p h) (sat_cons (step814 p h) (sat_cons (step783 p h) (sat_cons (step1356 p h) (sat_nil p)))))))))
def c1661 : List Lit := [(824, false), (839, true), (841, true)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c1379, c1363, c813, c1468] c1661 (by decide) p (sat_cons (step1379 p h) (sat_cons (step1363 p h) (sat_cons (step813 p h) (sat_cons (step1468 p h) (sat_nil p)))))
def c1662 : List Lit := [(919, true), (841, true), (890, false), (852, false), (57, false), (67, false), (30, true)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c850, c876, c941, c1617, c971, c957, c1660, c1511, c1512, c238, c592, c1383, c853, c880, c882, c947, c965, c1661, c782, c1303, c343, c855, c858, c863] c1662 (by decide) p (sat_cons (step850 p h) (sat_cons (step876 p h) (sat_cons (step941 p h) (sat_cons (step1617 p h) (sat_cons (step971 p h) (sat_cons (step957 p h) (sat_cons (step1660 p h) (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step238 p h) (sat_cons (step592 p h) (sat_cons (step1383 p h) (sat_cons (step853 p h) (sat_cons (step880 p h) (sat_cons (step882 p h) (sat_cons (step947 p h) (sat_cons (step965 p h) (sat_cons (step1661 p h) (sat_cons (step782 p h) (sat_cons (step1303 p h) (sat_cons (step343 p h) (sat_cons (step855 p h) (sat_cons (step858 p h) (sat_cons (step863 p h) (sat_nil p)))))))))))))))))))))))))
def c1663 : List Lit := [(64, true), (934, true), (936, true), (30, true), (61, true), (59, true)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c1022, c1023, c1026, c424, c1559, c442, c848, c850, c876, c445, c887, c889, c1561, c1025, c1564, c1563, c454, c451, c434, c455, c1138, c897, c1547, c1272, c901, c1275, c906, c1155, c917, c941, c1659, c1016, c1021, c1048, c1622, c1177, c1634, c979, c1662, c1633, c1181, c1178, c1109, c1156, c1292, c1149, c1053, c1269, c1131, c354, c782, c1363, c1474, c1407] c1663 (by decide) p (sat_cons (step1022 p h) (sat_cons (step1023 p h) (sat_cons (step1026 p h) (sat_cons (step424 p h) (sat_cons (step1559 p h) (sat_cons (step442 p h) (sat_cons (step848 p h) (sat_cons (step850 p h) (sat_cons (step876 p h) (sat_cons (step445 p h) (sat_cons (step887 p h) (sat_cons (step889 p h) (sat_cons (step1561 p h) (sat_cons (step1025 p h) (sat_cons (step1564 p h) (sat_cons (step1563 p h) (sat_cons (step454 p h) (sat_cons (step451 p h) (sat_cons (step434 p h) (sat_cons (step455 p h) (sat_cons (step1138 p h) (sat_cons (step897 p h) (sat_cons (step1547 p h) (sat_cons (step1272 p h) (sat_cons (step901 p h) (sat_cons (step1275 p h) (sat_cons (step906 p h) (sat_cons (step1155 p h) (sat_cons (step917 p h) (sat_cons (step941 p h) (sat_cons (step1659 p h) (sat_cons (step1016 p h) (sat_cons (step1021 p h) (sat_cons (step1048 p h) (sat_cons (step1622 p h) (sat_cons (step1177 p h) (sat_cons (step1634 p h) (sat_cons (step979 p h) (sat_cons (step1662 p h) (sat_cons (step1633 p h) (sat_cons (step1181 p h) (sat_cons (step1178 p h) (sat_cons (step1109 p h) (sat_cons (step1156 p h) (sat_cons (step1292 p h) (sat_cons (step1149 p h) (sat_cons (step1053 p h) (sat_cons (step1269 p h) (sat_cons (step1131 p h) (sat_cons (step354 p h) (sat_cons (step782 p h) (sat_cons (step1363 p h) (sat_cons (step1474 p h) (sat_cons (step1407 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1664 : List Lit := [(114, false), (68, false), (73, false)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c1595, c454] c1664 (by decide) p (sat_cons (step1595 p h) (sat_cons (step454 p h) (sat_nil p)))
def c1665 : List Lit := [(1055, true), (966, false), (114, true), (64, false), (73, false), (61, true)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c1657, c1104, c1138, c1272, c1275, c1155, c1178, c1156, c1276, c1273, c1140, c418, c1181, c1109, c417, c1016, c1048, c1021] c1665 (by decide) p (sat_cons (step1657 p h) (sat_cons (step1104 p h) (sat_cons (step1138 p h) (sat_cons (step1272 p h) (sat_cons (step1275 p h) (sat_cons (step1155 p h) (sat_cons (step1178 p h) (sat_cons (step1156 p h) (sat_cons (step1276 p h) (sat_cons (step1273 p h) (sat_cons (step1140 p h) (sat_cons (step418 p h) (sat_cons (step1181 p h) (sat_cons (step1109 p h) (sat_cons (step417 p h) (sat_cons (step1016 p h) (sat_cons (step1048 p h) (sat_cons (step1021 p h) (sat_nil p)))))))))))))))))))
def c1666 : List Lit := [(840, true), (901, true), (841, true), (824, false), (852, false), (48, true), (30, true), (881, false)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c902, c887, c889, c915, c955, c1363, c1468, c815, c1379, c1660, c818, c1511, c1399, c238, c858, c592, c860, c1383, c853, c882, c881, c863, c951, c854, c916, c920, c905, c890, c1453, c888] c1666 (by decide) p (sat_cons (step902 p h) (sat_cons (step887 p h) (sat_cons (step889 p h) (sat_cons (step915 p h) (sat_cons (step955 p h) (sat_cons (step1363 p h) (sat_cons (step1468 p h) (sat_cons (step815 p h) (sat_cons (step1379 p h) (sat_cons (step1660 p h) (sat_cons (step818 p h) (sat_cons (step1511 p h) (sat_cons (step1399 p h) (sat_cons (step238 p h) (sat_cons (step858 p h) (sat_cons (step592 p h) (sat_cons (step860 p h) (sat_cons (step1383 p h) (sat_cons (step853 p h) (sat_cons (step882 p h) (sat_cons (step881 p h) (sat_cons (step863 p h) (sat_cons (step951 p h) (sat_cons (step854 p h) (sat_cons (step916 p h) (sat_cons (step920 p h) (sat_cons (step905 p h) (sat_cons (step890 p h) (sat_cons (step1453 p h) (sat_cons (step888 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1667 : List Lit := [(855, false), (900, true), (48, true), (70, false), (883, false)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c887, c889, c915, c950, c880, c881, c946, c860, c920, c1432, c890, c888] c1667 (by decide) p (sat_cons (step887 p h) (sat_cons (step889 p h) (sat_cons (step915 p h) (sat_cons (step950 p h) (sat_cons (step880 p h) (sat_cons (step881 p h) (sat_cons (step946 p h) (sat_cons (step860 p h) (sat_cons (step920 p h) (sat_cons (step1432 p h) (sat_cons (step890 p h) (sat_cons (step888 p h) (sat_nil p)))))))))))))
def c1668 : List Lit := [(841, true), (824, false), (114, true), (64, false), (852, false), (48, true), (936, true), (30, true), (61, true), (881, false)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c902, c887, c889, c915, c850, c1026, c1025, c1363, c1474, c1661, c1410, c1407, c1053, c1292, c1665, c1633, c965, c1666, c971, c950, c878, c1667, c853, c1383, c592, c593, c238, c1511, c237, c783, c1384, c1356, c863, c819, c858, c1399] c1668 (by decide) p (sat_cons (step902 p h) (sat_cons (step887 p h) (sat_cons (step889 p h) (sat_cons (step915 p h) (sat_cons (step850 p h) (sat_cons (step1026 p h) (sat_cons (step1025 p h) (sat_cons (step1363 p h) (sat_cons (step1474 p h) (sat_cons (step1661 p h) (sat_cons (step1410 p h) (sat_cons (step1407 p h) (sat_cons (step1053 p h) (sat_cons (step1292 p h) (sat_cons (step1665 p h) (sat_cons (step1633 p h) (sat_cons (step965 p h) (sat_cons (step1666 p h) (sat_cons (step971 p h) (sat_cons (step950 p h) (sat_cons (step878 p h) (sat_cons (step1667 p h) (sat_cons (step853 p h) (sat_cons (step1383 p h) (sat_cons (step592 p h) (sat_cons (step593 p h) (sat_cons (step238 p h) (sat_cons (step1511 p h) (sat_cons (step237 p h) (sat_cons (step783 p h) (sat_cons (step1384 p h) (sat_cons (step1356 p h) (sat_cons (step863 p h) (sat_cons (step819 p h) (sat_cons (step858 p h) (sat_cons (step1399 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1669 : List Lit := [(858, true), (890, true), (934, true), (70, false), (59, true)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c1022, c1023, c424, c1559, c445, c1561, c858, c1432, c357, c888, c901, c890, c903, c921] c1669 (by decide) p (sat_cons (step1022 p h) (sat_cons (step1023 p h) (sat_cons (step424 p h) (sat_cons (step1559 p h) (sat_cons (step445 p h) (sat_cons (step1561 p h) (sat_cons (step858 p h) (sat_cons (step1432 p h) (sat_cons (step357 p h) (sat_cons (step888 p h) (sat_cons (step901 p h) (sat_cons (step890 p h) (sat_cons (step903 p h) (sat_cons (step921 p h) (sat_nil p)))))))))))))))
def c1670 : List Lit := [(900, true), (934, true), (70, false), (30, true), (59, true)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c899, c902, c1022, c1023, c424, c1559, c445, c887, c889, c915, c442, c848, c850, c876, c1561, c950, c941, c1667, c878, c853, c1383, c592, c593, c238, c1511, c1669, c860, c863, c877, c1384, c946, c237, c916, c347, c903, c901] c1670 (by decide) p (sat_cons (step899 p h) (sat_cons (step902 p h) (sat_cons (step1022 p h) (sat_cons (step1023 p h) (sat_cons (step424 p h) (sat_cons (step1559 p h) (sat_cons (step445 p h) (sat_cons (step887 p h) (sat_cons (step889 p h) (sat_cons (step915 p h) (sat_cons (step442 p h) (sat_cons (step848 p h) (sat_cons (step850 p h) (sat_cons (step876 p h) (sat_cons (step1561 p h) (sat_cons (step950 p h) (sat_cons (step941 p h) (sat_cons (step1667 p h) (sat_cons (step878 p h) (sat_cons (step853 p h) (sat_cons (step1383 p h) (sat_cons (step592 p h) (sat_cons (step593 p h) (sat_cons (step238 p h) (sat_cons (step1511 p h) (sat_cons (step1669 p h) (sat_cons (step860 p h) (sat_cons (step863 p h) (sat_cons (step877 p h) (sat_cons (step1384 p h) (sat_cons (step946 p h) (sat_cons (step237 p h) (sat_cons (step916 p h) (sat_cons (step347 p h) (sat_cons (step903 p h) (sat_cons (step901 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c1671 : List Lit := [(1054, true), (114, true), (64, false), (73, false), (61, true)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c1138, c1272, c1275, c1155, c1657, c1621, c1177, c1173, c1622, c1156, c1048, c1276, c1021, c1273, c1140, c418, c417, c1016] c1671 (by decide) p (sat_cons (step1138 p h) (sat_cons (step1272 p h) (sat_cons (step1275 p h) (sat_cons (step1155 p h) (sat_cons (step1657 p h) (sat_cons (step1621 p h) (sat_cons (step1177 p h) (sat_cons (step1173 p h) (sat_cons (step1622 p h) (sat_cons (step1156 p h) (sat_cons (step1048 p h) (sat_cons (step1276 p h) (sat_cons (step1021 p h) (sat_cons (step1273 p h) (sat_cons (step1140 p h) (sat_cons (step418 p h) (sat_cons (step417 p h) (sat_cons (step1016 p h) (sat_nil p)))))))))))))))))))
def c1672 : List Lit := [(934, true), (936, true), (30, true), (61, true), (59, true)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c1026, c1025, c899, c1022, c1023, c424, c1561, c1559, c442, c445, c848, c887, c850, c889, c1663, c1664, c1670, c1671, c1634, c979, c1668, c781, c782, c1511, c1512, c235, c229, c343, c347, c238, c855, c1317, c858, c901, c592, c743, c863, c903, c1383, c751, c878, c916, c853, c951, c882, c972, c956, c814, c966, c804, c1612, c1324, c756, c734] c1672 (by decide) p (sat_cons (step1026 p h) (sat_cons (step1025 p h) (sat_cons (step899 p h) (sat_cons (step1022 p h) (sat_cons (step1023 p h) (sat_cons (step424 p h) (sat_cons (step1561 p h) (sat_cons (step1559 p h) (sat_cons (step442 p h) (sat_cons (step445 p h) (sat_cons (step848 p h) (sat_cons (step887 p h) (sat_cons (step850 p h) (sat_cons (step889 p h) (sat_cons (step1663 p h) (sat_cons (step1664 p h) (sat_cons (step1670 p h) (sat_cons (step1671 p h) (sat_cons (step1634 p h) (sat_cons (step979 p h) (sat_cons (step1668 p h) (sat_cons (step781 p h) (sat_cons (step782 p h) (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step235 p h) (sat_cons (step229 p h) (sat_cons (step343 p h) (sat_cons (step347 p h) (sat_cons (step238 p h) (sat_cons (step855 p h) (sat_cons (step1317 p h) (sat_cons (step858 p h) (sat_cons (step901 p h) (sat_cons (step592 p h) (sat_cons (step743 p h) (sat_cons (step863 p h) (sat_cons (step903 p h) (sat_cons (step1383 p h) (sat_cons (step751 p h) (sat_cons (step878 p h) (sat_cons (step916 p h) (sat_cons (step853 p h) (sat_cons (step951 p h) (sat_cons (step882 p h) (sat_cons (step972 p h) (sat_cons (step956 p h) (sat_cons (step814 p h) (sat_cons (step966 p h) (sat_cons (step804 p h) (sat_cons (step1612 p h) (sat_cons (step1324 p h) (sat_cons (step756 p h) (sat_cons (step734 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1673 : List Lit := [(824, true), (57, false), (26, false), (919, true), (890, false), (854, false)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c876, c941, c971, c782, c1303, c229, c855, c1317, c862, c743, c877, c751, c947, c814, c965, c804, c1612, c1324, c756, c734] c1673 (by decide) p (sat_cons (step876 p h) (sat_cons (step941 p h) (sat_cons (step971 p h) (sat_cons (step782 p h) (sat_cons (step1303 p h) (sat_cons (step229 p h) (sat_cons (step855 p h) (sat_cons (step1317 p h) (sat_cons (step862 p h) (sat_cons (step743 p h) (sat_cons (step877 p h) (sat_cons (step751 p h) (sat_cons (step947 p h) (sat_cons (step814 p h) (sat_cons (step965 p h) (sat_cons (step804 p h) (sat_cons (step1612 p h) (sat_cons (step1324 p h) (sat_cons (step756 p h) (sat_cons (step734 p h) (sat_nil p)))))))))))))))))))))
def c1674 : List Lit := [(824, false), (39, false), (840, true), (841, true)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c1379, c1363, c818, c1399] c1674 (by decide) p (sat_cons (step1379 p h) (sat_cons (step1363 p h) (sat_cons (step818 p h) (sat_cons (step1399 p h) (sat_nil p)))))
def c1675 : List Lit := [(39, false), (919, true), (890, false), (854, false), (841, true)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c876, c941, c971, c1660, c1512, c1614, c1674, c782, c1673, c1509, c1401] c1675 (by decide) p (sat_cons (step876 p h) (sat_cons (step941 p h) (sat_cons (step971 p h) (sat_cons (step1660 p h) (sat_cons (step1512 p h) (sat_cons (step1614 p h) (sat_cons (step1674 p h) (sat_cons (step782 p h) (sat_cons (step1673 p h) (sat_cons (step1509 p h) (sat_cons (step1401 p h) (sat_nil p))))))))))))
def c1676 : List Lit := [(919, true), (890, false), (854, false), (841, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c876, c941, c971, c1660, c1512, c1675, c858, c860, c877, c947, c965, c1612, c1661, c782, c1673, c1509, c1409] c1676 (by decide) p (sat_cons (step876 p h) (sat_cons (step941 p h) (sat_cons (step971 p h) (sat_cons (step1660 p h) (sat_cons (step1512 p h) (sat_cons (step1675 p h) (sat_cons (step858 p h) (sat_cons (step860 p h) (sat_cons (step877 p h) (sat_cons (step947 p h) (sat_cons (step965 p h) (sat_cons (step1612 p h) (sat_cons (step1661 p h) (sat_cons (step782 p h) (sat_cons (step1673 p h) (sat_cons (step1509 p h) (sat_cons (step1409 p h) (sat_nil p))))))))))))))))))
def c1677 : List Lit := [(804, false), (840, true), (2, false), (24, false)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c1409, c818, c1334, c1369, c1613, c757, c743, c746, c761, c737, c738, c733, c1475, c1476, c731] c1677 (by decide) p (sat_cons (step1409 p h) (sat_cons (step818 p h) (sat_cons (step1334 p h) (sat_cons (step1369 p h) (sat_cons (step1613 p h) (sat_cons (step757 p h) (sat_cons (step743 p h) (sat_cons (step746 p h) (sat_cons (step761 p h) (sat_cons (step737 p h) (sat_cons (step738 p h) (sat_cons (step733 p h) (sat_cons (step1475 p h) (sat_cons (step1476 p h) (sat_cons (step731 p h) (sat_nil p))))))))))))))))
def c1678 : List Lit := [(840, true), (2, false), (24, false)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c1613, c765, c1677, c741, c14, c24, c30, c736, c731] c1678 (by decide) p (sat_cons (step1613 p h) (sat_cons (step765 p h) (sat_cons (step1677 p h) (sat_cons (step741 p h) (sat_cons (step14 p h) (sat_cons (step24 p h) (sat_cons (step30 p h) (sat_cons (step736 p h) (sat_cons (step731 p h) (sat_nil p))))))))))
def c1679 : List Lit := [(804, true), (856, false), (2, false), (24, false), (890, false), (854, false)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c740, c741, c36, c14, c37, c24, c30, c858, c1053, c731, c863, c1292, c736, c878, c1343, c765, c952, c1636, c981, c1614, c824, c766, c800, c1334, c745, c1471, c737, c738, c1500, c141, c770, c773, c776, c796, c171, c786, c1493, c779, c96] c1679 (by decide) p (sat_cons (step740 p h) (sat_cons (step741 p h) (sat_cons (step36 p h) (sat_cons (step14 p h) (sat_cons (step37 p h) (sat_cons (step24 p h) (sat_cons (step30 p h) (sat_cons (step858 p h) (sat_cons (step1053 p h) (sat_cons (step731 p h) (sat_cons (step863 p h) (sat_cons (step1292 p h) (sat_cons (step736 p h) (sat_cons (step878 p h) (sat_cons (step1343 p h) (sat_cons (step765 p h) (sat_cons (step952 p h) (sat_cons (step1636 p h) (sat_cons (step981 p h) (sat_cons (step1614 p h) (sat_cons (step824 p h) (sat_cons (step766 p h) (sat_cons (step800 p h) (sat_cons (step1334 p h) (sat_cons (step745 p h) (sat_cons (step1471 p h) (sat_cons (step737 p h) (sat_cons (step738 p h) (sat_cons (step1500 p h) (sat_cons (step141 p h) (sat_cons (step770 p h) (sat_cons (step773 p h) (sat_cons (step776 p h) (sat_cons (step796 p h) (sat_cons (step171 p h) (sat_cons (step786 p h) (sat_cons (step1493 p h) (sat_cons (step779 p h) (sat_cons (step96 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1680 : List Lit := [(938, true), (57, true)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c1028, c1030, c1026, c1022, c1023, c424, c1561] c1680 (by decide) p (sat_cons (step1028 p h) (sat_cons (step1030 p h) (sat_cons (step1026 p h) (sat_cons (step1022 p h) (sat_cons (step1023 p h) (sat_cons (step424 p h) (sat_cons (step1561 p h) (sat_nil p))))))))
def c1681 : List Lit := [(943, false), (841, false), (856, false), (2, false), (24, false), (890, false), (854, false)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c862, c877, c947, c980, c1635, c1283, c1621, c1104, c1282, c1292, c1636, c1053, c981, c39, c952, c858, c878, c863] c1681 (by decide) p (sat_cons (step862 p h) (sat_cons (step877 p h) (sat_cons (step947 p h) (sat_cons (step980 p h) (sat_cons (step1635 p h) (sat_cons (step1283 p h) (sat_cons (step1621 p h) (sat_cons (step1104 p h) (sat_cons (step1282 p h) (sat_cons (step1292 p h) (sat_cons (step1636 p h) (sat_cons (step1053 p h) (sat_cons (step981 p h) (sat_cons (step39 p h) (sat_cons (step952 p h) (sat_cons (step858 p h) (sat_cons (step878 p h) (sat_cons (step863 p h) (sat_nil p)))))))))))))))))))
def c1682 : List Lit := [(943, true), (57, true)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c1680, c1657, c1040, c1553, c1017, c1315] c1682 (by decide) p (sat_cons (step1680 p h) (sat_cons (step1657 p h) (sat_cons (step1040 p h) (sat_cons (step1553 p h) (sat_cons (step1017 p h) (sat_cons (step1315 p h) (sat_nil p)))))))
def c1683 : List Lit := [(798, false), (841, true), (804, false)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c743, c1614, c766, c733, c761, c824, c762, c793, c1334, c746, c736, c789, c737, c738, c58, c1639, c1495, c780, c96] c1683 (by decide) p (sat_cons (step743 p h) (sat_cons (step1614 p h) (sat_cons (step766 p h) (sat_cons (step733 p h) (sat_cons (step761 p h) (sat_cons (step824 p h) (sat_cons (step762 p h) (sat_cons (step793 p h) (sat_cons (step1334 p h) (sat_cons (step746 p h) (sat_cons (step736 p h) (sat_cons (step789 p h) (sat_cons (step737 p h) (sat_cons (step738 p h) (sat_cons (step58 p h) (sat_cons (step1639 p h) (sat_cons (step1495 p h) (sat_cons (step780 p h) (sat_cons (step96 p h) (sat_nil p))))))))))))))))))))
def c1684 : List Lit := [(824, true), (57, true), (890, false), (854, false)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c1682, c781, c782, c1512, c1509, c235, c855, c1678, c1679, c1681, c1614, c1401, c858, c863, c878, c952, c1683, c973, c1635, c1283, c1104, c1292, c1053, c34, c28, c731] c1684 (by decide) p (sat_cons (step1682 p h) (sat_cons (step781 p h) (sat_cons (step782 p h) (sat_cons (step1512 p h) (sat_cons (step1509 p h) (sat_cons (step235 p h) (sat_cons (step855 p h) (sat_cons (step1678 p h) (sat_cons (step1679 p h) (sat_cons (step1681 p h) (sat_cons (step1614 p h) (sat_cons (step1401 p h) (sat_cons (step858 p h) (sat_cons (step863 p h) (sat_cons (step878 p h) (sat_cons (step952 p h) (sat_cons (step1683 p h) (sat_cons (step973 p h) (sat_cons (step1635 p h) (sat_cons (step1283 p h) (sat_cons (step1104 p h) (sat_cons (step1292 p h) (sat_cons (step1053 p h) (sat_cons (step34 p h) (sat_cons (step28 p h) (sat_cons (step731 p h) (sat_nil p)))))))))))))))))))))))))))
def c1685 : List Lit := [(18, false), (1, false), (823, true), (9, false), (11, false)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c58, c1639, c1495, c780, c96] c1685 (by decide) p (sat_cons (step58 p h) (sat_cons (step1639 p h) (sat_cons (step1495 p h) (sat_cons (step780 p h) (sat_cons (step96 p h) (sat_nil p))))))
def c1686 : List Lit := [(817, false), (23, true), (832, true), (824, false)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c784, c801, c773, c776, c797, c1335, c787, c778] c1686 (by decide) p (sat_cons (step784 p h) (sat_cons (step801 p h) (sat_cons (step773 p h) (sat_cons (step776 p h) (sat_cons (step797 p h) (sat_cons (step1335 p h) (sat_cons (step787 p h) (sat_cons (step778 p h) (sat_nil p)))))))))
end B112E115
