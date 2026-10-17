import B112E153Part0000
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1611 : List Lit := [(99, false), (96, false), (98, true), (89, true), (91, false)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c690, c398, c391] c1611 (by decide) p (sat_cons (step690 p h) (sat_cons (step398 p h) (sat_cons (step391 p h) (sat_nil p))))
def c1612 : List Lit := [(261, true), (5, true), (3, true)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c652, c707, c708, c17, c1549, c18] c1612 (by decide) p (sat_cons (step652 p h) (sat_cons (step707 p h) (sat_cons (step708 p h) (sat_cons (step17 p h) (sat_cons (step1549 p h) (sat_cons (step18 p h) (sat_nil p)))))))
def c1613 : List Lit := [(879, true), (92, true)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c656, c916, c918, c912, c898, c904, c905, c895, c57, c53] c1613 (by decide) p (sat_cons (step656 p h) (sat_cons (step916 p h) (sat_cons (step918 p h) (sat_cons (step912 p h) (sat_cons (step898 p h) (sat_cons (step904 p h) (sat_cons (step905 p h) (sat_cons (step895 p h) (sat_cons (step57 p h) (sat_cons (step53 p h) (sat_nil p)))))))))))
def c1614 : List Lit := [(889, true), (846, false)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c653, c886, c930, c926, c887, c916, c918, c878, c912, c898, c875, c905, c896, c19, c33] c1614 (by decide) p (sat_cons (step653 p h) (sat_cons (step886 p h) (sat_cons (step930 p h) (sat_cons (step926 p h) (sat_cons (step887 p h) (sat_cons (step916 p h) (sat_cons (step918 p h) (sat_cons (step878 p h) (sat_cons (step912 p h) (sat_cons (step898 p h) (sat_cons (step875 p h) (sat_cons (step905 p h) (sat_cons (step896 p h) (sat_cons (step19 p h) (sat_cons (step33 p h) (sat_nil p))))))))))))))))
def c1615 : List Lit := [(867, true), (89, true)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c655, c898, c900, c896, c893, c48, c49, c1500] c1615 (by decide) p (sat_cons (step655 p h) (sat_cons (step898 p h) (sat_cons (step900 p h) (sat_cons (step896 p h) (sat_cons (step893 p h) (sat_cons (step48 p h) (sat_cons (step49 p h) (sat_cons (step1500 p h) (sat_nil p)))))))))
def c1616 : List Lit := [(852, true), (19, false), (54, false)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c652, c878, c880, c876, c874, c18, c9] c1616 (by decide) p (sat_cons (step652 p h) (sat_cons (step878 p h) (sat_cons (step880 p h) (sat_cons (step876 p h) (sat_cons (step874 p h) (sat_cons (step18 p h) (sat_cons (step9 p h) (sat_nil p))))))))
def c1617 : List Lit := [(852, false), (20, true), (865, false), (891, true), (3, true), (867, false)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c657, c918, c935, c869, c1573, c887, c891, c932, c1574, c922, c919, c870, c899, c901, c912, c897, c893, c904, c36, c55, c62] c1617 (by decide) p (sat_cons (step657 p h) (sat_cons (step918 p h) (sat_cons (step935 p h) (sat_cons (step869 p h) (sat_cons (step1573 p h) (sat_cons (step887 p h) (sat_cons (step891 p h) (sat_cons (step932 p h) (sat_cons (step1574 p h) (sat_cons (step922 p h) (sat_cons (step919 p h) (sat_cons (step870 p h) (sat_cons (step899 p h) (sat_cons (step901 p h) (sat_cons (step912 p h) (sat_cons (step897 p h) (sat_cons (step893 p h) (sat_cons (step904 p h) (sat_cons (step36 p h) (sat_cons (step55 p h) (sat_cons (step62 p h) (sat_nil p))))))))))))))))))))))
def c1618 : List Lit := [(880, true), (12, false), (865, false), (867, false)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c653, c19, c922, c919, c901, c912, c893, c905, c32] c1618 (by decide) p (sat_cons (step653 p h) (sat_cons (step19 p h) (sat_cons (step922 p h) (sat_cons (step919 p h) (sat_cons (step901 p h) (sat_cons (step912 p h) (sat_cons (step893 p h) (sat_cons (step905 p h) (sat_cons (step32 p h) (sat_nil p))))))))))
def c1619 : List Lit := [(912, false), (920, true), (902, false)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c946, c970, c958, c961, c973, c952, c953, c947, c1591, c941] c1619 (by decide) p (sat_cons (step946 p h) (sat_cons (step970 p h) (sat_cons (step958 p h) (sat_cons (step961 p h) (sat_cons (step973 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step947 p h) (sat_cons (step1591 p h) (sat_cons (step941 p h) (sat_nil p)))))))))))
def c1620 : List Lit := [(1016, true), (90, false), (91, false)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c1120, c1121, c332] c1620 (by decide) p (sat_cons (step1120 p h) (sat_cons (step1121 p h) (sat_cons (step332 p h) (sat_nil p))))
def c1621 : List Lit := [(1081, true), (912, true)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c667, c956, c955, c1265, c1266, c123, c629, c128] c1621 (by decide) p (sat_cons (step667 p h) (sat_cons (step956 p h) (sat_cons (step955 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step123 p h) (sat_cons (step629 p h) (sat_cons (step128 p h) (sat_nil p)))))))))
def c1622 : List Lit := [(1091, true), (119, true), (1081, false), (113, true), (1072, false)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c698, c1268, c1252, c1260, c1290, c1294, c1271, c1261, c1262, c1263, c1253, c593, c584] c1622 (by decide) p (sat_cons (step698 p h) (sat_cons (step1268 p h) (sat_cons (step1252 p h) (sat_cons (step1260 p h) (sat_cons (step1290 p h) (sat_cons (step1294 p h) (sat_cons (step1271 p h) (sat_cons (step1261 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step1253 p h) (sat_cons (step593 p h) (sat_cons (step584 p h) (sat_nil p))))))))))))))
def c1623 : List Lit := [(889, true), (879, false)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c926, c1614, c1575, c1573, c878, c869, c876, c1548] c1623 (by decide) p (sat_cons (step926 p h) (sat_cons (step1614 p h) (sat_cons (step1575 p h) (sat_cons (step1573 p h) (sat_cons (step878 p h) (sat_cons (step869 p h) (sat_cons (step876 p h) (sat_cons (step1548 p h) (sat_nil p)))))))))
def c1624 : List Lit := [(1091, true), (1072, false), (1081, false), (81, false), (46, false), (113, true)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c698, c1252, c1260, c1290, c1622, c1271, c1262, c1263, c617, c1545, c592] c1624 (by decide) p (sat_cons (step698 p h) (sat_cons (step1252 p h) (sat_cons (step1260 p h) (sat_cons (step1290 p h) (sat_cons (step1622 p h) (sat_cons (step1271 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step617 p h) (sat_cons (step1545 p h) (sat_cons (step592 p h) (sat_nil p))))))))))))
def c1625 : List Lit := [(108, false), (1072, true), (86, false), (109, false)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c500, c501, c1250] c1625 (by decide) p (sat_cons (step500 p h) (sat_cons (step501 p h) (sat_cons (step1250 p h) (sat_nil p))))
def c1626 : List Lit := [(65, false), (108, false), (67, true), (66, true)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c677, c203, c204, c1514] c1626 (by decide) p (sat_cons (step677 p h) (sat_cons (step203 p h) (sat_cons (step204 p h) (sat_cons (step1514 p h) (sat_nil p)))))
def c1627 : List Lit := [(100, false), (1085, true), (124, false), (81, false), (123, true)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c631, c632, c1262, c1267, c1272] c1627 (by decide) p (sat_cons (step631 p h) (sat_cons (step632 p h) (sat_cons (step1262 p h) (sat_cons (step1267 p h) (sat_cons (step1272 p h) (sat_nil p))))))
def c1628 : List Lit := [(1084, true), (124, false), (81, false), (123, true)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c1265, c1269, c1271, c1267, c1262, c637] c1628 (by decide) p (sat_cons (step1265 p h) (sat_cons (step1269 p h) (sat_cons (step1271 p h) (sat_cons (step1267 p h) (sat_cons (step1262 p h) (sat_cons (step637 p h) (sat_nil p)))))))
def c1629 : List Lit := [(93, false), (82, false), (94, false), (97, true)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c688, c371, c366] c1629 (by decide) p (sat_cons (step688 p h) (sat_cons (step371 p h) (sat_cons (step366 p h) (sat_nil p))))
def c1630 : List Lit := [(939, true), (94, false), (55, true)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c675, c993, c1003, c1001, c994, c995, c996, c175, c182, c188] c1630 (by decide) p (sat_cons (step675 p h) (sat_cons (step993 p h) (sat_cons (step1003 p h) (sat_cons (step1001 p h) (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step996 p h) (sat_cons (step175 p h) (sat_cons (step182 p h) (sat_cons (step188 p h) (sat_nil p)))))))))))
def c1631 : List Lit := [(105, false), (115, false), (92, true), (82, false), (117, false)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c696, c430, c578, c577] c1631 (by decide) p (sat_cons (step696 p h) (sat_cons (step430 p h) (sat_cons (step578 p h) (sat_cons (step577 p h) (sat_nil p)))))
def c1632 : List Lit := [(919, true), (912, false)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c958, c966, c969, c961, c944, c952, c953, c941, c1591] c1632 (by decide) p (sat_cons (step958 p h) (sat_cons (step966 p h) (sat_cons (step969 p h) (sat_cons (step961 p h) (sat_cons (step944 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step941 p h) (sat_cons (step1591 p h) (sat_nil p))))))))))
def c1633 : List Lit := [(1026, true), (1016, false), (57, false), (91, true), (97, true)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c688, c1124, c1129, c1136, c1140, c1130, c1112, c1125, c1110, c371, c360] c1633 (by decide) p (sat_cons (step688 p h) (sat_cons (step1124 p h) (sat_cons (step1129 p h) (sat_cons (step1136 p h) (sat_cons (step1140 p h) (sat_cons (step1130 p h) (sat_cons (step1112 p h) (sat_cons (step1125 p h) (sat_cons (step1110 p h) (sat_cons (step371 p h) (sat_cons (step360 p h) (sat_nil p))))))))))))
def c1634 : List Lit := [(93, false), (82, false), (57, false), (97, true)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c688, c371, c360] c1634 (by decide) p (sat_cons (step688 p h) (sat_cons (step371 p h) (sat_cons (step360 p h) (sat_nil p))))
def c1635 : List Lit := [(996, false), (70, false), (1004, true), (63, true), (52, false)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c1071, c1095, c1081, c1084, c1099, c1075, c1072, c218, c1067] c1635 (by decide) p (sat_cons (step1071 p h) (sat_cons (step1095 p h) (sat_cons (step1081 p h) (sat_cons (step1084 p h) (sat_cons (step1099 p h) (sat_cons (step1075 p h) (sat_cons (step1072 p h) (sat_cons (step218 p h) (sat_cons (step1067 p h) (sat_nil p))))))))))
def c1636 : List Lit := [(1059, true), (109, false), (86, false)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c1218, c1220, c1215, c1213, c497] c1636 (by decide) p (sat_cons (step1218 p h) (sat_cons (step1220 p h) (sat_cons (step1215 p h) (sat_cons (step1213 p h) (sat_cons (step497 p h) (sat_nil p))))))
def c1637 : List Lit := [(1092, true), (105, false), (1072, false), (103, false), (1080, false), (113, true)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c696, c1252, c1260, c1273, c1291, c1295, c1274, c1261, c1265, c1266, c1253, c580, c602, c433, c574] c1637 (by decide) p (sat_cons (step696 p h) (sat_cons (step1252 p h) (sat_cons (step1260 p h) (sat_cons (step1273 p h) (sat_cons (step1291 p h) (sat_cons (step1295 p h) (sat_cons (step1274 p h) (sat_cons (step1261 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step1253 p h) (sat_cons (step580 p h) (sat_cons (step602 p h) (sat_cons (step433 p h) (sat_cons (step574 p h) (sat_nil p))))))))))))))))
def c1638 : List Lit := [(115, false), (1081, true), (105, false), (103, false)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c696, c1266, c1265, c433, c580, c602, c574] c1638 (by decide) p (sat_cons (step696 p h) (sat_cons (step1266 p h) (sat_cons (step1265 p h) (sat_cons (step433 p h) (sat_cons (step580 p h) (sat_cons (step602 p h) (sat_cons (step574 p h) (sat_nil p))))))))
def c1639 : List Lit := [(934, true), (1026, true), (97, true), (86, false)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c685, c289, c992, c993, c311, c312, c1120, c1633] c1639 (by decide) p (sat_cons (step685 p h) (sat_cons (step289 p h) (sat_cons (step992 p h) (sat_cons (step993 p h) (sat_cons (step311 p h) (sat_cons (step312 p h) (sat_cons (step1120 p h) (sat_cons (step1633 p h) (sat_nil p)))))))))
def c1640 : List Lit := [(1016, false), (1025, true), (57, false), (97, true)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c1135, c1128, c1129, c1139, c1123, c1112, c1634, c1110] c1640 (by decide) p (sat_cons (step1135 p h) (sat_cons (step1128 p h) (sat_cons (step1129 p h) (sat_cons (step1139 p h) (sat_cons (step1123 p h) (sat_cons (step1112 p h) (sat_cons (step1634 p h) (sat_cons (step1110 p h) (sat_nil p)))))))))
def c1641 : List Lit := [(1008, true), (1081, true)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c683, c1266, c1265, c1106, c1107, c639, c258, c266] c1641 (by decide) p (sat_cons (step683 p h) (sat_cons (step1266 p h) (sat_cons (step1265 p h) (sat_cons (step1106 p h) (sat_cons (step1107 p h) (sat_cons (step639 p h) (sat_cons (step258 p h) (sat_cons (step266 p h) (sat_nil p)))))))))
def c1642 : List Lit := [(55, false), (1021, true), (89, false), (86, false)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c311, c312, c1120, c1124, c1129] c1642 (by decide) p (sat_cons (step311 p h) (sat_cons (step312 p h) (sat_cons (step1120 p h) (sat_cons (step1124 p h) (sat_cons (step1129 p h) (sat_nil p))))))
def c1643 : List Lit := [(843, true), (59, true), (927, true), (60, false), (61, false)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c675, c674, c187, c189, c868, c869, c140, c136, c983] c1643 (by decide) p (sat_cons (step675 p h) (sat_cons (step674 p h) (sat_cons (step187 p h) (sat_cons (step189 p h) (sat_cons (step868 p h) (sat_cons (step869 p h) (sat_cons (step140 p h) (sat_cons (step136 p h) (sat_cons (step983 p h) (sat_nil p))))))))))
def c1644 : List Lit := [(57, false), (117, false), (927, true), (60, false), (61, false), (1102, false), (993, false), (954, false), (97, true), (86, false)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c685, c675, c674, c1412, c289, c182, c188, c185, c1643, c173, c174, c250, c249, c1573, c1071, c1107, c1079, c1614, c1114, c1084, c1044, c1095, c1406, c1386, c1186, c1640, c1139, c1120, c1126, c321, c1124] c1644 (by decide) p (sat_cons (step685 p h) (sat_cons (step675 p h) (sat_cons (step674 p h) (sat_cons (step1412 p h) (sat_cons (step289 p h) (sat_cons (step182 p h) (sat_cons (step188 p h) (sat_cons (step185 p h) (sat_cons (step1643 p h) (sat_cons (step173 p h) (sat_cons (step174 p h) (sat_cons (step250 p h) (sat_cons (step249 p h) (sat_cons (step1573 p h) (sat_cons (step1071 p h) (sat_cons (step1107 p h) (sat_cons (step1079 p h) (sat_cons (step1614 p h) (sat_cons (step1114 p h) (sat_cons (step1084 p h) (sat_cons (step1044 p h) (sat_cons (step1095 p h) (sat_cons (step1406 p h) (sat_cons (step1386 p h) (sat_cons (step1186 p h) (sat_cons (step1640 p h) (sat_cons (step1139 p h) (sat_cons (step1120 p h) (sat_cons (step1126 p h) (sat_cons (step321 p h) (sat_cons (step1124 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1645 : List Lit := [(117, false), (944, true), (1102, false), (993, false), (954, false), (1026, true), (97, true), (86, false)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c685, c1595, c674, c1639, c1000, c1012, c990, c1008, c1001, c996, c995, c1003, c289, c1644, c994, c1642, c1140, c1114, c1107, c250, c186, c139, c138, c983] c1645 (by decide) p (sat_cons (step685 p h) (sat_cons (step1595 p h) (sat_cons (step674 p h) (sat_cons (step1639 p h) (sat_cons (step1000 p h) (sat_cons (step1012 p h) (sat_cons (step990 p h) (sat_cons (step1008 p h) (sat_cons (step1001 p h) (sat_cons (step996 p h) (sat_cons (step995 p h) (sat_cons (step1003 p h) (sat_cons (step289 p h) (sat_cons (step1644 p h) (sat_cons (step994 p h) (sat_cons (step1642 p h) (sat_cons (step1140 p h) (sat_cons (step1114 p h) (sat_cons (step1107 p h) (sat_cons (step250 p h) (sat_cons (step186 p h) (sat_cons (step139 p h) (sat_cons (step138 p h) (sat_cons (step983 p h) (sat_nil p)))))))))))))))))))))))))
def c1646 : List Lit := [(49, false), (55, false), (927, true), (60, false)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c139, c138, c983] c1646 (by decide) p (sat_cons (step139 p h) (sat_cons (step138 p h) (sat_cons (step983 p h) (sat_nil p))))
def c1647 : List Lit := [(20, false), (1021, true), (89, false), (86, false)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c301, c302, c1120, c1124, c1129] c1647 (by decide) p (sat_cons (step301 p h) (sat_cons (step302 p h) (sat_cons (step1120 p h) (sat_cons (step1124 p h) (sat_cons (step1129 p h) (sat_nil p))))))
def c1648 : List Lit := [(1020, true), (89, false), (86, false)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c1126, c1128, c1124, c1120, c321] c1648 (by decide) p (sat_cons (step1126 p h) (sat_cons (step1128 p h) (sat_cons (step1124 p h) (sat_cons (step1120 p h) (sat_cons (step321 p h) (sat_nil p))))))
def c1649 : List Lit := [(889, true)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c930, c1623, c1614, c1576, c918, c1573, c879, c898, c869, c896, c1548, c1602, c877] c1649 (by decide) p (sat_cons (step930 p h) (sat_cons (step1623 p h) (sat_cons (step1614 p h) (sat_cons (step1576 p h) (sat_cons (step918 p h) (sat_cons (step1573 p h) (sat_cons (step879 p h) (sat_cons (step898 p h) (sat_cons (step869 p h) (sat_cons (step896 p h) (sat_cons (step1548 p h) (sat_cons (step1602 p h) (sat_cons (step877 p h) (sat_nil p))))))))))))))
def c1650 : List Lit := [(1025, false), (1035, true), (1103, false), (935, false), (993, false), (920, false)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1649, c681, c1595, c1082, c1088, c1164, c1172, c1362, c1089, c1093, c1408, c1083, c1069, c1071, c1046, c1077, c1588, c1034, c244, c1009, c178, c1004, c995] c1650 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1649 p h) (sat_cons (step681 p h) (sat_cons (step1595 p h) (sat_cons (step1082 p h) (sat_cons (step1088 p h) (sat_cons (step1164 p h) (sat_cons (step1172 p h) (sat_cons (step1362 p h) (sat_cons (step1089 p h) (sat_cons (step1093 p h) (sat_cons (step1408 p h) (sat_cons (step1083 p h) (sat_cons (step1069 p h) (sat_cons (step1071 p h) (sat_cons (step1046 p h) (sat_cons (step1077 p h) (sat_cons (step1588 p h) (sat_cons (step1034 p h) (sat_cons (step244 p h) (sat_cons (step1009 p h) (sat_cons (step178 p h) (sat_cons (step1004 p h) (sat_cons (step995 p h) (sat_nil p)))))))))))))))))))))))))
def c1651 : List Lit := [(1002, true), (71, true), (72, false), (81, false), (997, false)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1093, c1085, c1069, c1076, c1066, c227] c1651 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1093 p h) (sat_cons (step1085 p h) (sat_cons (step1069 p h) (sat_cons (step1076 p h) (sat_cons (step1066 p h) (sat_cons (step227 p h) (sat_nil p))))))))
def c1652 : List Lit := [(881, true), (866, false), (96, false)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c657, c899, c925, c923, c902, c912, c893, c904, c905, c63, c60, c56] c1652 (by decide) p (sat_cons (step657 p h) (sat_cons (step899 p h) (sat_cons (step925 p h) (sat_cons (step923 p h) (sat_cons (step902 p h) (sat_cons (step912 p h) (sat_cons (step893 p h) (sat_cons (step904 p h) (sat_cons (step905 p h) (sat_cons (step63 p h) (sat_cons (step60 p h) (sat_cons (step56 p h) (sat_nil p)))))))))))))
def c1653 : List Lit := [(857, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c1575, c886, c878, c1573, c876, c869, c1548] c1653 (by decide) p (sat_cons (step1575 p h) (sat_cons (step886 p h) (sat_cons (step878 p h) (sat_cons (step1573 p h) (sat_cons (step876 p h) (sat_cons (step869 p h) (sat_cons (step1548 p h) (sat_nil p))))))))
def c1654 : List Lit := [(99, false), (866, true), (82, false), (1022, true), (97, true), (86, false)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c685, c688, c289, c322, c324, c303, c1120, c897, c1130, c1125, c371, c354] c1654 (by decide) p (sat_cons (step685 p h) (sat_cons (step688 p h) (sat_cons (step289 p h) (sat_cons (step322 p h) (sat_cons (step324 p h) (sat_cons (step303 p h) (sat_cons (step1120 p h) (sat_cons (step897 p h) (sat_cons (step1130 p h) (sat_cons (step1125 p h) (sat_cons (step371 p h) (sat_cons (step354 p h) (sat_nil p)))))))))))))
def c1655 : List Lit := [(91, true), (1016, false), (1103, false), (57, true), (955, false), (993, false), (1026, true), (920, false), (97, true), (86, false)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c685, c1649, c688, c1412, c1653, c1136, c1130, c1045, c1407, c1370, c1082, c1088, c289, c1124, c1125, c1129, c371, c1135, c1140, c1164, c1650, c1112, c1362, c994, c1110, c1408, c296, c354, c1052, c897, c927, c899, c922] c1655 (by decide) p (sat_cons (step685 p h) (sat_cons (step1649 p h) (sat_cons (step688 p h) (sat_cons (step1412 p h) (sat_cons (step1653 p h) (sat_cons (step1136 p h) (sat_cons (step1130 p h) (sat_cons (step1045 p h) (sat_cons (step1407 p h) (sat_cons (step1370 p h) (sat_cons (step1082 p h) (sat_cons (step1088 p h) (sat_cons (step289 p h) (sat_cons (step1124 p h) (sat_cons (step1125 p h) (sat_cons (step1129 p h) (sat_cons (step371 p h) (sat_cons (step1135 p h) (sat_cons (step1140 p h) (sat_cons (step1164 p h) (sat_cons (step1650 p h) (sat_cons (step1112 p h) (sat_cons (step1362 p h) (sat_cons (step994 p h) (sat_cons (step1110 p h) (sat_cons (step1408 p h) (sat_cons (step296 p h) (sat_cons (step354 p h) (sat_cons (step1052 p h) (sat_cons (step897 p h) (sat_cons (step927 p h) (sat_cons (step899 p h) (sat_cons (step922 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c1656 : List Lit := [(35, false), (1060, true), (109, false), (86, false)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c478, c477, c1215, c1213, c1221] c1656 (by decide) p (sat_cons (step478 p h) (sat_cons (step477 p h) (sat_cons (step1215 p h) (sat_cons (step1213 p h) (sat_cons (step1221 p h) (sat_nil p))))))
def c1657 : List Lit := [(903, false), (920, true)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c976, c949, c950, c973, c941, c960, c952, c953, c1591] c1657 (by decide) p (sat_cons (step976 p h) (sat_cons (step949 p h) (sat_cons (step950 p h) (sat_cons (step973 p h) (sat_cons (step941 p h) (sat_cons (step960 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step1591 p h) (sat_nil p))))))))))
def c1658 : List Lit := [(107, true), (1060, true), (109, false), (86, false)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c1219, c1216, c1217, c1221, c497, c1213] c1658 (by decide) p (sat_cons (step1219 p h) (sat_cons (step1216 p h) (sat_cons (step1217 p h) (sat_cons (step1221 p h) (sat_cons (step497 p h) (sat_cons (step1213 p h) (sat_nil p)))))))
def c1659 : List Lit := [(118, false), (124, true), (96, false), (107, false)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c698, c591, c595] c1659 (by decide) p (sat_cons (step698 p h) (sat_cons (step591 p h) (sat_cons (step595 p h) (sat_nil p))))
def c1660 : List Lit := [(1072, true), (1060, true), (97, true), (86, false)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c685, c287, c289, c1526, c1625, c1250, c1215, c498, c1221, c1213] c1660 (by decide) p (sat_cons (step685 p h) (sat_cons (step287 p h) (sat_cons (step289 p h) (sat_cons (step1526 p h) (sat_cons (step1625 p h) (sat_cons (step1250 p h) (sat_cons (step1215 p h) (sat_cons (step498 p h) (sat_cons (step1221 p h) (sat_cons (step1213 p h) (sat_nil p)))))))))))
def c1661 : List Lit := [(71, false), (1060, true), (109, false), (86, false)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c487, c488, c1213, c1215, c1221] c1661 (by decide) p (sat_cons (step487 p h) (sat_cons (step488 p h) (sat_cons (step1213 p h) (sat_cons (step1215 p h) (sat_cons (step1221 p h) (sat_nil p))))))
def c1662 : List Lit := [(881, true), (26, true), (866, false)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c658, c899, c925, c923, c902, c910, c892, c908, c72, c70, c1501] c1662 (by decide) p (sat_cons (step658 p h) (sat_cons (step899 p h) (sat_cons (step925 p h) (sat_cons (step923 p h) (sat_cons (step902 p h) (sat_cons (step910 p h) (sat_cons (step892 p h) (sat_cons (step908 p h) (sat_cons (step72 p h) (sat_cons (step70 p h) (sat_cons (step1501 p h) (sat_nil p))))))))))))
def c1663 : List Lit := [(1079, true), (105, false), (107, false)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c698, c1262, c1263, c581, c597, c593] c1663 (by decide) p (sat_cons (step698 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step581 p h) (sat_cons (step597 p h) (sat_cons (step593 p h) (sat_nil p)))))))
def c1664 : List Lit := [(118, false), (123, false), (105, false), (100, false)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c698, c644, c583, c592] c1664 (by decide) p (sat_cons (step698 p h) (sat_cons (step644 p h) (sat_cons (step583 p h) (sat_cons (step592 p h) (sat_nil p)))))
def c1665 : List Lit := [(920, true), (107, false), (35, true)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c662, c938, c1619, c1609, c1657, c955, c940, c96, c86, c104] c1665 (by decide) p (sat_cons (step662 p h) (sat_cons (step938 p h) (sat_cons (step1619 p h) (sat_cons (step1609 p h) (sat_cons (step1657 p h) (sat_cons (step955 p h) (sat_cons (step940 p h) (sat_cons (step96 p h) (sat_cons (step86 p h) (sat_cons (step104 p h) (sat_nil p)))))))))))
def c1666 : List Lit := [(105, true), (1060, true), (109, false), (86, false)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c1223, c1212, c1214, c1221, c497, c1215] c1666 (by decide) p (sat_cons (step1223 p h) (sat_cons (step1212 p h) (sat_cons (step1214 p h) (sat_cons (step1221 p h) (sat_cons (step497 p h) (sat_cons (step1215 p h) (sat_nil p)))))))
def c1667 : List Lit := [(1090, true), (108, false), (100, false), (1079, false), (1072, false)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c699, c1270, c1259, c1286, c1289, c1271, c1260, c1265, c1266, c1252, c645, c601, c516, c608] c1667 (by decide) p (sat_cons (step699 p h) (sat_cons (step1270 p h) (sat_cons (step1259 p h) (sat_cons (step1286 p h) (sat_cons (step1289 p h) (sat_cons (step1271 p h) (sat_cons (step1260 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step1252 p h) (sat_cons (step645 p h) (sat_cons (step601 p h) (sat_cons (step516 p h) (sat_cons (step608 p h) (sat_nil p)))))))))))))))
def c1668 : List Lit := [(1090, true), (103, false), (1079, false), (105, false), (1072, false)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1259, c1286, c1289, c1271, c1260, c1638, c1251] c1668 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1259 p h) (sat_cons (step1286 p h) (sat_cons (step1289 p h) (sat_cons (step1271 p h) (sat_cons (step1260 p h) (sat_cons (step1638 p h) (sat_cons (step1251 p h) (sat_nil p)))))))))
def c1669 : List Lit := [(1002, true), (103, false), (105, false), (993, false)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c677, c1082, c1089, c1093, c1083, c1069, c1077, c1066, c1067, c1588, c208, c420, c203] c1669 (by decide) p (sat_cons (step677 p h) (sat_cons (step1082 p h) (sat_cons (step1089 p h) (sat_cons (step1093 p h) (sat_cons (step1083 p h) (sat_cons (step1069 p h) (sat_cons (step1077 p h) (sat_cons (step1066 p h) (sat_cons (step1067 p h) (sat_cons (step1588 p h) (sat_cons (step208 p h) (sat_cons (step420 p h) (sat_cons (step203 p h) (sat_nil p))))))))))))))
def c1670 : List Lit := [(943, true)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1011, c1007, c990, c1593] c1670 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1011 p h) (sat_cons (step1007 p h) (sat_cons (step990 p h) (sat_cons (step1593 p h) (sat_nil p))))))
def c1671 : List Lit := [(951, true)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c1670, c1019] c1671 (by decide) p (sat_cons (step1670 p h) (sat_cons (step1019 p h) (sat_nil p)))
def c1672 : List Lit := [(988, true), (75, false), (103, false), (105, false)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c677, c1066, c1067, c1588, c208, c420, c203] c1672 (by decide) p (sat_cons (step677 p h) (sat_cons (step1066 p h) (sat_cons (step1067 p h) (sat_cons (step1588 p h) (sat_cons (step208 p h) (sat_cons (step420 p h) (sat_cons (step203 p h) (sat_nil p))))))))
def c1673 : List Lit := [(65, false), (68, false), (66, true), (103, false), (105, false)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c677, c420, c208, c203] c1673 (by decide) p (sat_cons (step677 p h) (sat_cons (step420 p h) (sat_cons (step208 p h) (sat_cons (step203 p h) (sat_nil p)))))
def c1674 : List Lit := [(939, true), (55, true), (934, false), (58, false), (75, false)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c1003, c1001, c994, c995, c174] c1674 (by decide) p (sat_cons (step1003 p h) (sat_cons (step1001 p h) (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step174 p h) (sat_nil p))))))
end B112E153
