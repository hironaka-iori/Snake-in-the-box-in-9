import B112E081Part0004
namespace B112E081
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1514 : List Lit := [(277, false), (283, false)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c1207, c615] c1514 (by decide) p (sat_cons (step1207 p h) (sat_cons (step615 p h) (sat_nil p)))
def c1515 : List Lit := [(259, false), (287, false)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c1202, c621] c1515 (by decide) p (sat_cons (step1202 p h) (sat_cons (step621 p h) (sat_nil p)))
def c1516 : List Lit := [(289, false), (345, false)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c1200, c655] c1516 (by decide) p (sat_cons (step1200 p h) (sat_cons (step655 p h) (sat_nil p)))
def c1517 : List Lit := [(359, false), (371, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c1203, c677] c1517 (by decide) p (sat_cons (step1203 p h) (sat_cons (step677 p h) (sat_nil p)))
def c1518 : List Lit := [(373, false), (401, false)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c1201, c690] c1518 (by decide) p (sat_cons (step1201 p h) (sat_cons (step690 p h) (sat_nil p)))
def c1519 : List Lit := [(347, false), (461, false)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c724, c722] c1519 (by decide) p (sat_cons (step724 p h) (sat_cons (step722 p h) (sat_nil p)))
def c1520 : List Lit := [(840, true), (832, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c1241, c792] c1520 (by decide) p (sat_cons (step1241 p h) (sat_cons (step792 p h) (sat_nil p)))
def c1521 : List Lit := [(833, false), (841, true)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c1241, c793] c1521 (by decide) p (sat_cons (step1241 p h) (sat_cons (step793 p h) (sat_nil p)))
def c1522 : List Lit := [(834, false), (842, true)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c1241, c794] c1522 (by decide) p (sat_cons (step1241 p h) (sat_cons (step794 p h) (sat_nil p)))
def c1523 : List Lit := [(835, false), (843, true)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c1241, c795] c1523 (by decide) p (sat_cons (step1241 p h) (sat_cons (step795 p h) (sat_nil p)))
def c1524 : List Lit := [(840, true), (811, false)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c1350, c796] c1524 (by decide) p (sat_cons (step1350 p h) (sat_cons (step796 p h) (sat_nil p)))
def c1525 : List Lit := [(916, true), (898, false)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c1351, c907] c1525 (by decide) p (sat_cons (step1351 p h) (sat_cons (step907 p h) (sat_nil p)))
def c1526 : List Lit := [(917, true), (899, false)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1351, c908] c1526 (by decide) p (sat_cons (step1351 p h) (sat_cons (step908 p h) (sat_nil p)))
def c1527 : List Lit := [(918, true), (900, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c1351, c909] c1527 (by decide) p (sat_cons (step1351 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1528 : List Lit := [(919, true), (901, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c1351, c910] c1528 (by decide) p (sat_cons (step1351 p h) (sat_cons (step910 p h) (sat_nil p)))
def c1529 : List Lit := [(902, false), (920, true)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c1351, c911] c1529 (by decide) p (sat_cons (step1351 p h) (sat_cons (step911 p h) (sat_nil p)))
def c1530 : List Lit := [(903, false), (921, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c1351, c912] c1530 (by decide) p (sat_cons (step1351 p h) (sat_cons (step912 p h) (sat_nil p)))
def c1531 : List Lit := [(904, false), (922, true)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c1351, c913] c1531 (by decide) p (sat_cons (step1351 p h) (sat_cons (step913 p h) (sat_nil p)))
def c1532 : List Lit := [(966, true), (953, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1011] c1532 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1011 p h) (sat_nil p)))
def c1533 : List Lit := [(967, true), (954, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1015] c1533 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c1534 : List Lit := [(955, false), (968, true)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1018] c1534 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1018 p h) (sat_nil p)))
def c1535 : List Lit := [(956, false), (969, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1020] c1535 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1020 p h) (sat_nil p)))
def c1536 : List Lit := [(966, false), (975, true)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1025] c1536 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1025 p h) (sat_nil p)))
def c1537 : List Lit := [(967, false), (976, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1026] c1537 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1026 p h) (sat_nil p)))
def c1538 : List Lit := [(968, false), (977, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1027] c1538 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1027 p h) (sat_nil p)))
def c1539 : List Lit := [(969, false), (978, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1028] c1539 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1028 p h) (sat_nil p)))
def c1540 : List Lit := [(943, false), (975, true)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1030] c1540 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1030 p h) (sat_nil p)))
def c1541 : List Lit := [(944, false), (976, true)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1036] c1541 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1036 p h) (sat_nil p)))
def c1542 : List Lit := [(945, false), (977, true)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1041] c1542 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1041 p h) (sat_nil p)))
def c1543 : List Lit := [(946, false), (978, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1045] c1543 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1045 p h) (sat_nil p)))
def c1544 : List Lit := [(947, false), (979, true)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1050] c1544 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1050 p h) (sat_nil p)))
def c1545 : List Lit := [(1050, true), (1033, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1292, c1109] c1545 (by decide) p (sat_cons (step1292 p h) (sat_cons (step1109 p h) (sat_nil p)))
def c1546 : List Lit := [(916, false), (1058, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1145] c1546 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1145 p h) (sat_nil p)))
def c1547 : List Lit := [(917, false), (1057, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1146] c1547 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1146 p h) (sat_nil p)))
def c1548 : List Lit := [(918, false), (1056, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1147] c1548 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1147 p h) (sat_nil p)))
def c1549 : List Lit := [(919, false), (1055, false)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1148] c1549 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1148 p h) (sat_nil p)))
def c1550 : List Lit := [(920, false), (1054, false)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1149] c1550 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1149 p h) (sat_nil p)))
def c1551 : List Lit := [(921, false), (1053, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1150] c1551 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1150 p h) (sat_nil p)))
def c1552 : List Lit := [(922, false), (1052, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1151] c1552 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1151 p h) (sat_nil p)))
def c1553 : List Lit := [(923, false), (1051, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1152] c1553 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1152 p h) (sat_nil p)))
def c1554 : List Lit := [(924, false), (1050, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1153] c1554 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1153 p h) (sat_nil p)))
def c1555 : List Lit := [(9, false), (59, false), (96, false), (944, true), (60, true)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c353, c351, c948, c941, c955, c943, c971] c1555 (by decide) p (sat_cons (step353 p h) (sat_cons (step351 p h) (sat_cons (step948 p h) (sat_cons (step941 p h) (sat_cons (step955 p h) (sat_cons (step943 p h) (sat_cons (step971 p h) (sat_nil p))))))))
def c1556 : List Lit := [(938, true), (52, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c953, c955, c951, c1359, c1466, c1465, c1179] c1556 (by decide) p (sat_cons (step953 p h) (sat_cons (step955 p h) (sat_cons (step951 p h) (sat_cons (step1359 p h) (sat_cons (step1466 p h) (sat_cons (step1465 p h) (sat_cons (step1179 p h) (sat_nil p))))))))
def c1557 : List Lit := [(68, false), (934, true), (58, false), (52, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1179, c1359, c1465] c1557 (by decide) p (sat_cons (step1179 p h) (sat_cons (step1359 p h) (sat_cons (step1465 p h) (sat_nil p))))
def c1558 : List Lit := [(60, true), (962, false), (1033, false), (884, false), (799, false), (77, true), (930, true), (944, true), (59, false), (936, false), (65, false), (943, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1381, c941, c734, c371, c359, c741, c985, c837, c747, c987, c1224, c1524, c1016, c863, c1033, c1233, c1129, c1550, c926, c917, c797, c879, c1363, c1219] c1558 (by decide) p (sat_cons (step1381 p h) (sat_cons (step941 p h) (sat_cons (step734 p h) (sat_cons (step371 p h) (sat_cons (step359 p h) (sat_cons (step741 p h) (sat_cons (step985 p h) (sat_cons (step837 p h) (sat_cons (step747 p h) (sat_cons (step987 p h) (sat_cons (step1224 p h) (sat_cons (step1524 p h) (sat_cons (step1016 p h) (sat_cons (step863 p h) (sat_cons (step1033 p h) (sat_cons (step1233 p h) (sat_cons (step1129 p h) (sat_cons (step1550 p h) (sat_cons (step926 p h) (sat_cons (step917 p h) (sat_cons (step797 p h) (sat_cons (step879 p h) (sat_cons (step1363 p h) (sat_cons (step1219 p h) (sat_nil p)))))))))))))))))))))))))
def c1559 : List Lit := [(962, false), (1033, false), (943, false), (884, false), (799, false), (77, true), (930, true), (944, true), (59, false), (936, false), (65, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1558, c368, c356, c346, c985, c837, c734, c987, c1224, c741, c1016, c863, c747, c1033, c1233, c1524, c1129, c1550, c926, c917, c797, c879, c1363, c1219] c1559 (by decide) p (sat_cons (step1558 p h) (sat_cons (step368 p h) (sat_cons (step356 p h) (sat_cons (step346 p h) (sat_cons (step985 p h) (sat_cons (step837 p h) (sat_cons (step734 p h) (sat_cons (step987 p h) (sat_cons (step1224 p h) (sat_cons (step741 p h) (sat_cons (step1016 p h) (sat_cons (step863 p h) (sat_cons (step747 p h) (sat_cons (step1033 p h) (sat_cons (step1233 p h) (sat_cons (step1524 p h) (sat_cons (step1129 p h) (sat_cons (step1550 p h) (sat_cons (step926 p h) (sat_cons (step917 p h) (sat_cons (step797 p h) (sat_cons (step879 p h) (sat_cons (step1363 p h) (sat_cons (step1219 p h) (sat_nil p)))))))))))))))))))))))))
def c1560 : List Lit := [(60, false), (949, false), (943, false), (884, false), (799, false), (77, true), (1033, false), (59, false), (65, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c368, c356, c346, c985, c837, c734, c990, c1224, c741, c1534, c863, c747, c1033, c1233, c1524, c1129, c1550, c926, c917, c797, c879, c1363, c1219] c1560 (by decide) p (sat_cons (step368 p h) (sat_cons (step356 p h) (sat_cons (step346 p h) (sat_cons (step985 p h) (sat_cons (step837 p h) (sat_cons (step734 p h) (sat_cons (step990 p h) (sat_cons (step1224 p h) (sat_cons (step741 p h) (sat_cons (step1534 p h) (sat_cons (step863 p h) (sat_cons (step747 p h) (sat_cons (step1033 p h) (sat_cons (step1233 p h) (sat_cons (step1524 p h) (sat_cons (step1129 p h) (sat_cons (step1550 p h) (sat_cons (step926 p h) (sat_cons (step917 p h) (sat_cons (step797 p h) (sat_cons (step879 p h) (sat_cons (step1363 p h) (sat_cons (step1219 p h) (sat_nil p))))))))))))))))))))))))
def c1561 : List Lit := [(943, false), (884, false), (799, false), (51, true), (77, true), (1033, false), (930, true), (944, true), (59, false), (936, false), (65, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1559, c1317, c981, c1560, c1381, c941, c734, c371, c359, c741, c985, c837, c747, c990, c1224, c1524, c1534, c863, c1033, c1233, c1129, c1550, c926, c917, c797, c879, c1363, c1219] c1561 (by decide) p (sat_cons (step1559 p h) (sat_cons (step1317 p h) (sat_cons (step981 p h) (sat_cons (step1560 p h) (sat_cons (step1381 p h) (sat_cons (step941 p h) (sat_cons (step734 p h) (sat_cons (step371 p h) (sat_cons (step359 p h) (sat_cons (step741 p h) (sat_cons (step985 p h) (sat_cons (step837 p h) (sat_cons (step747 p h) (sat_cons (step990 p h) (sat_cons (step1224 p h) (sat_cons (step1524 p h) (sat_cons (step1534 p h) (sat_cons (step863 p h) (sat_cons (step1033 p h) (sat_cons (step1233 p h) (sat_cons (step1129 p h) (sat_cons (step1550 p h) (sat_cons (step926 p h) (sat_cons (step917 p h) (sat_cons (step797 p h) (sat_cons (step879 p h) (sat_cons (step1363 p h) (sat_cons (step1219 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1562 : List Lit := [(929, true), (59, false), (65, false)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c939, c940, c365] c1562 (by decide) p (sat_cons (step939 p h) (sat_cons (step940 p h) (sat_cons (step365 p h) (sat_nil p))))
def c1563 : List Lit := [(993, false), (1033, true), (66, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1099, c1075, c1070, c1071, c1074, c1078, c1066, c1098, c1057, c1095, c1055, c1089, c1086, c514, c510, c1501] c1563 (by decide) p (sat_cons (step1099 p h) (sat_cons (step1075 p h) (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step1074 p h) (sat_cons (step1078 p h) (sat_cons (step1066 p h) (sat_cons (step1098 p h) (sat_cons (step1057 p h) (sat_cons (step1095 p h) (sat_cons (step1055 p h) (sat_cons (step1089 p h) (sat_cons (step1086 p h) (sat_cons (step514 p h) (sat_cons (step510 p h) (sat_cons (step1501 p h) (sat_nil p)))))))))))))))))
def c1564 : List Lit := [(920, true), (891, false), (811, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1233, c1524, c926, c917, c797, c879, c1363, c1219] c1564 (by decide) p (sat_cons (step1233 p h) (sat_cons (step1524 p h) (sat_cons (step926 p h) (sat_cons (step917 p h) (sat_cons (step797 p h) (sat_cons (step879 p h) (sat_cons (step1363 p h) (sat_cons (step1219 p h) (sat_nil p)))))))))
def c1565 : List Lit := [(966, true), (58, true), (52, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1008, c1251, c1532, c1317, c986, c988, c1177, c984, c980, c1478, c1477, c1191] c1565 (by decide) p (sat_cons (step1008 p h) (sat_cons (step1251 p h) (sat_cons (step1532 p h) (sat_cons (step1317 p h) (sat_cons (step986 p h) (sat_cons (step988 p h) (sat_cons (step1177 p h) (sat_cons (step984 p h) (sat_cons (step980 p h) (sat_cons (step1478 p h) (sat_cons (step1477 p h) (sat_cons (step1191 p h) (sat_nil p)))))))))))))
def c1566 : List Lit := [(921, true), (893, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1530, c918, c881, c1520, c1219, c1363] c1566 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1530 p h) (sat_cons (step918 p h) (sat_cons (step881 p h) (sat_cons (step1520 p h) (sat_cons (step1219 p h) (sat_cons (step1363 p h) (sat_nil p))))))))
def c1567 : List Lit := [(938, true), (58, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c953, c955, c951, c1466, c1359] c1567 (by decide) p (sat_cons (step953 p h) (sat_cons (step955 p h) (sat_cons (step951 p h) (sat_cons (step1466 p h) (sat_cons (step1359 p h) (sat_nil p))))))
def c1568 : List Lit := [(954, true), (69, false), (921, true), (77, true), (880, false), (48, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1566, c984, c836, c1224, c987, c989, c985, c980, c1301, c425, c1481, c1468, c434, c846, c854, c864, c869, c1234, c1225, c927, c838, c1280, c165, c343, c1346] c1568 (by decide) p (sat_cons (step1566 p h) (sat_cons (step984 p h) (sat_cons (step836 p h) (sat_cons (step1224 p h) (sat_cons (step987 p h) (sat_cons (step989 p h) (sat_cons (step985 p h) (sat_cons (step980 p h) (sat_cons (step1301 p h) (sat_cons (step425 p h) (sat_cons (step1481 p h) (sat_cons (step1468 p h) (sat_cons (step434 p h) (sat_cons (step846 p h) (sat_cons (step854 p h) (sat_cons (step864 p h) (sat_cons (step869 p h) (sat_cons (step1234 p h) (sat_cons (step1225 p h) (sat_cons (step927 p h) (sat_cons (step838 p h) (sat_cons (step1280 p h) (sat_cons (step165 p h) (sat_cons (step343 p h) (sat_cons (step1346 p h) (sat_nil p))))))))))))))))))))))))))
def c1569 : List Lit := [(1002, true), (69, false), (882, true), (58, true), (95, false), (89, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1055, c1057, c1080, c1078, c1058, c1060, c1068, c1070, c1056, c1065, c1062, c474, c493, c1495, c491, c847, c196, c487, c1487] c1569 (by decide) p (sat_cons (step1055 p h) (sat_cons (step1057 p h) (sat_cons (step1080 p h) (sat_cons (step1078 p h) (sat_cons (step1058 p h) (sat_cons (step1060 p h) (sat_cons (step1068 p h) (sat_cons (step1070 p h) (sat_cons (step1056 p h) (sat_cons (step1065 p h) (sat_cons (step1062 p h) (sat_cons (step474 p h) (sat_cons (step493 p h) (sat_cons (step1495 p h) (sat_cons (step491 p h) (sat_cons (step847 p h) (sat_cons (step196 p h) (sat_cons (step487 p h) (sat_cons (step1487 p h) (sat_nil p))))))))))))))))))))
def c1570 : List Lit := [(991, true), (96, false), (46, true), (53, false), (89, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1055, c1058, c1060, c1056, c487, c474, c1487] c1570 (by decide) p (sat_cons (step1055 p h) (sat_cons (step1058 p h) (sat_cons (step1060 p h) (sat_cons (step1056 p h) (sat_cons (step487 p h) (sat_cons (step474 p h) (sat_cons (step1487 p h) (sat_nil p))))))))
def c1571 : List Lit := [(92, false), (87, false), (96, false), (46, true), (53, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c474, c487, c1487] c1571 (by decide) p (sat_cons (step474 p h) (sat_cons (step487 p h) (sat_cons (step1487 p h) (sat_nil p))))
def c1572 : List Lit := [(91, false), (58, true), (73, false), (53, false), (57, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c276, c274, c1451] c1572 (by decide) p (sat_cons (step276 p h) (sat_cons (step274 p h) (sat_cons (step1451 p h) (sat_nil p))))
def c1573 : List Lit := [(7, true), (841, true), (3, true), (16, false), (87, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1280, c1260, c727, c54, c53, c51, c729, c763, c755, c760, c749, c770, c797, c783] c1573 (by decide) p (sat_cons (step1280 p h) (sat_cons (step1260 p h) (sat_cons (step727 p h) (sat_cons (step54 p h) (sat_cons (step53 p h) (sat_cons (step51 p h) (sat_cons (step729 p h) (sat_cons (step763 p h) (sat_cons (step755 p h) (sat_cons (step760 p h) (sat_cons (step749 p h) (sat_cons (step770 p h) (sat_cons (step797 p h) (sat_cons (step783 p h) (sat_nil p)))))))))))))))
def c1574 : List Lit := [(1, false), (32, true), (143, true), (833, true), (16, false), (87, false)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c54, c53, c51, c763, c755, c118, c760, c1430, c784, c766, c771] c1574 (by decide) p (sat_cons (step54 p h) (sat_cons (step53 p h) (sat_cons (step51 p h) (sat_cons (step763 p h) (sat_cons (step755 p h) (sat_cons (step118 p h) (sat_cons (step760 p h) (sat_cons (step1430 p h) (sat_cons (step784 p h) (sat_cons (step766 p h) (sat_cons (step771 p h) (sat_nil p))))))))))))
def c1575 : List Lit := [(977, false), (1033, false), (797, false), (880, false), (89, true), (878, false), (16, false), (87, false)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c853, c868, c1234, c1124, c1551, c1530, c927, c886, c1401, c880, c918, c1520, c1524, c1363, c749, c826, c731, c820, c53, c51, c1215, c755, c760, c1264, c783] c1575 (by decide) p (sat_cons (step853 p h) (sat_cons (step868 p h) (sat_cons (step1234 p h) (sat_cons (step1124 p h) (sat_cons (step1551 p h) (sat_cons (step1530 p h) (sat_cons (step927 p h) (sat_cons (step886 p h) (sat_cons (step1401 p h) (sat_cons (step880 p h) (sat_cons (step918 p h) (sat_cons (step1520 p h) (sat_cons (step1524 p h) (sat_cons (step1363 p h) (sat_cons (step749 p h) (sat_cons (step826 p h) (sat_cons (step731 p h) (sat_cons (step820 p h) (sat_cons (step53 p h) (sat_cons (step51 p h) (sat_cons (step1215 p h) (sat_cons (step755 p h) (sat_cons (step760 p h) (sat_cons (step1264 p h) (sat_cons (step783 p h) (sat_nil p))))))))))))))))))))))))))
def c1576 : List Lit := [(71, false), (51, false), (57, false), (811, true), (1, false), (833, true), (16, false), (87, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.TreeRup.prove_clause [c53, c51, c54, c763, c770, c787, c761, c756, c755, c760, c784, c771, c766, c765, c773, c764, c783, c1520, c252, c1285, c230, c240, c853, c726, c836, c728, c1224, c747, c863, c739, c737, c128, c1398, c1574, c1431, c1099, c611, c1545, c612, c1554, c613, c1514, c921, c616, c609, c610, c899, c618, c608, c606, c1516, c114, c652, c1428, c1427, c636, c637, c93, c111, c124, c634, c635, c627, c1245, c633, c631, c626, c831, c632, c630, c625, c150, c1441, c152, c1439, c1438, c817, c1436, c822, c1215] c1576 (by decide) p (sat_cons (step53 p h) (sat_cons (step51 p h) (sat_cons (step54 p h) (sat_cons (step763 p h) (sat_cons (step770 p h) (sat_cons (step787 p h) (sat_cons (step761 p h) (sat_cons (step756 p h) (sat_cons (step755 p h) (sat_cons (step760 p h) (sat_cons (step784 p h) (sat_cons (step771 p h) (sat_cons (step766 p h) (sat_cons (step765 p h) (sat_cons (step773 p h) (sat_cons (step764 p h) (sat_cons (step783 p h) (sat_cons (step1520 p h) (sat_cons (step252 p h) (sat_cons (step1285 p h) (sat_cons (step230 p h) (sat_cons (step240 p h) (sat_cons (step853 p h) (sat_cons (step726 p h) (sat_cons (step836 p h) (sat_cons (step728 p h) (sat_cons (step1224 p h) (sat_cons (step747 p h) (sat_cons (step863 p h) (sat_cons (step739 p h) (sat_cons (step737 p h) (sat_cons (step128 p h) (sat_cons (step1398 p h) (sat_cons (step1574 p h) (sat_cons (step1431 p h) (sat_cons (step1099 p h) (sat_cons (step611 p h) (sat_cons (step1545 p h) (sat_cons (step612 p h) (sat_cons (step1554 p h) (sat_cons (step613 p h) (sat_cons (step1514 p h) (sat_cons (step921 p h) (sat_cons (step616 p h) (sat_cons (step609 p h) (sat_cons (step610 p h) (sat_cons (step899 p h) (sat_cons (step618 p h) (sat_cons (step608 p h) (sat_cons (step606 p h) (sat_cons (step1516 p h) (sat_cons (step114 p h) (sat_cons (step652 p h) (sat_cons (step1428 p h) (sat_cons (step1427 p h) (sat_cons (step636 p h) (sat_cons (step637 p h) (sat_cons (step93 p h) (sat_cons (step111 p h) (sat_cons (step124 p h) (sat_cons (step634 p h) (sat_cons (step635 p h) (sat_cons (step627 p h) (sat_cons (step1245 p h) (sat_cons (step633 p h) (sat_cons (step631 p h) (sat_cons (step626 p h) (sat_cons (step831 p h) (sat_cons (step632 p h) (sat_cons (step630 p h) (sat_cons (step625 p h) (sat_cons (step150 p h) (sat_cons (step1441 p h) (sat_cons (step152 p h) (sat_cons (step1439 p h) (sat_cons (step1438 p h) (sat_cons (step817 p h) (sat_cons (step1436 p h) (sat_cons (step822 p h) (sat_cons (step1215 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1577 : List Lit := [(32, true), (975, false), (1, false), (833, true), (88, false), (16, false), (87, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.TreeRup.prove_clause [c53, c51, c54, c763, c770, c787, c761, c756, c755, c760, c784, c771, c765, c773, c764, c783, c1520, c1574, c1432, c1431, c611, c612, c613, c1514, c616, c609, c610, c618, c608, c606, c607, c1516, c114, c652, c1428, c1427, c636, c637, c94, c93, c111, c124, c634, c635, c627, c1398, c1245, c633, c631, c626, c1099, c632, c630, c625, c1113, c150, c1553, c1441, c920, c152, c1439, c1438, c817, c1436, c1215, c106, c822, c471, c831, c1370, c898] c1577 (by decide) p (sat_cons (step53 p h) (sat_cons (step51 p h) (sat_cons (step54 p h) (sat_cons (step763 p h) (sat_cons (step770 p h) (sat_cons (step787 p h) (sat_cons (step761 p h) (sat_cons (step756 p h) (sat_cons (step755 p h) (sat_cons (step760 p h) (sat_cons (step784 p h) (sat_cons (step771 p h) (sat_cons (step765 p h) (sat_cons (step773 p h) (sat_cons (step764 p h) (sat_cons (step783 p h) (sat_cons (step1520 p h) (sat_cons (step1574 p h) (sat_cons (step1432 p h) (sat_cons (step1431 p h) (sat_cons (step611 p h) (sat_cons (step612 p h) (sat_cons (step613 p h) (sat_cons (step1514 p h) (sat_cons (step616 p h) (sat_cons (step609 p h) (sat_cons (step610 p h) (sat_cons (step618 p h) (sat_cons (step608 p h) (sat_cons (step606 p h) (sat_cons (step607 p h) (sat_cons (step1516 p h) (sat_cons (step114 p h) (sat_cons (step652 p h) (sat_cons (step1428 p h) (sat_cons (step1427 p h) (sat_cons (step636 p h) (sat_cons (step637 p h) (sat_cons (step94 p h) (sat_cons (step93 p h) (sat_cons (step111 p h) (sat_cons (step124 p h) (sat_cons (step634 p h) (sat_cons (step635 p h) (sat_cons (step627 p h) (sat_cons (step1398 p h) (sat_cons (step1245 p h) (sat_cons (step633 p h) (sat_cons (step631 p h) (sat_cons (step626 p h) (sat_cons (step1099 p h) (sat_cons (step632 p h) (sat_cons (step630 p h) (sat_cons (step625 p h) (sat_cons (step1113 p h) (sat_cons (step150 p h) (sat_cons (step1553 p h) (sat_cons (step1441 p h) (sat_cons (step920 p h) (sat_cons (step152 p h) (sat_cons (step1439 p h) (sat_cons (step1438 p h) (sat_cons (step817 p h) (sat_cons (step1436 p h) (sat_cons (step1215 p h) (sat_cons (step106 p h) (sat_cons (step822 p h) (sat_cons (step471 p h) (sat_cons (step831 p h) (sat_cons (step1370 p h) (sat_cons (step898 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end B112E081
