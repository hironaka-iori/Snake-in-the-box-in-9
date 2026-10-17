import B112E027Part0000
namespace B112E027
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1514 : List Lit := [(1477, true)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c1513, c1002] c1514 (by decide) p (sat_cons (step1513 p h) (sat_cons (step1002 p h) (sat_nil p)))
def c1515 : List Lit := [(1444, true), (68, false), (21, true), (1504, true)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c1045, c1042, c1035, c1048, c1031, c1029, c1036, c189, c937, c938, c167, c53, c182] c1515 (by decide) p (sat_cons (step1045 p h) (sat_cons (step1042 p h) (sat_cons (step1035 p h) (sat_cons (step1048 p h) (sat_cons (step1031 p h) (sat_cons (step1029 p h) (sat_cons (step1036 p h) (sat_cons (step189 p h) (sat_cons (step937 p h) (sat_cons (step938 p h) (sat_cons (step167 p h) (sat_cons (step53 p h) (sat_cons (step182 p h) (sat_nil p))))))))))))))
def c1516 : List Lit := [(1444, false), (1451, true)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c949, c940, c943, c953, c934, c935, c929, c926, c927, c31, c21, c39] c1516 (by decide) p (sat_cons (step949 p h) (sat_cons (step940 p h) (sat_cons (step943 p h) (sat_cons (step953 p h) (sat_cons (step934 p h) (sat_cons (step935 p h) (sat_cons (step929 p h) (sat_cons (step926 p h) (sat_cons (step927 p h) (sat_cons (step31 p h) (sat_cons (step21 p h) (sat_cons (step39 p h) (sat_nil p)))))))))))))
def c1517 : List Lit := [(29, true), (1459, false), (1480, true), (1504, true)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c1513, c632, c1452, c1005, c990, c979, c1045, c1042, c1035, c1048, c1031, c1029, c1036, c189, c150, c975, c977, c978, c981, c989, c972, c973, c1010, c122, c1516, c937, c95, c167, c148, c183, c716, c740, c719, c742, c720, c746, c724, c748, c729, c790, c796] c1517 (by decide) p (sat_cons (step1513 p h) (sat_cons (step632 p h) (sat_cons (step1452 p h) (sat_cons (step1005 p h) (sat_cons (step990 p h) (sat_cons (step979 p h) (sat_cons (step1045 p h) (sat_cons (step1042 p h) (sat_cons (step1035 p h) (sat_cons (step1048 p h) (sat_cons (step1031 p h) (sat_cons (step1029 p h) (sat_cons (step1036 p h) (sat_cons (step189 p h) (sat_cons (step150 p h) (sat_cons (step975 p h) (sat_cons (step977 p h) (sat_cons (step978 p h) (sat_cons (step981 p h) (sat_cons (step989 p h) (sat_cons (step972 p h) (sat_cons (step973 p h) (sat_cons (step1010 p h) (sat_cons (step122 p h) (sat_cons (step1516 p h) (sat_cons (step937 p h) (sat_cons (step95 p h) (sat_cons (step167 p h) (sat_cons (step148 p h) (sat_cons (step183 p h) (sat_cons (step716 p h) (sat_cons (step740 p h) (sat_cons (step719 p h) (sat_cons (step742 p h) (sat_cons (step720 p h) (sat_cons (step746 p h) (sat_cons (step724 p h) (sat_cons (step748 p h) (sat_cons (step729 p h) (sat_cons (step790 p h) (sat_cons (step796 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))
def c1518 : List Lit := [(20, false), (1460, true), (1480, true), (1504, true)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c1048, c1031, c1028, c1512, c1517, c105, c108, c970, c965] c1518 (by decide) p (sat_cons (step1048 p h) (sat_cons (step1031 p h) (sat_cons (step1028 p h) (sat_cons (step1512 p h) (sat_cons (step1517 p h) (sat_cons (step105 p h) (sat_cons (step108 p h) (sat_cons (step970 p h) (sat_cons (step965 p h) (sat_nil p))))))))))
def c1519 : List Lit := [(21, false), (1463, true), (15, false), (39, false)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c117, c118, c974] c1519 (by decide) p (sat_cons (step117 p h) (sat_cons (step118 p h) (sat_cons (step974 p h) (sat_nil p))))
def c1520 : List Lit := [(7, true), (1, true), (1441, true), (3, true), (120, true)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c620, c29, c928, c6, c933] c1520 (by decide) p (sat_cons (step620 p h) (sat_cons (step29 p h) (sat_cons (step928 p h) (sat_cons (step6 p h) (sat_cons (step933 p h) (sat_nil p))))))
def c1521 : List Lit := [(52, true), (1514, true), (46, false), (50, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c1060, c1056, c1058, c1062, c214] c1521 (by decide) p (sat_cons (step1060 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1062 p h) (sat_cons (step214 p h) (sat_nil p))))))
def c1522 : List Lit := [(20, false), (157, true), (1480, true), (1504, true)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c1513, c1005, c996, c1045, c1042, c1035, c1048, c1031, c1029, c1036, c189, c1028, c1512, c1518, c1517, c992, c993, c105, c108, c1010, c980, c971, c966, c1516, c972, c973, c937, c119, c167, c183] c1522 (by decide) p (sat_cons (step1513 p h) (sat_cons (step1005 p h) (sat_cons (step996 p h) (sat_cons (step1045 p h) (sat_cons (step1042 p h) (sat_cons (step1035 p h) (sat_cons (step1048 p h) (sat_cons (step1031 p h) (sat_cons (step1029 p h) (sat_cons (step1036 p h) (sat_cons (step189 p h) (sat_cons (step1028 p h) (sat_cons (step1512 p h) (sat_cons (step1518 p h) (sat_cons (step1517 p h) (sat_cons (step992 p h) (sat_cons (step993 p h) (sat_cons (step105 p h) (sat_cons (step108 p h) (sat_cons (step1010 p h) (sat_cons (step980 p h) (sat_cons (step971 p h) (sat_cons (step966 p h) (sat_cons (step1516 p h) (sat_cons (step972 p h) (sat_cons (step973 p h) (sat_cons (step937 p h) (sat_cons (step119 p h) (sat_cons (step167 p h) (sat_cons (step183 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1523 : List Lit := [(1462, true), (21, false), (39, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c972, c973, c122] c1523 (by decide) p (sat_cons (step972 p h) (sat_cons (step973 p h) (sat_cons (step122 p h) (sat_nil p))))
def c1524 : List Lit := [(11, true), (15, true), (1448, true), (131, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c625, c60, c934, c58, c944, c939] c1524 (by decide) p (sat_cons (step625 p h) (sat_cons (step60 p h) (sat_cons (step934 p h) (sat_cons (step58 p h) (sat_cons (step944 p h) (sat_cons (step939 p h) (sat_nil p)))))))
def c1525 : List Lit := [(15, true), (82, true), (3, true), (120, true), (125, true), (131, true), (135, true), (126, true), (20, true), (21, false), (39, false), (1481, true)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c618, c621, c626, c1523, c980, c985, c1020, c927, c929, c955, c937, c2, c940, c1516, c962, c1011, c1520, c993, c36, c968, c33, c41, c1524, c26, c965, c966, c970, c120, c92, c84] c1525 (by decide) p (sat_cons (step618 p h) (sat_cons (step621 p h) (sat_cons (step626 p h) (sat_cons (step1523 p h) (sat_cons (step980 p h) (sat_cons (step985 p h) (sat_cons (step1020 p h) (sat_cons (step927 p h) (sat_cons (step929 p h) (sat_cons (step955 p h) (sat_cons (step937 p h) (sat_cons (step2 p h) (sat_cons (step940 p h) (sat_cons (step1516 p h) (sat_cons (step962 p h) (sat_cons (step1011 p h) (sat_cons (step1520 p h) (sat_cons (step993 p h) (sat_cons (step36 p h) (sat_cons (step968 p h) (sat_cons (step33 p h) (sat_cons (step41 p h) (sat_cons (step1524 p h) (sat_cons (step26 p h) (sat_cons (step965 p h) (sat_cons (step966 p h) (sat_cons (step970 p h) (sat_cons (step120 p h) (sat_cons (step92 p h) (sat_cons (step84 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1526 : List Lit := [(11, true), (1452, true), (15, true)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1478, c937, c950, c946, c934, c1524, c936, c943, c691, c954, c692, c929, c696, c926, c927, c689, c31, c40] c1526 (by decide) p (sat_cons (step1478 p h) (sat_cons (step937 p h) (sat_cons (step950 p h) (sat_cons (step946 p h) (sat_cons (step934 p h) (sat_cons (step1524 p h) (sat_cons (step936 p h) (sat_cons (step943 p h) (sat_cons (step691 p h) (sat_cons (step954 p h) (sat_cons (step692 p h) (sat_cons (step929 p h) (sat_cons (step696 p h) (sat_cons (step926 p h) (sat_cons (step927 p h) (sat_cons (step689 p h) (sat_cons (step31 p h) (sat_cons (step40 p h) (sat_nil p)))))))))))))))))))
def c1527 : List Lit := [(1471, true), (20, false), (38, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c1512, c992, c989, c978, c975, c105, c108, c970, c965] c1527 (by decide) p (sat_cons (step1512 p h) (sat_cons (step992 p h) (sat_cons (step989 p h) (sat_cons (step978 p h) (sat_cons (step975 p h) (sat_cons (step105 p h) (sat_cons (step108 p h) (sat_cons (step970 p h) (sat_cons (step965 p h) (sat_nil p))))))))))
def c1528 : List Lit := [(66, true), (185, true), (67, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c653, c309, c307, c319, c1432] c1528 (by decide) p (sat_cons (step653 p h) (sat_cons (step309 p h) (sat_cons (step307 p h) (sat_cons (step319 p h) (sat_cons (step1432 p h) (sat_nil p))))))
def c1529 : List Lit := [(1452, true), (66, false), (4, false), (131, true), (1439, false), (15, true)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c1526, c954, c47, c941, c58, c939] c1529 (by decide) p (sat_cons (step1526 p h) (sat_cons (step954 p h) (sat_cons (step47 p h) (sat_cons (step941 p h) (sat_cons (step58 p h) (sat_cons (step939 p h) (sat_nil p)))))))
def c1530 : List Lit := [(1447, true), (66, false), (4, false), (131, true), (15, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c937, c941, c943, c939, c934, c58, c47] c1530 (by decide) p (sat_cons (step937 p h) (sat_cons (step941 p h) (sat_cons (step943 p h) (sat_cons (step939 p h) (sat_cons (step934 p h) (sat_cons (step58 p h) (sat_cons (step47 p h) (sat_nil p))))))))
def c1531 : List Lit := [(387, true), (78, true), (72, true), (1564, false), (1606, true), (75, true)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c655, c657, c828, c829, c827, c824, c826, c327, c334, c1160, c325, c338, c1163, c330, c1174, c1183, c1239, c1188, c1216] c1531 (by decide) p (sat_cons (step655 p h) (sat_cons (step657 p h) (sat_cons (step828 p h) (sat_cons (step829 p h) (sat_cons (step827 p h) (sat_cons (step824 p h) (sat_cons (step826 p h) (sat_cons (step327 p h) (sat_cons (step334 p h) (sat_cons (step1160 p h) (sat_cons (step325 p h) (sat_cons (step338 p h) (sat_cons (step1163 p h) (sat_cons (step330 p h) (sat_cons (step1174 p h) (sat_cons (step1183 p h) (sat_cons (step1239 p h) (sat_cons (step1188 p h) (sat_cons (step1216 p h) (sat_nil p))))))))))))))))))))
def c1532 : List Lit := [(76, false), (79, true), (72, true), (75, true)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c655, c1484, c330, c331, c325, c821, c327, c825] c1532 (by decide) p (sat_cons (step655 p h) (sat_cons (step1484 p h) (sat_cons (step330 p h) (sat_cons (step331 p h) (sat_cons (step325 p h) (sat_cons (step821 p h) (sat_cons (step327 p h) (sat_cons (step825 p h) (sat_nil p)))))))))
def c1533 : List Lit := [(1521, false), (1534, true), (1496, false), (166, true)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1042, c1045, c1102, c1079, c1084, c1106, c1059, c1061, c1046, c1057, c1043, c210, c214, c1037] c1533 (by decide) p (sat_cons (step1042 p h) (sat_cons (step1045 p h) (sat_cons (step1102 p h) (sat_cons (step1079 p h) (sat_cons (step1084 p h) (sat_cons (step1106 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1046 p h) (sat_cons (step1057 p h) (sat_cons (step1043 p h) (sat_cons (step210 p h) (sat_cons (step214 p h) (sat_cons (step1037 p h) (sat_nil p)))))))))))))))
def c1534 : List Lit := [(1525, true), (170, true), (1516, false), (3, false)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1072, c1079, c1083, c1073, c1059, c1068, c1056, c234, c217] c1534 (by decide) p (sat_cons (step1072 p h) (sat_cons (step1079 p h) (sat_cons (step1083 p h) (sat_cons (step1073 p h) (sat_cons (step1059 p h) (sat_cons (step1068 p h) (sat_cons (step1056 p h) (sat_cons (step234 p h) (sat_cons (step217 p h) (sat_nil p))))))))))
def c1535 : List Lit := [(49, true), (41, false), (159, true), (40, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c640, c192, c193, c196, c1424] c1535 (by decide) p (sat_cons (step640 p h) (sat_cons (step192 p h) (sat_cons (step193 p h) (sat_cons (step196 p h) (sat_cons (step1424 p h) (sat_nil p))))))
def c1536 : List Lit := [(1535, true), (1493, false), (1521, false), (1511, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c641, c1474, c1455, c643, c1048, c1059, c1084, c1103, c1107, c1089, c1049, c1062, c1040, c1042, c1037, c1038, c1035, c1036, c198, c201, c200, c753, c197, c755, c189, c764, c765, c785, c760, c791, c758, c748, c207, c745, c214, c744, c212, c743, c1535] c1536 (by decide) p (sat_cons (step641 p h) (sat_cons (step1474 p h) (sat_cons (step1455 p h) (sat_cons (step643 p h) (sat_cons (step1048 p h) (sat_cons (step1059 p h) (sat_cons (step1084 p h) (sat_cons (step1103 p h) (sat_cons (step1107 p h) (sat_cons (step1089 p h) (sat_cons (step1049 p h) (sat_cons (step1062 p h) (sat_cons (step1040 p h) (sat_cons (step1042 p h) (sat_cons (step1037 p h) (sat_cons (step1038 p h) (sat_cons (step1035 p h) (sat_cons (step1036 p h) (sat_cons (step198 p h) (sat_cons (step201 p h) (sat_cons (step200 p h) (sat_cons (step753 p h) (sat_cons (step197 p h) (sat_cons (step755 p h) (sat_cons (step189 p h) (sat_cons (step764 p h) (sat_cons (step765 p h) (sat_cons (step785 p h) (sat_cons (step760 p h) (sat_cons (step791 p h) (sat_cons (step758 p h) (sat_cons (step748 p h) (sat_cons (step207 p h) (sat_cons (step745 p h) (sat_cons (step214 p h) (sat_cons (step744 p h) (sat_cons (step212 p h) (sat_cons (step743 p h) (sat_cons (step1535 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1537 : List Lit := [(15, false), (157, true), (35, false), (39, false), (40, true), (1463, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c167, c1519, c183] c1537 (by decide) p (sat_cons (step167 p h) (sat_cons (step1519 p h) (sat_cons (step183 p h) (sat_nil p))))
def c1538 : List Lit := [(36, true), (37, true), (159, true), (20, true), (156, true), (41, false), (40, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c640, c180, c194, c196] c1538 (by decide) p (sat_cons (step640 p h) (sat_cons (step180 p h) (sat_cons (step194 p h) (sat_cons (step196 p h) (sat_nil p)))))
def c1539 : List Lit := [(1630, true), (1621, false), (88, false), (24, false)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1277, c1281, c1271, c1259, c1266, c462] c1539 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1277 p h) (sat_cons (step1281 p h) (sat_cons (step1271 p h) (sat_cons (step1259 p h) (sat_cons (step1266 p h) (sat_cons (step462 p h) (sat_nil p))))))))
def c1540 : List Lit := [(1665, true), (105, false), (1626, false), (90, true), (1641, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1259, c1282, c1324, c1348, c1344, c1287, c1325, c1260, c1314, c1316, c1255, c1311, c1312, c1309, c590, c610, c607] c1540 (by decide) p (sat_cons (step1259 p h) (sat_cons (step1282 p h) (sat_cons (step1324 p h) (sat_cons (step1348 p h) (sat_cons (step1344 p h) (sat_cons (step1287 p h) (sat_cons (step1325 p h) (sat_cons (step1260 p h) (sat_cons (step1314 p h) (sat_cons (step1316 p h) (sat_cons (step1255 p h) (sat_cons (step1311 p h) (sat_cons (step1312 p h) (sat_cons (step1309 p h) (sat_cons (step590 p h) (sat_cons (step610 p h) (sat_cons (step607 p h) (sat_nil p))))))))))))))))))
def c1541 : List Lit := [(1452, true), (1444, false), (11, true), (126, true)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c934, c943, c950, c954, c946, c929, c936, c926, c927, c40, c31] c1541 (by decide) p (sat_cons (step934 p h) (sat_cons (step943 p h) (sat_cons (step950 p h) (sat_cons (step954 p h) (sat_cons (step946 p h) (sat_cons (step929 p h) (sat_cons (step936 p h) (sat_cons (step926 p h) (sat_cons (step927 p h) (sat_cons (step40 p h) (sat_cons (step31 p h) (sat_nil p))))))))))))
def c1542 : List Lit := [(1470, true), (20, true), (135, true)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c985, c988, c980, c967, c969, c973, c965, c92, c82] c1542 (by decide) p (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step980 p h) (sat_cons (step967 p h) (sat_cons (step969 p h) (sat_cons (step973 p h) (sat_cons (step965 p h) (sat_cons (step92 p h) (sat_cons (step82 p h) (sat_nil p))))))))))
def c1543 : List Lit := [(1459, true), (16, false), (1452, true), (261, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c618, c621, c961, c699, c686, c681, c679, c685, c684, c683, c697, c695, c689, c967, c969, c965, c77, c71, c1526, c2, c1520, c36, c33, c41, c26] c1543 (by decide) p (sat_cons (step618 p h) (sat_cons (step621 p h) (sat_cons (step961 p h) (sat_cons (step699 p h) (sat_cons (step686 p h) (sat_cons (step681 p h) (sat_cons (step679 p h) (sat_cons (step685 p h) (sat_cons (step684 p h) (sat_cons (step683 p h) (sat_cons (step697 p h) (sat_cons (step695 p h) (sat_cons (step689 p h) (sat_cons (step967 p h) (sat_cons (step969 p h) (sat_cons (step965 p h) (sat_cons (step77 p h) (sat_cons (step71 p h) (sat_cons (step1526 p h) (sat_cons (step2 p h) (sat_cons (step1520 p h) (sat_cons (step36 p h) (sat_cons (step33 p h) (sat_cons (step41 p h) (sat_cons (step26 p h) (sat_nil p))))))))))))))))))))))))))
def c1544 : List Lit := [(1471, true), (15, false), (17, true), (1459, false), (16, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c992, c989, c970, c980, c965, c973, c80] c1544 (by decide) p (sat_cons (step992 p h) (sat_cons (step989 p h) (sat_cons (step970 p h) (sat_cons (step980 p h) (sat_cons (step965 p h) (sat_cons (step973 p h) (sat_cons (step80 p h) (sat_nil p))))))))
def c1545 : List Lit := [(15, true), (17, true), (1480, true), (92, true), (145, true), (24, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c631, c969, c937, c147, c1516, c1010, c992, c989, c970, c978, c965, c976, c96, c149] c1545 (by decide) p (sat_cons (step631 p h) (sat_cons (step969 p h) (sat_cons (step937 p h) (sat_cons (step147 p h) (sat_cons (step1516 p h) (sat_cons (step1010 p h) (sat_cons (step992 p h) (sat_cons (step989 p h) (sat_cons (step970 p h) (sat_cons (step978 p h) (sat_cons (step965 p h) (sat_cons (step976 p h) (sat_cons (step96 p h) (sat_cons (step149 p h) (sat_nil p)))))))))))))))
def c1546 : List Lit := [(1471, true), (15, false), (17, true), (142, true), (24, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c969, c992, c989, c970, c978, c980, c964, c965, c976, c973, c114, c94, c140, c139] c1546 (by decide) p (sat_cons (step969 p h) (sat_cons (step992 p h) (sat_cons (step989 p h) (sat_cons (step970 p h) (sat_cons (step978 p h) (sat_cons (step980 p h) (sat_cons (step964 p h) (sat_cons (step965 p h) (sat_cons (step976 p h) (sat_cons (step973 p h) (sat_cons (step114 p h) (sat_cons (step94 p h) (sat_cons (step140 p h) (sat_cons (step139 p h) (sat_nil p)))))))))))))))
def c1547 : List Lit := [(1591, true), (15, false), (199, true), (105, false), (89, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1195, c1197, c1193, c1189, c1190, c399, c340, c419, c433, c350] c1547 (by decide) p (sat_cons (step1195 p h) (sat_cons (step1197 p h) (sat_cons (step1193 p h) (sat_cons (step1189 p h) (sat_cons (step1190 p h) (sat_cons (step399 p h) (sat_cons (step340 p h) (sat_cons (step419 p h) (sat_cons (step433 p h) (sat_cons (step350 p h) (sat_nil p)))))))))))
def c1548 : List Lit := [(1533, true), (1493, false), (1504, false), (163, true), (1520, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1078, c1105, c1101, c1049, c1083, c1040, c1061, c1037, c1038, c198, c201] c1548 (by decide) p (sat_cons (step1078 p h) (sat_cons (step1105 p h) (sat_cons (step1101 p h) (sat_cons (step1049 p h) (sat_cons (step1083 p h) (sat_cons (step1040 p h) (sat_cons (step1061 p h) (sat_cons (step1037 p h) (sat_cons (step1038 p h) (sat_cons (step198 p h) (sat_cons (step201 p h) (sat_nil p))))))))))))
def c1549 : List Lit := [(52, false), (1588, true), (17, false), (170, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c233, c374, c375, c1191] c1549 (by decide) p (sat_cons (step233 p h) (sat_cons (step374 p h) (sat_cons (step375 p h) (sat_cons (step1191 p h) (sat_nil p)))))
def c1550 : List Lit := [(11, true), (1452, true), (259, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c625, c694, c692, c691, c695, c689, c60, c1541, c58, c938] c1550 (by decide) p (sat_cons (step625 p h) (sat_cons (step694 p h) (sat_cons (step692 p h) (sat_cons (step691 p h) (sat_cons (step695 p h) (sat_cons (step689 p h) (sat_cons (step60 p h) (sat_cons (step1541 p h) (sat_cons (step58 p h) (sat_cons (step938 p h) (sat_nil p)))))))))))
def c1551 : List Lit := [(67, true), (1576, true), (405, true), (105, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c653, c1171, c1168, c850, c816, c814, c808, c807, c813, c812, c811, c848, c845, c829, c824, c320, c1158, c1159, c1165, c1166, c1174, c1160, c1161, c1154, c327, c315, c1153, c311, c318, c290] c1551 (by decide) p (sat_cons (step653 p h) (sat_cons (step1171 p h) (sat_cons (step1168 p h) (sat_cons (step850 p h) (sat_cons (step816 p h) (sat_cons (step814 p h) (sat_cons (step808 p h) (sat_cons (step807 p h) (sat_cons (step813 p h) (sat_cons (step812 p h) (sat_cons (step811 p h) (sat_cons (step848 p h) (sat_cons (step845 p h) (sat_cons (step829 p h) (sat_cons (step824 p h) (sat_cons (step320 p h) (sat_cons (step1158 p h) (sat_cons (step1159 p h) (sat_cons (step1165 p h) (sat_cons (step1166 p h) (sat_cons (step1174 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1154 p h) (sat_cons (step327 p h) (sat_cons (step315 p h) (sat_cons (step1153 p h) (sat_cons (step311 p h) (sat_cons (step318 p h) (sat_cons (step290 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1552 : List Lit := [(1525, true), (170, true), (57, true)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1067, c1070, c1079, c1083, c1071, c1073, c1059, c1069, c1064, c1056, c234, c222] c1552 (by decide) p (sat_cons (step1067 p h) (sat_cons (step1070 p h) (sat_cons (step1079 p h) (sat_cons (step1083 p h) (sat_cons (step1071 p h) (sat_cons (step1073 p h) (sat_cons (step1059 p h) (sat_cons (step1069 p h) (sat_cons (step1064 p h) (sat_cons (step1056 p h) (sat_cons (step234 p h) (sat_cons (step222 p h) (sat_nil p)))))))))))))
def c1553 : List Lit := [(52, false), (55, false), (56, false), (170, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c234, c222] c1553 (by decide) p (sat_cons (step234 p h) (sat_cons (step222 p h) (sat_nil p)))
def c1554 : List Lit := [(1587, true), (83, false), (95, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1189, c1190, c400] c1554 (by decide) p (sat_cons (step1189 p h) (sat_cons (step1190 p h) (sat_cons (step400 p h) (sat_nil p))))
def c1555 : List Lit := [(83, false), (1592, true), (95, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1200, c1554, c1198, c1193, c402, c405, c1191] c1555 (by decide) p (sat_cons (step1200 p h) (sat_cons (step1554 p h) (sat_cons (step1198 p h) (sat_cons (step1193 p h) (sat_cons (step402 p h) (sat_cons (step405 p h) (sat_cons (step1191 p h) (sat_nil p))))))))
def c1556 : List Lit := [(83, true), (92, false), (95, false), (213, true), (110, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c523, c522, c505] c1556 (by decide) p (sat_cons (step523 p h) (sat_cons (step522 p h) (sat_cons (step505 p h) (sat_nil p))))
def c1557 : List Lit := [(17, false), (1593, true), (95, false), (83, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c386, c381, c384, c1193, c1191, c1201] c1557 (by decide) p (sat_cons (step386 p h) (sat_cons (step381 p h) (sat_cons (step384 p h) (sat_cons (step1193 p h) (sat_cons (step1191 p h) (sat_cons (step1201 p h) (sat_nil p)))))))
def c1558 : List Lit := [(1533, true), (1521, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1495, c1079, c1095, c1101, c1084, c1045, c1059, c1061, c1040, c1057, c1037, c1038, c1511, c198, c210, c207, c759] c1558 (by decide) p (sat_cons (step1495 p h) (sat_cons (step1079 p h) (sat_cons (step1095 p h) (sat_cons (step1101 p h) (sat_cons (step1084 p h) (sat_cons (step1045 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1040 p h) (sat_cons (step1057 p h) (sat_cons (step1037 p h) (sat_cons (step1038 p h) (sat_cons (step1511 p h) (sat_cons (step198 p h) (sat_cons (step210 p h) (sat_cons (step207 p h) (sat_cons (step759 p h) (sat_nil p))))))))))))))))))
def c1559 : List Lit := [(54, false), (59, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1486, c1450, c280, c282, c278, c798, c801] c1559 (by decide) p (sat_cons (step1486 p h) (sat_cons (step1450 p h) (sat_cons (step280 p h) (sat_cons (step282 p h) (sat_cons (step278 p h) (sat_cons (step798 p h) (sat_cons (step801 p h) (sat_nil p))))))))
def c1560 : List Lit := [(1470, true), (24, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1463, c985, c988, c978, c980, c967, c969, c975, c976, c973, c964, c965, c102, c96, c140, c119, c1542, c139, c702, c712, c703, c713, c708, c721, c727] c1560 (by decide) p (sat_cons (step1463 p h) (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step978 p h) (sat_cons (step980 p h) (sat_cons (step967 p h) (sat_cons (step969 p h) (sat_cons (step975 p h) (sat_cons (step976 p h) (sat_cons (step973 p h) (sat_cons (step964 p h) (sat_cons (step965 p h) (sat_cons (step102 p h) (sat_cons (step96 p h) (sat_cons (step140 p h) (sat_cons (step119 p h) (sat_cons (step1542 p h) (sat_cons (step139 p h) (sat_cons (step702 p h) (sat_cons (step712 p h) (sat_cons (step703 p h) (sat_cons (step713 p h) (sat_cons (step708 p h) (sat_cons (step721 p h) (sat_cons (step727 p h) (sat_nil p))))))))))))))))))))))))))
def c1561 : List Lit := [(1587, true), (83, false), (17, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1189, c1190, c379] c1561 (by decide) p (sat_cons (step1189 p h) (sat_cons (step1190 p h) (sat_cons (step379 p h) (sat_nil p))))
def c1562 : List Lit := [(1592, true), (83, false), (17, false)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1200, c1198, c1193, c383, c380, c1191] c1562 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1200 p h) (sat_cons (step1198 p h) (sat_cons (step1193 p h) (sat_cons (step383 p h) (sat_cons (step380 p h) (sat_cons (step1191 p h) (sat_nil p))))))))
def c1563 : List Lit := [(1514, true), (45, false), (46, false), (52, true)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1495, c1056, c1060, c1521, c1062, c1058, c210, c198, c759, c207] c1563 (by decide) p (sat_cons (step1495 p h) (sat_cons (step1056 p h) (sat_cons (step1060 p h) (sat_cons (step1521 p h) (sat_cons (step1062 p h) (sat_cons (step1058 p h) (sat_cons (step210 p h) (sat_cons (step198 p h) (sat_cons (step759 p h) (sat_cons (step207 p h) (sat_nil p)))))))))))
def c1564 : List Lit := [(1621, true), (88, true), (98, false), (92, false), (90, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1482, c1262, c1263, c517, c546, c528, c540, c864, c866, c869] c1564 (by decide) p (sat_cons (step1482 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step517 p h) (sat_cons (step546 p h) (sat_cons (step528 p h) (sat_cons (step540 p h) (sat_cons (step864 p h) (sat_cons (step866 p h) (sat_cons (step869 p h) (sat_nil p)))))))))))
def c1565 : List Lit := [(216, true), (100, true), (98, false), (89, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c540, c539, c1441] c1565 (by decide) p (sat_cons (step540 p h) (sat_cons (step539 p h) (sat_cons (step1441 p h) (sat_nil p))))
def c1566 : List Lit := [(1498, true), (1514, true), (52, true)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1037, c1038, c1563] c1566 (by decide) p (sat_cons (step1037 p h) (sat_cons (step1038 p h) (sat_cons (step1563 p h) (sat_nil p))))
def c1567 : List Lit := [(35, false), (15, false), (39, false), (1463, true), (41, false), (157, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c189, c1537] c1567 (by decide) p (sat_cons (step189 p h) (sat_cons (step1537 p h) (sat_nil p)))
def c1568 : List Lit := [(17, false), (1471, true), (135, true), (20, true), (15, false)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c92, c77, c78, c965, c973, c967, c980, c989] c1568 (by decide) p (sat_cons (step92 p h) (sat_cons (step77 p h) (sat_cons (step78 p h) (sat_cons (step965 p h) (sat_cons (step973 p h) (sat_cons (step967 p h) (sat_cons (step980 p h) (sat_cons (step989 p h) (sat_nil p)))))))))
def c1569 : List Lit := [(22, false), (41, false), (140, true), (30, true), (39, false), (21, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c188, c124] c1569 (by decide) p (sat_cons (step188 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1570 : List Lit := [(106, false), (83, true), (102, false), (82, false), (117, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c578, c551, c556] c1570 (by decide) p (sat_cons (step578 p h) (sat_cons (step551 p h) (sat_cons (step556 p h) (sat_nil p))))
def c1571 : List Lit := [(1621, true), (100, false), (98, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1263, c547] c1571 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step547 p h) (sat_nil p))))
def c1572 : List Lit := [(103, false), (232, true), (110, false), (1644, true)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1309, c1308, c593, c594, c605] c1572 (by decide) p (sat_cons (step1309 p h) (sat_cons (step1308 p h) (sat_cons (step593 p h) (sat_cons (step594 p h) (sat_cons (step605 p h) (sat_nil p))))))
def c1573 : List Lit := [(39, false), (1471, true), (21, false), (24, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1523, c121, c980, c964, c989, c967] c1573 (by decide) p (sat_cons (step1523 p h) (sat_cons (step121 p h) (sat_cons (step980 p h) (sat_cons (step964 p h) (sat_cons (step989 p h) (sat_cons (step967 p h) (sat_nil p)))))))
def c1574 : List Lit := [(1505, false), (1525, false), (1513, false), (1479, false), (1666, false), (1596, false)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1411, c1222, c1366, c1406, c1127, c1106, c1107, c1126, c1084, c1405, c1504, c1373, c1155, c1230, c1173] c1574 (by decide) p (sat_cons (step1411 p h) (sat_cons (step1222 p h) (sat_cons (step1366 p h) (sat_cons (step1406 p h) (sat_cons (step1127 p h) (sat_cons (step1106 p h) (sat_cons (step1107 p h) (sat_cons (step1126 p h) (sat_cons (step1084 p h) (sat_cons (step1405 p h) (sat_cons (step1504 p h) (sat_cons (step1373 p h) (sat_cons (step1155 p h) (sat_cons (step1230 p h) (sat_cons (step1173 p h) (sat_nil p))))))))))))))))
def c1575 : List Lit := [(1470, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c985, c1560, c980, c972] c1575 (by decide) p (sat_cons (step985 p h) (sat_cons (step1560 p h) (sat_cons (step980 p h) (sat_cons (step972 p h) (sat_nil p)))))
def c1576 : List Lit := [(1478, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1513, c1003] c1576 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1513 p h) (sat_cons (step1003 p h) (sat_nil p))))
def c1577 : List Lit := [(114, false), (232, true), (118, true), (111, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c603, c604, c1449] c1577 (by decide) p (sat_cons (step603 p h) (sat_cons (step604 p h) (sat_cons (step1449 p h) (sat_nil p))))
end B112E027
