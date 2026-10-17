import B112E186Part0000
namespace B112E186
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1464 : List Lit := [(70, true), (1697, true), (1676, true), (83, true), (1678, false), (85, false), (13, false)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c691, c1101, c1461, c1122, c1067, c1075, c1081, c1156, c1139, c1110, c1462, c1463, c1162, c1134, c1107, c1098, c1099, c274, c283] c1464 (by decide) p (sat_cons (step691 p h) (sat_cons (step1101 p h) (sat_cons (step1461 p h) (sat_cons (step1122 p h) (sat_cons (step1067 p h) (sat_cons (step1075 p h) (sat_cons (step1081 p h) (sat_cons (step1156 p h) (sat_cons (step1139 p h) (sat_cons (step1110 p h) (sat_cons (step1462 p h) (sat_cons (step1463 p h) (sat_cons (step1162 p h) (sat_cons (step1134 p h) (sat_cons (step1107 p h) (sat_cons (step1098 p h) (sat_cons (step1099 p h) (sat_cons (step274 p h) (sat_cons (step283 p h) (sat_nil p))))))))))))))))))))
def c1465 : List Lit := [(1667, true), (81, false)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c691, c1098, c1099, c274, c283] c1465 (by decide) p (sat_cons (step691 p h) (sat_cons (step1098 p h) (sat_cons (step1099 p h) (sat_cons (step274 p h) (sat_cons (step283 p h) (sat_nil p))))))
def c1466 : List Lit := [(1759, true), (1743, false), (1747, false), (1717, false), (1712, false)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c705, c704, c1202, c1216, c1282, c1278, c1217, c1257, c1261, c1203, c1205, c1234, c1236, c1197, c1231, c1232, c1228, c1229, c624, c600, c1444, c617, c641, c560, c612, c1201, c551] c1466 (by decide) p (sat_cons (step705 p h) (sat_cons (step704 p h) (sat_cons (step1202 p h) (sat_cons (step1216 p h) (sat_cons (step1282 p h) (sat_cons (step1278 p h) (sat_cons (step1217 p h) (sat_cons (step1257 p h) (sat_cons (step1261 p h) (sat_cons (step1203 p h) (sat_cons (step1205 p h) (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1197 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step1228 p h) (sat_cons (step1229 p h) (sat_cons (step624 p h) (sat_cons (step600 p h) (sat_cons (step1444 p h) (sat_cons (step617 p h) (sat_cons (step641 p h) (sat_cons (step560 p h) (sat_cons (step612 p h) (sat_cons (step1201 p h) (sat_cons (step551 p h) (sat_nil p))))))))))))))))))))))))))))
def c1467 : List Lit := [(1748, true), (101, false), (107, false), (1743, false)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c704, c1257, c1261, c1234, c1236, c1231, c1232, c1228, c1229, c624, c551, c600, c1444, c612, c641] c1467 (by decide) p (sat_cons (step704 p h) (sat_cons (step1257 p h) (sat_cons (step1261 p h) (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step1228 p h) (sat_cons (step1229 p h) (sat_cons (step624 p h) (sat_cons (step551 p h) (sat_cons (step600 p h) (sat_cons (step1444 p h) (sat_cons (step612 p h) (sat_cons (step641 p h) (sat_nil p))))))))))))))))
def c1468 : List Lit := [(113, false), (1731, true), (114, false), (101, false), (107, false)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c704, c1229, c1228, c624, c551, c600, c612, c614, c1385] c1468 (by decide) p (sat_cons (step704 p h) (sat_cons (step1229 p h) (sat_cons (step1228 p h) (sat_cons (step624 p h) (sat_cons (step551 p h) (sat_cons (step600 p h) (sat_cons (step612 p h) (sat_cons (step614 p h) (sat_cons (step1385 p h) (sat_nil p))))))))))
def c1469 : List Lit := [(1544, true), (1519, false)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c1426, c854, c877, c890, c893, c880, c878, c1449, c857, c868, c830, c848, c865, c866, c79, c1450] c1469 (by decide) p (sat_cons (step1426 p h) (sat_cons (step854 p h) (sat_cons (step877 p h) (sat_cons (step890 p h) (sat_cons (step893 p h) (sat_cons (step880 p h) (sat_cons (step878 p h) (sat_cons (step1449 p h) (sat_cons (step857 p h) (sat_cons (step868 p h) (sat_cons (step830 p h) (sat_cons (step848 p h) (sat_cons (step865 p h) (sat_cons (step866 p h) (sat_cons (step79 p h) (sat_cons (step1450 p h) (sat_nil p)))))))))))))))))
def c1470 : List Lit := [(1590, true), (50, false)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c682, c965, c966, c201, c199] c1470 (by decide) p (sat_cons (step682 p h) (sat_cons (step965 p h) (sat_cons (step966 p h) (sat_cons (step201 p h) (sat_cons (step199 p h) (sat_nil p))))))
def c1471 : List Lit := [(1712, true), (98, true), (101, false)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c1186, c1189, c1191, c1187, c1454] c1471 (by decide) p (sat_cons (step1186 p h) (sat_cons (step1189 p h) (sat_cons (step1191 p h) (sat_cons (step1187 p h) (sat_cons (step1454 p h) (sat_nil p))))))
def c1472 : List Lit := [(51, false), (100, false), (103, false), (111, true), (112, false)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c703, c678, c383, c602, c173, c495] c1472 (by decide) p (sat_cons (step703 p h) (sat_cons (step678 p h) (sat_cons (step383 p h) (sat_cons (step602 p h) (sat_cons (step173 p h) (sat_cons (step495 p h) (sat_nil p)))))))
def c1473 : List Lit := [(1671, true)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c1104, c1106, c1102, c1465] c1473 (by decide) p (sat_cons (step1104 p h) (sat_cons (step1106 p h) (sat_cons (step1102 p h) (sat_cons (step1465 p h) (sat_nil p)))))
def c1474 : List Lit := [(1517, false), (1546, true), (26, true), (27, true), (19, true)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c1426, c668, c866, c868, c892, c885, c851, c857, c858, c881, c882, c853, c895, c869, c1449, c867, c830, c47, c86] c1474 (by decide) p (sat_cons (step1426 p h) (sat_cons (step668 p h) (sat_cons (step866 p h) (sat_cons (step868 p h) (sat_cons (step892 p h) (sat_cons (step885 p h) (sat_cons (step851 p h) (sat_cons (step857 p h) (sat_cons (step858 p h) (sat_cons (step881 p h) (sat_cons (step882 p h) (sat_cons (step853 p h) (sat_cons (step895 p h) (sat_cons (step869 p h) (sat_cons (step1449 p h) (sat_cons (step867 p h) (sat_cons (step830 p h) (sat_cons (step47 p h) (sat_cons (step86 p h) (sat_nil p))))))))))))))))))))
def c1475 : List Lit := [(1598, false), (1630, true), (26, true), (27, true), (35, false), (1556, false), (19, true), (112, false)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c1429, c851, c1469, c1025, c914, c936, c994, c1004, c1038, c943, c916, c1474, c848, c115, c116, c911] c1475 (by decide) p (sat_cons (step1429 p h) (sat_cons (step851 p h) (sat_cons (step1469 p h) (sat_cons (step1025 p h) (sat_cons (step914 p h) (sat_cons (step936 p h) (sat_cons (step994 p h) (sat_cons (step1004 p h) (sat_cons (step1038 p h) (sat_cons (step943 p h) (sat_cons (step916 p h) (sat_cons (step1474 p h) (sat_cons (step848 p h) (sat_cons (step115 p h) (sat_cons (step116 p h) (sat_cons (step911 p h) (sat_nil p)))))))))))))))))
def c1476 : List Lit := [(1598, true), (51, true), (1588, false)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c951, c954, c970, c983, c980, c955, c971, c953, c1470] c1476 (by decide) p (sat_cons (step951 p h) (sat_cons (step954 p h) (sat_cons (step970 p h) (sat_cons (step983 p h) (sat_cons (step980 p h) (sat_cons (step955 p h) (sat_cons (step971 p h) (sat_cons (step953 p h) (sat_cons (step1470 p h) (sat_nil p))))))))))
def c1477 : List Lit := [(35, true), (100, false), (103, false), (111, true), (112, false)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c703, c605, c603, c498] c1477 (by decide) p (sat_cons (step703 p h) (sat_cons (step605 p h) (sat_cons (step603 p h) (sat_cons (step498 p h) (sat_nil p)))))
def c1478 : List Lit := [(1672, true), (83, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c1101, c1105, c1107, c1103, c1465] c1478 (by decide) p (sat_cons (step1101 p h) (sat_cons (step1105 p h) (sat_cons (step1107 p h) (sat_cons (step1103 p h) (sat_cons (step1465 p h) (sat_nil p))))))
def c1479 : List Lit := [(1741, true), (120, false), (112, false)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1246, c638] c1479 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1246 p h) (sat_cons (step638 p h) (sat_nil p))))
def c1480 : List Lit := [(1580, false), (1598, true), (1588, false)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c970, c983, c956, c957, c980, c952, c971, c1470] c1480 (by decide) p (sat_cons (step970 p h) (sat_cons (step983 p h) (sat_cons (step956 p h) (sat_cons (step957 p h) (sat_cons (step980 p h) (sat_cons (step952 p h) (sat_cons (step971 p h) (sat_cons (step1470 p h) (sat_nil p)))))))))
def c1481 : List Lit := [(48, false), (67, false), (1662, true), (107, false)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c233, c236, c238, c239, c1058, c1067, c1070, c1060, c1076, c1091] c1481 (by decide) p (sat_cons (step233 p h) (sat_cons (step236 p h) (sat_cons (step238 p h) (sat_cons (step239 p h) (sat_cons (step1058 p h) (sat_cons (step1067 p h) (sat_cons (step1070 p h) (sat_cons (step1060 p h) (sat_cons (step1076 p h) (sat_cons (step1091 p h) (sat_nil p)))))))))))
def c1482 : List Lit := [(1597, true), (1588, false)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c970, c976, c979, c971, c954, c1470, c952] c1482 (by decide) p (sat_cons (step970 p h) (sat_cons (step976 p h) (sat_cons (step979 p h) (sat_cons (step971 p h) (sat_cons (step954 p h) (sat_cons (step1470 p h) (sat_cons (step952 p h) (sat_nil p))))))))
def c1483 : List Lit := [(1655, true), (67, false), (107, false)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c1073, c1075, c1070, c1067, c249] c1483 (by decide) p (sat_cons (step1073 p h) (sat_cons (step1075 p h) (sat_cons (step1070 p h) (sat_cons (step1067 p h) (sat_cons (step249 p h) (sat_nil p))))))
def c1484 : List Lit := [(70, false), (1646, true), (67, false), (107, false)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c244, c247, c1058] c1484 (by decide) p (sat_cons (step244 p h) (sat_cons (step247 p h) (sat_cons (step1058 p h) (sat_nil p))))
def c1485 : List Lit := [(65, true), (1661, true), (67, false), (107, false)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c1483, c1090, c1060, c1484, c1067, c1057, c1058, c1059, c248, c1087, c1070, c1076] c1485 (by decide) p (sat_cons (step1483 p h) (sat_cons (step1090 p h) (sat_cons (step1060 p h) (sat_cons (step1484 p h) (sat_cons (step1067 p h) (sat_cons (step1057 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step248 p h) (sat_cons (step1087 p h) (sat_cons (step1070 p h) (sat_cons (step1076 p h) (sat_nil p)))))))))))))
def c1486 : List Lit := [(1661, true), (67, false), (107, false)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c1483, c1090, c1060, c1484, c1067, c1485, c242, c245, c1056, c1070, c1059, c1076, c1087] c1486 (by decide) p (sat_cons (step1483 p h) (sat_cons (step1090 p h) (sat_cons (step1060 p h) (sat_cons (step1484 p h) (sat_cons (step1067 p h) (sat_cons (step1485 p h) (sat_cons (step242 p h) (sat_cons (step245 p h) (sat_cons (step1056 p h) (sat_cons (step1070 p h) (sat_cons (step1059 p h) (sat_cons (step1076 p h) (sat_cons (step1087 p h) (sat_nil p))))))))))))))
def c1487 : List Lit := [(1712, true), (1715, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c698, c1197, c1196, c1193, c1471, c524, c466, c460, c461, c1184] c1487 (by decide) p (sat_cons (step698 p h) (sat_cons (step1197 p h) (sat_cons (step1196 p h) (sat_cons (step1193 p h) (sat_cons (step1471 p h) (sat_cons (step524 p h) (sat_cons (step466 p h) (sat_cons (step460 p h) (sat_cons (step461 p h) (sat_cons (step1184 p h) (sat_nil p)))))))))))
def c1488 : List Lit := [(83, true), (1697, true), (67, true), (1682, false), (111, true)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c690, c687, c1151, c1140, c1101, c1478, c1110, c1135, c1156, c1081, c1085, c1073, c1075, c1059, c1061, c1070, c1068, c1056, c1057, c1054, c272, c217, c269, c254, c1100, c276] c1488 (by decide) p (sat_cons (step690 p h) (sat_cons (step687 p h) (sat_cons (step1151 p h) (sat_cons (step1140 p h) (sat_cons (step1101 p h) (sat_cons (step1478 p h) (sat_cons (step1110 p h) (sat_cons (step1135 p h) (sat_cons (step1156 p h) (sat_cons (step1081 p h) (sat_cons (step1085 p h) (sat_cons (step1073 p h) (sat_cons (step1075 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1070 p h) (sat_cons (step1068 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1054 p h) (sat_cons (step272 p h) (sat_cons (step217 p h) (sat_cons (step269 p h) (sat_cons (step254 p h) (sat_cons (step1100 p h) (sat_cons (step276 p h) (sat_nil p)))))))))))))))))))))))))))
def c1489 : List Lit := [(99, false), (1714, true), (97, true), (121, false), (1715, true)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c698, c1197, c1196, c1392, c484, c483, c505, c1184, c466, c1195, c1187] c1489 (by decide) p (sat_cons (step698 p h) (sat_cons (step1197 p h) (sat_cons (step1196 p h) (sat_cons (step1392 p h) (sat_cons (step484 p h) (sat_cons (step483 p h) (sat_cons (step505 p h) (sat_cons (step1184 p h) (sat_cons (step466 p h) (sat_cons (step1195 p h) (sat_cons (step1187 p h) (sat_nil p))))))))))))
def c1490 : List Lit := [(98, false), (1525, true), (1715, true)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c698, c863, c862, c1197, c1196, c524, c467, c71] c1490 (by decide) p (sat_cons (step698 p h) (sat_cons (step863 p h) (sat_cons (step862 p h) (sat_cons (step1197 p h) (sat_cons (step1196 p h) (sat_cons (step524 p h) (sat_cons (step467 p h) (sat_cons (step71 p h) (sat_nil p)))))))))
def c1491 : List Lit := [(1683, true)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c1473, c1126] c1491 (by decide) p (sat_cons (step1473 p h) (sat_cons (step1126 p h) (sat_nil p)))
def c1492 : List Lit := [(1691, true)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c1491, c1145] c1492 (by decide) p (sat_cons (step1491 p h) (sat_cons (step1145 p h) (sat_nil p)))
def c1493 : List Lit := [(1599, true), (1581, false), (1588, false)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c959, c970, c986, c984, c960, c971, c952, c1470] c1493 (by decide) p (sat_cons (step959 p h) (sat_cons (step970 p h) (sat_cons (step986 p h) (sat_cons (step984 p h) (sat_cons (step960 p h) (sat_cons (step971 p h) (sat_cons (step952 p h) (sat_cons (step1470 p h) (sat_nil p)))))))))
def c1494 : List Lit := [(1561, true), (35, false), (33, true), (112, false)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c906, c917, c915, c908, c910, c120] c1494 (by decide) p (sat_cons (step906 p h) (sat_cons (step917 p h) (sat_cons (step915 p h) (sat_cons (step908 p h) (sat_cons (step910 p h) (sat_cons (step120 p h) (sat_nil p)))))))
def c1495 : List Lit := [(83, true), (1696, true), (67, true), (1681, false), (111, true)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c690, c687, c1150, c1139, c1101, c1478, c1110, c1134, c1155, c1081, c1085, c1073, c1075, c1059, c1061, c1070, c1068, c1056, c1057, c1054, c272, c217, c269, c254, c1100, c276] c1495 (by decide) p (sat_cons (step690 p h) (sat_cons (step687 p h) (sat_cons (step1150 p h) (sat_cons (step1139 p h) (sat_cons (step1101 p h) (sat_cons (step1478 p h) (sat_cons (step1110 p h) (sat_cons (step1134 p h) (sat_cons (step1155 p h) (sat_cons (step1081 p h) (sat_cons (step1085 p h) (sat_cons (step1073 p h) (sat_cons (step1075 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1070 p h) (sat_cons (step1068 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1054 p h) (sat_cons (step272 p h) (sat_cons (step217 p h) (sat_cons (step269 p h) (sat_cons (step254 p h) (sat_cons (step1100 p h) (sat_cons (step276 p h) (sat_nil p)))))))))))))))))))))))))))
def c1496 : List Lit := [(1713, false), (94, false), (1726, true), (1760, true), (119, true), (108, true), (1735, false)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c706, c1220, c1221, c1279, c1202, c1262, c1200, c1253, c1244, c628, c625] c1496 (by decide) p (sat_cons (step706 p h) (sat_cons (step1220 p h) (sat_cons (step1221 p h) (sat_cons (step1279 p h) (sat_cons (step1202 p h) (sat_cons (step1262 p h) (sat_cons (step1200 p h) (sat_cons (step1253 p h) (sat_cons (step1244 p h) (sat_cons (step628 p h) (sat_cons (step625 p h) (sat_nil p))))))))))))
def c1497 : List Lit := [(1659, true), (1668, true), (67, true), (111, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c690, c687, c1081, c1085, c1073, c1075, c1059, c1061, c1070, c1068, c1056, c1057, c1054, c272, c217, c269, c254, c1100, c276] c1497 (by decide) p (sat_cons (step690 p h) (sat_cons (step687 p h) (sat_cons (step1081 p h) (sat_cons (step1085 p h) (sat_cons (step1073 p h) (sat_cons (step1075 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1070 p h) (sat_cons (step1068 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1054 p h) (sat_cons (step272 p h) (sat_cons (step217 p h) (sat_cons (step269 p h) (sat_cons (step254 p h) (sat_cons (step1100 p h) (sat_cons (step276 p h) (sat_nil p))))))))))))))))))))
def c1498 : List Lit := [(1653, true), (1647, true), (1672, true), (1687, false), (1580, false), (1504, false), (1760, false), (1573, false), (67, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c690, c689, c692, c658, c682, c684, c1350, c1061, c1053, c1059, c1057, c1056, c1109, c1070, c1071, c272, c269, c1099, c1100, c1107, c1102, c280, c261, c262, c277, c264, c286, c288, c250, c251, c1463, c17, c200, c214, c213, c1422, c1162, c829, c965, c1367, c1326, c836, c968, c953, c1344, c843, c958, c898, c986, c1024, c995] c1498 (by decide) p (sat_cons (step690 p h) (sat_cons (step689 p h) (sat_cons (step692 p h) (sat_cons (step658 p h) (sat_cons (step682 p h) (sat_cons (step684 p h) (sat_cons (step1350 p h) (sat_cons (step1061 p h) (sat_cons (step1053 p h) (sat_cons (step1059 p h) (sat_cons (step1057 p h) (sat_cons (step1056 p h) (sat_cons (step1109 p h) (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step272 p h) (sat_cons (step269 p h) (sat_cons (step1099 p h) (sat_cons (step1100 p h) (sat_cons (step1107 p h) (sat_cons (step1102 p h) (sat_cons (step280 p h) (sat_cons (step261 p h) (sat_cons (step262 p h) (sat_cons (step277 p h) (sat_cons (step264 p h) (sat_cons (step286 p h) (sat_cons (step288 p h) (sat_cons (step250 p h) (sat_cons (step251 p h) (sat_cons (step1463 p h) (sat_cons (step17 p h) (sat_cons (step200 p h) (sat_cons (step214 p h) (sat_cons (step213 p h) (sat_cons (step1422 p h) (sat_cons (step1162 p h) (sat_cons (step829 p h) (sat_cons (step965 p h) (sat_cons (step1367 p h) (sat_cons (step1326 p h) (sat_cons (step836 p h) (sat_cons (step968 p h) (sat_cons (step953 p h) (sat_cons (step1344 p h) (sat_cons (step843 p h) (sat_cons (step958 p h) (sat_cons (step898 p h) (sat_cons (step986 p h) (sat_cons (step1024 p h) (sat_cons (step995 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1499 : List Lit := [(59, false), (81, false), (62, false)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c682, c200, c216] c1499 (by decide) p (sat_cons (step682 p h) (sat_cons (step200 p h) (sat_cons (step216 p h) (sat_nil p))))
def c1500 : List Lit := [(69, false), (78, false), (1647, true), (111, true)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c687, c1061, c1054, c1059, c1057, c1056, c217, c276, c254] c1500 (by decide) p (sat_cons (step687 p h) (sat_cons (step1061 p h) (sat_cons (step1054 p h) (sat_cons (step1059 p h) (sat_cons (step1057 p h) (sat_cons (step1056 p h) (sat_cons (step217 p h) (sat_cons (step276 p h) (sat_cons (step254 p h) (sat_nil p))))))))))
def c1501 : List Lit := [(1544, true), (1512, false)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c668, c893, c1469, c874, c877, c852, c868, c856, c865, c866, c848, c79, c50, c86] c1501 (by decide) p (sat_cons (step668 p h) (sat_cons (step893 p h) (sat_cons (step1469 p h) (sat_cons (step874 p h) (sat_cons (step877 p h) (sat_cons (step852 p h) (sat_cons (step868 p h) (sat_cons (step856 p h) (sat_cons (step865 p h) (sat_cons (step866 p h) (sat_cons (step848 p h) (sat_cons (step79 p h) (sat_cons (step50 p h) (sat_cons (step86 p h) (sat_nil p)))))))))))))))
def c1502 : List Lit := [(16, false), (17, false), (1527, true)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c668, c866, c865, c50, c79, c86] c1502 (by decide) p (sat_cons (step668 p h) (sat_cons (step866 p h) (sat_cons (step865 p h) (sat_cons (step50 p h) (sat_cons (step79 p h) (sat_cons (step86 p h) (sat_nil p)))))))
def c1503 : List Lit := [(1598, true), (70, false), (1643, true), (1580, false)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c684, c1054, c1053, c985, c1480, c958, c963, c190, c215, c208, c951, c953, c957, c1470, c983, c968] c1503 (by decide) p (sat_cons (step684 p h) (sat_cons (step1054 p h) (sat_cons (step1053 p h) (sat_cons (step985 p h) (sat_cons (step1480 p h) (sat_cons (step958 p h) (sat_cons (step963 p h) (sat_cons (step190 p h) (sat_cons (step215 p h) (sat_cons (step208 p h) (sat_cons (step951 p h) (sat_cons (step953 p h) (sat_cons (step957 p h) (sat_cons (step1470 p h) (sat_cons (step983 p h) (sat_cons (step968 p h) (sat_nil p)))))))))))))))))
def c1504 : List Lit := [(1545, false), (69, true), (1653, false), (1643, true), (1687, false), (1580, false), (1760, false), (1573, false)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c1350, c1068, c1076, c1082, c1162, c1326, c1344, c1431, c993, c1029, c1030, c1343, c994, c1332, c1503, c1169, c1069, c1083, c1079] c1504 (by decide) p (sat_cons (step1350 p h) (sat_cons (step1068 p h) (sat_cons (step1076 p h) (sat_cons (step1082 p h) (sat_cons (step1162 p h) (sat_cons (step1326 p h) (sat_cons (step1344 p h) (sat_cons (step1431 p h) (sat_cons (step993 p h) (sat_cons (step1029 p h) (sat_cons (step1030 p h) (sat_cons (step1343 p h) (sat_cons (step994 p h) (sat_cons (step1332 p h) (sat_cons (step1503 p h) (sat_cons (step1169 p h) (sat_cons (step1069 p h) (sat_cons (step1083 p h) (sat_cons (step1079 p h) (sat_nil p))))))))))))))))))))
def c1505 : List Lit := [(1, true), (1513, true), (131, true), (81, false), (13, true)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c658, c1422, c1404, c843, c17, c834, c22, c832] c1505 (by decide) p (sat_cons (step658 p h) (sat_cons (step1422 p h) (sat_cons (step1404 p h) (sat_cons (step843 p h) (sat_cons (step17 p h) (sat_cons (step834 p h) (sat_cons (step22 p h) (sat_cons (step832 p h) (sat_nil p)))))))))
def c1506 : List Lit := [(51, false), (52, false), (60, false), (62, false)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c678, c208, c187, c175] c1506 (by decide) p (sat_cons (step678 p h) (sat_cons (step208 p h) (sat_cons (step187 p h) (sat_cons (step175 p h) (sat_nil p)))))
def c1507 : List Lit := [(1533, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c874, c877, c868, c854, c856, c852, c848, c1502] c1507 (by decide) p (sat_cons (step874 p h) (sat_cons (step877 p h) (sat_cons (step868 p h) (sat_cons (step854 p h) (sat_cons (step856 p h) (sat_cons (step852 p h) (sat_cons (step848 p h) (sat_cons (step1502 p h) (sat_nil p)))))))))
def c1508 : List Lit := [(131, false), (1513, true), (1504, false)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1403, c1422, c829, c843, c836] c1508 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step1422 p h) (sat_cons (step829 p h) (sat_cons (step843 p h) (sat_cons (step836 p h) (sat_nil p)))))))
def c1509 : List Lit := [(1598, true), (51, true), (1580, false)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c951, c957, c985, c983, c958, c968, c953, c1470] c1509 (by decide) p (sat_cons (step951 p h) (sat_cons (step957 p h) (sat_cons (step985 p h) (sat_cons (step983 p h) (sat_cons (step958 p h) (sat_cons (step968 p h) (sat_cons (step953 p h) (sat_cons (step1470 p h) (sat_nil p)))))))))
def c1510 : List Lit := [(70, false), (36, false), (1514, true), (52, false), (62, false), (13, true), (67, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c688, c190, c259, c8, c9, c1420, c832, c826, c834, c844, c847, c837, c828, c829, c1401] c1510 (by decide) p (sat_cons (step688 p h) (sat_cons (step190 p h) (sat_cons (step259 p h) (sat_cons (step8 p h) (sat_cons (step9 p h) (sat_cons (step1420 p h) (sat_cons (step832 p h) (sat_cons (step826 p h) (sat_cons (step834 p h) (sat_cons (step844 p h) (sat_cons (step847 p h) (sat_cons (step837 p h) (sat_cons (step828 p h) (sat_cons (step829 p h) (sat_cons (step1401 p h) (sat_nil p))))))))))))))))
def c1511 : List Lit := [(1651, false), (1697, true), (1682, false), (1580, false), (1504, false), (1760, false), (1573, false), (67, true)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c1473, c1130, c1162, c1082, c1075, c1076, c1081, c1086, c1156, c1498, c1135] c1511 (by decide) p (sat_cons (step1473 p h) (sat_cons (step1130 p h) (sat_cons (step1162 p h) (sat_cons (step1082 p h) (sat_cons (step1075 p h) (sat_cons (step1076 p h) (sat_cons (step1081 p h) (sat_cons (step1086 p h) (sat_cons (step1156 p h) (sat_cons (step1498 p h) (sat_cons (step1135 p h) (sat_nil p))))))))))))
def c1512 : List Lit := [(51, false), (70, false), (60, false), (62, false)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c678, c208, c189, c175] c1512 (by decide) p (sat_cons (step678 p h) (sat_cons (step208 p h) (sat_cons (step189 p h) (sat_cons (step175 p h) (sat_nil p)))))
def c1513 : List Lit := [(1660, true), (50, false), (69, false), (1643, false), (67, true)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c685, c1061, c1089, c1086, c1062, c1073, c1056, c1057, c1071, c217, c251, c223] c1513 (by decide) p (sat_cons (step685 p h) (sat_cons (step1061 p h) (sat_cons (step1089 p h) (sat_cons (step1086 p h) (sat_cons (step1062 p h) (sat_cons (step1073 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1071 p h) (sat_cons (step217 p h) (sat_cons (step251 p h) (sat_cons (step223 p h) (sat_nil p)))))))))))))
def c1514 : List Lit := [(1534, true), (16, true), (86, true)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c661, c848, c856, c880, c878, c859, c857, c870, c850, c851, c862, c863, c28, c69, c35] c1514 (by decide) p (sat_cons (step661 p h) (sat_cons (step848 p h) (sat_cons (step856 p h) (sat_cons (step880 p h) (sat_cons (step878 p h) (sat_cons (step859 p h) (sat_cons (step857 p h) (sat_cons (step870 p h) (sat_cons (step850 p h) (sat_cons (step851 p h) (sat_cons (step862 p h) (sat_cons (step863 p h) (sat_cons (step28 p h) (sat_cons (step69 p h) (sat_cons (step35 p h) (sat_nil p))))))))))))))))
def c1515 : List Lit := [(1672, true), (1644, true), (50, true), (77, false), (76, true), (71, false), (69, false), (1599, true), (1580, false)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c689, c692, c684, c1099, c1109, c1107, c1100, c1102, c276, c280, c1055, c261, c277, c1499, c288, c965, c214, c213, c968, c1367, c986, c953, c958] c1515 (by decide) p (sat_cons (step689 p h) (sat_cons (step692 p h) (sat_cons (step684 p h) (sat_cons (step1099 p h) (sat_cons (step1109 p h) (sat_cons (step1107 p h) (sat_cons (step1100 p h) (sat_cons (step1102 p h) (sat_cons (step276 p h) (sat_cons (step280 p h) (sat_cons (step1055 p h) (sat_cons (step261 p h) (sat_cons (step277 p h) (sat_cons (step1499 p h) (sat_cons (step288 p h) (sat_cons (step965 p h) (sat_cons (step214 p h) (sat_cons (step213 p h) (sat_cons (step968 p h) (sat_cons (step1367 p h) (sat_cons (step986 p h) (sat_cons (step953 p h) (sat_cons (step958 p h) (sat_nil p))))))))))))))))))))))))
def c1516 : List Lit := [(1543, true)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c1507, c1426, c889] c1516 (by decide) p (sat_cons (step1507 p h) (sat_cons (step1426 p h) (sat_cons (step889 p h) (sat_nil p))))
def c1517 : List Lit := [(1643, true), (52, false), (51, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c1053, c1054, c1506] c1517 (by decide) p (sat_cons (step1053 p h) (sat_cons (step1054 p h) (sat_cons (step1506 p h) (sat_nil p))))
def c1518 : List Lit := [(1512, true), (1, true), (1559, true), (69, false)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c656, c845, c1449, c828, c831, c1420, c4, c5, c6, c3, c911] c1518 (by decide) p (sat_cons (step656 p h) (sat_cons (step845 p h) (sat_cons (step1449 p h) (sat_cons (step828 p h) (sat_cons (step831 p h) (sat_cons (step1420 p h) (sat_cons (step4 p h) (sat_cons (step5 p h) (sat_cons (step6 p h) (sat_cons (step3 p h) (sat_cons (step911 p h) (sat_nil p))))))))))))
def c1519 : List Lit := [(1598, true), (1580, false), (1643, true)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c1480, c1509, c963, c1517] c1519 (by decide) p (sat_cons (step1480 p h) (sat_cons (step1509 p h) (sat_cons (step963 p h) (sat_cons (step1517 p h) (sat_nil p)))))
def c1520 : List Lit := [(16, true), (1534, true), (87, false), (83, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c880, c859, c1514, c356, c850] c1520 (by decide) p (sat_cons (step880 p h) (sat_cons (step859 p h) (sat_cons (step1514 p h) (sat_cons (step356 p h) (sat_cons (step850 p h) (sat_nil p))))))
def c1521 : List Lit := [(1517, false), (1534, true), (16, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c880, c856, c857, c878, c852, c868, c1502] c1521 (by decide) p (sat_cons (step880 p h) (sat_cons (step856 p h) (sat_cons (step857 p h) (sat_cons (step878 p h) (sat_cons (step852 p h) (sat_cons (step868 p h) (sat_cons (step1502 p h) (sat_nil p))))))))
def c1522 : List Lit := [(1519, true), (86, true), (15, false), (1530, true), (16, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c661, c851, c852, c1502, c871, c862, c863, c69, c28, c35] c1522 (by decide) p (sat_cons (step661 p h) (sat_cons (step851 p h) (sat_cons (step852 p h) (sat_cons (step1502 p h) (sat_cons (step871 p h) (sat_cons (step862 p h) (sat_cons (step863 p h) (sat_cons (step69 p h) (sat_cons (step28 p h) (sat_cons (step35 p h) (sat_nil p)))))))))))
def c1523 : List Lit := [(1534, true), (83, false), (16, false), (87, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c661, c875, c880, c855, c1521, c849, c356, c1522, c854, c878, c868, c870, c1502, c862, c863, c853, c69, c28, c35] c1523 (by decide) p (sat_cons (step661 p h) (sat_cons (step875 p h) (sat_cons (step880 p h) (sat_cons (step855 p h) (sat_cons (step1521 p h) (sat_cons (step849 p h) (sat_cons (step356 p h) (sat_cons (step1522 p h) (sat_cons (step854 p h) (sat_cons (step878 p h) (sat_cons (step868 p h) (sat_cons (step870 p h) (sat_cons (step1502 p h) (sat_cons (step862 p h) (sat_cons (step863 p h) (sat_cons (step853 p h) (sat_cons (step69 p h) (sat_cons (step28 p h) (sat_cons (step35 p h) (sat_nil p))))))))))))))))))))
def c1524 : List Lit := [(1525, true), (21, false), (86, true), (15, false)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c666, c661, c862, c863, c69, c75, c35, c66] c1524 (by decide) p (sat_cons (step666 p h) (sat_cons (step661 p h) (sat_cons (step862 p h) (sat_cons (step863 p h) (sat_cons (step69 p h) (sat_cons (step75 p h) (sat_cons (step35 p h) (sat_cons (step66 p h) (sat_nil p)))))))))
def c1525 : List Lit := [(1747, true)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c1256, c1260, c1248, c1250, c1234, c1236, c1245, c1231, c1229, c1445] c1525 (by decide) p (sat_cons (step1256 p h) (sat_cons (step1260 p h) (sat_cons (step1248 p h) (sat_cons (step1250 p h) (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1245 p h) (sat_cons (step1231 p h) (sat_cons (step1229 p h) (sat_cons (step1445 p h) (sat_nil p)))))))))))
def c1526 : List Lit := [(1677, true), (93, false), (87, false)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1115, c1116, c439] c1526 (by decide) p (sat_cons (step1115 p h) (sat_cons (step1116 p h) (sat_cons (step439 p h) (sat_nil p))))
def c1527 : List Lit := [(1693, true), (1679, false), (1669, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c1473, c691, c1127, c1147, c1132, c1152, c1107, c1081, c1085, c1099, c1073, c1059, c275, c1070, c1056, c269] c1527 (by decide) p (sat_cons (step1473 p h) (sat_cons (step691 p h) (sat_cons (step1127 p h) (sat_cons (step1147 p h) (sat_cons (step1132 p h) (sat_cons (step1152 p h) (sat_cons (step1107 p h) (sat_cons (step1081 p h) (sat_cons (step1085 p h) (sat_cons (step1099 p h) (sat_cons (step1073 p h) (sat_cons (step1059 p h) (sat_cons (step275 p h) (sat_cons (step1070 p h) (sat_cons (step1056 p h) (sat_cons (step269 p h) (sat_nil p)))))))))))))))))
end B112E186
