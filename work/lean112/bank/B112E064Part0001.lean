import B112E064Part0000
namespace B112E064
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1483 : List Lit := [(11, true), (1446, true)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c642, c647, c1479, c1481, c972, c1459, c948, c1463, c931, c1482, c935, c911, c908, c909, c10, c30, c917, c925, c919, c920, c70, c61] c1483 (by decide) p (sat_cons (step642 p h) (sat_cons (step647 p h) (sat_cons (step1479 p h) (sat_cons (step1481 p h) (sat_cons (step972 p h) (sat_cons (step1459 p h) (sat_cons (step948 p h) (sat_cons (step1463 p h) (sat_cons (step931 p h) (sat_cons (step1482 p h) (sat_cons (step935 p h) (sat_cons (step911 p h) (sat_cons (step908 p h) (sat_cons (step909 p h) (sat_cons (step10 p h) (sat_cons (step30 p h) (sat_cons (step917 p h) (sat_cons (step925 p h) (sat_cons (step919 p h) (sat_cons (step920 p h) (sat_cons (step70 p h) (sat_cons (step61 p h) (sat_nil p)))))))))))))))))))))))
def c1484 : List Lit := [(1405, true), (1446, true)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c642, c1483, c1479, c1481, c972, c1459, c948, c1463, c931, c911, c913, c909, c46, c10, c919, c30, c925, c917] c1484 (by decide) p (sat_cons (step642 p h) (sat_cons (step1483 p h) (sat_cons (step1479 p h) (sat_cons (step1481 p h) (sat_cons (step972 p h) (sat_cons (step1459 p h) (sat_cons (step948 p h) (sat_cons (step1463 p h) (sat_cons (step931 p h) (sat_cons (step911 p h) (sat_cons (step913 p h) (sat_cons (step909 p h) (sat_cons (step46 p h) (sat_cons (step10 p h) (sat_cons (step919 p h) (sat_cons (step30 p h) (sat_cons (step925 p h) (sat_cons (step917 p h) (sat_nil p)))))))))))))))))))
def c1485 : List Lit := [(1446, true)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c642, c1463, c1479, c938, c1481, c972, c1459, c948, c1483, c1484, c935, c922, c924, c919, c917, c46, c914, c909, c10, c30] c1485 (by decide) p (sat_cons (step642 p h) (sat_cons (step1463 p h) (sat_cons (step1479 p h) (sat_cons (step938 p h) (sat_cons (step1481 p h) (sat_cons (step972 p h) (sat_cons (step1459 p h) (sat_cons (step948 p h) (sat_cons (step1483 p h) (sat_cons (step1484 p h) (sat_cons (step935 p h) (sat_cons (step922 p h) (sat_cons (step924 p h) (sat_cons (step919 p h) (sat_cons (step917 p h) (sat_cons (step46 p h) (sat_cons (step914 p h) (sat_cons (step909 p h) (sat_cons (step10 p h) (sat_cons (step30 p h) (sat_nil p)))))))))))))))))))))
def c1486 : List Lit := [(1477, true), (45, true), (13, false)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c662, c1021, c1022, c186, c177] c1486 (by decide) p (sat_cons (step662 p h) (sat_cons (step1021 p h) (sat_cons (step1022 p h) (sat_cons (step186 p h) (sat_cons (step177 p h) (sat_nil p))))))
def c1487 : List Lit := [(1462, true), (36, false), (46, false)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c994, c995, c140] c1487 (by decide) p (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step140 p h) (sat_nil p))))
def c1488 : List Lit := [(1477, true), (45, false), (46, false)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c1021, c1022, c223] c1488 (by decide) p (sat_cons (step1021 p h) (sat_cons (step1022 p h) (sat_cons (step223 p h) (sat_nil p))))
def c1489 : List Lit := [(1472, true), (46, false), (1464, false)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c658, c1000, c1470, c1013, c1003, c1467, c994, c995, c1487, c989, c128, c132] c1489 (by decide) p (sat_cons (step658 p h) (sat_cons (step1000 p h) (sat_cons (step1470 p h) (sat_cons (step1013 p h) (sat_cons (step1003 p h) (sat_cons (step1467 p h) (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step1487 p h) (sat_cons (step989 p h) (sat_cons (step128 p h) (sat_cons (step132 p h) (sat_nil p)))))))))))))
def c1490 : List Lit := [(1462, true), (32, false), (103, false)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c994, c995, c131] c1490 (by decide) p (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step131 p h) (sat_nil p))))
def c1491 : List Lit := [(1481, true), (13, false)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c1027, c1029, c1025, c1486, c1488] c1491 (by decide) p (sat_cons (step1027 p h) (sat_cons (step1029 p h) (sat_cons (step1025 p h) (sat_cons (step1486 p h) (sat_cons (step1488 p h) (sat_nil p))))))
def c1492 : List Lit := [(1632, true), (1472, true), (1625, false)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c691, c1470, c1005, c1286, c1295, c1299, c1289, c1274, c1279, c1280, c1267, c613, c577, c1490, c1002, c1013, c1467, c989, c130, c129, c996] c1492 (by decide) p (sat_cons (step691 p h) (sat_cons (step1470 p h) (sat_cons (step1005 p h) (sat_cons (step1286 p h) (sat_cons (step1295 p h) (sat_cons (step1299 p h) (sat_cons (step1289 p h) (sat_cons (step1274 p h) (sat_cons (step1279 p h) (sat_cons (step1280 p h) (sat_cons (step1267 p h) (sat_cons (step613 p h) (sat_cons (step577 p h) (sat_cons (step1490 p h) (sat_cons (step1002 p h) (sat_cons (step1013 p h) (sat_cons (step1467 p h) (sat_cons (step989 p h) (sat_cons (step130 p h) (sat_cons (step129 p h) (sat_cons (step996 p h) (sat_nil p))))))))))))))))))))))
def c1493 : List Lit := [(1477, true), (46, false), (13, false)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c1486, c1488] c1493 (by decide) p (sat_cons (step1486 p h) (sat_cons (step1488 p h) (sat_nil p)))
def c1494 : List Lit := [(22, false), (110, false), (29, false)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c651, c88, c156] c1494 (by decide) p (sat_cons (step651 p h) (sat_cons (step88 p h) (sat_cons (step156 p h) (sat_nil p))))
def c1495 : List Lit := [(1464, true), (45, true)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c661, c997, c998, c171, c172, c1388] c1495 (by decide) p (sat_cons (step661 p h) (sat_cons (step997 p h) (sat_cons (step998 p h) (sat_cons (step171 p h) (sat_cons (step172 p h) (sat_cons (step1388 p h) (sat_nil p)))))))
def c1496 : List Lit := [(103, false), (32, false), (1463, true), (29, false)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c130, c129, c996] c1496 (by decide) p (sat_cons (step130 p h) (sat_cons (step129 p h) (sat_cons (step996 p h) (sat_nil p))))
def c1497 : List Lit := [(1626, true), (115, false), (105, false)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c1285, c1287, c1283, c1280, c627] c1497 (by decide) p (sat_cons (step1285 p h) (sat_cons (step1287 p h) (sat_cons (step1283 p h) (sat_cons (step1280 p h) (sat_cons (step627 p h) (sat_nil p))))))
def c1498 : List Lit := [(1490, true), (51, true), (53, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c668, c1035, c1046, c1044, c1037, c1039, c245, c247, c1394] c1498 (by decide) p (sat_cons (step668 p h) (sat_cons (step1035 p h) (sat_cons (step1046 p h) (sat_cons (step1044 p h) (sat_cons (step1037 p h) (sat_cons (step1039 p h) (sat_cons (step245 p h) (sat_cons (step247 p h) (sat_cons (step1394 p h) (sat_nil p))))))))))
def c1499 : List Lit := [(1471, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c658, c1469, c1012, c1002, c1467, c994, c995, c988, c989, c128, c109, c134] c1499 (by decide) p (sat_cons (step658 p h) (sat_cons (step1469 p h) (sat_cons (step1012 p h) (sat_cons (step1002 p h) (sat_cons (step1467 p h) (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step988 p h) (sat_cons (step989 p h) (sat_cons (step128 p h) (sat_cons (step109 p h) (sat_cons (step134 p h) (sat_nil p)))))))))))))
def c1500 : List Lit := [(1502, true)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1064] c1500 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1064 p h) (sat_nil p)))
def c1501 : List Lit := [(1521, true)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c1500, c1485, c1094] c1501 (by decide) p (sat_cons (step1500 p h) (sat_cons (step1485 p h) (sat_cons (step1094 p h) (sat_nil p))))
def c1502 : List Lit := [(1665, false)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1375, c1365] c1502 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1375 p h) (sat_cons (step1365 p h) (sat_nil p))))
def c1503 : List Lit := [(5, false), (1417, true), (7, false), (70, false)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c647, c931, c927, c26, c917, c918, c924, c925, c935, c919, c920, c913, c61, c70, c46] c1503 (by decide) p (sat_cons (step647 p h) (sat_cons (step931 p h) (sat_cons (step927 p h) (sat_cons (step26 p h) (sat_cons (step917 p h) (sat_cons (step918 p h) (sat_cons (step924 p h) (sat_cons (step925 p h) (sat_cons (step935 p h) (sat_cons (step919 p h) (sat_cons (step920 p h) (sat_cons (step913 p h) (sat_cons (step61 p h) (sat_cons (step70 p h) (sat_cons (step46 p h) (sat_nil p))))))))))))))))
def c1504 : List Lit := [(59, false), (1563, false), (76, true), (84, false), (79, false), (15, false), (12, false), (1575, true)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c408, c409, c1170, c1182, c1172, c1188, c1205, c1208, c1189, c1175, c1184, c1166, c494] c1504 (by decide) p (sat_cons (step408 p h) (sat_cons (step409 p h) (sat_cons (step1170 p h) (sat_cons (step1182 p h) (sat_cons (step1172 p h) (sat_cons (step1188 p h) (sat_cons (step1205 p h) (sat_cons (step1208 p h) (sat_cons (step1189 p h) (sat_cons (step1175 p h) (sat_cons (step1184 p h) (sat_cons (step1166 p h) (sat_cons (step494 p h) (sat_nil p))))))))))))))
def c1505 : List Lit := [(70, true), (1545, true), (72, true), (68, false), (86, true), (190, true)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c675, c1136, c367, c1142, c307, c1133, c1134, c296] c1505 (by decide) p (sat_cons (step675 p h) (sat_cons (step1136 p h) (sat_cons (step367 p h) (sat_cons (step1142 p h) (sat_cons (step307 p h) (sat_cons (step1133 p h) (sat_cons (step1134 p h) (sat_cons (step296 p h) (sat_nil p)))))))))
def c1506 : List Lit := [(1618, true), (116, false), (70, false)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c694, c1272, c1274, c1269, c1270, c1266, c597, c592, c588] c1506 (by decide) p (sat_cons (step694 p h) (sat_cons (step1272 p h) (sat_cons (step1274 p h) (sat_cons (step1269 p h) (sat_cons (step1270 p h) (sat_cons (step1266 p h) (sat_cons (step597 p h) (sat_cons (step592 p h) (sat_cons (step588 p h) (sat_nil p))))))))))
def c1507 : List Lit := [(1622, false), (1632, true), (107, true), (105, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c694, c1270, c1272, c1299, c1287, c1288, c1303, c1282, c1273, c1275, c1271, c1266, c597, c588] c1507 (by decide) p (sat_cons (step694 p h) (sat_cons (step1270 p h) (sat_cons (step1272 p h) (sat_cons (step1299 p h) (sat_cons (step1287 p h) (sat_cons (step1288 p h) (sat_cons (step1303 p h) (sat_cons (step1282 p h) (sat_cons (step1273 p h) (sat_cons (step1275 p h) (sat_cons (step1271 p h) (sat_cons (step1266 p h) (sat_cons (step597 p h) (sat_cons (step588 p h) (sat_nil p)))))))))))))))
def c1508 : List Lit := [(82, false), (85, true), (1560, true)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c682, c483, c482, c1408, c1165, c1174, c1168, c1169, c393] c1508 (by decide) p (sat_cons (step682 p h) (sat_cons (step483 p h) (sat_cons (step482 p h) (sat_cons (step1408 p h) (sat_cons (step1165 p h) (sat_cons (step1174 p h) (sat_cons (step1168 p h) (sat_cons (step1169 p h) (sat_cons (step393 p h) (sat_nil p))))))))))
def c1509 : List Lit := [(85, true), (86, false), (1565, false), (1574, true), (81, true)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c680, c1180, c1188, c1204, c1508, c1181, c1191, c1200, c1171, c1173, c1168, c1169, c1165, c434, c390, c403] c1509 (by decide) p (sat_cons (step680 p h) (sat_cons (step1180 p h) (sat_cons (step1188 p h) (sat_cons (step1204 p h) (sat_cons (step1508 p h) (sat_cons (step1181 p h) (sat_cons (step1191 p h) (sat_cons (step1200 p h) (sat_cons (step1171 p h) (sat_cons (step1173 p h) (sat_cons (step1168 p h) (sat_cons (step1169 p h) (sat_cons (step1165 p h) (sat_cons (step434 p h) (sat_cons (step390 p h) (sat_cons (step403 p h) (sat_nil p)))))))))))))))))
def c1510 : List Lit := [(62, false), (86, false), (1565, false), (1574, true), (81, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c1509, c521, c524, c1168, c1181, c1171, c1191, c1200] c1510 (by decide) p (sat_cons (step1509 p h) (sat_cons (step521 p h) (sat_cons (step524 p h) (sat_cons (step1168 p h) (sat_cons (step1181 p h) (sat_cons (step1171 p h) (sat_cons (step1191 p h) (sat_cons (step1200 p h) (sat_nil p)))))))))
def c1511 : List Lit := [(86, false), (1565, false), (1574, true), (1585, true), (59, true), (1545, false), (81, true)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c1180, c1188, c1509, c1510, c1125, c1131, c1158, c1239, c1195, c1199, c1191, c1171, c1181, c1168, c530] c1511 (by decide) p (sat_cons (step1180 p h) (sat_cons (step1188 p h) (sat_cons (step1509 p h) (sat_cons (step1510 p h) (sat_cons (step1125 p h) (sat_cons (step1131 p h) (sat_cons (step1158 p h) (sat_cons (step1239 p h) (sat_cons (step1195 p h) (sat_cons (step1199 p h) (sat_cons (step1191 p h) (sat_cons (step1171 p h) (sat_cons (step1181 p h) (sat_cons (step1168 p h) (sat_cons (step530 p h) (sat_nil p))))))))))))))))
def c1512 : List Lit := [(83, true), (1574, true), (1585, true), (59, true), (1545, false), (81, true)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c1196, c1180, c1183, c1188, c1204, c1511, c1184, c1189, c1192, c1195, c1200, c1181, c1239, c1171, c1508, c1158, c1168, c1131, c519, c1125] c1512 (by decide) p (sat_cons (step1196 p h) (sat_cons (step1180 p h) (sat_cons (step1183 p h) (sat_cons (step1188 p h) (sat_cons (step1204 p h) (sat_cons (step1511 p h) (sat_cons (step1184 p h) (sat_cons (step1189 p h) (sat_cons (step1192 p h) (sat_cons (step1195 p h) (sat_cons (step1200 p h) (sat_cons (step1181 p h) (sat_cons (step1239 p h) (sat_cons (step1171 p h) (sat_cons (step1508 p h) (sat_cons (step1158 p h) (sat_cons (step1168 p h) (sat_cons (step1131 p h) (sat_cons (step519 p h) (sat_cons (step1125 p h) (sat_nil p)))))))))))))))))))))
def c1513 : List Lit := [(13, true), (1417, true), (79, true)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c645, c931, c923, c920, c921, c922, c925, c935, c916, c913, c46, c51] c1513 (by decide) p (sat_cons (step645 p h) (sat_cons (step931 p h) (sat_cons (step923 p h) (sat_cons (step920 p h) (sat_cons (step921 p h) (sat_cons (step922 p h) (sat_cons (step925 p h) (sat_cons (step935 p h) (sat_cons (step916 p h) (sat_cons (step913 p h) (sat_cons (step46 p h) (sat_cons (step51 p h) (sat_nil p)))))))))))))
def c1514 : List Lit := [(49, true), (1482, true), (13, false)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c1028, c1024, c1026, c1030, c1493] c1514 (by decide) p (sat_cons (step1028 p h) (sat_cons (step1024 p h) (sat_cons (step1026 p h) (sat_cons (step1030 p h) (sat_cons (step1493 p h) (sat_nil p))))))
def c1515 : List Lit := [(1542, true), (79, true), (76, false)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c675, c1136, c1137, c304, c306] c1515 (by decide) p (sat_cons (step675 p h) (sat_cons (step1136 p h) (sat_cons (step1137 p h) (sat_cons (step304 p h) (sat_cons (step306 p h) (sat_nil p))))))
def c1516 : List Lit := [(68, false), (70, false), (79, true), (76, false)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c675, c304, c306] c1516 (by decide) p (sat_cons (step675 p h) (sat_cons (step304 p h) (sat_cons (step306 p h) (sat_nil p))))
def c1517 : List Lit := [(1489, true), (70, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c668, c1041, c1043, c1039, c1035, c1036, c250, c247, c245, c1394] c1517 (by decide) p (sat_cons (step668 p h) (sat_cons (step1041 p h) (sat_cons (step1043 p h) (sat_cons (step1039 p h) (sat_cons (step1035 p h) (sat_cons (step1036 p h) (sat_cons (step250 p h) (sat_cons (step247 p h) (sat_cons (step245 p h) (sat_cons (step1394 p h) (sat_nil p)))))))))))
def c1518 : List Lit := [(1403, false), (1417, true), (79, true)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c645, c938, c911, c914, c935, c922, c924, c919, c916, c46, c51] c1518 (by decide) p (sat_cons (step645 p h) (sat_cons (step938 p h) (sat_cons (step911 p h) (sat_cons (step914 p h) (sat_cons (step935 p h) (sat_cons (step922 p h) (sat_cons (step924 p h) (sat_cons (step919 p h) (sat_cons (step916 p h) (sat_cons (step46 p h) (sat_cons (step51 p h) (sat_nil p))))))))))))
def c1519 : List Lit := [(6, false), (7, true), (5, false), (13, false)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c644, c12, c25] c1519 (by decide) p (sat_cons (step644 p h) (sat_cons (step12 p h) (sat_cons (step25 p h) (sat_nil p))))
def c1520 : List Lit := [(1417, true), (70, false), (79, true)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c645, c931, c1513, c927, c1518, c908, c1503, c1519, c917, c918, c924, c925, c51, c935, c919, c46, c913] c1520 (by decide) p (sat_cons (step645 p h) (sat_cons (step931 p h) (sat_cons (step1513 p h) (sat_cons (step927 p h) (sat_cons (step1518 p h) (sat_cons (step908 p h) (sat_cons (step1503 p h) (sat_cons (step1519 p h) (sat_cons (step917 p h) (sat_cons (step918 p h) (sat_cons (step924 p h) (sat_cons (step925 p h) (sat_cons (step51 p h) (sat_cons (step935 p h) (sat_cons (step919 p h) (sat_cons (step46 p h) (sat_cons (step913 p h) (sat_nil p))))))))))))))))))
def c1521 : List Lit := [(85, false), (62, false), (1570, true), (81, true), (78, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c521, c519, c520, c1184, c1181, c1192] c1521 (by decide) p (sat_cons (step521 p h) (sat_cons (step519 p h) (sat_cons (step520 p h) (sat_cons (step1184 p h) (sat_cons (step1181 p h) (sat_cons (step1192 p h) (sat_nil p)))))))
def c1522 : List Lit := [(1632, true), (107, true), (105, true), (79, true), (76, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c696, c694, c1270, c1306, c1507, c1278, c1279, c1280, c612, c618, c613, c1267, c1268, c1275, c1276, c1303, c1271, c1285, c588, c1282, c597] c1522 (by decide) p (sat_cons (step696 p h) (sat_cons (step694 p h) (sat_cons (step1270 p h) (sat_cons (step1306 p h) (sat_cons (step1507 p h) (sat_cons (step1278 p h) (sat_cons (step1279 p h) (sat_cons (step1280 p h) (sat_cons (step612 p h) (sat_cons (step618 p h) (sat_cons (step613 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step1275 p h) (sat_cons (step1276 p h) (sat_cons (step1303 p h) (sat_cons (step1271 p h) (sat_cons (step1285 p h) (sat_cons (step588 p h) (sat_cons (step1282 p h) (sat_cons (step597 p h) (sat_nil p))))))))))))))))))))))
def c1523 : List Lit := [(1620, true), (103, true), (107, true), (105, true)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c694, c1267, c1270, c1278, c1276, c1268, c1271, c588, c590, c1416] c1523 (by decide) p (sat_cons (step694 p h) (sat_cons (step1267 p h) (sat_cons (step1270 p h) (sat_cons (step1278 p h) (sat_cons (step1276 p h) (sat_cons (step1268 p h) (sat_cons (step1271 p h) (sat_cons (step588 p h) (sat_cons (step590 p h) (sat_cons (step1416 p h) (sat_nil p)))))))))))
def c1524 : List Lit := [(82, false), (86, false), (1557, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c682, c1169, c1168, c393, c530, c483] c1524 (by decide) p (sat_cons (step682 p h) (sat_cons (step1169 p h) (sat_cons (step1168 p h) (sat_cons (step393 p h) (sat_cons (step530 p h) (sat_cons (step483 p h) (sat_nil p)))))))
def c1525 : List Lit := [(1504, true), (1489, false)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1048, c1066, c1072, c1051, c1027, c1029, c1025, c1488, c1489, c1495] c1525 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1048 p h) (sat_cons (step1066 p h) (sat_cons (step1072 p h) (sat_cons (step1051 p h) (sat_cons (step1027 p h) (sat_cons (step1029 p h) (sat_cons (step1025 p h) (sat_cons (step1488 p h) (sat_cons (step1489 p h) (sat_cons (step1495 p h) (sat_nil p))))))))))))
def c1526 : List Lit := [(1565, true), (85, false), (78, false)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1182, c1183, c532] c1526 (by decide) p (sat_cons (step1182 p h) (sat_cons (step1183 p h) (sat_cons (step532 p h) (sat_nil p))))
def c1527 : List Lit := [(64, false), (77, false), (74, false), (60, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c671, c384, c380, c271] c1527 (by decide) p (sat_cons (step671 p h) (sat_cons (step384 p h) (sat_cons (step380 p h) (sat_cons (step271 p h) (sat_nil p)))))
def c1528 : List Lit := [(65, false), (70, false), (72, false), (76, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c673, c301, c334, c291] c1528 (by decide) p (sat_cons (step673 p h) (sat_cons (step301 p h) (sat_cons (step334 p h) (sat_cons (step291 p h) (sat_nil p)))))
def c1529 : List Lit := [(1491, true), (53, true), (51, true), (56, true)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c668, c1035, c1038, c1047, c1045, c1037, c1040, c247, c245, c1394] c1529 (by decide) p (sat_cons (step668 p h) (sat_cons (step1035 p h) (sat_cons (step1038 p h) (sat_cons (step1047 p h) (sat_cons (step1045 p h) (sat_cons (step1037 p h) (sat_cons (step1040 p h) (sat_cons (step247 p h) (sat_cons (step245 p h) (sat_cons (step1394 p h) (sat_nil p)))))))))))
def c1530 : List Lit := [(52, false), (53, true), (171, true), (62, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c668, c247, c245, c1394, c256] c1530 (by decide) p (sat_cons (step668 p h) (sat_cons (step247 p h) (sat_cons (step245 p h) (sat_cons (step1394 p h) (sat_cons (step256 p h) (sat_nil p))))))
def c1531 : List Lit := [(65, true), (64, true), (75, true), (76, false), (1546, true), (47, true), (70, true)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c674, c1136, c1145, c1134, c1135, c1143, c295, c1138, c303] c1531 (by decide) p (sat_cons (step674 p h) (sat_cons (step1136 p h) (sat_cons (step1145 p h) (sat_cons (step1134 p h) (sat_cons (step1135 p h) (sat_cons (step1143 p h) (sat_cons (step295 p h) (sat_cons (step1138 p h) (sat_cons (step303 p h) (sat_nil p))))))))))
def c1532 : List Lit := [(68, false), (72, false), (79, true), (86, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c675, c305, c364] c1532 (by decide) p (sat_cons (step675 p h) (sat_cons (step305 p h) (sat_cons (step364 p h) (sat_nil p))))
def c1533 : List Lit := [(71, true), (69, true), (72, false), (86, false), (85, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c677, c361, c360, c544] c1533 (by decide) p (sat_cons (step677 p h) (sat_cons (step361 p h) (sat_cons (step360 p h) (sat_cons (step544 p h) (sat_nil p)))))
def c1534 : List Lit := [(65, false), (66, false), (69, true)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c673, c291, c292, c1400] c1534 (by decide) p (sat_cons (step673 p h) (sat_cons (step291 p h) (sat_cons (step292 p h) (sat_cons (step1400 p h) (sat_nil p)))))
def c1535 : List Lit := [(1574, false), (1537, false), (68, true), (1540, false), (1661, true), (114, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1137, c1142, c1153, c1283, c1285, c1293, c1308, c1351, c1234, c1240, c1346, c1154, c1309, c1143, c1294, c1298, c1138, c1286, c1506, c1284] c1535 (by decide) p (sat_cons (step1137 p h) (sat_cons (step1142 p h) (sat_cons (step1153 p h) (sat_cons (step1283 p h) (sat_cons (step1285 p h) (sat_cons (step1293 p h) (sat_cons (step1308 p h) (sat_cons (step1351 p h) (sat_cons (step1234 p h) (sat_cons (step1240 p h) (sat_cons (step1346 p h) (sat_cons (step1154 p h) (sat_cons (step1309 p h) (sat_cons (step1143 p h) (sat_cons (step1294 p h) (sat_cons (step1298 p h) (sat_cons (step1138 p h) (sat_cons (step1286 p h) (sat_cons (step1506 p h) (sat_cons (step1284 p h) (sat_nil p)))))))))))))))))))))
def c1536 : List Lit := [(74, false), (1569, true), (79, true), (78, false), (86, true), (85, false), (66, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c680, c682, c386, c405, c1413, c1184, c1189, c1179, c1180, c484, c459] c1536 (by decide) p (sat_cons (step680 p h) (sat_cons (step682 p h) (sat_cons (step386 p h) (sat_cons (step405 p h) (sat_cons (step1413 p h) (sat_cons (step1184 p h) (sat_cons (step1189 p h) (sat_cons (step1179 p h) (sat_cons (step1180 p h) (sat_cons (step484 p h) (sat_cons (step459 p h) (sat_nil p))))))))))))
def c1537 : List Lit := [(1568, true), (78, false), (86, true), (85, false)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1182, c1186, c1188, c1184, c1179, c529] c1537 (by decide) p (sat_cons (step1182 p h) (sat_cons (step1186 p h) (sat_cons (step1188 p h) (sat_cons (step1184 p h) (sat_cons (step1179 p h) (sat_cons (step529 p h) (sat_nil p)))))))
def c1538 : List Lit := [(81, false), (1585, true), (80, false), (62, true), (82, false), (1560, true), (1568, false), (78, false), (1540, false)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1141, c459, c453, c1165, c1127, c1173, c1174, c1129, c1199, c1169, c1239, c1162, c1158, c1132, c1142, c425, c1515] c1538 (by decide) p (sat_cons (step1141 p h) (sat_cons (step459 p h) (sat_cons (step453 p h) (sat_cons (step1165 p h) (sat_cons (step1127 p h) (sat_cons (step1173 p h) (sat_cons (step1174 p h) (sat_cons (step1129 p h) (sat_cons (step1199 p h) (sat_cons (step1169 p h) (sat_cons (step1239 p h) (sat_cons (step1162 p h) (sat_cons (step1158 p h) (sat_cons (step1132 p h) (sat_cons (step1142 p h) (sat_cons (step425 p h) (sat_cons (step1515 p h) (sat_nil p))))))))))))))))))
def c1539 : List Lit := [(82, false), (78, false), (86, true), (85, false), (114, true), (1574, true), (1661, true), (1540, false)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c682, c1537, c1204, c1141, c529, c531, c1412, c519, c1184, c1284, c484, c1286, c1294, c1309, c1346, c1538, c1180, c1189, c1195, c1200, c1239, c1171, c1173, c1162, c1169, c1165, c450, c1127, c1129, c1132, c1158, c425, c1142, c1515] c1539 (by decide) p (sat_cons (step682 p h) (sat_cons (step1537 p h) (sat_cons (step1204 p h) (sat_cons (step1141 p h) (sat_cons (step529 p h) (sat_cons (step531 p h) (sat_cons (step1412 p h) (sat_cons (step519 p h) (sat_cons (step1184 p h) (sat_cons (step1284 p h) (sat_cons (step484 p h) (sat_cons (step1286 p h) (sat_cons (step1294 p h) (sat_cons (step1309 p h) (sat_cons (step1346 p h) (sat_cons (step1538 p h) (sat_cons (step1180 p h) (sat_cons (step1189 p h) (sat_cons (step1195 p h) (sat_cons (step1200 p h) (sat_cons (step1239 p h) (sat_cons (step1171 p h) (sat_cons (step1173 p h) (sat_cons (step1162 p h) (sat_cons (step1169 p h) (sat_cons (step1165 p h) (sat_cons (step450 p h) (sat_cons (step1127 p h) (sat_cons (step1129 p h) (sat_cons (step1132 p h) (sat_cons (step1158 p h) (sat_cons (step425 p h) (sat_cons (step1142 p h) (sat_cons (step1515 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c1540 : List Lit := [(1625, false), (1632, true), (81, false), (69, true)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c693, c1295, c1286, c1289, c1299, c1280, c1272, c1270, c624, c585] c1540 (by decide) p (sat_cons (step693 p h) (sat_cons (step1295 p h) (sat_cons (step1286 p h) (sat_cons (step1289 p h) (sat_cons (step1299 p h) (sat_cons (step1280 p h) (sat_cons (step1272 p h) (sat_cons (step1270 p h) (sat_cons (step624 p h) (sat_cons (step585 p h) (sat_nil p)))))))))))
def c1541 : List Lit := [(78, false), (85, false), (1585, true), (1618, true), (116, false), (1563, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c692, c675, c1506, c1136, c1272, c1269, c1274, c1266, c597, c581, c571, c1133, c1142, c534, c522, c533, c1125, c1184, c1128, c1189, c1153, c1195, c1234, c1239, c1200, c1154, c1158, c1171, c1143, c1145, c1131, c1169, c1138, c1135, c425, c306, c300] c1541 (by decide) p (sat_cons (step692 p h) (sat_cons (step675 p h) (sat_cons (step1506 p h) (sat_cons (step1136 p h) (sat_cons (step1272 p h) (sat_cons (step1269 p h) (sat_cons (step1274 p h) (sat_cons (step1266 p h) (sat_cons (step597 p h) (sat_cons (step581 p h) (sat_cons (step571 p h) (sat_cons (step1133 p h) (sat_cons (step1142 p h) (sat_cons (step534 p h) (sat_cons (step522 p h) (sat_cons (step533 p h) (sat_cons (step1125 p h) (sat_cons (step1184 p h) (sat_cons (step1128 p h) (sat_cons (step1189 p h) (sat_cons (step1153 p h) (sat_cons (step1195 p h) (sat_cons (step1234 p h) (sat_cons (step1239 p h) (sat_cons (step1200 p h) (sat_cons (step1154 p h) (sat_cons (step1158 p h) (sat_cons (step1171 p h) (sat_cons (step1143 p h) (sat_cons (step1145 p h) (sat_cons (step1131 p h) (sat_cons (step1169 p h) (sat_cons (step1138 p h) (sat_cons (step1135 p h) (sat_cons (step425 p h) (sat_cons (step306 p h) (sat_cons (step300 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c1542 : List Lit := [(1535, false), (1551, true), (78, true), (1585, true), (113, false), (66, true), (70, true), (69, true), (1563, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1475, c673, c1136, c1133, c1142, c1158, c1128, c1131, c1153, c1154, c1234, c1143, c1145, c1207, c1138, c1135, c424, c291, c300, c1170, c1172, c1175, c1204, c1166, c1188, c1532, c1182] c1542 (by decide) p (sat_cons (step1475 p h) (sat_cons (step673 p h) (sat_cons (step1136 p h) (sat_cons (step1133 p h) (sat_cons (step1142 p h) (sat_cons (step1158 p h) (sat_cons (step1128 p h) (sat_cons (step1131 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step1234 p h) (sat_cons (step1143 p h) (sat_cons (step1145 p h) (sat_cons (step1207 p h) (sat_cons (step1138 p h) (sat_cons (step1135 p h) (sat_cons (step424 p h) (sat_cons (step291 p h) (sat_cons (step300 p h) (sat_cons (step1170 p h) (sat_cons (step1172 p h) (sat_cons (step1175 p h) (sat_cons (step1204 p h) (sat_cons (step1166 p h) (sat_cons (step1188 p h) (sat_cons (step1532 p h) (sat_cons (step1182 p h) (sat_nil p))))))))))))))))))))))))))))
def c1543 : List Lit := [(1569, false), (78, true), (1585, true), (66, true), (70, true), (69, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c673, c1168, c1171, c1136, c1133, c1142, c1148, c1229, c1205, c1200, c1172, c1234, c1170, c1149, c1143, c1145, c1138, c1135, c300, c291] c1543 (by decide) p (sat_cons (step673 p h) (sat_cons (step1168 p h) (sat_cons (step1171 p h) (sat_cons (step1136 p h) (sat_cons (step1133 p h) (sat_cons (step1142 p h) (sat_cons (step1148 p h) (sat_cons (step1229 p h) (sat_cons (step1205 p h) (sat_cons (step1200 p h) (sat_cons (step1172 p h) (sat_cons (step1234 p h) (sat_cons (step1170 p h) (sat_cons (step1149 p h) (sat_cons (step1143 p h) (sat_cons (step1145 p h) (sat_cons (step1138 p h) (sat_cons (step1135 p h) (sat_cons (step300 p h) (sat_cons (step291 p h) (sat_nil p)))))))))))))))))))))
def c1544 : List Lit := [(68, false), (66, false), (76, false), (59, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c675, c421, c303, c306] c1544 (by decide) p (sat_cons (step675 p h) (sat_cons (step421 p h) (sat_cons (step303 p h) (sat_cons (step306 p h) (sat_nil p)))))
def c1545 : List Lit := [(104, false), (106, false), (66, false), (116, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c692, c597, c581, c571] c1545 (by decide) p (sat_cons (step692 p h) (sat_cons (step597 p h) (sat_cons (step581 p h) (sat_cons (step571 p h) (sat_nil p)))))
def c1546 : List Lit := [(1626, true), (80, true), (81, false), (74, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c697, c1285, c1287, c1283, c1280, c603, c620, c626] c1546 (by decide) p (sat_cons (step697 p h) (sat_cons (step1285 p h) (sat_cons (step1287 p h) (sat_cons (step1283 p h) (sat_cons (step1280 p h) (sat_cons (step603 p h) (sat_cons (step620 p h) (sat_cons (step626 p h) (sat_nil p)))))))))
end B112E064
