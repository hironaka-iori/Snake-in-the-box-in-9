import B112E040Inputs
namespace B112E040
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1525 : List Lit := [(118, true)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c662, c661] c1525 (by decide) p (sat_cons (step662 p h) (sat_cons (step661 p h) (sat_nil p)))
def c1526 : List Lit := [(238, true), (120, true)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1525, c663] c1526 (by decide) p (sat_cons (step1525 p h) (sat_cons (step663 p h) (sat_nil p)))
def c1527 : List Lit := [(474, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c883, c880] c1527 (by decide) p (sat_cons (step883 p h) (sat_cons (step880 p h) (sat_nil p)))
def c1528 : List Lit := [(356, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c883, c882] c1528 (by decide) p (sat_cons (step883 p h) (sat_cons (step882 p h) (sat_nil p)))
def c1529 : List Lit := [(472, false)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c1527, c876] c1529 (by decide) p (sat_cons (step1527 p h) (sat_cons (step876 p h) (sat_nil p)))
def c1530 : List Lit := [(414, false)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c1527, c879] c1530 (by decide) p (sat_cons (step1527 p h) (sat_cons (step879 p h) (sat_nil p)))
def c1531 : List Lit := [(354, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c1528, c795] c1531 (by decide) p (sat_cons (step1528 p h) (sat_cons (step795 p h) (sat_nil p)))
def c1532 : List Lit := [(296, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c1528, c798] c1532 (by decide) p (sat_cons (step1528 p h) (sat_cons (step798 p h) (sat_nil p)))
def c1533 : List Lit := [(470, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1529, c871] c1533 (by decide) p (sat_cons (step1529 p h) (sat_cons (step871 p h) (sat_nil p)))
def c1534 : List Lit := [(442, false)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1529, c874] c1534 (by decide) p (sat_cons (step1529 p h) (sat_cons (step874 p h) (sat_nil p)))
def c1535 : List Lit := [(412, false)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1530, c830] c1535 (by decide) p (sat_cons (step1530 p h) (sat_cons (step830 p h) (sat_nil p)))
def c1536 : List Lit := [(384, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1530, c833] c1536 (by decide) p (sat_cons (step1530 p h) (sat_cons (step833 p h) (sat_nil p)))
def c1537 : List Lit := [(352, false)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1531, c791] c1537 (by decide) p (sat_cons (step1531 p h) (sat_cons (step791 p h) (sat_nil p)))
def c1538 : List Lit := [(294, false)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1532, c759] c1538 (by decide) p (sat_cons (step1532 p h) (sat_cons (step759 p h) (sat_nil p)))
def c1539 : List Lit := [(266, false)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1532, c762] c1539 (by decide) p (sat_cons (step1532 p h) (sat_cons (step762 p h) (sat_nil p)))
def c1540 : List Lit := [(468, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1533, c868] c1540 (by decide) p (sat_cons (step1533 p h) (sat_cons (step868 p h) (sat_nil p)))
def c1541 : List Lit := [(440, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1534, c851] c1541 (by decide) p (sat_cons (step1534 p h) (sat_cons (step851 p h) (sat_nil p)))
def c1542 : List Lit := [(350, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1537, c787] c1542 (by decide) p (sat_cons (step1537 p h) (sat_cons (step787 p h) (sat_nil p)))
def c1543 : List Lit := [(264, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1539, c740] c1543 (by decide) p (sat_cons (step1539 p h) (sat_cons (step740 p h) (sat_nil p)))
def c1544 : List Lit := [(460, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1540, c866] c1544 (by decide) p (sat_cons (step1540 p h) (sat_cons (step866 p h) (sat_nil p)))
def c1545 : List Lit := [(262, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1543, c736] c1545 (by decide) p (sat_cons (step1543 p h) (sat_cons (step736 p h) (sat_nil p)))
def c1546 : List Lit := [(1454, true)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c666, c952, c956, c946, c933, c935, c938, c931, c7, c4] c1546 (by decide) p (sat_cons (step666 p h) (sat_cons (step952 p h) (sat_cons (step956 p h) (sat_cons (step946 p h) (sat_cons (step933 p h) (sat_cons (step935 p h) (sat_cons (step938 p h) (sat_cons (step931 p h) (sat_cons (step7 p h) (sat_cons (step4 p h) (sat_nil p)))))))))))
def c1547 : List Lit := [(1593, true)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c697, c1249, c1252, c1241, c1243, c1230, c1238, c1236, c1228, c441, c446] c1547 (by decide) p (sat_cons (step697 p h) (sat_cons (step1249 p h) (sat_cons (step1252 p h) (sat_cons (step1241 p h) (sat_cons (step1243 p h) (sat_cons (step1230 p h) (sat_cons (step1238 p h) (sat_cons (step1236 p h) (sat_cons (step1228 p h) (sat_cons (step441 p h) (sat_cons (step446 p h) (sat_nil p))))))))))))
def c1548 : List Lit := [(76, false), (80, false), (77, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c701, c472, c478] c1548 (by decide) p (sat_cons (step701 p h) (sat_cons (step472 p h) (sat_cons (step478 p h) (sat_nil p))))
def c1549 : List Lit := [(1604, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1266, c1268, c1263, c1260, c1261, c1548] c1549 (by decide) p (sat_cons (step1266 p h) (sat_cons (step1268 p h) (sat_cons (step1263 p h) (sat_cons (step1260 p h) (sat_cons (step1261 p h) (sat_cons (step1548 p h) (sat_nil p)))))))
def c1550 : List Lit := [(1612, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c706, c1279, c1281, c1276, c1277, c1273, c507, c503] c1550 (by decide) p (sat_cons (step706 p h) (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step1273 p h) (sat_cons (step507 p h) (sat_cons (step503 p h) (sat_nil p)))))))))
def c1551 : List Lit := [(1616, true)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1286] c1551 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1286 p h) (sat_nil p)))
def c1552 : List Lit := [(1617, true)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1549, c1287] c1552 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1549 p h) (sat_cons (step1287 p h) (sat_nil p))))
def c1553 : List Lit := [(1625, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1551, c1547, c1295] c1553 (by decide) p (sat_cons (step1551 p h) (sat_cons (step1547 p h) (sat_cons (step1295 p h) (sat_nil p))))
def c1554 : List Lit := [(1626, true)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1547, c1296] c1554 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1547 p h) (sat_cons (step1296 p h) (sat_nil p))))
def c1555 : List Lit := [(1610, true), (77, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c706, c1276, c1277, c507, c502] c1555 (by decide) p (sat_cons (step706 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step507 p h) (sat_cons (step502 p h) (sat_nil p))))))
def c1556 : List Lit := [(1618, true), (75, true), (1600, false), (77, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1549, c1550, c702, c1555, c1288, c1290, c1280, c1269, c1264, c1282, c1273, c482, c479, c500, c501, c1278] c1556 (by decide) p (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step702 p h) (sat_cons (step1555 p h) (sat_cons (step1288 p h) (sat_cons (step1290 p h) (sat_cons (step1280 p h) (sat_cons (step1269 p h) (sat_cons (step1264 p h) (sat_cons (step1282 p h) (sat_cons (step1273 p h) (sat_cons (step482 p h) (sat_cons (step479 p h) (sat_cons (step500 p h) (sat_cons (step501 p h) (sat_cons (step1278 p h) (sat_nil p)))))))))))))))))
def c1557 : List Lit := [(62, true), (180, true), (1583, true)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c694, c1228, c432, c1233, c435] c1557 (by decide) p (sat_cons (step694 p h) (sat_cons (step1228 p h) (sat_cons (step432 p h) (sat_cons (step1233 p h) (sat_cons (step435 p h) (sat_nil p))))))
def c1558 : List Lit := [(1589, true), (62, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c695, c436, c1241, c1243, c1238, c1236, c446] c1558 (by decide) p (sat_cons (step695 p h) (sat_cons (step436 p h) (sat_cons (step1241 p h) (sat_cons (step1243 p h) (sat_cons (step1238 p h) (sat_cons (step1236 p h) (sat_cons (step446 p h) (sat_nil p))))))))
def c1559 : List Lit := [(1536, true)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c691, c1122, c1125, c1114, c1116, c1100, c1111, c1108, c1097, c395, c393] c1559 (by decide) p (sat_cons (step691 p h) (sat_cons (step1122 p h) (sat_cons (step1125 p h) (sat_cons (step1114 p h) (sat_cons (step1116 p h) (sat_cons (step1100 p h) (sat_cons (step1111 p h) (sat_cons (step1108 p h) (sat_cons (step1097 p h) (sat_cons (step395 p h) (sat_cons (step393 p h) (sat_nil p))))))))))))
def c1560 : List Lit := [(1513, true)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c681, c1075, c1079, c1067, c1069, c1056, c1058, c1065, c1061, c1062, c1054, c220, c343, c228, c249] c1560 (by decide) p (sat_cons (step681 p h) (sat_cons (step1075 p h) (sat_cons (step1079 p h) (sat_cons (step1067 p h) (sat_cons (step1069 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1065 p h) (sat_cons (step1061 p h) (sat_cons (step1062 p h) (sat_cons (step1054 p h) (sat_cons (step220 p h) (sat_cons (step343 p h) (sat_cons (step228 p h) (sat_cons (step249 p h) (sat_nil p))))))))))))))))
def c1561 : List Lit := [(1477, true), (63, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c996, c1000, c988, c990, c974, c985, c986, c982, c983, c971, c972, c140, c112, c94, c98] c1561 (by decide) p (sat_cons (step996 p h) (sat_cons (step1000 p h) (sat_cons (step988 p h) (sat_cons (step990 p h) (sat_cons (step974 p h) (sat_cons (step985 p h) (sat_cons (step986 p h) (sat_cons (step982 p h) (sat_cons (step983 p h) (sat_cons (step971 p h) (sat_cons (step972 p h) (sat_cons (step140 p h) (sat_cons (step112 p h) (sat_cons (step94 p h) (sat_cons (step98 p h) (sat_nil p))))))))))))))))
def c1562 : List Lit := [(9, false), (17, true), (1444, true), (16, false), (80, false), (25, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c668, c666, c934, c29, c36, c930, c932, c936, c7, c4] c1562 (by decide) p (sat_cons (step668 p h) (sat_cons (step666 p h) (sat_cons (step934 p h) (sat_cons (step29 p h) (sat_cons (step36 p h) (sat_cons (step930 p h) (sat_cons (step932 p h) (sat_cons (step936 p h) (sat_cons (step7 p h) (sat_cons (step4 p h) (sat_nil p)))))))))))
def c1563 : List Lit := [(1, true), (23, true), (22, false), (30, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c676, c103, c105, c1490] c1563 (by decide) p (sat_cons (step676 p h) (sat_cons (step103 p h) (sat_cons (step105 p h) (sat_cons (step1490 p h) (sat_nil p)))))
def c1564 : List Lit := [(6, false), (5, true), (12, false), (16, false), (25, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c668, c82, c36] c1564 (by decide) p (sat_cons (step668 p h) (sat_cons (step82 p h) (sat_cons (step36 p h) (sat_nil p))))
def c1565 : List Lit := [(3, false), (1448, true)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c666, c942, c941, c6, c68] c1565 (by decide) p (sat_cons (step666 p h) (sat_cons (step942 p h) (sat_cons (step941 p h) (sat_cons (step6 p h) (sat_cons (step68 p h) (sat_nil p))))))
def c1566 : List Lit := [(111, true), (1680, true), (80, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c719, c1387, c1365, c1362, c1363, c1364, c650, c643, c1384, c1373, c1377] c1566 (by decide) p (sat_cons (step719 p h) (sat_cons (step1387 p h) (sat_cons (step1365 p h) (sat_cons (step1362 p h) (sat_cons (step1363 p h) (sat_cons (step1364 p h) (sat_cons (step650 p h) (sat_cons (step643 p h) (sat_cons (step1384 p h) (sat_cons (step1373 p h) (sat_cons (step1377 p h) (sat_nil p))))))))))))
def c1567 : List Lit := [(1503, false), (1522, false), (1550, true), (1506, false), (42, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1559, c686, c1100, c1167, c1065, c1073, c1087, c1088, c1163, c1074, c1130, c1126, c1066, c1103, c1116, c368, c1095, c1109, c370] c1567 (by decide) p (sat_cons (step1559 p h) (sat_cons (step686 p h) (sat_cons (step1100 p h) (sat_cons (step1167 p h) (sat_cons (step1065 p h) (sat_cons (step1073 p h) (sat_cons (step1087 p h) (sat_cons (step1088 p h) (sat_cons (step1163 p h) (sat_cons (step1074 p h) (sat_cons (step1130 p h) (sat_cons (step1126 p h) (sat_cons (step1066 p h) (sat_cons (step1103 p h) (sat_cons (step1116 p h) (sat_cons (step368 p h) (sat_cons (step1095 p h) (sat_cons (step1109 p h) (sat_cons (step370 p h) (sat_nil p))))))))))))))))))))
def c1568 : List Lit := [(1549, true), (1522, false), (1502, false), (1506, false), (42, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1559, c686, c1100, c1065, c1073, c1082, c1162, c1157, c1083, c1130, c1126, c1074, c1103, c1116, c1066, c1095, c1109, c368, c370] c1568 (by decide) p (sat_cons (step1559 p h) (sat_cons (step686 p h) (sat_cons (step1100 p h) (sat_cons (step1065 p h) (sat_cons (step1073 p h) (sat_cons (step1082 p h) (sat_cons (step1162 p h) (sat_cons (step1157 p h) (sat_cons (step1083 p h) (sat_cons (step1130 p h) (sat_cons (step1126 p h) (sat_cons (step1074 p h) (sat_cons (step1103 p h) (sat_cons (step1116 p h) (sat_cons (step1066 p h) (sat_cons (step1095 p h) (sat_cons (step1109 p h) (sat_cons (step368 p h) (sat_cons (step370 p h) (sat_nil p))))))))))))))))))))
def c1569 : List Lit := [(21, false), (23, true), (26, false), (37, false)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c675, c99, c136] c1569 (by decide) p (sat_cons (step675 p h) (sat_cons (step99 p h) (sat_cons (step136 p h) (sat_nil p))))
def c1570 : List Lit := [(6, true), (1461, false), (10, true), (3, true), (1474, false), (21, true), (1491, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c667, c972, c977, c1007, c1039, c965, c937, c930, c932, c936, c10, c961, c962, c1032, c946, c1012, c939, c978, c1, c973] c1570 (by decide) p (sat_cons (step667 p h) (sat_cons (step972 p h) (sat_cons (step977 p h) (sat_cons (step1007 p h) (sat_cons (step1039 p h) (sat_cons (step965 p h) (sat_cons (step937 p h) (sat_cons (step930 p h) (sat_cons (step932 p h) (sat_cons (step936 p h) (sat_cons (step10 p h) (sat_cons (step961 p h) (sat_cons (step962 p h) (sat_cons (step1032 p h) (sat_cons (step946 p h) (sat_cons (step1012 p h) (sat_cons (step939 p h) (sat_cons (step978 p h) (sat_cons (step1 p h) (sat_cons (step973 p h) (sat_nil p)))))))))))))))))))))
def c1571 : List Lit := [(1532, true), (50, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c691, c1114, c1116, c1111, c1108, c395, c393] c1571 (by decide) p (sat_cons (step691 p h) (sat_cons (step1114 p h) (sat_cons (step1116 p h) (sat_cons (step1111 p h) (sat_cons (step1108 p h) (sat_cons (step395 p h) (sat_cons (step393 p h) (sat_nil p))))))))
def c1572 : List Lit := [(44, false), (1538, true), (50, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c686, c691, c1571, c1131, c1105, c368, c369, c365, c1094, c1096, c1102, c370, c1127, c1109, c1119, c1117, c1110, c1111, c395, c393] c1572 (by decide) p (sat_cons (step686 p h) (sat_cons (step691 p h) (sat_cons (step1571 p h) (sat_cons (step1131 p h) (sat_cons (step1105 p h) (sat_cons (step368 p h) (sat_cons (step369 p h) (sat_cons (step365 p h) (sat_cons (step1094 p h) (sat_cons (step1096 p h) (sat_cons (step1102 p h) (sat_cons (step370 p h) (sat_cons (step1127 p h) (sat_cons (step1109 p h) (sat_cons (step1119 p h) (sat_cons (step1117 p h) (sat_cons (step1110 p h) (sat_cons (step1111 p h) (sat_cons (step395 p h) (sat_cons (step393 p h) (sat_nil p)))))))))))))))))))))
def c1573 : List Lit := [(54, false), (50, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c691, c395, c396, c1513] c1573 (by decide) p (sat_cons (step691 p h) (sat_cons (step395 p h) (sat_cons (step396 p h) (sat_cons (step1513 p h) (sat_nil p)))))
def c1574 : List Lit := [(111, false), (1506, true), (41, false), (18, false)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c329, c326, c1063] c1574 (by decide) p (sat_cons (step329 p h) (sat_cons (step326 p h) (sat_cons (step1063 p h) (sat_nil p))))
def c1575 : List Lit := [(28, true), (1480, true), (1, true), (21, true), (23, true), (1461, false)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c972, c977, c1007, c989, c986, c987, c988, c1563, c1011, c973, c978] c1575 (by decide) p (sat_cons (step972 p h) (sat_cons (step977 p h) (sat_cons (step1007 p h) (sat_cons (step989 p h) (sat_cons (step986 p h) (sat_cons (step987 p h) (sat_cons (step988 p h) (sat_cons (step1563 p h) (sat_cons (step1011 p h) (sat_cons (step973 p h) (sat_cons (step978 p h) (sat_nil p))))))))))))
def c1576 : List Lit := [(1469, false), (1480, true), (1, true), (21, true), (23, true), (1461, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c972, c977, c1007, c990, c991, c1011, c985, c978, c1563, c973] c1576 (by decide) p (sat_cons (step972 p h) (sat_cons (step977 p h) (sat_cons (step1007 p h) (sat_cons (step990 p h) (sat_cons (step991 p h) (sat_cons (step1011 p h) (sat_cons (step985 p h) (sat_cons (step978 p h) (sat_cons (step1563 p h) (sat_cons (step973 p h) (sat_nil p)))))))))))
def c1577 : List Lit := [(1532, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c691, c1114, c1116, c1112, c1108, c1109, c396, c390] c1577 (by decide) p (sat_cons (step691 p h) (sat_cons (step1114 p h) (sat_cons (step1116 p h) (sat_cons (step1112 p h) (sat_cons (step1108 p h) (sat_cons (step1109 p h) (sat_cons (step396 p h) (sat_cons (step390 p h) (sat_nil p)))))))))
def c1578 : List Lit := [(1537, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1577, c692, c1123, c1126, c1119, c1100, c1102, c1097, c1094, c1573, c1108, c1110, c1117, c1111, c1112, c412, c389, c427] c1578 (by decide) p (sat_cons (step1577 p h) (sat_cons (step692 p h) (sat_cons (step1123 p h) (sat_cons (step1126 p h) (sat_cons (step1119 p h) (sat_cons (step1100 p h) (sat_cons (step1102 p h) (sat_cons (step1097 p h) (sat_cons (step1094 p h) (sat_cons (step1573 p h) (sat_cons (step1108 p h) (sat_cons (step1110 p h) (sat_cons (step1117 p h) (sat_cons (step1111 p h) (sat_cons (step1112 p h) (sat_cons (step412 p h) (sat_cons (step389 p h) (sat_cons (step427 p h) (sat_nil p)))))))))))))))))))
def c1579 : List Lit := [(1546, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1578, c1560, c1139] c1579 (by decide) p (sat_cons (step1578 p h) (sat_cons (step1560 p h) (sat_cons (step1139 p h) (sat_nil p))))
def c1580 : List Lit := [(1548, true), (1502, false), (42, true), (1520, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1578, c1577, c1065, c1067, c1080, c1145, c1151, c1131, c1081, c1103, c1068, c1097, c1066, c1572] c1580 (by decide) p (sat_cons (step1578 p h) (sat_cons (step1577 p h) (sat_cons (step1065 p h) (sat_cons (step1067 p h) (sat_cons (step1080 p h) (sat_cons (step1145 p h) (sat_cons (step1151 p h) (sat_cons (step1131 p h) (sat_cons (step1081 p h) (sat_cons (step1103 p h) (sat_cons (step1068 p h) (sat_cons (step1097 p h) (sat_cons (step1066 p h) (sat_cons (step1572 p h) (sat_nil p)))))))))))))))
def c1581 : List Lit := [(1478, true), (1461, false), (32, false), (26, false)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c675, c976, c1005, c1001, c977, c988, c971, c972, c985, c114, c94, c101] c1581 (by decide) p (sat_cons (step675 p h) (sat_cons (step976 p h) (sat_cons (step1005 p h) (sat_cons (step1001 p h) (sat_cons (step977 p h) (sat_cons (step988 p h) (sat_cons (step971 p h) (sat_cons (step972 p h) (sat_cons (step985 p h) (sat_cons (step114 p h) (sat_cons (step94 p h) (sat_cons (step101 p h) (sat_nil p)))))))))))))
def c1582 : List Lit := [(24, false), (29, true), (35, true), (26, false), (32, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c677, c115, c119] c1582 (by decide) p (sat_cons (step677 p h) (sat_cons (step115 p h) (sat_cons (step119 p h) (sat_nil p))))
def c1583 : List Lit := [(1594, true), (26, false), (1587, false)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c697, c1241, c1250, c1253, c1244, c1230, c1236, c1227, c442, c443] c1583 (by decide) p (sat_cons (step697 p h) (sat_cons (step1241 p h) (sat_cons (step1250 p h) (sat_cons (step1253 p h) (sat_cons (step1244 p h) (sat_cons (step1230 p h) (sat_cons (step1236 p h) (sat_cons (step1227 p h) (sat_cons (step442 p h) (sat_cons (step443 p h) (sat_nil p)))))))))))
def c1584 : List Lit := [(1641, true), (99, false), (105, false), (111, false)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c711, c1314, c1315, c540, c529, c569] c1584 (by decide) p (sat_cons (step711 p h) (sat_cons (step1314 p h) (sat_cons (step1315 p h) (sat_cons (step540 p h) (sat_cons (step529 p h) (sat_cons (step569 p h) (sat_nil p)))))))
def c1585 : List Lit := [(1658, true), (111, false), (106, true), (1639, false), (98, true)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c1326, c1328, c1334, c1319, c1346, c1335, c1330, c1337, c1327, c1584, c1350, c1320] c1585 (by decide) p (sat_cons (step1326 p h) (sat_cons (step1328 p h) (sat_cons (step1334 p h) (sat_cons (step1319 p h) (sat_cons (step1346 p h) (sat_cons (step1335 p h) (sat_cons (step1330 p h) (sat_cons (step1337 p h) (sat_cons (step1327 p h) (sat_cons (step1584 p h) (sat_cons (step1350 p h) (sat_cons (step1320 p h) (sat_nil p)))))))))))))
def c1586 : List Lit := [(1455, true), (1441, false)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c933, c961, c957, c936, c944, c1565] c1586 (by decide) p (sat_cons (step933 p h) (sat_cons (step961 p h) (sat_cons (step957 p h) (sat_cons (step936 p h) (sat_cons (step944 p h) (sat_cons (step1565 p h) (sat_nil p)))))))
def c1587 : List Lit := [(1479, true), (20, false), (28, true), (21, false), (1461, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c986, c988, c976, c1002, c1006, c989, c977, c987, c971, c94] c1587 (by decide) p (sat_cons (step986 p h) (sat_cons (step988 p h) (sat_cons (step976 p h) (sat_cons (step1002 p h) (sat_cons (step1006 p h) (sat_cons (step989 p h) (sat_cons (step977 p h) (sat_cons (step987 p h) (sat_cons (step971 p h) (sat_cons (step94 p h) (sat_nil p)))))))))))
def c1588 : List Lit := [(1448, false), (1456, true), (6, true)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c666, c930, c933, c958, c944, c947, c962, c938, c934, c936, c932, c7, c4] c1588 (by decide) p (sat_cons (step666 p h) (sat_cons (step930 p h) (sat_cons (step933 p h) (sat_cons (step958 p h) (sat_cons (step944 p h) (sat_cons (step947 p h) (sat_cons (step962 p h) (sat_cons (step938 p h) (sat_cons (step934 p h) (sat_cons (step936 p h) (sat_cons (step932 p h) (sat_cons (step7 p h) (sat_cons (step4 p h) (sat_nil p))))))))))))))
end B112E040
