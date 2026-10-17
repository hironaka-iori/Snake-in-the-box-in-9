import B112E007Part0001
namespace B112E007
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1428 : List Lit := [(1467, false), (1489, true), (1448, false), (17, true), (146, true), (83, false)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c841, c844, c860, c918, c890, c891, c921, c880, c882, c861, c878, c874, c875, c845, c90, c843, c109, c69] c1428 (by decide) p (sat_cons (step841 p h) (sat_cons (step844 p h) (sat_cons (step860 p h) (sat_cons (step918 p h) (sat_cons (step890 p h) (sat_cons (step891 p h) (sat_cons (step921 p h) (sat_cons (step880 p h) (sat_cons (step882 p h) (sat_cons (step861 p h) (sat_cons (step878 p h) (sat_cons (step874 p h) (sat_cons (step875 p h) (sat_cons (step845 p h) (sat_cons (step90 p h) (sat_cons (step843 p h) (sat_cons (step109 p h) (sat_cons (step69 p h) (sat_nil p)))))))))))))))))))
def c1429 : List Lit := [(1535, true), (12, false), (1475, true), (56, true), (1519, false), (165, true), (172, true), (1526, false), (1529, false), (55, true), (93, false)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c960, c985, c988, c977, c963, c967, c1393, c204, c415] c1429 (by decide) p (sat_cons (step960 p h) (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step977 p h) (sat_cons (step963 p h) (sat_cons (step967 p h) (sat_cons (step1393 p h) (sat_cons (step204 p h) (sat_cons (step415 p h) (sat_nil p))))))))))
def c1430 : List Lit := [(1508, true), (158, true), (160, true), (114, false)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c937, c939, c935, c931, c932, c152, c146, c154] c1430 (by decide) p (sat_cons (step937 p h) (sat_cons (step939 p h) (sat_cons (step935 p h) (sat_cons (step931 p h) (sat_cons (step932 p h) (sat_cons (step152 p h) (sat_cons (step146 p h) (sat_cons (step154 p h) (sat_nil p)))))))))
def c1431 : List Lit := [(42, false), (36, false), (43, false), (160, true)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c152, c155] c1431 (by decide) p (sat_cons (step152 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1432 : List Lit := [(1513, true), (43, false), (1508, false), (158, true), (160, true)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c946, c950, c942, c927, c925, c1431, c933, c146, c127] c1432 (by decide) p (sat_cons (step946 p h) (sat_cons (step950 p h) (sat_cons (step942 p h) (sat_cons (step927 p h) (sat_cons (step925 p h) (sat_cons (step1431 p h) (sat_cons (step933 p h) (sat_cons (step146 p h) (sat_cons (step127 p h) (sat_nil p))))))))))
def c1433 : List Lit := [(40, false), (36, false), (43, false), (158, true)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c146, c127] c1433 (by decide) p (sat_cons (step146 p h) (sat_cons (step127 p h) (sat_nil p)))
def c1434 : List Lit := [(1652, true), (45, true), (233, true)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c1186, c1188, c1370, c1183, c1184, c1180, c1181, c519, c1299, c537] c1434 (by decide) p (sat_cons (step1186 p h) (sat_cons (step1188 p h) (sat_cons (step1370 p h) (sat_cons (step1183 p h) (sat_cons (step1184 p h) (sat_cons (step1180 p h) (sat_cons (step1181 p h) (sat_cons (step519 p h) (sat_cons (step1299 p h) (sat_cons (step537 p h) (sat_nil p)))))))))))
def c1435 : List Lit := [(55, false), (54, false), (1527, true), (1519, true)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c1415, c1413] c1435 (by decide) p (sat_cons (step1415 p h) (sat_cons (step1413 p h) (sat_nil p)))
def c1436 : List Lit := [(1664, true), (1652, false)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1199, c1202, c1194, c1157, c1424, c1149] c1436 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1199 p h) (sat_cons (step1202 p h) (sat_cons (step1194 p h) (sat_cons (step1157 p h) (sat_cons (step1424 p h) (sat_cons (step1149 p h) (sat_nil p))))))))
def c1437 : List Lit := [(55, true), (1529, true)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c828, c1405, c965, c1358, c974, c223, c716, c969, c1350, c723, c196, c735, c215, c759, c692, c822, c693, c826, c695, c709, c699, c704] c1437 (by decide) p (sat_cons (step828 p h) (sat_cons (step1405 p h) (sat_cons (step965 p h) (sat_cons (step1358 p h) (sat_cons (step974 p h) (sat_cons (step223 p h) (sat_cons (step716 p h) (sat_cons (step969 p h) (sat_cons (step1350 p h) (sat_cons (step723 p h) (sat_cons (step196 p h) (sat_cons (step735 p h) (sat_cons (step215 p h) (sat_cons (step759 p h) (sat_cons (step692 p h) (sat_cons (step822 p h) (sat_cons (step693 p h) (sat_cons (step826 p h) (sat_cons (step695 p h) (sat_cons (step709 p h) (sat_cons (step699 p h) (sat_cons (step704 p h) (sat_nil p)))))))))))))))))))))))
def c1438 : List Lit := [(57, false), (175, true), (1529, true)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c1300, c972, c1405, c1437, c1413, c220, c216] c1438 (by decide) p (sat_cons (step1300 p h) (sat_cons (step972 p h) (sat_cons (step1405 p h) (sat_cons (step1437 p h) (sat_cons (step1413 p h) (sat_cons (step220 p h) (sat_cons (step216 p h) (sat_nil p))))))))
def c1439 : List Lit := [(34, true), (40, true), (1514, true), (160, true)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c932, c939, c955, c929, c930, c951, c925, c942, c940, c933, c935, c152, c155] c1439 (by decide) p (sat_cons (step932 p h) (sat_cons (step939 p h) (sat_cons (step955 p h) (sat_cons (step929 p h) (sat_cons (step930 p h) (sat_cons (step951 p h) (sat_cons (step925 p h) (sat_cons (step942 p h) (sat_cons (step940 p h) (sat_cons (step933 p h) (sat_cons (step935 p h) (sat_cons (step152 p h) (sat_cons (step155 p h) (sat_nil p))))))))))))))
def c1440 : List Lit := [(3, true), (1449, true), (58, true), (245, true)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c546, c545, c610, c607, c609, c608, c7, c837, c8, c832, c3, c15] c1440 (by decide) p (sat_cons (step546 p h) (sat_cons (step545 p h) (sat_cons (step610 p h) (sat_cons (step607 p h) (sat_cons (step609 p h) (sat_cons (step608 p h) (sat_cons (step7 p h) (sat_cons (step837 p h) (sat_cons (step8 p h) (sat_cons (step832 p h) (sat_cons (step3 p h) (sat_cons (step15 p h) (sat_nil p)))))))))))))
def c1441 : List Lit := [(7, false), (26, false), (58, true), (125, true), (55, false)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c14, c12] c1441 (by decide) p (sat_cons (step14 p h) (sat_cons (step12 p h) (sat_nil p)))
def c1442 : List Lit := [(1488, true), (139, true), (1460, false), (1448, false), (26, false)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c920, c917, c861, c887, c890, c845, c880, c869, c1376, c877, c867, c81, c110] c1442 (by decide) p (sat_cons (step920 p h) (sat_cons (step917 p h) (sat_cons (step861 p h) (sat_cons (step887 p h) (sat_cons (step890 p h) (sat_cons (step845 p h) (sat_cons (step880 p h) (sat_cons (step869 p h) (sat_cons (step1376 p h) (sat_cons (step877 p h) (sat_cons (step867 p h) (sat_cons (step81 p h) (sat_cons (step110 p h) (sat_nil p))))))))))))))
def c1443 : List Lit := [(43, true), (1513, true), (38, false)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c946, c938, c1363, c935, c936, c937, c140, c950, c924, c927] c1443 (by decide) p (sat_cons (step946 p h) (sat_cons (step938 p h) (sat_cons (step1363 p h) (sat_cons (step935 p h) (sat_cons (step936 p h) (sat_cons (step937 p h) (sat_cons (step140 p h) (sat_cons (step950 p h) (sat_cons (step924 p h) (sat_cons (step927 p h) (sat_nil p)))))))))))
def c1444 : List Lit := [(1513, true), (38, false), (313, true)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c667, c663, c666, c665, c954, c1363, c1443, c928, c1432, c937, c1356, c934, c926, c140] c1444 (by decide) p (sat_cons (step667 p h) (sat_cons (step663 p h) (sat_cons (step666 p h) (sat_cons (step665 p h) (sat_cons (step954 p h) (sat_cons (step1363 p h) (sat_cons (step1443 p h) (sat_cons (step928 p h) (sat_cons (step1432 p h) (sat_cons (step937 p h) (sat_cons (step1356 p h) (sat_cons (step934 p h) (sat_cons (step926 p h) (sat_cons (step140 p h) (sat_nil p)))))))))))))))
def c1445 : List Lit := [(1486, true), (20, true), (1467, false), (34, false)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c890, c1396, c907, c841, c852, c844] c1445 (by decide) p (sat_cons (step890 p h) (sat_cons (step1396 p h) (sat_cons (step907 p h) (sat_cons (step841 p h) (sat_cons (step852 p h) (sat_cons (step844 p h) (sat_nil p)))))))
def c1446 : List Lit := [(7, true), (123, true), (1446, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c545, c2, c832, c9] c1446 (by decide) p (sat_cons (step545 p h) (sat_cons (step2 p h) (sat_cons (step832 p h) (sat_cons (step9 p h) (sat_nil p)))))
def c1447 : List Lit := [(25, false), (91, false), (92, false), (1666, true), (1652, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1212, c418, c419, c1136, c1144, c1138, c1151, c1162, c1161, c1152, c1208, c1424, c1194] c1447 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1212 p h) (sat_cons (step418 p h) (sat_cons (step419 p h) (sat_cons (step1136 p h) (sat_cons (step1144 p h) (sat_cons (step1138 p h) (sat_cons (step1151 p h) (sat_cons (step1162 p h) (sat_cons (step1161 p h) (sat_cons (step1152 p h) (sat_cons (step1208 p h) (sat_cons (step1424 p h) (sat_cons (step1194 p h) (sat_nil p)))))))))))))))
def c1448 : List Lit := [(11, false), (1583, true), (34, false), (13, true)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c828, c1067, c1045, c24, c23, c614, c17, c617, c1042, c1043, c618, c1044, c619, c1063, c652, c1052, c1054, c711, c1050, c1047, c826, c248, c822, c252, c759, c727, c733, c731] c1448 (by decide) p (sat_cons (step828 p h) (sat_cons (step1067 p h) (sat_cons (step1045 p h) (sat_cons (step24 p h) (sat_cons (step23 p h) (sat_cons (step614 p h) (sat_cons (step17 p h) (sat_cons (step617 p h) (sat_cons (step1042 p h) (sat_cons (step1043 p h) (sat_cons (step618 p h) (sat_cons (step1044 p h) (sat_cons (step619 p h) (sat_cons (step1063 p h) (sat_cons (step652 p h) (sat_cons (step1052 p h) (sat_cons (step1054 p h) (sat_cons (step711 p h) (sat_cons (step1050 p h) (sat_cons (step1047 p h) (sat_cons (step826 p h) (sat_cons (step248 p h) (sat_cons (step822 p h) (sat_cons (step252 p h) (sat_cons (step759 p h) (sat_cons (step727 p h) (sat_cons (step733 p h) (sat_cons (step731 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1449 : List Lit := [(405, true), (1583, true), (73, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c582, c584, c583, c1067, c1045, c1060, c757, c759, c1371, c755, c733, c743, c744, c731, c742, c739, c740, c727, c741, c738, c1374, c252, c251, c248, c295, c1041, c1043, c293, c1044, c307, c1063, c1054, c1046, c257, c300, c305, c304, c276] c1449 (by decide) p (sat_cons (step582 p h) (sat_cons (step584 p h) (sat_cons (step583 p h) (sat_cons (step1067 p h) (sat_cons (step1045 p h) (sat_cons (step1060 p h) (sat_cons (step757 p h) (sat_cons (step759 p h) (sat_cons (step1371 p h) (sat_cons (step755 p h) (sat_cons (step733 p h) (sat_cons (step743 p h) (sat_cons (step744 p h) (sat_cons (step731 p h) (sat_cons (step742 p h) (sat_cons (step739 p h) (sat_cons (step740 p h) (sat_cons (step727 p h) (sat_cons (step741 p h) (sat_cons (step738 p h) (sat_cons (step1374 p h) (sat_cons (step252 p h) (sat_cons (step251 p h) (sat_cons (step248 p h) (sat_cons (step295 p h) (sat_cons (step1041 p h) (sat_cons (step1043 p h) (sat_cons (step293 p h) (sat_cons (step1044 p h) (sat_cons (step307 p h) (sat_cons (step1063 p h) (sat_cons (step1054 p h) (sat_cons (step1046 p h) (sat_cons (step257 p h) (sat_cons (step300 p h) (sat_cons (step305 p h) (sat_cons (step304 p h) (sat_cons (step276 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c1450 : List Lit := [(106, true), (1665, true), (1652, false)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c1200, c1197, c1174, c1420, c1176, c1149, c1194, c1157, c1203] c1450 (by decide) p (sat_cons (step1200 p h) (sat_cons (step1197 p h) (sat_cons (step1174 p h) (sat_cons (step1420 p h) (sat_cons (step1176 p h) (sat_cons (step1149 p h) (sat_cons (step1194 p h) (sat_cons (step1157 p h) (sat_cons (step1203 p h) (sat_nil p))))))))))
def c1451 : List Lit := [(1636, true), (1658, true)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c1303, c1157, c1160, c1149, c1151, c1138, c1140, c1147, c1424, c1144, c1135, c1136, c1195, c454, c430, c1344, c764, c768, c770, c783, c818, c810, c805, c807, c802, c798, c801, c795, c1387, c1388] c1451 (by decide) p (sat_cons (step1303 p h) (sat_cons (step1157 p h) (sat_cons (step1160 p h) (sat_cons (step1149 p h) (sat_cons (step1151 p h) (sat_cons (step1138 p h) (sat_cons (step1140 p h) (sat_cons (step1147 p h) (sat_cons (step1424 p h) (sat_cons (step1144 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step1195 p h) (sat_cons (step454 p h) (sat_cons (step430 p h) (sat_cons (step1344 p h) (sat_cons (step764 p h) (sat_cons (step768 p h) (sat_cons (step770 p h) (sat_cons (step783 p h) (sat_cons (step818 p h) (sat_cons (step810 p h) (sat_cons (step805 p h) (sat_cons (step807 p h) (sat_cons (step802 p h) (sat_cons (step798 p h) (sat_cons (step801 p h) (sat_cons (step795 p h) (sat_cons (step1387 p h) (sat_cons (step1388 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c1452 : List Lit := [(1665, true), (1652, false)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c1303, c1191, c1200, c1207, c1450, c1158, c1150, c1451, c1203, c1192, c1194, c1176, c1178, c1424, c1173, c1149, c1152, c512, c1161, c1144, c1138, c1140, c1135, c1136, c454, c430, c1344, c764, c768, c770, c783, c818, c810, c812, c805, c807, c792, c802, c798, c791, c801, c795, c790, c1387, c518, c1388, c513, c1148] c1452 (by decide) p (sat_cons (step1303 p h) (sat_cons (step1191 p h) (sat_cons (step1200 p h) (sat_cons (step1207 p h) (sat_cons (step1450 p h) (sat_cons (step1158 p h) (sat_cons (step1150 p h) (sat_cons (step1451 p h) (sat_cons (step1203 p h) (sat_cons (step1192 p h) (sat_cons (step1194 p h) (sat_cons (step1176 p h) (sat_cons (step1178 p h) (sat_cons (step1424 p h) (sat_cons (step1173 p h) (sat_cons (step1149 p h) (sat_cons (step1152 p h) (sat_cons (step512 p h) (sat_cons (step1161 p h) (sat_cons (step1144 p h) (sat_cons (step1138 p h) (sat_cons (step1140 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step454 p h) (sat_cons (step430 p h) (sat_cons (step1344 p h) (sat_cons (step764 p h) (sat_cons (step768 p h) (sat_cons (step770 p h) (sat_cons (step783 p h) (sat_cons (step818 p h) (sat_cons (step810 p h) (sat_cons (step812 p h) (sat_cons (step805 p h) (sat_cons (step807 p h) (sat_cons (step792 p h) (sat_cons (step802 p h) (sat_cons (step798 p h) (sat_cons (step791 p h) (sat_cons (step801 p h) (sat_cons (step795 p h) (sat_cons (step790 p h) (sat_cons (step1387 p h) (sat_cons (step518 p h) (sat_cons (step1388 p h) (sat_cons (step513 p h) (sat_cons (step1148 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c1453 : List Lit := [(1, false), (14, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c544, c1] c1453 (by decide) p (sat_cons (step544 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1454 : List Lit := [(2, false), (7, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c545, c2] c1454 (by decide) p (sat_cons (step545 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1455 : List Lit := [(2, false), (5, true)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c545, c3] c1455 (by decide) p (sat_cons (step545 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1456 : List Lit := [(4, false), (5, true)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c546, c6] c1456 (by decide) p (sat_cons (step546 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1457 : List Lit := [(4, false), (3, true)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c546, c7] c1457 (by decide) p (sat_cons (step546 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1458 : List Lit := [(26, true), (12, true), (6, false), (55, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c547, c13] c1458 (by decide) p (sat_cons (step547 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1459 : List Lit := [(11, true), (8, false), (34, true)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c548, c18] c1459 (by decide) p (sat_cons (step548 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1460 : List Lit := [(9, false), (65, true)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c549, c19] c1460 (by decide) p (sat_cons (step549 p h) (sat_cons (step19 p h) (sat_nil p)))
def c1461 : List Lit := [(68, true), (10, false), (37, true)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c550, c21] c1461 (by decide) p (sat_cons (step550 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1462 : List Lit := [(13, false), (12, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c551, c32] c1462 (by decide) p (sat_cons (step551 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1463 : List Lit := [(13, false), (11, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c551, c33] c1463 (by decide) p (sat_cons (step551 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1464 : List Lit := [(16, false), (26, true), (17, true), (81, true), (14, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c553, c62] c1464 (by decide) p (sat_cons (step553 p h) (sat_cons (step62 p h) (sat_nil p)))
def c1465 : List Lit := [(18, false), (14, true), (83, true)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c554, c70] c1465 (by decide) p (sat_cons (step554 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1466 : List Lit := [(22, false), (23, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c556, c82] c1466 (by decide) p (sat_cons (step556 p h) (sat_cons (step82 p h) (sat_nil p)))
def c1467 : List Lit := [(22, false), (20, true)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c556, c83] c1467 (by decide) p (sat_cons (step556 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1468 : List Lit := [(30, false), (31, true)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c560, c120] c1468 (by decide) p (sat_cons (step560 p h) (sat_cons (step120 p h) (sat_nil p)))
def c1469 : List Lit := [(32, false), (31, true)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c561, c121] c1469 (by decide) p (sat_cons (step561 p h) (sat_cons (step121 p h) (sat_nil p)))
def c1470 : List Lit := [(35, false), (40, true), (43, true)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c563, c128] c1470 (by decide) p (sat_cons (step563 p h) (sat_cons (step128 p h) (sat_nil p)))
def c1471 : List Lit := [(35, false), (36, true), (43, true)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c563, c129] c1471 (by decide) p (sat_cons (step563 p h) (sat_cons (step129 p h) (sat_nil p)))
def c1472 : List Lit := [(39, false), (40, true)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c565, c143] c1472 (by decide) p (sat_cons (step565 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1473 : List Lit := [(39, false), (37, true)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c565, c144] c1473 (by decide) p (sat_cons (step565 p h) (sat_cons (step144 p h) (sat_nil p)))
def c1474 : List Lit := [(26, true), (43, true), (12, true), (41, false)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c566, c150] c1474 (by decide) p (sat_cons (step566 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1475 : List Lit := [(44, false), (42, true), (43, true)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c567, c156] c1475 (by decide) p (sat_cons (step567 p h) (sat_cons (step156 p h) (sat_nil p)))
def c1476 : List Lit := [(36, true), (44, false), (43, true)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c567, c157] c1476 (by decide) p (sat_cons (step567 p h) (sat_cons (step157 p h) (sat_nil p)))
def c1477 : List Lit := [(48, false), (47, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c569, c168] c1477 (by decide) p (sat_cons (step569 p h) (sat_cons (step168 p h) (sat_nil p)))
def c1478 : List Lit := [(48, false), (46, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c569, c169] c1478 (by decide) p (sat_cons (step569 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1479 : List Lit := [(49, false), (46, true)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c570, c170] c1479 (by decide) p (sat_cons (step570 p h) (sat_cons (step170 p h) (sat_nil p)))
def c1480 : List Lit := [(49, false), (42, true)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c570, c171] c1480 (by decide) p (sat_cons (step570 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1481 : List Lit := [(50, false), (55, true), (81, true), (52, true), (65, true)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c571, c182] c1481 (by decide) p (sat_cons (step571 p h) (sat_cons (step182 p h) (sat_nil p)))
def c1482 : List Lit := [(50, false), (51, true), (55, true), (65, true), (81, true)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c571, c183] c1482 (by decide) p (sat_cons (step571 p h) (sat_cons (step183 p h) (sat_nil p)))
def c1483 : List Lit := [(50, false), (51, true), (55, true), (65, true), (52, true)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c571, c184] c1483 (by decide) p (sat_cons (step571 p h) (sat_cons (step184 p h) (sat_nil p)))
def c1484 : List Lit := [(53, false), (59, true), (55, true), (54, true)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c572, c198] c1484 (by decide) p (sat_cons (step572 p h) (sat_cons (step198 p h) (sat_nil p)))
def c1485 : List Lit := [(53, false), (57, true), (55, true), (54, true)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c572, c199] c1485 (by decide) p (sat_cons (step572 p h) (sat_cons (step199 p h) (sat_nil p)))
def c1486 : List Lit := [(56, false), (54, true), (92, true), (55, true)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c573, c211] c1486 (by decide) p (sat_cons (step573 p h) (sat_cons (step211 p h) (sat_nil p)))
def c1487 : List Lit := [(56, false), (51, true), (55, true), (92, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c573, c212] c1487 (by decide) p (sat_cons (step573 p h) (sat_cons (step212 p h) (sat_nil p)))
def c1488 : List Lit := [(58, false), (55, false), (7, false)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c1300, c217] c1488 (by decide) p (sat_cons (step1300 p h) (sat_cons (step217 p h) (sat_nil p)))
def c1489 : List Lit := [(58, false), (57, false), (7, false)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c1300, c218] c1489 (by decide) p (sat_cons (step1300 p h) (sat_cons (step218 p h) (sat_nil p)))
def c1490 : List Lit := [(58, false), (7, false), (94, false)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c1300, c219] c1490 (by decide) p (sat_cons (step1300 p h) (sat_cons (step219 p h) (sat_nil p)))
def c1491 : List Lit := [(58, false), (55, false), (94, false)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c1300, c221] c1491 (by decide) p (sat_cons (step1300 p h) (sat_cons (step221 p h) (sat_nil p)))
end B112E007
