import B112E026Part0000
namespace B112E026
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1466 : List Lit := [(1666, true), (99, true), (1593, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c658, c1193, c1080, c1072, c1078, c1076, c1073, c229, c232, c1204, c1202, c1195, c1197, c507] c1466 (by decide) p (sat_cons (step658 p h) (sat_cons (step1193 p h) (sat_cons (step1080 p h) (sat_cons (step1072 p h) (sat_cons (step1078 p h) (sat_cons (step1076 p h) (sat_cons (step1073 p h) (sat_cons (step229 p h) (sat_cons (step232 p h) (sat_cons (step1204 p h) (sat_cons (step1202 p h) (sat_cons (step1195 p h) (sat_cons (step1197 p h) (sat_cons (step507 p h) (sat_nil p)))))))))))))))
def c1467 : List Lit := [(1506, true), (90, true), (93, false), (19, false)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c936, c938, c934, c930, c1461, c82] c1467 (by decide) p (sat_cons (step936 p h) (sat_cons (step938 p h) (sat_cons (step934 p h) (sat_cons (step930 p h) (sat_cons (step1461 p h) (sat_cons (step82 p h) (sat_nil p)))))))
def c1468 : List Lit := [(108, true), (1683, true), (110, true), (52, false), (93, false)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c678, c1235, c1243, c1231, c1233, c1241, c381, c1236, c578, c595] c1468 (by decide) p (sat_cons (step678 p h) (sat_cons (step1235 p h) (sat_cons (step1243 p h) (sat_cons (step1231 p h) (sat_cons (step1233 p h) (sat_cons (step1241 p h) (sat_cons (step381 p h) (sat_cons (step1236 p h) (sat_cons (step578 p h) (sat_cons (step595 p h) (sat_nil p)))))))))))
def c1469 : List Lit := [(1491, true), (1476, false), (33, false), (19, false)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1402, c16, c630, c894, c912, c917, c898, c856, c1451, c873, c837, c865, c2, c3, c1434, c54, c842, c859, c851, c839, c846, c1, c21] c1469 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1402 p h) (sat_cons (step16 p h) (sat_cons (step630 p h) (sat_cons (step894 p h) (sat_cons (step912 p h) (sat_cons (step917 p h) (sat_cons (step898 p h) (sat_cons (step856 p h) (sat_cons (step1451 p h) (sat_cons (step873 p h) (sat_cons (step837 p h) (sat_cons (step865 p h) (sat_cons (step2 p h) (sat_cons (step3 p h) (sat_cons (step1434 p h) (sat_cons (step54 p h) (sat_cons (step842 p h) (sat_cons (step859 p h) (sat_cons (step851 p h) (sat_cons (step839 p h) (sat_cons (step846 p h) (sat_cons (step1 p h) (sat_cons (step21 p h) (sat_nil p)))))))))))))))))))))))))
def c1470 : List Lit := [(67, true), (1640, true), (1625, false)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c662, c1425, c1164, c1098, c1096, c1086, c1087, c1093, c260, c261, c1380, c1097, c1110, c1159, c1422, c1140] c1470 (by decide) p (sat_cons (step662 p h) (sat_cons (step1425 p h) (sat_cons (step1164 p h) (sat_cons (step1098 p h) (sat_cons (step1096 p h) (sat_cons (step1086 p h) (sat_cons (step1087 p h) (sat_cons (step1093 p h) (sat_cons (step260 p h) (sat_cons (step261 p h) (sat_cons (step1380 p h) (sat_cons (step1097 p h) (sat_cons (step1110 p h) (sat_cons (step1159 p h) (sat_cons (step1422 p h) (sat_cons (step1140 p h) (sat_nil p)))))))))))))))))
def c1471 : List Lit := [(70, true), (1640, true), (1625, false)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c664, c662, c1425, c1164, c1098, c1092, c1089, c1090, c1091, c1094, c274, c1097, c1085, c1159, c260, c1380, c1140, c1110, c1422] c1471 (by decide) p (sat_cons (step664 p h) (sat_cons (step662 p h) (sat_cons (step1425 p h) (sat_cons (step1164 p h) (sat_cons (step1098 p h) (sat_cons (step1092 p h) (sat_cons (step1089 p h) (sat_cons (step1090 p h) (sat_cons (step1091 p h) (sat_cons (step1094 p h) (sat_cons (step274 p h) (sat_cons (step1097 p h) (sat_cons (step1085 p h) (sat_cons (step1159 p h) (sat_cons (step260 p h) (sat_cons (step1380 p h) (sat_cons (step1140 p h) (sat_cons (step1110 p h) (sat_cons (step1422 p h) (sat_nil p))))))))))))))))))))
def c1472 : List Lit := [(1616, false), (1640, true), (1625, false)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c1153, c1144, c1115, c1117, c1140, c1110, c1159, c1457, c1097, c1085, c1093] c1472 (by decide) p (sat_cons (step1153 p h) (sat_cons (step1144 p h) (sat_cons (step1115 p h) (sat_cons (step1117 p h) (sat_cons (step1140 p h) (sat_cons (step1110 p h) (sat_cons (step1159 p h) (sat_cons (step1457 p h) (sat_cons (step1097 p h) (sat_cons (step1085 p h) (sat_cons (step1093 p h) (sat_nil p))))))))))))
def c1473 : List Lit := [(69, false), (3, true), (11, true), (1, true), (123, true), (125, true), (128, true), (72, false), (185, true), (75, false), (1640, true), (1625, false)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c664, c1402, c660, c659, c631, c656, c632, c274, c1380, c258, c1110, c6, c1422, c1140, c1159, c1100, c1078, c1080, c1075, c1076, c1072, c1073, c235, c252, c229, c249, c17, c253, c18, c212, c20, c202, c14] c1473 (by decide) p (sat_cons (step664 p h) (sat_cons (step1402 p h) (sat_cons (step660 p h) (sat_cons (step659 p h) (sat_cons (step631 p h) (sat_cons (step656 p h) (sat_cons (step632 p h) (sat_cons (step274 p h) (sat_cons (step1380 p h) (sat_cons (step258 p h) (sat_cons (step1110 p h) (sat_cons (step6 p h) (sat_cons (step1422 p h) (sat_cons (step1140 p h) (sat_cons (step1159 p h) (sat_cons (step1100 p h) (sat_cons (step1078 p h) (sat_cons (step1080 p h) (sat_cons (step1075 p h) (sat_cons (step1076 p h) (sat_cons (step1072 p h) (sat_cons (step1073 p h) (sat_cons (step235 p h) (sat_cons (step252 p h) (sat_cons (step229 p h) (sat_cons (step249 p h) (sat_cons (step17 p h) (sat_cons (step253 p h) (sat_cons (step18 p h) (sat_cons (step212 p h) (sat_cons (step20 p h) (sat_cons (step202 p h) (sat_cons (step14 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c1474 : List Lit := [(3, true), (11, true), (1, true), (123, true), (125, true), (128, true), (72, false), (185, true), (196, true), (75, false), (1640, true), (1625, false)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c664, c1402, c631, c632, c660, c656, c274, c1425, c1164, c1473, c1085, c281, c1093, c259, c277, c1101, c6, c17, c1078, c18, c1075, c20, c252, c1458, c14, c253, c202, c212] c1474 (by decide) p (sat_cons (step664 p h) (sat_cons (step1402 p h) (sat_cons (step631 p h) (sat_cons (step632 p h) (sat_cons (step660 p h) (sat_cons (step656 p h) (sat_cons (step274 p h) (sat_cons (step1425 p h) (sat_cons (step1164 p h) (sat_cons (step1473 p h) (sat_cons (step1085 p h) (sat_cons (step281 p h) (sat_cons (step1093 p h) (sat_cons (step259 p h) (sat_cons (step277 p h) (sat_cons (step1101 p h) (sat_cons (step6 p h) (sat_cons (step17 p h) (sat_cons (step1078 p h) (sat_cons (step18 p h) (sat_cons (step1075 p h) (sat_cons (step20 p h) (sat_cons (step252 p h) (sat_cons (step1458 p h) (sat_cons (step14 p h) (sat_cons (step253 p h) (sat_cons (step202 p h) (sat_cons (step212 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1475 : List Lit := [(8, false), (3, false)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c632, c1402, c19, c20, c7] c1475 (by decide) p (sat_cons (step632 p h) (sat_cons (step1402 p h) (sat_cons (step19 p h) (sat_cons (step20 p h) (sat_cons (step7 p h) (sat_nil p))))))
def c1476 : List Lit := [(1593, false), (68, false), (75, false), (1640, true), (1625, false)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c1425, c1164, c1100, c1101, c1159, c1093, c1140, c1085, c1422, c1380, c1110] c1476 (by decide) p (sat_cons (step1425 p h) (sat_cons (step1164 p h) (sat_cons (step1100 p h) (sat_cons (step1101 p h) (sat_cons (step1159 p h) (sat_cons (step1093 p h) (sat_cons (step1140 p h) (sat_cons (step1085 p h) (sat_cons (step1422 p h) (sat_cons (step1380 p h) (sat_cons (step1110 p h) (sat_nil p))))))))))))
def c1477 : List Lit := [(1555, true), (1539, false), (1504, false), (50, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c1459, c649, c974, c977, c1004, c936, c961, c1023, c1028, c1008, c965, c978, c980, c939, c976, c972, c930, c171, c185] c1477 (by decide) p (sat_cons (step1459 p h) (sat_cons (step649 p h) (sat_cons (step974 p h) (sat_cons (step977 p h) (sat_cons (step1004 p h) (sat_cons (step936 p h) (sat_cons (step961 p h) (sat_cons (step1023 p h) (sat_cons (step1028 p h) (sat_cons (step1008 p h) (sat_cons (step965 p h) (sat_cons (step978 p h) (sat_cons (step980 p h) (sat_cons (step939 p h) (sat_cons (step976 p h) (sat_cons (step972 p h) (sat_cons (step930 p h) (sat_cons (step171 p h) (sat_cons (step185 p h) (sat_nil p))))))))))))))))))))
def c1478 : List Lit := [(43, false), (47, false), (31, false)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c649, c171, c185] c1478 (by decide) p (sat_cons (step649 p h) (sat_cons (step171 p h) (sat_cons (step185 p h) (sat_nil p))))
def c1479 : List Lit := [(1472, false), (28, false), (31, false), (1482, true), (13, true)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c641, c866, c873, c899, c890, c891, c902, c882, c883, c876, c124, c867, c104, c95] c1479 (by decide) p (sat_cons (step641 p h) (sat_cons (step866 p h) (sat_cons (step873 p h) (sat_cons (step899 p h) (sat_cons (step890 p h) (sat_cons (step891 p h) (sat_cons (step902 p h) (sat_cons (step882 p h) (sat_cons (step883 p h) (sat_cons (step876 p h) (sat_cons (step124 p h) (sat_cons (step867 p h) (sat_cons (step104 p h) (sat_cons (step95 p h) (sat_nil p)))))))))))))))
def c1480 : List Lit := [(44, false), (27, false), (20, true), (28, false), (1463, false), (1482, true)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c110, c113, c869, c881, c874, c890, c902] c1480 (by decide) p (sat_cons (step110 p h) (sat_cons (step113 p h) (sat_cons (step869 p h) (sat_cons (step881 p h) (sat_cons (step874 p h) (sat_cons (step890 p h) (sat_cons (step902 p h) (sat_nil p))))))))
def c1481 : List Lit := [(19, true), (27, false), (20, true), (28, false), (1463, false), (1482, true)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c880, c887, c906, c875, c868, c870, c874, c107, c902, c881, c890] c1481 (by decide) p (sat_cons (step880 p h) (sat_cons (step887 p h) (sat_cons (step906 p h) (sat_cons (step875 p h) (sat_cons (step868 p h) (sat_cons (step870 p h) (sat_cons (step874 p h) (sat_cons (step107 p h) (sat_cons (step902 p h) (sat_cons (step881 p h) (sat_cons (step890 p h) (sat_nil p))))))))))))
def c1482 : List Lit := [(1626, false), (1640, true)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c1153, c1426, c1141, c1159, c1422, c1097, c1110, c1093, c1457, c1085] c1482 (by decide) p (sat_cons (step1153 p h) (sat_cons (step1426 p h) (sat_cons (step1141 p h) (sat_cons (step1159 p h) (sat_cons (step1422 p h) (sat_cons (step1097 p h) (sat_cons (step1110 p h) (sat_cons (step1093 p h) (sat_cons (step1457 p h) (sat_cons (step1085 p h) (sat_nil p)))))))))))
def c1483 : List Lit := [(1639, true), (1625, false)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c1425, c1152, c1158, c1140, c1097, c1422, c1093, c1110, c1085, c1457] c1483 (by decide) p (sat_cons (step1425 p h) (sat_cons (step1152 p h) (sat_cons (step1158 p h) (sat_cons (step1140 p h) (sat_cons (step1097 p h) (sat_cons (step1422 p h) (sat_cons (step1093 p h) (sat_cons (step1110 p h) (sat_cons (step1085 p h) (sat_cons (step1457 p h) (sat_nil p)))))))))))
def c1484 : List Lit := [(27, true), (47, false), (44, false)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c650, c174, c175, c1373] c1484 (by decide) p (sat_cons (step650 p h) (sat_cons (step174 p h) (sat_cons (step175 p h) (sat_cons (step1373 p h) (sat_nil p)))))
def c1485 : List Lit := [(1521, true), (43, false), (1503, false), (16, false)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c649, c1459, c647, c172, c941, c968, c966, c942, c951, c933, c168, c142, c949, c162] c1485 (by decide) p (sat_cons (step649 p h) (sat_cons (step1459 p h) (sat_cons (step647 p h) (sat_cons (step172 p h) (sat_cons (step941 p h) (sat_cons (step968 p h) (sat_cons (step966 p h) (sat_cons (step942 p h) (sat_cons (step951 p h) (sat_cons (step933 p h) (sat_cons (step168 p h) (sat_cons (step142 p h) (sat_cons (step949 p h) (sat_cons (step162 p h) (sat_nil p)))))))))))))))
def c1486 : List Lit := [(1520, true), (43, false), (1502, false), (16, false)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c649, c1459, c647, c172, c938, c965, c962, c939, c951, c933, c168, c142, c949, c162] c1486 (by decide) p (sat_cons (step649 p h) (sat_cons (step1459 p h) (sat_cons (step647 p h) (sat_cons (step172 p h) (sat_cons (step938 p h) (sat_cons (step965 p h) (sat_cons (step962 p h) (sat_cons (step939 p h) (sat_cons (step951 p h) (sat_cons (step933 p h) (sat_cons (step168 p h) (sat_cons (step142 p h) (sat_cons (step949 p h) (sat_cons (step162 p h) (sat_nil p)))))))))))))))
def c1487 : List Lit := [(90, false), (177, true), (19, false), (89, false), (52, true), (56, false)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c438, c434, c217] c1487 (by decide) p (sat_cons (step438 p h) (sat_cons (step434 p h) (sat_cons (step217 p h) (sat_nil p))))
def c1488 : List Lit := [(1532, true), (1463, false), (20, true), (1482, true), (50, true), (1502, true), (1526, false)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c974, c931, c930, c983, c981, c976, c1478, c973, c1484, c1480] c1488 (by decide) p (sat_cons (step974 p h) (sat_cons (step931 p h) (sat_cons (step930 p h) (sat_cons (step983 p h) (sat_cons (step981 p h) (sat_cons (step976 p h) (sat_cons (step1478 p h) (sat_cons (step973 p h) (sat_cons (step1484 p h) (sat_cons (step1480 p h) (sat_nil p)))))))))))
def c1489 : List Lit := [(39, false), (41, false), (37, true), (161, true)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c647, c161, c162, c165, c141] c1489 (by decide) p (sat_cons (step647 p h) (sat_cons (step161 p h) (sat_cons (step162 p h) (sat_cons (step165 p h) (sat_cons (step141 p h) (sat_nil p))))))
def c1490 : List Lit := [(48, false), (21, false), (31, false), (28, false)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c642, c127, c126, c118] c1490 (by decide) p (sat_cons (step642 p h) (sat_cons (step127 p h) (sat_cons (step126 p h) (sat_cons (step118 p h) (sat_nil p)))))
def c1491 : List Lit := [(86, true), (1640, true), (52, true)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c663, c667, c1403, c1415, c1407, c836, c665, c664, c659, c1124, c1126, c1470, c1471, c1472, c1420, c269, c289, c263, c288, c286, c768, c769, c775, c776, c781, c773, c784, c787, c770, c830, c766, c291, c834, c765, c283, c750, c764, c746, c761, c743, c275, c732, c274, c731, c1476, c730, c1078, c1080, c201, c1075, c1076, c1072, c1073, c229, c238, c249] c1491 (by decide) p (sat_cons (step663 p h) (sat_cons (step667 p h) (sat_cons (step1403 p h) (sat_cons (step1415 p h) (sat_cons (step1407 p h) (sat_cons (step836 p h) (sat_cons (step665 p h) (sat_cons (step664 p h) (sat_cons (step659 p h) (sat_cons (step1124 p h) (sat_cons (step1126 p h) (sat_cons (step1470 p h) (sat_cons (step1471 p h) (sat_cons (step1472 p h) (sat_cons (step1420 p h) (sat_cons (step269 p h) (sat_cons (step289 p h) (sat_cons (step263 p h) (sat_cons (step288 p h) (sat_cons (step286 p h) (sat_cons (step768 p h) (sat_cons (step769 p h) (sat_cons (step775 p h) (sat_cons (step776 p h) (sat_cons (step781 p h) (sat_cons (step773 p h) (sat_cons (step784 p h) (sat_cons (step787 p h) (sat_cons (step770 p h) (sat_cons (step830 p h) (sat_cons (step766 p h) (sat_cons (step291 p h) (sat_cons (step834 p h) (sat_cons (step765 p h) (sat_cons (step283 p h) (sat_cons (step750 p h) (sat_cons (step764 p h) (sat_cons (step746 p h) (sat_cons (step761 p h) (sat_cons (step743 p h) (sat_cons (step275 p h) (sat_cons (step732 p h) (sat_cons (step274 p h) (sat_cons (step731 p h) (sat_cons (step1476 p h) (sat_cons (step730 p h) (sat_cons (step1078 p h) (sat_cons (step1080 p h) (sat_cons (step201 p h) (sat_cons (step1075 p h) (sat_cons (step1076 p h) (sat_cons (step1072 p h) (sat_cons (step1073 p h) (sat_cons (step229 p h) (sat_cons (step238 p h) (sat_cons (step249 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1492 : List Lit := [(1689, true), (102, false), (89, false)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c1250, c1453, c1248, c542] c1492 (by decide) p (sat_cons (step1250 p h) (sat_cons (step1453 p h) (sat_cons (step1248 p h) (sat_cons (step542 p h) (sat_nil p)))))
def c1493 : List Lit := [(25, true), (1465, false), (1481, true), (86, false)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c871, c898, c886, c883, c884, c885, c888, c901, c879, c874, c1441, c865, c66] c1493 (by decide) p (sat_cons (step871 p h) (sat_cons (step898 p h) (sat_cons (step886 p h) (sat_cons (step883 p h) (sat_cons (step884 p h) (sat_cons (step885 p h) (sat_cons (step888 p h) (sat_cons (step901 p h) (sat_cons (step879 p h) (sat_cons (step874 p h) (sat_cons (step1441 p h) (sat_cons (step865 p h) (sat_cons (step66 p h) (sat_nil p))))))))))))))
def c1494 : List Lit := [(95, true), (60, false), (57, false)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c658, c233, c232, c1377] c1494 (by decide) p (sat_cons (step658 p h) (sat_cons (step233 p h) (sat_cons (step232 p h) (sat_cons (step1377 p h) (sat_nil p)))))
def c1495 : List Lit := [(1481, true), (25, true), (81, false), (89, false), (86, false)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c636, c883, c885, c1493, c869, c901, c397, c876, c71, c34, c31, c867] c1495 (by decide) p (sat_cons (step636 p h) (sat_cons (step883 p h) (sat_cons (step885 p h) (sat_cons (step1493 p h) (sat_cons (step869 p h) (sat_cons (step901 p h) (sat_cons (step397 p h) (sat_cons (step876 p h) (sat_cons (step71 p h) (sat_cons (step34 p h) (sat_cons (step31 p h) (sat_cons (step867 p h) (sat_nil p)))))))))))))
def c1496 : List Lit := [(81, false), (89, false), (13, false), (18, false)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c636, c397, c31, c71] c1496 (by decide) p (sat_cons (step636 p h) (sat_cons (step397 p h) (sat_cons (step31 p h) (sat_cons (step71 p h) (sat_nil p)))))
def c1497 : List Lit := [(82, true), (105, false), (113, true), (225, true), (81, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c677, c570, c569, c565, c1399] c1497 (by decide) p (sat_cons (step677 p h) (sat_cons (step570 p h) (sat_cons (step569 p h) (sat_cons (step565 p h) (sat_cons (step1399 p h) (sat_nil p))))))
def c1498 : List Lit := [(108, false), (105, false), (88, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c679, c581, c582, c1399] c1498 (by decide) p (sat_cons (step679 p h) (sat_cons (step581 p h) (sat_cons (step582 p h) (sat_cons (step1399 p h) (sat_nil p)))))
def c1499 : List Lit := [(1689, true), (1663, false), (1694, false), (99, true), (1727, true), (1626, false)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c685, c682, c1193, c1202, c1482, c1317, c1292, c1250, c1252, c1247, c1248, c1244, c1245, c629, c602, c625, c606, c605, c614, c613, c1396, c1110, c1184, c1422, c1186, c1141, c1218, c1219, c1287, c1205, c1324, c1195, c1160, c508, c1100, c1072, c1080] c1499 (by decide) p (sat_cons (step685 p h) (sat_cons (step682 p h) (sat_cons (step1193 p h) (sat_cons (step1202 p h) (sat_cons (step1482 p h) (sat_cons (step1317 p h) (sat_cons (step1292 p h) (sat_cons (step1250 p h) (sat_cons (step1252 p h) (sat_cons (step1247 p h) (sat_cons (step1248 p h) (sat_cons (step1244 p h) (sat_cons (step1245 p h) (sat_cons (step629 p h) (sat_cons (step602 p h) (sat_cons (step625 p h) (sat_cons (step606 p h) (sat_cons (step605 p h) (sat_cons (step614 p h) (sat_cons (step613 p h) (sat_cons (step1396 p h) (sat_cons (step1110 p h) (sat_cons (step1184 p h) (sat_cons (step1422 p h) (sat_cons (step1186 p h) (sat_cons (step1141 p h) (sat_cons (step1218 p h) (sat_cons (step1219 p h) (sat_cons (step1287 p h) (sat_cons (step1205 p h) (sat_cons (step1324 p h) (sat_cons (step1195 p h) (sat_cons (step1160 p h) (sat_cons (step508 p h) (sat_cons (step1100 p h) (sat_cons (step1072 p h) (sat_cons (step1080 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c1500 : List Lit := [(1627, true), (93, false), (81, true), (89, true), (91, false)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c672, c1121, c1123, c1130, c1132, c1125, c1122, c340, c459, c455] c1500 (by decide) p (sat_cons (step672 p h) (sat_cons (step1121 p h) (sat_cons (step1123 p h) (sat_cons (step1130 p h) (sat_cons (step1132 p h) (sat_cons (step1125 p h) (sat_cons (step1122 p h) (sat_cons (step340 p h) (sat_cons (step459 p h) (sat_cons (step455 p h) (sat_nil p)))))))))))
def c1501 : List Lit := [(1641, true), (1627, false)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1154, c1142, c1160, c1422, c1097, c1110, c1093, c1457, c1085] c1501 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1154 p h) (sat_cons (step1142 p h) (sat_cons (step1160 p h) (sat_cons (step1422 p h) (sat_cons (step1097 p h) (sat_cons (step1110 p h) (sat_cons (step1093 p h) (sat_cons (step1457 p h) (sat_cons (step1085 p h) (sat_nil p)))))))))))
def c1502 : List Lit := [(1682, true), (105, false), (108, true)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c681, c1231, c1242, c1240, c1233, c1234, c1235, c597, c585, c593] c1502 (by decide) p (sat_cons (step681 p h) (sat_cons (step1231 p h) (sat_cons (step1242 p h) (sat_cons (step1240 p h) (sat_cons (step1233 p h) (sat_cons (step1234 p h) (sat_cons (step1235 p h) (sat_cons (step597 p h) (sat_cons (step585 p h) (sat_cons (step593 p h) (sat_nil p)))))))))))
def c1503 : List Lit := [(1682, true), (85, false), (86, false), (108, true)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c678, c1231, c1242, c1240, c1233, c1234, c1235, c597, c385, c578] c1503 (by decide) p (sat_cons (step678 p h) (sat_cons (step1231 p h) (sat_cons (step1242 p h) (sat_cons (step1240 p h) (sat_cons (step1233 p h) (sat_cons (step1234 p h) (sat_cons (step1235 p h) (sat_cons (step597 p h) (sat_cons (step385 p h) (sat_cons (step578 p h) (sat_nil p)))))))))))
def c1504 : List Lit := [(79, false), (1603, true), (417, true), (110, false)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c1403, c667, c664, c784, c781, c775, c769, c768, c286, c786, c766, c765, c764, c761, c289, c272, c271, c276, c1086, c273, c1095, c1090] c1504 (by decide) p (sat_cons (step1403 p h) (sat_cons (step667 p h) (sat_cons (step664 p h) (sat_cons (step784 p h) (sat_cons (step781 p h) (sat_cons (step775 p h) (sat_cons (step769 p h) (sat_cons (step768 p h) (sat_cons (step286 p h) (sat_cons (step786 p h) (sat_cons (step766 p h) (sat_cons (step765 p h) (sat_cons (step764 p h) (sat_cons (step761 p h) (sat_cons (step289 p h) (sat_cons (step272 p h) (sat_cons (step271 p h) (sat_cons (step276 p h) (sat_cons (step1086 p h) (sat_cons (step273 p h) (sat_cons (step1095 p h) (sat_cons (step1090 p h) (sat_nil p)))))))))))))))))))))))
def c1505 : List Lit := [(1553, true), (1512, false), (1539, false)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c1460, c1000, c1016, c1021, c1004, c959, c1436, c953] c1505 (by decide) p (sat_cons (step1460 p h) (sat_cons (step1000 p h) (sat_cons (step1016 p h) (sat_cons (step1021 p h) (sat_cons (step1004 p h) (sat_cons (step959 p h) (sat_cons (step1436 p h) (sat_cons (step953 p h) (sat_nil p)))))))))
def c1506 : List Lit := [(1458, true)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c1402, c16, c856, c1451, c837, c2, c3, c1475, c845, c843, c853] c1506 (by decide) p (sat_cons (step1402 p h) (sat_cons (step16 p h) (sat_cons (step856 p h) (sat_cons (step1451 p h) (sat_cons (step837 p h) (sat_cons (step2 p h) (sat_cons (step3 p h) (sat_cons (step1475 p h) (sat_cons (step845 p h) (sat_cons (step843 p h) (sat_cons (step853 p h) (sat_nil p))))))))))))
def c1507 : List Lit := [(1489, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c1506, c915] c1507 (by decide) p (sat_cons (step1506 p h) (sat_cons (step915 p h) (sat_nil p)))
def c1508 : List Lit := [(1463, true), (1473, true), (22, false)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c639, c882, c883, c96, c865, c866, c28, c88, c87] c1508 (by decide) p (sat_cons (step639 p h) (sat_cons (step882 p h) (sat_cons (step883 p h) (sat_cons (step96 p h) (sat_cons (step865 p h) (sat_cons (step866 p h) (sat_cons (step28 p h) (sat_cons (step88 p h) (sat_cons (step87 p h) (sat_nil p))))))))))
def c1509 : List Lit := [(1705, true), (1661, false), (108, true), (1689, false), (1657, false)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c1231, c1239, c1258, c1201, c1212, c1282, c1278, c1213, c1262, c1202, c1502, c1196] c1509 (by decide) p (sat_cons (step1231 p h) (sat_cons (step1239 p h) (sat_cons (step1258 p h) (sat_cons (step1201 p h) (sat_cons (step1212 p h) (sat_cons (step1282 p h) (sat_cons (step1278 p h) (sat_cons (step1213 p h) (sat_cons (step1262 p h) (sat_cons (step1202 p h) (sat_cons (step1502 p h) (sat_cons (step1196 p h) (sat_nil p)))))))))))))
def c1510 : List Lit := [(1644, true), (1606, false), (1627, false), (1593, false), (110, false), (417, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c665, c1427, c784, c781, c774, c773, c770, c1178, c1168, c1103, c1146, c1504, c1420, c290, c1117, c282, c1109] c1510 (by decide) p (sat_cons (step665 p h) (sat_cons (step1427 p h) (sat_cons (step784 p h) (sat_cons (step781 p h) (sat_cons (step774 p h) (sat_cons (step773 p h) (sat_cons (step770 p h) (sat_cons (step1178 p h) (sat_cons (step1168 p h) (sat_cons (step1103 p h) (sat_cons (step1146 p h) (sat_cons (step1504 p h) (sat_cons (step1420 p h) (sat_cons (step290 p h) (sat_cons (step1117 p h) (sat_cons (step282 p h) (sat_cons (step1109 p h) (sat_nil p))))))))))))))))))
def c1511 : List Lit := [(1555, true), (35, false), (1539, false), (1506, false), (44, true), (1510, false)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c1459, c649, c971, c979, c1004, c961, c1023, c1028, c1008, c962, c982, c953, c973, c947, c172, c168] c1511 (by decide) p (sat_cons (step1459 p h) (sat_cons (step649 p h) (sat_cons (step971 p h) (sat_cons (step979 p h) (sat_cons (step1004 p h) (sat_cons (step961 p h) (sat_cons (step1023 p h) (sat_cons (step1028 p h) (sat_cons (step1008 p h) (sat_cons (step962 p h) (sat_cons (step982 p h) (sat_cons (step953 p h) (sat_cons (step973 p h) (sat_cons (step947 p h) (sat_cons (step172 p h) (sat_cons (step168 p h) (sat_nil p)))))))))))))))))
def c1512 : List Lit := [(1512, true), (35, false)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c947, c948, c1450] c1512 (by decide) p (sat_cons (step947 p h) (sat_cons (step948 p h) (sat_cons (step1450 p h) (sat_nil p))))
def c1513 : List Lit := [(43, false), (41, false), (35, false)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c649, c172, c168] c1513 (by decide) p (sat_cons (step649 p h) (sat_cons (step172 p h) (sat_cons (step168 p h) (sat_nil p))))
def c1514 : List Lit := [(1681, true), (110, false)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c681, c1237, c1239, c1234, c1231, c1232, c586, c597, c593] c1514 (by decide) p (sat_cons (step681 p h) (sat_cons (step1237 p h) (sat_cons (step1239 p h) (sat_cons (step1234 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step586 p h) (sat_cons (step597 p h) (sat_cons (step593 p h) (sat_nil p))))))))))
def c1515 : List Lit := [(1689, true), (116, true)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c685, c1250, c1252, c1247, c1248, c1244, c625, c629] c1515 (by decide) p (sat_cons (step685 p h) (sat_cons (step1250 p h) (sat_cons (step1252 p h) (sat_cons (step1247 p h) (sat_cons (step1248 p h) (sat_cons (step1244 p h) (sat_cons (step625 p h) (sat_cons (step629 p h) (sat_nil p)))))))))
def c1516 : List Lit := [(111, false), (107, false), (108, false), (110, false)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c681, c586, c597, c593] c1516 (by decide) p (sat_cons (step681 p h) (sat_cons (step586 p h) (sat_cons (step597 p h) (sat_cons (step593 p h) (sat_nil p)))))
def c1517 : List Lit := [(1539, true), (53, true)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c656, c985, c996, c994, c987, c988, c989, c212, c213] c1517 (by decide) p (sat_cons (step656 p h) (sat_cons (step985 p h) (sat_cons (step996 p h) (sat_cons (step994 p h) (sat_cons (step987 p h) (sat_cons (step988 p h) (sat_cons (step989 p h) (sat_cons (step212 p h) (sat_cons (step213 p h) (sat_nil p))))))))))
def c1518 : List Lit := [(1465, false), (1481, true), (22, true), (16, false), (35, false)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c879, c887, c901, c871, c874, c898, c866, c890, c61, c881] c1518 (by decide) p (sat_cons (step879 p h) (sat_cons (step887 p h) (sat_cons (step901 p h) (sat_cons (step871 p h) (sat_cons (step874 p h) (sat_cons (step898 p h) (sat_cons (step866 p h) (sat_cons (step890 p h) (sat_cons (step61 p h) (sat_cons (step881 p h) (sat_nil p)))))))))))
def c1519 : List Lit := [(1510, true), (38, true), (47, false), (44, false), (33, false)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c646, c944, c945, c132, c178, c150] c1519 (by decide) p (sat_cons (step646 p h) (sat_cons (step944 p h) (sat_cons (step945 p h) (sat_cons (step132 p h) (sat_cons (step178 p h) (sat_cons (step150 p h) (sat_nil p)))))))
def c1520 : List Lit := [(1471, false), (13, true), (1482, true), (15, false), (33, false), (1465, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c866, c874, c902, c887, c888, c906, c883, c877, c55, c867] c1520 (by decide) p (sat_cons (step866 p h) (sat_cons (step874 p h) (sat_cons (step902 p h) (sat_cons (step887 p h) (sat_cons (step888 p h) (sat_cons (step906 p h) (sat_cons (step883 p h) (sat_cons (step877 p h) (sat_cons (step55 p h) (sat_cons (step867 p h) (sat_nil p)))))))))))
def c1521 : List Lit := [(1642, true), (1593, false), (1627, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c1100, c1427, c1161, c1166, c1142, c1101, c1422, c1093, c1110, c1085, c1457] c1521 (by decide) p (sat_cons (step1100 p h) (sat_cons (step1427 p h) (sat_cons (step1161 p h) (sat_cons (step1166 p h) (sat_cons (step1142 p h) (sat_cons (step1101 p h) (sat_cons (step1422 p h) (sat_cons (step1093 p h) (sat_cons (step1110 p h) (sat_cons (step1085 p h) (sat_cons (step1457 p h) (sat_nil p))))))))))))
def c1522 : List Lit := [(1601, true), (71, false), (110, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c1091, c1093, c1089, c1086, c270] c1522 (by decide) p (sat_cons (step1091 p h) (sat_cons (step1093 p h) (sat_cons (step1089 p h) (sat_cons (step1086 p h) (sat_cons (step270 p h) (sat_nil p))))))
def c1523 : List Lit := [(1540, false), (1555, true), (1502, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c1459, c938, c961, c1023, c1001, c1005, c1028, c1436, c965, c962, c939, c953, c933, c1512] c1523 (by decide) p (sat_cons (step1459 p h) (sat_cons (step938 p h) (sat_cons (step961 p h) (sat_cons (step1023 p h) (sat_cons (step1001 p h) (sat_cons (step1005 p h) (sat_cons (step1028 p h) (sat_cons (step1436 p h) (sat_cons (step965 p h) (sat_cons (step962 p h) (sat_cons (step939 p h) (sat_cons (step953 p h) (sat_cons (step933 p h) (sat_cons (step1512 p h) (sat_nil p)))))))))))))))
def c1524 : List Lit := [(1628, false), (1616, false), (67, true), (1635, true), (1593, false), (1645, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c1115, c1143, c1175, c1147, c1102, c1117, c1096, c1110, c1087, c1457] c1524 (by decide) p (sat_cons (step1115 p h) (sat_cons (step1143 p h) (sat_cons (step1175 p h) (sat_cons (step1147 p h) (sat_cons (step1102 p h) (sat_cons (step1117 p h) (sat_cons (step1096 p h) (sat_cons (step1110 p h) (sat_cons (step1087 p h) (sat_cons (step1457 p h) (sat_nil p)))))))))))
def c1525 : List Lit := [(1689, true), (95, true)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c682, c1250, c1252, c1248, c1244, c1245, c602, c606] c1525 (by decide) p (sat_cons (step682 p h) (sat_cons (step1250 p h) (sat_cons (step1252 p h) (sat_cons (step1248 p h) (sat_cons (step1244 p h) (sat_cons (step1245 p h) (sat_cons (step602 p h) (sat_cons (step606 p h) (sat_nil p)))))))))
def c1526 : List Lit := [(115, false), (94, false), (105, false), (95, true)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c682, c607, c599] c1526 (by decide) p (sat_cons (step682 p h) (sat_cons (step607 p h) (sat_cons (step599 p h) (sat_nil p))))
def c1527 : List Lit := [(117, false), (118, false), (119, false), (96, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c685, c614, c629, c625] c1527 (by decide) p (sat_cons (step685 p h) (sat_cons (step614 p h) (sat_cons (step629 p h) (sat_cons (step625 p h) (sat_nil p)))))
def c1528 : List Lit := [(1682, false), (1653, false), (95, true), (1706, true), (1661, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c1201, c1187, c1212, c1279, c1525, c1263, c1255, c1262, c1283, c1213, c1217, c1202, c1188, c1196, c1182, c1183, c1526, c1245, c1253, c1247, c1248, c1527, c1246] c1528 (by decide) p (sat_cons (step1201 p h) (sat_cons (step1187 p h) (sat_cons (step1212 p h) (sat_cons (step1279 p h) (sat_cons (step1525 p h) (sat_cons (step1263 p h) (sat_cons (step1255 p h) (sat_cons (step1262 p h) (sat_cons (step1283 p h) (sat_cons (step1213 p h) (sat_cons (step1217 p h) (sat_cons (step1202 p h) (sat_cons (step1188 p h) (sat_cons (step1196 p h) (sat_cons (step1182 p h) (sat_cons (step1183 p h) (sat_cons (step1526 p h) (sat_cons (step1245 p h) (sat_cons (step1253 p h) (sat_cons (step1247 p h) (sat_cons (step1248 p h) (sat_cons (step1527 p h) (sat_cons (step1246 p h) (sat_nil p))))))))))))))))))))))))
def c1529 : List Lit := [(3, false), (6, false)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c16, c1402, c2] c1529 (by decide) p (sat_cons (step16 p h) (sat_cons (step1402 p h) (sat_cons (step2 p h) (sat_nil p))))
end B112E026
