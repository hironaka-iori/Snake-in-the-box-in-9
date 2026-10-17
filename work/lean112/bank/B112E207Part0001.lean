import B112E207Part0000
namespace B112E207
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1411 : List Lit := [(74, false), (75, false), (191, true), (54, true), (69, false)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c474, c465] c1411 (by decide) p (sat_cons (step474 p h) (sat_cons (step465 p h) (sat_nil p)))
def c1412 : List Lit := [(1628, true)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c1264, c1265, c1262, c1263, c1260, c1261, c622, c611, c616] c1412 (by decide) p (sat_cons (step1264 p h) (sat_cons (step1265 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step1260 p h) (sat_cons (step1261 p h) (sat_cons (step622 p h) (sat_cons (step611 p h) (sat_cons (step616 p h) (sat_nil p))))))))))
def c1413 : List Lit := [(1632, true)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c1412, c1266] c1413 (by decide) p (sat_cons (step1412 p h) (sat_cons (step1266 p h) (sat_nil p)))
def c1414 : List Lit := [(1640, true)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1268] c1414 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1268 p h) (sat_nil p)))
def c1415 : List Lit := [(1425, true), (10, true), (1420, false), (57, false), (54, true)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c925, c929, c921, c905, c912, c902, c24, c30] c1415 (by decide) p (sat_cons (step925 p h) (sat_cons (step929 p h) (sat_cons (step921 p h) (sat_cons (step905 p h) (sat_cons (step912 p h) (sat_cons (step902 p h) (sat_cons (step24 p h) (sat_cons (step30 p h) (sat_nil p)))))))))
def c1416 : List Lit := [(69, false), (86, false), (1606, true), (186, true), (215, true), (212, true), (119, true), (68, true), (2, false), (10, true)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c628, c1243, c217, c449, c12, c35, c371, c378, c583, c1233, c1235, c1242, c566, c1236, c1237, c578] c1416 (by decide) p (sat_cons (step628 p h) (sat_cons (step1243 p h) (sat_cons (step217 p h) (sat_cons (step449 p h) (sat_cons (step12 p h) (sat_cons (step35 p h) (sat_cons (step371 p h) (sat_cons (step378 p h) (sat_cons (step583 p h) (sat_cons (step1233 p h) (sat_cons (step1235 p h) (sat_cons (step1242 p h) (sat_cons (step566 p h) (sat_cons (step1236 p h) (sat_cons (step1237 p h) (sat_cons (step578 p h) (sat_nil p)))))))))))))))))
def c1417 : List Lit := [(1596, true), (209, true), (57, false), (54, true)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c1225, c1226, c561, c555] c1417 (by decide) p (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step561 p h) (sat_cons (step555 p h) (sat_nil p)))))
def c1418 : List Lit := [(1643, true), (1599, false), (216, true)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1412, c1251, c1274, c1252, c1273, c1239, c1241, c1267, c1236, c1237, c1233, c1259, c579, c1258, c587, c595] c1418 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1412 p h) (sat_cons (step1251 p h) (sat_cons (step1274 p h) (sat_cons (step1252 p h) (sat_cons (step1273 p h) (sat_cons (step1239 p h) (sat_cons (step1241 p h) (sat_cons (step1267 p h) (sat_cons (step1236 p h) (sat_cons (step1237 p h) (sat_cons (step1233 p h) (sat_cons (step1259 p h) (sat_cons (step579 p h) (sat_cons (step1258 p h) (sat_cons (step587 p h) (sat_cons (step595 p h) (sat_nil p))))))))))))))))))
def c1419 : List Lit := [(1479, true), (1465, false), (100, false), (155, true)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c1013, c1036, c1034, c1016, c1026, c1018, c167, c136] c1419 (by decide) p (sat_cons (step1013 p h) (sat_cons (step1036 p h) (sat_cons (step1034 p h) (sat_cons (step1016 p h) (sat_cons (step1026 p h) (sat_cons (step1018 p h) (sat_cons (step167 p h) (sat_cons (step136 p h) (sat_nil p)))))))))
def c1420 : List Lit := [(15, false), (1440, true)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c1387, c954, c948, c947, c953, c951, c67, c94, c122, c115, c707, c705, c710] c1420 (by decide) p (sat_cons (step1387 p h) (sat_cons (step954 p h) (sat_cons (step948 p h) (sat_cons (step947 p h) (sat_cons (step953 p h) (sat_cons (step951 p h) (sat_cons (step67 p h) (sat_cons (step94 p h) (sat_cons (step122 p h) (sat_cons (step115 p h) (sat_cons (step707 p h) (sat_cons (step705 p h) (sat_cons (step710 p h) (sat_nil p))))))))))))))
def c1421 : List Lit := [(1431, true), (1440, true)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c954, c948, c947, c953, c951, c939, c940, c97, c116, c68, c112] c1421 (by decide) p (sat_cons (step954 p h) (sat_cons (step948 p h) (sat_cons (step947 p h) (sat_cons (step953 p h) (sat_cons (step951 p h) (sat_cons (step939 p h) (sat_cons (step940 p h) (sat_cons (step97 p h) (sat_cons (step116 p h) (sat_cons (step68 p h) (sat_cons (step112 p h) (sat_nil p))))))))))))
def c1422 : List Lit := [(17, true), (20, true), (23, false), (25, false)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c1387, c122, c115, c707, c705, c710] c1422 (by decide) p (sat_cons (step1387 p h) (sat_cons (step122 p h) (sat_cons (step115 p h) (sat_cons (step707 p h) (sat_cons (step705 p h) (sat_cons (step710 p h) (sat_nil p)))))))
def c1423 : List Lit := [(86, false), (1644, true), (218, true), (91, false), (31, true), (21, false)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c664, c1412, c541, c542, c543, c1227, c594, c1232, c592, c1255, c1258, c1275, c1259, c1267] c1423 (by decide) p (sat_cons (step664 p h) (sat_cons (step1412 p h) (sat_cons (step541 p h) (sat_cons (step542 p h) (sat_cons (step543 p h) (sat_cons (step1227 p h) (sat_cons (step594 p h) (sat_cons (step1232 p h) (sat_cons (step592 p h) (sat_cons (step1255 p h) (sat_cons (step1258 p h) (sat_cons (step1275 p h) (sat_cons (step1259 p h) (sat_cons (step1267 p h) (sat_nil p)))))))))))))))
def c1424 : List Lit := [(92, true), (1599, true), (91, false), (21, false)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c1229, c1226, c1231, c1227, c545] c1424 (by decide) p (sat_cons (step1229 p h) (sat_cons (step1226 p h) (sat_cons (step1231 p h) (sat_cons (step1227 p h) (sat_cons (step545 p h) (sat_nil p))))))
def c1425 : List Lit := [(1599, true), (91, false), (21, false)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c1424, c544, c546, c1231, c1225] c1425 (by decide) p (sat_cons (step1424 p h) (sat_cons (step544 p h) (sat_cons (step546 p h) (sat_cons (step1231 p h) (sat_cons (step1225 p h) (sat_nil p))))))
def c1426 : List Lit := [(92, false), (1543, true), (1550, true), (52, false), (54, false), (4, false), (5, false)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c334, c335, c1143, c1154, c289] c1426 (by decide) p (sat_cons (step334 p h) (sat_cons (step335 p h) (sat_cons (step1143 p h) (sat_cons (step1154 p h) (sat_cons (step289 p h) (sat_nil p))))))
def c1427 : List Lit := [(53, true), (1504, true), (57, true), (45, true)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c1041, c1054, c1062, c1081, c1050, c1043, c1045, c1049, c1052, c1077, c1042, c1065, c1063, c1056, c1057, c1058, c234, c408, c404] c1427 (by decide) p (sat_cons (step1041 p h) (sat_cons (step1054 p h) (sat_cons (step1062 p h) (sat_cons (step1081 p h) (sat_cons (step1050 p h) (sat_cons (step1043 p h) (sat_cons (step1045 p h) (sat_cons (step1049 p h) (sat_cons (step1052 p h) (sat_cons (step1077 p h) (sat_cons (step1042 p h) (sat_cons (step1065 p h) (sat_cons (step1063 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1058 p h) (sat_cons (step234 p h) (sat_cons (step408 p h) (sat_cons (step404 p h) (sat_nil p))))))))))))))))))))
def c1428 : List Lit := [(1504, true), (57, true), (45, true), (52, false), (4, false)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c1041, c1048, c1073, c1427, c282, c1056, c1065, c1066, c1077, c1057, c1058, c1051, c1049, c1042, c1044, c408, c235, c404] c1428 (by decide) p (sat_cons (step1041 p h) (sat_cons (step1048 p h) (sat_cons (step1073 p h) (sat_cons (step1427 p h) (sat_cons (step282 p h) (sat_cons (step1056 p h) (sat_cons (step1065 p h) (sat_cons (step1066 p h) (sat_cons (step1077 p h) (sat_cons (step1057 p h) (sat_cons (step1058 p h) (sat_cons (step1051 p h) (sat_cons (step1049 p h) (sat_cons (step1042 p h) (sat_cons (step1044 p h) (sat_cons (step408 p h) (sat_cons (step235 p h) (sat_cons (step404 p h) (sat_nil p)))))))))))))))))))
def c1429 : List Lit := [(1545, true), (183, true), (54, true), (64, true), (63, true), (53, false), (10, false), (100, false)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c1142, c1145, c1147, c1143, c392, c431, c441] c1429 (by decide) p (sat_cons (step1142 p h) (sat_cons (step1145 p h) (sat_cons (step1147 p h) (sat_cons (step1143 p h) (sat_cons (step392 p h) (sat_cons (step431 p h) (sat_cons (step441 p h) (sat_nil p))))))))
def c1430 : List Lit := [(243, false), (58, false), (1587, true), (1542, false), (1549, false), (1424, true)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c1378, c1364, c924, c918, c910, c928, c907, c34, c682, c685, c697, c673, c692, c672, c687, c12, c686, c215, c216, c42, c1150, c1190, c390, c388, c1158, c1192, c1180, c1147, c1172, c1182, c1220, c1203] c1430 (by decide) p (sat_cons (step1378 p h) (sat_cons (step1364 p h) (sat_cons (step924 p h) (sat_cons (step918 p h) (sat_cons (step910 p h) (sat_cons (step928 p h) (sat_cons (step907 p h) (sat_cons (step34 p h) (sat_cons (step682 p h) (sat_cons (step685 p h) (sat_cons (step697 p h) (sat_cons (step673 p h) (sat_cons (step692 p h) (sat_cons (step672 p h) (sat_cons (step687 p h) (sat_cons (step12 p h) (sat_cons (step686 p h) (sat_cons (step215 p h) (sat_cons (step216 p h) (sat_cons (step42 p h) (sat_cons (step1150 p h) (sat_cons (step1190 p h) (sat_cons (step390 p h) (sat_cons (step388 p h) (sat_cons (step1158 p h) (sat_cons (step1192 p h) (sat_cons (step1180 p h) (sat_cons (step1147 p h) (sat_cons (step1172 p h) (sat_cons (step1182 p h) (sat_cons (step1220 p h) (sat_cons (step1203 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1431 : List Lit := [(1575, true)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1202, c1194, c1182, c1400] c1431 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1202 p h) (sat_cons (step1194 p h) (sat_cons (step1182 p h) (sat_cons (step1400 p h) (sat_nil p))))))
def c1432 : List Lit := [(1643, false), (1586, false), (243, false), (1445, false), (1664, true), (1542, false), (1549, false), (58, false), (1514, false)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c1313, c1302, c1297, c1430, c1308, c984, c1112] c1432 (by decide) p (sat_cons (step1313 p h) (sat_cons (step1302 p h) (sat_cons (step1297 p h) (sat_cons (step1430 p h) (sat_cons (step1308 p h) (sat_cons (step984 p h) (sat_cons (step1112 p h) (sat_nil p))))))))
def c1433 : List Lit := [(1599, true), (209, true), (21, false), (90, true), (5, false), (53, false)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c1425, c1231, c1226, c329, c556] c1433 (by decide) p (sat_cons (step1425 p h) (sat_cons (step1231 p h) (sat_cons (step1226 p h) (sat_cons (step329 p h) (sat_cons (step556 p h) (sat_nil p))))))
def c1434 : List Lit := [(1643, true), (1599, false)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1412, c1379, c1251, c1274, c1418, c1273, c1252, c584, c854, c1267, c1239, c860, c1259, c1236, c857, c1258, c591, c595] c1434 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1412 p h) (sat_cons (step1379 p h) (sat_cons (step1251 p h) (sat_cons (step1274 p h) (sat_cons (step1418 p h) (sat_cons (step1273 p h) (sat_cons (step1252 p h) (sat_cons (step584 p h) (sat_cons (step854 p h) (sat_cons (step1267 p h) (sat_cons (step1239 p h) (sat_cons (step860 p h) (sat_cons (step1259 p h) (sat_cons (step1236 p h) (sat_cons (step857 p h) (sat_cons (step1258 p h) (sat_cons (step591 p h) (sat_cons (step595 p h) (sat_nil p))))))))))))))))))))
def c1435 : List Lit := [(54, false), (1558, true), (5, false), (63, true), (72, true), (53, false)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c328, c327, c1154, c1143, c1156, c1145, c1172] c1435 (by decide) p (sat_cons (step328 p h) (sat_cons (step327 p h) (sat_cons (step1154 p h) (sat_cons (step1143 p h) (sat_cons (step1156 p h) (sat_cons (step1145 p h) (sat_cons (step1172 p h) (sat_nil p))))))))
def c1436 : List Lit := [(1605, true), (100, false), (59, true), (215, true)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1241, c1237, c1233, c579, c582] c1436 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1241 p h) (sat_cons (step1237 p h) (sat_cons (step1233 p h) (sat_cons (step579 p h) (sat_cons (step582 p h) (sat_nil p)))))))
def c1437 : List Lit := [(100, false), (59, true), (1644, true), (215, true), (218, true), (1599, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1412, c1276, c1253, c1436, c1252, c1275, c1267, c1259, c1258, c591, c595, c1237, c1242, c1233, c1234, c582, c577] c1437 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1412 p h) (sat_cons (step1276 p h) (sat_cons (step1253 p h) (sat_cons (step1436 p h) (sat_cons (step1252 p h) (sat_cons (step1275 p h) (sat_cons (step1267 p h) (sat_cons (step1259 p h) (sat_cons (step1258 p h) (sat_cons (step591 p h) (sat_cons (step595 p h) (sat_cons (step1237 p h) (sat_cons (step1242 p h) (sat_cons (step1233 p h) (sat_cons (step1234 p h) (sat_cons (step582 p h) (sat_cons (step577 p h) (sat_nil p)))))))))))))))))))
def c1438 : List Lit := [(1552, false), (215, true), (218, true), (1599, false), (1663, true), (58, false), (63, true)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1413, c1434, c1297, c1219, c1142, c1144, c1168, c1172, c1216, c1145, c1147, c1292, c1143, c1276, c397, c1253, c1240, c1437, c1236, c1238, c1242, c1233, c1234, c582, c576] c1438 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1413 p h) (sat_cons (step1434 p h) (sat_cons (step1297 p h) (sat_cons (step1219 p h) (sat_cons (step1142 p h) (sat_cons (step1144 p h) (sat_cons (step1168 p h) (sat_cons (step1172 p h) (sat_cons (step1216 p h) (sat_cons (step1145 p h) (sat_cons (step1147 p h) (sat_cons (step1292 p h) (sat_cons (step1143 p h) (sat_cons (step1276 p h) (sat_cons (step397 p h) (sat_cons (step1253 p h) (sat_cons (step1240 p h) (sat_cons (step1437 p h) (sat_cons (step1236 p h) (sat_cons (step1238 p h) (sat_cons (step1242 p h) (sat_cons (step1233 p h) (sat_cons (step1234 p h) (sat_cons (step582 p h) (sat_cons (step576 p h) (sat_nil p)))))))))))))))))))))))))))
def c1439 : List Lit := [(1599, false), (5, false), (1663, true), (58, false), (63, true), (72, true), (53, false)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.TreeRup.prove_clause [c1431, c901, c659, c1153, c1155, c1142, c1144, c1167, c1434, c1297, c1215, c1219, c1435, c25, c674, c679, c682, c696, c724, c779, c899, c893, c895, c890, c836, c866, c832, c834, c862, c830, c818, c858, c859, c823, c824, c813, c857, c855, c822, c820, c811, c1438, c1156, c1158, c1154, c1150, c1411, c499, c1184, c1398, c497, c1204, c1217, c1186, c1197, c1171, c1194, c1188, c1145, c1206, c1143, c1185, c430, c1179, c494, c493, c1342] c1439 (by decide) p (sat_cons (step1431 p h) (sat_cons (step901 p h) (sat_cons (step659 p h) (sat_cons (step1153 p h) (sat_cons (step1155 p h) (sat_cons (step1142 p h) (sat_cons (step1144 p h) (sat_cons (step1167 p h) (sat_cons (step1434 p h) (sat_cons (step1297 p h) (sat_cons (step1215 p h) (sat_cons (step1219 p h) (sat_cons (step1435 p h) (sat_cons (step25 p h) (sat_cons (step674 p h) (sat_cons (step679 p h) (sat_cons (step682 p h) (sat_cons (step696 p h) (sat_cons (step724 p h) (sat_cons (step779 p h) (sat_cons (step899 p h) (sat_cons (step893 p h) (sat_cons (step895 p h) (sat_cons (step890 p h) (sat_cons (step836 p h) (sat_cons (step866 p h) (sat_cons (step832 p h) (sat_cons (step834 p h) (sat_cons (step862 p h) (sat_cons (step830 p h) (sat_cons (step818 p h) (sat_cons (step858 p h) (sat_cons (step859 p h) (sat_cons (step823 p h) (sat_cons (step824 p h) (sat_cons (step813 p h) (sat_cons (step857 p h) (sat_cons (step855 p h) (sat_cons (step822 p h) (sat_cons (step820 p h) (sat_cons (step811 p h) (sat_cons (step1438 p h) (sat_cons (step1156 p h) (sat_cons (step1158 p h) (sat_cons (step1154 p h) (sat_cons (step1150 p h) (sat_cons (step1411 p h) (sat_cons (step499 p h) (sat_cons (step1184 p h) (sat_cons (step1398 p h) (sat_cons (step497 p h) (sat_cons (step1204 p h) (sat_cons (step1217 p h) (sat_cons (step1186 p h) (sat_cons (step1197 p h) (sat_cons (step1171 p h) (sat_cons (step1194 p h) (sat_cons (step1188 p h) (sat_cons (step1145 p h) (sat_cons (step1206 p h) (sat_cons (step1143 p h) (sat_cons (step1185 p h) (sat_cons (step430 p h) (sat_cons (step1179 p h) (sat_cons (step494 p h) (sat_cons (step493 p h) (sat_cons (step1342 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1440 : List Lit := [(5, false), (1663, true), (58, false), (63, true), (72, true), (90, true), (53, false)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c901, c1439, c1231, c1225, c1226, c329, c25, c674, c679, c682, c696, c724, c779, c899, c893, c890, c868, c849, c847, c844, c555, c556, c1345] c1440 (by decide) p (sat_cons (step901 p h) (sat_cons (step1439 p h) (sat_cons (step1231 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step329 p h) (sat_cons (step25 p h) (sat_cons (step674 p h) (sat_cons (step679 p h) (sat_cons (step682 p h) (sat_cons (step696 p h) (sat_cons (step724 p h) (sat_cons (step779 p h) (sat_cons (step899 p h) (sat_cons (step893 p h) (sat_cons (step890 p h) (sat_cons (step868 p h) (sat_cons (step849 p h) (sat_cons (step847 p h) (sat_cons (step844 p h) (sat_cons (step555 p h) (sat_cons (step556 p h) (sat_cons (step1345 p h) (sat_nil p))))))))))))))))))))))))
def c1441 : List Lit := [(209, true), (54, true), (1596, true)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c1226, c1225, c555, c556, c1345] c1441 (by decide) p (sat_cons (step1226 p h) (sat_cons (step1225 p h) (sat_cons (step555 p h) (sat_cons (step556 p h) (sat_cons (step1345 p h) (sat_nil p))))))
def c1442 : List Lit := [(1431, false), (1445, true)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c968, c942, c945, c964, c1420] c1442 (by decide) p (sat_cons (step968 p h) (sat_cons (step942 p h) (sat_cons (step945 p h) (sat_cons (step964 p h) (sat_cons (step1420 p h) (sat_nil p))))))
def c1443 : List Lit := [(79, false), (59, true), (69, false), (196, true), (58, false)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c484, c488] c1443 (by decide) p (sat_cons (step484 p h) (sat_cons (step488 p h) (sat_nil p)))
def c1444 : List Lit := [(74, false), (69, true), (191, true), (54, true), (72, true)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c656, c473, c474, c1341, c468] c1444 (by decide) p (sat_cons (step656 p h) (sat_cons (step473 p h) (sat_cons (step474 p h) (sat_cons (step1341 p h) (sat_cons (step468 p h) (sat_nil p))))))
def c1445 : List Lit := [(75, true), (1577, true), (1569, false)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c1192, c1206, c1184, c1185, c1204, c1400, c1195] c1445 (by decide) p (sat_cons (step1192 p h) (sat_cons (step1206 p h) (sat_cons (step1184 p h) (sat_cons (step1185 p h) (sat_cons (step1204 p h) (sat_cons (step1400 p h) (sat_cons (step1195 p h) (sat_nil p))))))))
def c1446 : List Lit := [(51, false), (71, false), (62, false), (1490, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c270, c266, c1044, c1040, c1049] c1446 (by decide) p (sat_cons (step270 p h) (sat_cons (step266 p h) (sat_cons (step1044 p h) (sat_cons (step1040 p h) (sat_cons (step1049 p h) (sat_nil p))))))
def c1447 : List Lit := [(61, false), (62, false), (1504, true), (1494, false), (58, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c409, c411, c1040, c1057, c1048, c1066, c1073] c1447 (by decide) p (sat_cons (step409 p h) (sat_cons (step411 p h) (sat_cons (step1040 p h) (sat_cons (step1057 p h) (sat_cons (step1048 p h) (sat_cons (step1066 p h) (sat_cons (step1073 p h) (sat_nil p))))))))
def c1448 : List Lit := [(62, false), (59, true), (1504, true), (359, true), (1494, false), (58, false)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c791, c783, c782, c789, c787, c785, c1447, c419, c406, c1057, c1066, c1073, c1046, c1048, c1044, c1040, c260] c1448 (by decide) p (sat_cons (step791 p h) (sat_cons (step783 p h) (sat_cons (step782 p h) (sat_cons (step789 p h) (sat_cons (step787 p h) (sat_cons (step785 p h) (sat_cons (step1447 p h) (sat_cons (step419 p h) (sat_cons (step406 p h) (sat_cons (step1057 p h) (sat_cons (step1066 p h) (sat_cons (step1073 p h) (sat_cons (step1046 p h) (sat_cons (step1048 p h) (sat_cons (step1044 p h) (sat_cons (step1040 p h) (sat_cons (step260 p h) (sat_nil p))))))))))))))))))
def c1449 : List Lit := [(69, true), (1553, true), (191, true), (54, true), (72, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c1150, c1444, c1159, c1154] c1449 (by decide) p (sat_cons (step1150 p h) (sat_cons (step1444 p h) (sat_cons (step1159 p h) (sat_cons (step1154 p h) (sat_nil p)))))
def c1450 : List Lit := [(1503, true), (1494, false), (58, false)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c1065, c1069, c1072, c1066, c1046, c1048, c1057, c1044, c1040, c235, c408, c404] c1450 (by decide) p (sat_cons (step1065 p h) (sat_cons (step1069 p h) (sat_cons (step1072 p h) (sat_cons (step1066 p h) (sat_cons (step1046 p h) (sat_cons (step1048 p h) (sat_cons (step1057 p h) (sat_cons (step1044 p h) (sat_cons (step1040 p h) (sat_cons (step235 p h) (sat_cons (step408 p h) (sat_cons (step404 p h) (sat_nil p)))))))))))))
def c1451 : List Lit := [(1, true), (8, true), (2, false), (20, true), (4, false)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c1378, c23, c14, c675, c672, c679, c673, c685] c1451 (by decide) p (sat_cons (step1378 p h) (sat_cons (step23 p h) (sat_cons (step14 p h) (sat_cons (step675 p h) (sat_cons (step672 p h) (sat_cons (step679 p h) (sat_cons (step673 p h) (sat_cons (step685 p h) (sat_nil p)))))))))
def c1452 : List Lit := [(1494, false), (45, true), (58, false), (1505, true), (1487, false), (177, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c1041, c1049, c1078, c1065, c1066, c1082, c1057, c1052, c406, c408, c1042] c1452 (by decide) p (sat_cons (step1041 p h) (sat_cons (step1049 p h) (sat_cons (step1078 p h) (sat_cons (step1065 p h) (sat_cons (step1066 p h) (sat_cons (step1082 p h) (sat_cons (step1057 p h) (sat_cons (step1052 p h) (sat_cons (step406 p h) (sat_cons (step408 p h) (sat_cons (step1042 p h) (sat_nil p))))))))))))
def c1453 : List Lit := [(1532, true), (1516, false), (1515, false)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c1105, c1107, c977, c978, c960, c1442, c1421] c1453 (by decide) p (sat_cons (step1105 p h) (sat_cons (step1107 p h) (sat_cons (step977 p h) (sat_cons (step978 p h) (sat_cons (step960 p h) (sat_cons (step1442 p h) (sat_cons (step1421 p h) (sat_nil p))))))))
def c1454 : List Lit := [(1598, false), (1642, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1412, c1379, c1272, c1248, c1249, c1271, c1239, c1241, c1267, c1236, c1237, c1233, c1234, c1259, c577, c1258, c595, c591, c587, c857, c854, c860] c1454 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1412 p h) (sat_cons (step1379 p h) (sat_cons (step1272 p h) (sat_cons (step1248 p h) (sat_cons (step1249 p h) (sat_cons (step1271 p h) (sat_cons (step1239 p h) (sat_cons (step1241 p h) (sat_cons (step1267 p h) (sat_cons (step1236 p h) (sat_cons (step1237 p h) (sat_cons (step1233 p h) (sat_cons (step1234 p h) (sat_cons (step1259 p h) (sat_cons (step577 p h) (sat_cons (step1258 p h) (sat_cons (step595 p h) (sat_cons (step591 p h) (sat_cons (step587 p h) (sat_cons (step857 p h) (sat_cons (step854 p h) (sat_cons (step860 p h) (sat_nil p))))))))))))))))))))))))
def c1455 : List Lit := [(20, false), (90, false), (1447, true), (4, false)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c84, c87, c89, c90, c939, c949, c945, c957, c970] c1455 (by decide) p (sat_cons (step84 p h) (sat_cons (step87 p h) (sat_cons (step89 p h) (sat_cons (step90 p h) (sat_cons (step939 p h) (sat_cons (step949 p h) (sat_cons (step945 p h) (sat_cons (step957 p h) (sat_cons (step970 p h) (sat_nil p))))))))))
def c1456 : List Lit := [(1516, false), (1452, false), (52, true), (1586, false), (4, false)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c1414, c1313, c901, c1294, c1311, c1120, c1108, c980, c1309, c1296, c1454, c1228, c1230, c1225, c1226, c550, c1455, c21, c539, c675, c841, c679, c843, c682, c851, c696, c868, c724, c890, c779, c893, c899] c1456 (by decide) p (sat_cons (step1414 p h) (sat_cons (step1313 p h) (sat_cons (step901 p h) (sat_cons (step1294 p h) (sat_cons (step1311 p h) (sat_cons (step1120 p h) (sat_cons (step1108 p h) (sat_cons (step980 p h) (sat_cons (step1309 p h) (sat_cons (step1296 p h) (sat_cons (step1454 p h) (sat_cons (step1228 p h) (sat_cons (step1230 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step550 p h) (sat_cons (step1455 p h) (sat_cons (step21 p h) (sat_cons (step539 p h) (sat_cons (step675 p h) (sat_cons (step841 p h) (sat_cons (step679 p h) (sat_cons (step843 p h) (sat_cons (step682 p h) (sat_cons (step851 p h) (sat_cons (step696 p h) (sat_cons (step868 p h) (sat_cons (step724 p h) (sat_cons (step890 p h) (sat_cons (step779 p h) (sat_cons (step893 p h) (sat_cons (step899 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c1457 : List Lit := [(20, true), (91, true), (90, false), (52, true), (4, false)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c901, c21, c539, c675, c841, c679, c843, c682, c851, c696, c868, c724, c890, c779, c893, c899] c1457 (by decide) p (sat_cons (step901 p h) (sat_cons (step21 p h) (sat_cons (step539 p h) (sat_cons (step675 p h) (sat_cons (step841 p h) (sat_cons (step679 p h) (sat_cons (step843 p h) (sat_cons (step682 p h) (sat_cons (step851 p h) (sat_cons (step696 p h) (sat_cons (step868 p h) (sat_cons (step724 p h) (sat_cons (step890 p h) (sat_cons (step779 p h) (sat_cons (step893 p h) (sat_cons (step899 p h) (sat_nil p)))))))))))))))))
def c1458 : List Lit := [(429, true), (1606, true), (91, true), (90, false), (52, true), (45, false), (58, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c663, c1243, c866, c868, c862, c851, c859, c843, c855, c841, c537, c509, c507, c1234, c575, c1235, c1242, c581, c1236, c1237, c579] c1458 (by decide) p (sat_cons (step663 p h) (sat_cons (step1243 p h) (sat_cons (step866 p h) (sat_cons (step868 p h) (sat_cons (step862 p h) (sat_cons (step851 p h) (sat_cons (step859 p h) (sat_cons (step843 p h) (sat_cons (step855 p h) (sat_cons (step841 p h) (sat_cons (step537 p h) (sat_cons (step509 p h) (sat_cons (step507 p h) (sat_cons (step1234 p h) (sat_cons (step575 p h) (sat_cons (step1235 p h) (sat_cons (step1242 p h) (sat_cons (step581 p h) (sat_cons (step1236 p h) (sat_cons (step1237 p h) (sat_cons (step579 p h) (sat_nil p))))))))))))))))))))))
def c1459 : List Lit := [(1445, true), (1433, false)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c1442, c964, c1421] c1459 (by decide) p (sat_cons (step1442 p h) (sat_cons (step964 p h) (sat_cons (step1421 p h) (sat_nil p))))
def c1460 : List Lit := [(1503, true), (52, true), (45, false), (58, true), (57, true)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c1054, c1058, c1063, c1069, c1072, c1064, c1066, c1046, c1059, c1056, c1043, c1044, c232, c349, c354] c1460 (by decide) p (sat_cons (step1054 p h) (sat_cons (step1058 p h) (sat_cons (step1063 p h) (sat_cons (step1069 p h) (sat_cons (step1072 p h) (sat_cons (step1064 p h) (sat_cons (step1066 p h) (sat_cons (step1046 p h) (sat_cons (step1059 p h) (sat_cons (step1056 p h) (sat_cons (step1043 p h) (sat_cons (step1044 p h) (sat_cons (step232 p h) (sat_cons (step349 p h) (sat_cons (step354 p h) (sat_nil p))))))))))))))))
def c1461 : List Lit := [(1445, true), (20, false), (4, false)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c1442, c1459, c939, c944, c81] c1461 (by decide) p (sat_cons (step1442 p h) (sat_cons (step1459 p h) (sat_cons (step939 p h) (sat_cons (step944 p h) (sat_cons (step81 p h) (sat_nil p))))))
def c1462 : List Lit := [(1504, true), (52, true), (45, true), (1495, false), (57, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c1041, c1048, c1054, c1063, c1427, c1077, c1073, c1051, c1049, c1066, c1042, c1044, c1056, c234, c349, c354] c1462 (by decide) p (sat_cons (step1041 p h) (sat_cons (step1048 p h) (sat_cons (step1054 p h) (sat_cons (step1063 p h) (sat_cons (step1427 p h) (sat_cons (step1077 p h) (sat_cons (step1073 p h) (sat_cons (step1051 p h) (sat_cons (step1049 p h) (sat_cons (step1066 p h) (sat_cons (step1042 p h) (sat_cons (step1044 p h) (sat_cons (step1056 p h) (sat_cons (step234 p h) (sat_cons (step349 p h) (sat_cons (step354 p h) (sat_nil p)))))))))))))))))
def c1463 : List Lit := [(1516, false), (52, true), (4, false), (1586, false)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c1456, c978, c1442, c1459, c1461, c1421, c944, c18, c960, c1, c983, c907, c928] c1463 (by decide) p (sat_cons (step1456 p h) (sat_cons (step978 p h) (sat_cons (step1442 p h) (sat_cons (step1459 p h) (sat_cons (step1461 p h) (sat_cons (step1421 p h) (sat_cons (step944 p h) (sat_cons (step18 p h) (sat_cons (step960 p h) (sat_cons (step1 p h) (sat_cons (step983 p h) (sat_cons (step907 p h) (sat_cons (step928 p h) (sat_nil p))))))))))))))
def c1464 : List Lit := [(1642, true), (207, true), (215, true), (91, true), (15, false), (20, true), (58, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c1413, c663, c1272, c1454, c1246, c1230, c1243, c538, c506, c504, c1234, c575, c1235, c1242, c581, c1236, c1237, c579] c1464 (by decide) p (sat_cons (step1413 p h) (sat_cons (step663 p h) (sat_cons (step1272 p h) (sat_cons (step1454 p h) (sat_cons (step1246 p h) (sat_cons (step1230 p h) (sat_cons (step1243 p h) (sat_cons (step538 p h) (sat_cons (step506 p h) (sat_cons (step504 p h) (sat_cons (step1234 p h) (sat_cons (step575 p h) (sat_cons (step1235 p h) (sat_cons (step1242 p h) (sat_cons (step581 p h) (sat_cons (step1236 p h) (sat_cons (step1237 p h) (sat_cons (step579 p h) (sat_nil p)))))))))))))))))))
def c1465 : List Lit := [(1487, false), (1505, true), (177, true), (45, true), (58, true), (57, true)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c1054, c1058, c1063, c1082, c1041, c1049, c1078, c1052, c1064, c1066, c1042, c1059, c1056, c407, c236] c1465 (by decide) p (sat_cons (step1054 p h) (sat_cons (step1058 p h) (sat_cons (step1063 p h) (sat_cons (step1082 p h) (sat_cons (step1041 p h) (sat_cons (step1049 p h) (sat_cons (step1078 p h) (sat_cons (step1052 p h) (sat_cons (step1064 p h) (sat_cons (step1066 p h) (sat_cons (step1042 p h) (sat_cons (step1059 p h) (sat_cons (step1056 p h) (sat_cons (step407 p h) (sat_cons (step236 p h) (sat_nil p))))))))))))))))
def c1466 : List Lit := [(1641, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c1413, c1412, c1379, c1269, c1270, c1267, c1245, c1259, c1239, c1241, c1258, c1236, c1237, c1233, c1234, c595, c577, c591, c587, c857, c854, c860] c1466 (by decide) p (sat_cons (step1413 p h) (sat_cons (step1412 p h) (sat_cons (step1379 p h) (sat_cons (step1269 p h) (sat_cons (step1270 p h) (sat_cons (step1267 p h) (sat_cons (step1245 p h) (sat_cons (step1259 p h) (sat_cons (step1239 p h) (sat_cons (step1241 p h) (sat_cons (step1258 p h) (sat_cons (step1236 p h) (sat_cons (step1237 p h) (sat_cons (step1233 p h) (sat_cons (step1234 p h) (sat_cons (step595 p h) (sat_cons (step577 p h) (sat_cons (step591 p h) (sat_cons (step587 p h) (sat_cons (step857 p h) (sat_cons (step854 p h) (sat_cons (step860 p h) (sat_nil p)))))))))))))))))))))))
def c1467 : List Lit := [(1662, true), (1505, true), (1447, true), (1487, false), (57, false), (45, true), (1495, false), (1586, false), (4, false)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1380, c1296, c1300, c1454, c1228, c1230, c1225, c1226, c1455, c561, c550, c552, c554, c1457, c344, c343, c844, c291, c288, c290, c1154, c1143, c848, c1055, c1156, c1145, c845, c1063, c1172, c559, c1082, c1220, c1052, c1200, c1042, c1193, c520, c521, c1191] c1467 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1380 p h) (sat_cons (step1296 p h) (sat_cons (step1300 p h) (sat_cons (step1454 p h) (sat_cons (step1228 p h) (sat_cons (step1230 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step1455 p h) (sat_cons (step561 p h) (sat_cons (step550 p h) (sat_cons (step552 p h) (sat_cons (step554 p h) (sat_cons (step1457 p h) (sat_cons (step344 p h) (sat_cons (step343 p h) (sat_cons (step844 p h) (sat_cons (step291 p h) (sat_cons (step288 p h) (sat_cons (step290 p h) (sat_cons (step1154 p h) (sat_cons (step1143 p h) (sat_cons (step848 p h) (sat_cons (step1055 p h) (sat_cons (step1156 p h) (sat_cons (step1145 p h) (sat_cons (step845 p h) (sat_cons (step1063 p h) (sat_cons (step1172 p h) (sat_cons (step559 p h) (sat_cons (step1082 p h) (sat_cons (step1220 p h) (sat_cons (step1052 p h) (sat_cons (step1200 p h) (sat_cons (step1042 p h) (sat_cons (step1193 p h) (sat_cons (step520 p h) (sat_cons (step521 p h) (sat_cons (step1191 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c1468 : List Lit := [(1498, true), (56, true), (50, false), (53, false), (58, true), (4, false)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c1058, c1061, c1063, c1059, c1055, c237, c282, c349] c1468 (by decide) p (sat_cons (step1058 p h) (sat_cons (step1061 p h) (sat_cons (step1063 p h) (sat_cons (step1059 p h) (sat_cons (step1055 p h) (sat_cons (step237 p h) (sat_cons (step282 p h) (sat_cons (step349 p h) (sat_nil p)))))))))
def c1469 : List Lit := [(60, false), (49, false), (177, true), (50, false)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c235, c407] c1469 (by decide) p (sat_cons (step235 p h) (sat_cons (step407 p h) (sat_nil p)))
def c1470 : List Lit := [(1424, true), (123, true), (57, false)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c924, c928, c918, c905, c911, c902, c30, c29] c1470 (by decide) p (sat_cons (step924 p h) (sat_cons (step928 p h) (sat_cons (step918 p h) (sat_cons (step905 p h) (sat_cons (step911 p h) (sat_cons (step902 p h) (sat_cons (step30 p h) (sat_cons (step29 p h) (sat_nil p)))))))))
def c1471 : List Lit := [(1596, true), (91, false), (90, false)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c1225, c1226, c550] c1471 (by decide) p (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step550 p h) (sat_nil p))))
def c1472 : List Lit := [(15, true), (1446, true), (142, true), (21, true)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c973, c939, c946, c945, c941, c969, c953, c954, c951, c947, c122, c68] c1472 (by decide) p (sat_cons (step973 p h) (sat_cons (step939 p h) (sat_cons (step946 p h) (sat_cons (step945 p h) (sat_cons (step941 p h) (sat_cons (step969 p h) (sat_cons (step953 p h) (sat_cons (step954 p h) (sat_cons (step951 p h) (sat_cons (step947 p h) (sat_cons (step122 p h) (sat_cons (step68 p h) (sat_nil p)))))))))))))
def c1473 : List Lit := [(5, false), (122, true), (53, false), (57, false)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c326, c25] c1473 (by decide) p (sat_cons (step326 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1474 : List Lit := [(1454, true), (1411, false), (142, true), (21, true), (1, false), (1424, false), (1445, false), (4, false)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c991, c985, c933, c1472, c908, c1] c1474 (by decide) p (sat_cons (step991 p h) (sat_cons (step985 p h) (sat_cons (step933 p h) (sat_cons (step1472 p h) (sat_cons (step908 p h) (sat_cons (step1 p h) (sat_nil p)))))))
end B112E207
