import B112E203Part0001
namespace B112E203
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1401 : List Lit := [(833, true), (865, true)]
theorem step1401 (p : Nat → Bool) (h : Constraints p) : clause p c1401 = true :=
  Snake9.LocalRup.prove_clause [c532, c1306, c830, c828, c827, c844, c1304, c838, c1341, c1399, c1391, c1400, c770, c794, c1393, c125, c122, c778, c780, c783, c798, c1343] c1401 (by decide) p (sat_cons (step532 p h) (sat_cons (step1306 p h) (sat_cons (step830 p h) (sat_cons (step828 p h) (sat_cons (step827 p h) (sat_cons (step844 p h) (sat_cons (step1304 p h) (sat_cons (step838 p h) (sat_cons (step1341 p h) (sat_cons (step1399 p h) (sat_cons (step1391 p h) (sat_cons (step1400 p h) (sat_cons (step770 p h) (sat_cons (step794 p h) (sat_cons (step1393 p h) (sat_cons (step125 p h) (sat_cons (step122 p h) (sat_cons (step778 p h) (sat_cons (step780 p h) (sat_cons (step783 p h) (sat_cons (step798 p h) (sat_cons (step1343 p h) (sat_nil p)))))))))))))))))))))))
def c1402 : List Lit := [(24, false), (818, true), (18, false), (33, false)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true :=
  Snake9.LocalRup.prove_clause [c84, c83, c767] c1402 (by decide) p (sat_cons (step84 p h) (sat_cons (step83 p h) (sat_cons (step767 p h) (sat_nil p))))
def c1403 : List Lit := [(828, true), (19, false), (822, false), (18, false), (865, true)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true :=
  Snake9.LocalRup.prove_clause [c532, c1306, c830, c828, c827, c844, c1304, c838, c1341, c783, c1392, c778, c125, c122] c1403 (by decide) p (sat_cons (step532 p h) (sat_cons (step1306 p h) (sat_cons (step830 p h) (sat_cons (step828 p h) (sat_cons (step827 p h) (sat_cons (step844 p h) (sat_cons (step1304 p h) (sat_cons (step838 p h) (sat_cons (step1341 p h) (sat_cons (step783 p h) (sat_cons (step1392 p h) (sat_cons (step778 p h) (sat_cons (step125 p h) (sat_cons (step122 p h) (sat_nil p)))))))))))))))
def c1404 : List Lit := [(1628, true)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c1228, c1229, c1226, c1227, c1224, c1225, c517, c506, c511] c1404 (by decide) p (sat_cons (step1228 p h) (sat_cons (step1229 p h) (sat_cons (step1226 p h) (sat_cons (step1227 p h) (sat_cons (step1224 p h) (sat_cons (step1225 p h) (sat_cons (step517 p h) (sat_cons (step506 p h) (sat_cons (step511 p h) (sat_nil p))))))))))
def c1405 : List Lit := [(1632, true)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.LocalRup.prove_clause [c1404, c1230] c1405 (by decide) p (sat_cons (step1404 p h) (sat_cons (step1230 p h) (sat_nil p)))
def c1406 : List Lit := [(122, true), (5, false), (6, true)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c522, c21, c20, c25, c1243] c1406 (by decide) p (sat_cons (step522 p h) (sat_cons (step21 p h) (sat_cons (step20 p h) (sat_cons (step25 p h) (sat_cons (step1243 p h) (sat_nil p))))))
def c1407 : List Lit := [(251, true), (1419, true), (13, true), (3, true)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.LocalRup.prove_clause [c526, c586, c587, c42, c47, c1147, c40] c1407 (by decide) p (sat_cons (step526 p h) (sat_cons (step586 p h) (sat_cons (step587 p h) (sat_cons (step42 p h) (sat_cons (step47 p h) (sat_cons (step1147 p h) (sat_cons (step40 p h) (sat_nil p))))))))
def c1408 : List Lit := [(40, false), (27, false), (31, false), (13, false), (144, true)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c116, c113, c105] c1408 (by decide) p (sat_cons (step116 p h) (sat_cons (step113 p h) (sat_cons (step105 p h) (sat_nil p))))
def c1409 : List Lit := [(94, false), (57, true), (54, false), (102, false), (91, false)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c559, c469, c470, c471] c1409 (by decide) p (sat_cons (step559 p h) (sat_cons (step469 p h) (sat_cons (step470 p h) (sat_cons (step471 p h) (sat_nil p)))))
def c1410 : List Lit := [(1603, true), (103, false), (101, false)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c1216, c1217, c490] c1410 (by decide) p (sat_cons (step1216 p h) (sat_cons (step1217 p h) (sat_cons (step490 p h) (sat_nil p))))
def c1411 : List Lit := [(1601, true), (212, true), (86, true)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c1214, c1215, c476, c475, c1272] c1411 (by decide) p (sat_cons (step1214 p h) (sat_cons (step1215 p h) (sat_cons (step476 p h) (sat_cons (step475 p h) (sat_cons (step1272 p h) (sat_nil p))))))
def c1412 : List Lit := [(101, false), (1603, true), (218, true)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c487, c1410] c1412 (by decide) p (sat_cons (step487 p h) (sat_cons (step1410 p h) (sat_nil p)))
def c1413 : List Lit := [(427, true), (1642, true), (86, true)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c1405, c1404, c1233, c1221, c700, c701, c699, c697, c698, c1411, c1218, c1219, c1220, c1412, c1232, c1222, c1231, c1223] c1413 (by decide) p (sat_cons (step1405 p h) (sat_cons (step1404 p h) (sat_cons (step1233 p h) (sat_cons (step1221 p h) (sat_cons (step700 p h) (sat_cons (step701 p h) (sat_cons (step699 p h) (sat_cons (step697 p h) (sat_cons (step698 p h) (sat_cons (step1411 p h) (sat_cons (step1218 p h) (sat_cons (step1219 p h) (sat_cons (step1220 p h) (sat_cons (step1412 p h) (sat_cons (step1232 p h) (sat_cons (step1222 p h) (sat_cons (step1231 p h) (sat_cons (step1223 p h) (sat_nil p)))))))))))))))))))
def c1414 : List Lit := [(1474, true), (41, false), (37, false)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c1163, c1164, c1162, c1160, c138] c1414 (by decide) p (sat_cons (step1163 p h) (sat_cons (step1164 p h) (sat_cons (step1162 p h) (sat_cons (step1160 p h) (sat_cons (step138 p h) (sat_nil p))))))
def c1415 : List Lit := [(1474, true), (156, true)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c1163, c1164, c1162, c1160, c1161, c135, c138] c1415 (by decide) p (sat_cons (step1163 p h) (sat_cons (step1164 p h) (sat_cons (step1162 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step135 p h) (sat_cons (step138 p h) (sat_nil p))))))))
def c1416 : List Lit := [(25, false), (18, false), (142, true), (15, false)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c100, c59] c1416 (by decide) p (sat_cons (step100 p h) (sat_cons (step59 p h) (sat_nil p)))
def c1417 : List Lit := [(1002, true), (988, false), (87, true), (45, true), (90, true)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c556, c1058, c1079, c1077, c1061, c1365, c451] c1417 (by decide) p (sat_cons (step556 p h) (sat_cons (step1058 p h) (sat_cons (step1079 p h) (sat_cons (step1077 p h) (sat_cons (step1061 p h) (sat_cons (step1365 p h) (sat_cons (step451 p h) (sat_nil p))))))))
def c1418 : List Lit := [(962, true), (84, true), (80, false), (81, false)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c1006, c1009, c1011, c1007, c1003, c440] c1418 (by decide) p (sat_cons (step1006 p h) (sat_cons (step1009 p h) (sat_cons (step1011 p h) (sat_cons (step1007 p h) (sat_cons (step1003 p h) (sat_cons (step440 p h) (sat_nil p)))))))
def c1419 : List Lit := [(954, false), (944, false), (1033, false), (810, false), (891, false), (962, false)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1141, c1376, c1318, c1021, c1040, c1120, c1136, c926, c808, c1401, c896, c1022, c912, c1041, c1135, c1125] c1419 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1141 p h) (sat_cons (step1376 p h) (sat_cons (step1318 p h) (sat_cons (step1021 p h) (sat_cons (step1040 p h) (sat_cons (step1120 p h) (sat_cons (step1136 p h) (sat_cons (step926 p h) (sat_cons (step808 p h) (sat_cons (step1401 p h) (sat_cons (step896 p h) (sat_cons (step1022 p h) (sat_cons (step912 p h) (sat_cons (step1041 p h) (sat_cons (step1135 p h) (sat_cons (step1125 p h) (sat_nil p))))))))))))))))))
def c1420 : List Lit := [(954, true), (46, false), (58, true), (70, true)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c551, c989, c999, c997, c990, c991, c430, c400] c1420 (by decide) p (sat_cons (step551 p h) (sat_cons (step989 p h) (sat_cons (step999 p h) (sat_cons (step997 p h) (sat_cons (step990 p h) (sat_cons (step991 p h) (sat_cons (step430 p h) (sat_cons (step400 p h) (sat_nil p)))))))))
def c1421 : List Lit := [(935, false), (62, true), (76, false), (944, true)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c546, c971, c966, c967, c975, c959, c952, c394, c323] c1421 (by decide) p (sat_cons (step546 p h) (sat_cons (step971 p h) (sat_cons (step966 p h) (sat_cons (step967 p h) (sat_cons (step975 p h) (sat_cons (step959 p h) (sat_cons (step952 p h) (sat_cons (step394 p h) (sat_cons (step323 p h) (sat_nil p))))))))))
def c1422 : List Lit := [(15, true), (45, true), (4, true), (1, false)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c520, c5] c1422 (by decide) p (sat_cons (step520 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1423 : List Lit := [(15, true), (1, false), (45, true), (2, true)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c520, c6] c1423 (by decide) p (sat_cons (step520 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1424 : List Lit := [(4, true), (1, false), (45, true), (2, true)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c520, c7] c1424 (by decide) p (sat_cons (step520 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1425 : List Lit := [(15, true), (1, false), (4, true), (2, true)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c520, c8] c1425 (by decide) p (sat_cons (step520 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1426 : List Lit := [(50, true), (3, false), (18, true)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c521, c13] c1426 (by decide) p (sat_cons (step521 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1427 : List Lit := [(11, true), (3, false), (50, true)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c521, c14] c1427 (by decide) p (sat_cons (step521 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1428 : List Lit := [(11, true), (18, true), (3, false)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c521, c15] c1428 (by decide) p (sat_cons (step521 p h) (sat_cons (step15 p h) (sat_nil p)))
def c1429 : List Lit := [(7, false), (6, true), (57, true)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c522, c25] c1429 (by decide) p (sat_cons (step522 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1430 : List Lit := [(7, false), (5, true), (57, true)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c522, c26] c1430 (by decide) p (sat_cons (step522 p h) (sat_cons (step26 p h) (sat_nil p)))
def c1431 : List Lit := [(7, false), (6, true), (5, true)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c522, c27] c1431 (by decide) p (sat_cons (step522 p h) (sat_cons (step27 p h) (sat_nil p)))
def c1432 : List Lit := [(10, true), (8, false), (58, true)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c523, c29] c1432 (by decide) p (sat_cons (step523 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1433 : List Lit := [(2, true), (58, true), (8, false)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c523, c30] c1433 (by decide) p (sat_cons (step523 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1434 : List Lit := [(10, true), (2, true), (8, false)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c523, c31] c1434 (by decide) p (sat_cons (step523 p h) (sat_cons (step31 p h) (sat_nil p)))
def c1435 : List Lit := [(9, false), (11, true)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c524, c32] c1435 (by decide) p (sat_cons (step524 p h) (sat_cons (step32 p h) (sat_nil p)))
def c1436 : List Lit := [(9, false), (10, true)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c524, c33] c1436 (by decide) p (sat_cons (step524 p h) (sat_cons (step33 p h) (sat_nil p)))
def c1437 : List Lit := [(12, true), (31, true), (13, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c525, c44] c1437 (by decide) p (sat_cons (step525 p h) (sat_cons (step44 p h) (sat_nil p)))
def c1438 : List Lit := [(31, true), (13, false), (6, true)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c525, c45] c1438 (by decide) p (sat_cons (step525 p h) (sat_cons (step45 p h) (sat_nil p)))
def c1439 : List Lit := [(12, true), (13, false), (6, true)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c525, c46] c1439 (by decide) p (sat_cons (step525 p h) (sat_cons (step46 p h) (sat_nil p)))
def c1440 : List Lit := [(14, false), (12, true)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c526, c47] c1440 (by decide) p (sat_cons (step526 p h) (sat_cons (step47 p h) (sat_nil p)))
def c1441 : List Lit := [(14, false), (11, true)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c526, c48] c1441 (by decide) p (sat_cons (step526 p h) (sat_cons (step48 p h) (sat_nil p)))
def c1442 : List Lit := [(16, false), (22, true), (18, true)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c527, c56] c1442 (by decide) p (sat_cons (step527 p h) (sat_cons (step56 p h) (sat_nil p)))
def c1443 : List Lit := [(16, false), (15, true), (18, true)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c527, c58] c1443 (by decide) p (sat_cons (step527 p h) (sat_cons (step58 p h) (sat_nil p)))
def c1444 : List Lit := [(19, false), (18, true), (89, true)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c528, c85] c1444 (by decide) p (sat_cons (step528 p h) (sat_cons (step85 p h) (sat_nil p)))
def c1445 : List Lit := [(27, true), (18, true), (19, false)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c528, c86] c1445 (by decide) p (sat_cons (step528 p h) (sat_cons (step86 p h) (sat_nil p)))
def c1446 : List Lit := [(24, false), (23, true), (18, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c529, c98] c1446 (by decide) p (sat_cons (step529 p h) (sat_cons (step98 p h) (sat_nil p)))
def c1447 : List Lit := [(24, false), (22, true), (18, true)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c529, c99] c1447 (by decide) p (sat_cons (step529 p h) (sat_cons (step99 p h) (sat_nil p)))
def c1448 : List Lit := [(26, false), (27, true), (31, true)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c530, c101] c1448 (by decide) p (sat_cons (step530 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1449 : List Lit := [(26, false), (25, true), (31, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c530, c102] c1449 (by decide) p (sat_cons (step530 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1450 : List Lit := [(27, true), (26, false), (25, true)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c530, c103] c1450 (by decide) p (sat_cons (step530 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1451 : List Lit := [(30, true), (28, false), (31, true)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c531, c108] c1451 (by decide) p (sat_cons (step531 p h) (sat_cons (step108 p h) (sat_nil p)))
def c1452 : List Lit := [(28, false), (21, true), (31, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c531, c109] c1452 (by decide) p (sat_cons (step531 p h) (sat_cons (step109 p h) (sat_nil p)))
def c1453 : List Lit := [(27, true), (32, false), (31, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c532, c125] c1453 (by decide) p (sat_cons (step532 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1454 : List Lit := [(37, true), (33, false), (18, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c533, c127] c1454 (by decide) p (sat_cons (step533 p h) (sat_cons (step127 p h) (sat_nil p)))
def c1455 : List Lit := [(34, false), (35, true)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c534, c128] c1455 (by decide) p (sat_cons (step534 p h) (sat_cons (step128 p h) (sat_nil p)))
def c1456 : List Lit := [(35, false), (40, true), (152, true)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c1275, c129] c1456 (by decide) p (sat_cons (step1275 p h) (sat_cons (step129 p h) (sat_nil p)))
def c1457 : List Lit := [(38, true), (41, false), (39, true)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c536, c139] c1457 (by decide) p (sat_cons (step536 p h) (sat_cons (step139 p h) (sat_nil p)))
def c1458 : List Lit := [(41, false), (37, true), (39, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c536, c140] c1458 (by decide) p (sat_cons (step536 p h) (sat_cons (step140 p h) (sat_nil p)))
def c1459 : List Lit := [(43, false), (33, true), (160, true)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c1276, c1277, c142] c1459 (by decide) p (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step142 p h) (sat_nil p))))
def c1460 : List Lit := [(47, false), (53, true), (50, true)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c539, c188] c1460 (by decide) p (sat_cons (step539 p h) (sat_cons (step188 p h) (sat_nil p)))
def c1461 : List Lit := [(47, false), (45, true), (53, true)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c539, c189] c1461 (by decide) p (sat_cons (step539 p h) (sat_cons (step189 p h) (sat_nil p)))
def c1462 : List Lit := [(47, false), (50, true), (45, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c539, c190] c1462 (by decide) p (sat_cons (step539 p h) (sat_cons (step190 p h) (sat_nil p)))
def c1463 : List Lit := [(48, false), (60, true), (45, true), (50, true), (55, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c540, c197] c1463 (by decide) p (sat_cons (step540 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1464 : List Lit := [(60, true), (55, true), (45, true), (48, false), (49, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c540, c198] c1464 (by decide) p (sat_cons (step540 p h) (sat_cons (step198 p h) (sat_nil p)))
end B112E203
