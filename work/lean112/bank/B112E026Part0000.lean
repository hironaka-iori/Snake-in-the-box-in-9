import B112E026Inputs
namespace B112E026
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1402 : List Lit := [(2, true)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true :=
  Snake9.LocalRup.prove_clause [c16, c15] c1402 (by decide) p (sat_cons (step16 p h) (sat_cons (step15 p h) (sat_nil p)))
def c1403 : List Lit := [(77, false)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true :=
  Snake9.LocalRup.prove_clause [c666, c284] c1403 (by decide) p (sat_cons (step666 p h) (sat_cons (step284 p h) (sat_nil p)))
def c1404 : List Lit := [(478, false)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c836, c833] c1404 (by decide) p (sat_cons (step836 p h) (sat_cons (step833 p h) (sat_nil p)))
def c1405 : List Lit := [(360, false)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.LocalRup.prove_clause [c836, c835] c1405 (by decide) p (sat_cons (step836 p h) (sat_cons (step835 p h) (sat_nil p)))
def c1406 : List Lit := [(476, false)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c1404, c829] c1406 (by decide) p (sat_cons (step1404 p h) (sat_cons (step829 p h) (sat_nil p)))
def c1407 : List Lit := [(418, false)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.LocalRup.prove_clause [c1404, c832] c1407 (by decide) p (sat_cons (step1404 p h) (sat_cons (step832 p h) (sat_nil p)))
def c1408 : List Lit := [(358, false)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c1405, c751] c1408 (by decide) p (sat_cons (step1405 p h) (sat_cons (step751 p h) (sat_nil p)))
def c1409 : List Lit := [(300, false)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c1405, c754] c1409 (by decide) p (sat_cons (step1405 p h) (sat_cons (step754 p h) (sat_nil p)))
def c1410 : List Lit := [(474, false)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c1406, c824] c1410 (by decide) p (sat_cons (step1406 p h) (sat_cons (step824 p h) (sat_nil p)))
def c1411 : List Lit := [(446, false)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c1406, c827] c1411 (by decide) p (sat_cons (step1406 p h) (sat_cons (step827 p h) (sat_nil p)))
def c1412 : List Lit := [(416, false)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c1407, c785] c1412 (by decide) p (sat_cons (step1407 p h) (sat_cons (step785 p h) (sat_nil p)))
def c1413 : List Lit := [(356, false)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c1408, c747] c1413 (by decide) p (sat_cons (step1408 p h) (sat_cons (step747 p h) (sat_nil p)))
def c1414 : List Lit := [(298, false)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c1409, c714] c1414 (by decide) p (sat_cons (step1409 p h) (sat_cons (step714 p h) (sat_nil p)))
def c1415 : List Lit := [(400, false)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c1412, c783] c1415 (by decide) p (sat_cons (step1412 p h) (sat_cons (step783 p h) (sat_nil p)))
def c1416 : List Lit := [(340, false)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c1413, c745] c1416 (by decide) p (sat_cons (step1413 p h) (sat_cons (step745 p h) (sat_nil p)))
def c1417 : List Lit := [(296, false)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c1414, c711] c1417 (by decide) p (sat_cons (step1414 p h) (sat_cons (step711 p h) (sat_nil p)))
def c1418 : List Lit := [(294, false)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c1417, c708] c1418 (by decide) p (sat_cons (step1417 p h) (sat_cons (step708 p h) (sat_nil p)))
def c1419 : List Lit := [(1615, true)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c1403, c1112] c1419 (by decide) p (sat_cons (step1403 p h) (sat_cons (step1112 p h) (sat_nil p)))
def c1420 : List Lit := [(79, true), (1616, true)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c1403, c1113] c1420 (by decide) p (sat_cons (step1403 p h) (sat_cons (step1113 p h) (sat_nil p)))
def c1421 : List Lit := [(1617, true)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c1419, c1114] c1421 (by decide) p (sat_cons (step1419 p h) (sat_cons (step1114 p h) (sat_nil p)))
def c1422 : List Lit := [(1613, false), (1618, true)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c1419, c1116] c1422 (by decide) p (sat_cons (step1419 p h) (sat_cons (step1116 p h) (sat_nil p)))
def c1423 : List Lit := [(1614, false), (1619, true)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c1419, c1118] c1423 (by decide) p (sat_cons (step1419 p h) (sat_cons (step1118 p h) (sat_nil p)))
def c1424 : List Lit := [(1629, true)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1134] c1424 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c1425 : List Lit := [(1625, false), (1630, true)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1135] c1425 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1135 p h) (sat_nil p)))
def c1426 : List Lit := [(1626, false), (1631, true)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1136] c1426 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1136 p h) (sat_nil p)))
def c1427 : List Lit := [(1627, false), (1632, true)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1137] c1427 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1137 p h) (sat_nil p)))
def c1428 : List Lit := [(1628, false), (1633, true)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1138] c1428 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1138 p h) (sat_nil p)))
def c1429 : List Lit := [(1605, false), (1638, true)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1157] c1429 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1157 p h) (sat_nil p)))
def c1430 : List Lit := [(1606, false), (1639, true)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1163] c1430 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1163 p h) (sat_nil p)))
def c1431 : List Lit := [(1607, false), (1640, true)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1170] c1431 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1170 p h) (sat_nil p)))
def c1432 : List Lit := [(1538, true)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c656, c991, c993, c988, c989, c986, c212, c213] c1432 (by decide) p (sat_cons (step656 p h) (sat_cons (step991 p h) (sat_cons (step993 p h) (sat_cons (step988 p h) (sat_cons (step989 p h) (sat_cons (step986 p h) (sat_cons (step212 p h) (sat_cons (step213 p h) (sat_nil p)))))))))
def c1433 : List Lit := [(1542, true)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c1432, c999] c1433 (by decide) p (sat_cons (step1432 p h) (sat_cons (step999 p h) (sat_nil p)))
def c1434 : List Lit := [(3, false), (1453, true)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c1402, c16, c2, c3, c842, c845, c850] c1434 (by decide) p (sat_cons (step1402 p h) (sat_cons (step16 p h) (sat_cons (step2 p h) (sat_cons (step3 p h) (sat_cons (step842 p h) (sat_cons (step845 p h) (sat_cons (step850 p h) (sat_nil p))))))))
def c1435 : List Lit := [(1457, true)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c633, c855, c862, c1434, c837, c838, c840, c858, c847, c844, c25, c26, c1357] c1435 (by decide) p (sat_cons (step633 p h) (sat_cons (step855 p h) (sat_cons (step862 p h) (sat_cons (step1434 p h) (sat_cons (step837 p h) (sat_cons (step838 p h) (sat_cons (step840 p h) (sat_cons (step858 p h) (sat_cons (step847 p h) (sat_cons (step844 p h) (sat_cons (step25 p h) (sat_cons (step26 p h) (sat_cons (step1357 p h) (sat_nil p))))))))))))))
def c1436 : List Lit := [(1510, true), (1530, true)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c649, c650, c646, c979, c972, c171, c971, c977, c975, c944, c945, c178, c173, c182, c149, c150, c1370] c1436 (by decide) p (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step646 p h) (sat_cons (step979 p h) (sat_cons (step972 p h) (sat_cons (step171 p h) (sat_cons (step971 p h) (sat_cons (step977 p h) (sat_cons (step975 p h) (sat_cons (step944 p h) (sat_cons (step945 p h) (sat_cons (step178 p h) (sat_cons (step173 p h) (sat_cons (step182 p h) (sat_cons (step149 p h) (sat_cons (step150 p h) (sat_cons (step1370 p h) (sat_nil p))))))))))))))))))
def c1437 : List Lit := [(1481, true), (1465, false), (1471, false), (17, false), (36, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c871, c887, c901, c898, c874, c888, c865, c882, c65] c1437 (by decide) p (sat_cons (step871 p h) (sat_cons (step887 p h) (sat_cons (step901 p h) (sat_cons (step898 p h) (sat_cons (step874 p h) (sat_cons (step888 p h) (sat_cons (step865 p h) (sat_cons (step882 p h) (sat_cons (step65 p h) (sat_nil p))))))))))
def c1438 : List Lit := [(13, true), (1465, false), (1481, true), (22, false), (17, true)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c641, c905, c877, c866, c867, c874, c901, c885, c882, c94, c106] c1438 (by decide) p (sat_cons (step641 p h) (sat_cons (step905 p h) (sat_cons (step877 p h) (sat_cons (step866 p h) (sat_cons (step867 p h) (sat_cons (step874 p h) (sat_cons (step901 p h) (sat_cons (step885 p h) (sat_cons (step882 p h) (sat_cons (step94 p h) (sat_cons (step106 p h) (sat_nil p))))))))))))
def c1439 : List Lit := [(1473, true), (22, false), (17, true)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c641, c882, c883, c106, c96] c1439 (by decide) p (sat_cons (step641 p h) (sat_cons (step882 p h) (sat_cons (step883 p h) (sat_cons (step106 p h) (sat_cons (step96 p h) (sat_nil p))))))
def c1440 : List Lit := [(26, false), (14, false), (22, false), (17, true)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c641, c94, c106] c1440 (by decide) p (sat_cons (step641 p h) (sat_cons (step94 p h) (sat_cons (step106 p h) (sat_nil p))))
def c1441 : List Lit := [(1465, false), (1481, true), (22, false), (17, true)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c640, c1439, c885, c901, c871, c898, c886, c1438, c874, c865, c1440, c884, c93, c88, c103, c48] c1441 (by decide) p (sat_cons (step640 p h) (sat_cons (step1439 p h) (sat_cons (step885 p h) (sat_cons (step901 p h) (sat_cons (step871 p h) (sat_cons (step898 p h) (sat_cons (step886 p h) (sat_cons (step1438 p h) (sat_cons (step874 p h) (sat_cons (step865 p h) (sat_cons (step1440 p h) (sat_cons (step884 p h) (sat_cons (step93 p h) (sat_cons (step88 p h) (sat_cons (step103 p h) (sat_cons (step48 p h) (sat_nil p)))))))))))))))))
def c1442 : List Lit := [(1452, true)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c1402, c16, c847, c849, c845, c842, c4] c1442 (by decide) p (sat_cons (step1402 p h) (sat_cons (step16 p h) (sat_cons (step847 p h) (sat_cons (step849 p h) (sat_cons (step845 p h) (sat_cons (step842 p h) (sat_cons (step4 p h) (sat_nil p))))))))
def c1443 : List Lit := [(1689, true), (116, false), (41, false)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c1250, c1252, c1247, c1244, c610] c1443 (by decide) p (sat_cons (step1250 p h) (sat_cons (step1252 p h) (sat_cons (step1247 p h) (sat_cons (step1244 p h) (sat_cons (step610 p h) (sat_nil p))))))
def c1444 : List Lit := [(1666, true), (95, false), (25, false), (99, true)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c1193, c1204, c1202, c1195, c1197, c501] c1444 (by decide) p (sat_cons (step1193 p h) (sat_cons (step1204 p h) (sat_cons (step1202 p h) (sat_cons (step1195 p h) (sat_cons (step1197 p h) (sat_cons (step501 p h) (sat_nil p)))))))
def c1445 : List Lit := [(8, true), (1453, true)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c1402, c16, c852, c841, c843, c850, c4, c845] c1445 (by decide) p (sat_cons (step1402 p h) (sat_cons (step16 p h) (sat_cons (step852 p h) (sat_cons (step841 p h) (sat_cons (step843 p h) (sat_cons (step850 p h) (sat_cons (step4 p h) (sat_cons (step845 p h) (sat_nil p)))))))))
def c1446 : List Lit := [(11, true), (1453, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c1402, c16, c848, c844, c846, c850, c4, c842] c1446 (by decide) p (sat_cons (step1402 p h) (sat_cons (step16 p h) (sat_cons (step848 p h) (sat_cons (step844 p h) (sat_cons (step846 p h) (sat_cons (step850 p h) (sat_cons (step4 p h) (sat_cons (step842 p h) (sat_nil p)))))))))
def c1447 : List Lit := [(1502, true), (20, false), (19, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c638, c930, c931, c80, c121, c77] c1447 (by decide) p (sat_cons (step638 p h) (sat_cons (step930 p h) (sat_cons (step931 p h) (sat_cons (step80 p h) (sat_cons (step121 p h) (sat_cons (step77 p h) (sat_nil p)))))))
def c1448 : List Lit := [(1514, true), (41, false)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c647, c950, c952, c948, c945, c162, c141] c1448 (by decide) p (sat_cons (step647 p h) (sat_cons (step950 p h) (sat_cons (step952 p h) (sat_cons (step948 p h) (sat_cons (step945 p h) (sat_cons (step162 p h) (sat_cons (step141 p h) (sat_nil p))))))))
def c1449 : List Lit := [(37, true), (36, true), (1516, true), (161, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c647, c946, c165, c956, c161, c948] c1449 (by decide) p (sat_cons (step647 p h) (sat_cons (step946 p h) (sat_cons (step165 p h) (sat_cons (step956 p h) (sat_cons (step161 p h) (sat_cons (step948 p h) (sat_nil p)))))))
def c1450 : List Lit := [(39, false), (41, false), (35, false)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c647, c162, c140] c1450 (by decide) p (sat_cons (step647 p h) (sat_cons (step162 p h) (sat_cons (step140 p h) (sat_nil p))))
def c1451 : List Lit := [(1458, true), (1443, false)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c1442, c632, c838, c859, c863, c1445, c1446, c840, c20, c10] c1451 (by decide) p (sat_cons (step1442 p h) (sat_cons (step632 p h) (sat_cons (step838 p h) (sat_cons (step859 p h) (sat_cons (step863 p h) (sat_cons (step1445 p h) (sat_cons (step1446 p h) (sat_cons (step840 p h) (sat_cons (step20 p h) (sat_cons (step10 p h) (sat_nil p)))))))))))
def c1452 : List Lit := [(25, true), (36, false), (14, false), (1476, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c886, c883, c888, c884, c879, c65, c1440] c1452 (by decide) p (sat_cons (step886 p h) (sat_cons (step883 p h) (sat_cons (step888 p h) (sat_cons (step884 p h) (sat_cons (step879 p h) (sat_cons (step65 p h) (sat_cons (step1440 p h) (sat_nil p))))))))
def c1453 : List Lit := [(1689, true), (101, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c684, c1250, c1252, c1247, c1248, c1244, c1245, c629, c602, c620] c1453 (by decide) p (sat_cons (step684 p h) (sat_cons (step1250 p h) (sat_cons (step1252 p h) (sat_cons (step1247 p h) (sat_cons (step1248 p h) (sat_cons (step1244 p h) (sat_cons (step1245 p h) (sat_cons (step629 p h) (sat_cons (step602 p h) (sat_cons (step620 p h) (sat_nil p)))))))))))
def c1454 : List Lit := [(1659, false), (1708, true), (1689, false), (102, true), (110, false), (111, false), (108, true), (1661, false)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c681, c1231, c1239, c1258, c1298, c1197, c1202, c1223, c1224, c1293, c1203, c1262, c1198, c1242, c585, c1233, c593, c597] c1454 (by decide) p (sat_cons (step681 p h) (sat_cons (step1231 p h) (sat_cons (step1239 p h) (sat_cons (step1258 p h) (sat_cons (step1298 p h) (sat_cons (step1197 p h) (sat_cons (step1202 p h) (sat_cons (step1223 p h) (sat_cons (step1224 p h) (sat_cons (step1293 p h) (sat_cons (step1203 p h) (sat_cons (step1262 p h) (sat_cons (step1198 p h) (sat_cons (step1242 p h) (sat_cons (step585 p h) (sat_cons (step1233 p h) (sat_cons (step593 p h) (sat_cons (step597 p h) (sat_nil p)))))))))))))))))))
def c1455 : List Lit := [(1613, false), (1643, true), (78, true), (110, false), (1628, false)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c667, c1156, c1147, c1422, c1117, c1143, c1420, c1162, c289, c1097, c271, c1093, c1086] c1455 (by decide) p (sat_cons (step667 p h) (sat_cons (step1156 p h) (sat_cons (step1147 p h) (sat_cons (step1422 p h) (sat_cons (step1117 p h) (sat_cons (step1143 p h) (sat_cons (step1420 p h) (sat_cons (step1162 p h) (sat_cons (step289 p h) (sat_cons (step1097 p h) (sat_cons (step271 p h) (sat_cons (step1093 p h) (sat_cons (step1086 p h) (sat_nil p))))))))))))))
def c1456 : List Lit := [(1643, true), (78, true), (201, true), (110, false), (1628, false)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c665, c667, c1428, c1167, c1098, c1096, c1455, c1109, c1110, c282, c283, c290, c279, c289, c1087, c271] c1456 (by decide) p (sat_cons (step665 p h) (sat_cons (step667 p h) (sat_cons (step1428 p h) (sat_cons (step1167 p h) (sat_cons (step1098 p h) (sat_cons (step1096 p h) (sat_cons (step1455 p h) (sat_cons (step1109 p h) (sat_cons (step1110 p h) (sat_cons (step282 p h) (sat_cons (step283 p h) (sat_cons (step290 p h) (sat_cons (step279 p h) (sat_cons (step289 p h) (sat_cons (step1087 p h) (sat_cons (step271 p h) (sat_nil p)))))))))))))))))
def c1457 : List Lit := [(69, false), (74, false)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c662, c260, c261, c1380] c1457 (by decide) p (sat_cons (step662 p h) (sat_cons (step260 p h) (sat_cons (step261 p h) (sat_cons (step1380 p h) (sat_nil p)))))
def c1458 : List Lit := [(74, false), (1606, true), (63, false), (51, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c659, c1457, c1085, c1093, c1101, c1078, c1080, c1076, c1072, c1073, c242, c249, c229] c1458 (by decide) p (sat_cons (step659 p h) (sat_cons (step1457 p h) (sat_cons (step1085 p h) (sat_cons (step1093 p h) (sat_cons (step1101 p h) (sat_cons (step1078 p h) (sat_cons (step1080 p h) (sat_cons (step1076 p h) (sat_cons (step1072 p h) (sat_cons (step1073 p h) (sat_cons (step242 p h) (sat_cons (step249 p h) (sat_cons (step229 p h) (sat_nil p))))))))))))))
def c1459 : List Lit := [(1514, true)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c950, c1448, c947] c1459 (by decide) p (sat_cons (step950 p h) (sat_cons (step1448 p h) (sat_cons (step947 p h) (sat_nil p))))
def c1460 : List Lit := [(1518, true)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c1459, c958] c1460 (by decide) p (sat_cons (step1459 p h) (sat_cons (step958 p h) (sat_nil p)))
def c1461 : List Lit := [(21, true), (90, true), (33, false), (19, false)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c637, c76, c74, c1363] c1461 (by decide) p (sat_cons (step637 p h) (sat_cons (step76 p h) (sat_cons (step74 p h) (sat_cons (step1363 p h) (sat_nil p)))))
def c1462 : List Lit := [(99, false), (170, true), (1593, true), (88, false), (18, false)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c657, c658, c1080, c1072, c1073, c1078, c1076, c229, c234, c223, c1075, c238, c221, c395, c399, c194] c1462 (by decide) p (sat_cons (step657 p h) (sat_cons (step658 p h) (sat_cons (step1080 p h) (sat_cons (step1072 p h) (sat_cons (step1073 p h) (sat_cons (step1078 p h) (sat_cons (step1076 p h) (sat_cons (step229 p h) (sat_cons (step234 p h) (sat_cons (step223 p h) (sat_cons (step1075 p h) (sat_cons (step238 p h) (sat_cons (step221 p h) (sat_cons (step395 p h) (sat_cons (step399 p h) (sat_cons (step194 p h) (sat_nil p)))))))))))))))))
def c1463 : List Lit := [(1689, true), (99, true), (222, true), (1593, true), (89, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c658, c1080, c1072, c1078, c1076, c1073, c229, c232, c1252, c1453, c1245, c545, c509] c1463 (by decide) p (sat_cons (step658 p h) (sat_cons (step1080 p h) (sat_cons (step1072 p h) (sat_cons (step1078 p h) (sat_cons (step1076 p h) (sat_cons (step1073 p h) (sat_cons (step229 p h) (sat_cons (step232 p h) (sat_cons (step1252 p h) (sat_cons (step1453 p h) (sat_cons (step1245 p h) (sat_cons (step545 p h) (sat_cons (step509 p h) (sat_nil p))))))))))))))
def c1464 : List Lit := [(91, false), (170, true), (1593, true), (88, false), (18, false)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c657, c658, c1080, c1072, c1073, c1078, c1076, c229, c234, c223, c1075, c238, c221, c394, c398, c194] c1464 (by decide) p (sat_cons (step657 p h) (sat_cons (step658 p h) (sat_cons (step1080 p h) (sat_cons (step1072 p h) (sat_cons (step1073 p h) (sat_cons (step1078 p h) (sat_cons (step1076 p h) (sat_cons (step229 p h) (sat_cons (step234 p h) (sat_cons (step223 p h) (sat_cons (step1075 p h) (sat_cons (step238 p h) (sat_cons (step221 p h) (sat_cons (step394 p h) (sat_cons (step398 p h) (sat_cons (step194 p h) (sat_nil p)))))))))))))))))
def c1465 : List Lit := [(9, true), (73, false), (70, false), (67, false)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c661, c256, c257, c262] c1465 (by decide) p (sat_cons (step661 p h) (sat_cons (step256 p h) (sat_cons (step257 p h) (sat_cons (step262 p h) (sat_nil p)))))
end B112E026
