import B112E186Inputs
namespace B112E186
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1400 : List Lit := [(7, true)]
theorem step1400 (p : Nat → Bool) (h : Constraints p) : clause p c1400 = true :=
  Snake9.LocalRup.prove_clause [c12, c11] c1400 (by decide) p (sat_cons (step12 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1401 : List Lit := [(1, false), (8, false)]
theorem step1401 (p : Nat → Bool) (h : Constraints p) : clause p c1401 = true :=
  Snake9.LocalRup.prove_clause [c1400, c12, c13] c1401 (by decide) p (sat_cons (step1400 p h) (sat_cons (step12 p h) (sat_cons (step13 p h) (sat_nil p))))
def c1402 : List Lit := [(131, false), (1, false)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true :=
  Snake9.LocalRup.prove_clause [c12, c14] c1402 (by decide) p (sat_cons (step12 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1403 : List Lit := [(131, false), (8, false)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true :=
  Snake9.LocalRup.prove_clause [c12, c15] c1403 (by decide) p (sat_cons (step12 p h) (sat_cons (step15 p h) (sat_nil p)))
def c1404 : List Lit := [(131, true), (1, true), (8, true)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c1400, c16] c1404 (by decide) p (sat_cons (step1400 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1405 : List Lit := [(5, false)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.LocalRup.prove_clause [c657, c10] c1405 (by decide) p (sat_cons (step657 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1406 : List Lit := [(490, false)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c822, c819] c1406 (by decide) p (sat_cons (step822 p h) (sat_cons (step819 p h) (sat_nil p)))
def c1407 : List Lit := [(368, false)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.LocalRup.prove_clause [c822, c821] c1407 (by decide) p (sat_cons (step822 p h) (sat_cons (step821 p h) (sat_nil p)))
def c1408 : List Lit := [(428, false)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c1406, c818] c1408 (by decide) p (sat_cons (step1406 p h) (sat_cons (step818 p h) (sat_nil p)))
def c1409 : List Lit := [(366, false)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c1407, c766] c1409 (by decide) p (sat_cons (step1407 p h) (sat_cons (step766 p h) (sat_nil p)))
def c1410 : List Lit := [(306, false)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c1407, c769] c1410 (by decide) p (sat_cons (step1407 p h) (sat_cons (step769 p h) (sat_nil p)))
def c1411 : List Lit := [(396, false)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c1408, c800] c1411 (by decide) p (sat_cons (step1408 p h) (sat_cons (step800 p h) (sat_nil p)))
def c1412 : List Lit := [(334, false)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c1409, c764] c1412 (by decide) p (sat_cons (step1409 p h) (sat_cons (step764 p h) (sat_nil p)))
def c1413 : List Lit := [(304, false)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c1410, c739] c1413 (by decide) p (sat_cons (step1410 p h) (sat_cons (step739 p h) (sat_nil p)))
def c1414 : List Lit := [(394, false)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c1411, c784] c1414 (by decide) p (sat_cons (step1411 p h) (sat_cons (step784 p h) (sat_nil p)))
def c1415 : List Lit := [(332, false)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c1412, c755] c1415 (by decide) p (sat_cons (step1412 p h) (sat_cons (step755 p h) (sat_nil p)))
def c1416 : List Lit := [(302, false)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c1413, c735] c1416 (by decide) p (sat_cons (step1413 p h) (sat_cons (step735 p h) (sat_nil p)))
def c1417 : List Lit := [(386, false)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c1414, c782] c1417 (by decide) p (sat_cons (step1414 p h) (sat_cons (step782 p h) (sat_nil p)))
def c1418 : List Lit := [(384, false)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c1417, c777] c1418 (by decide) p (sat_cons (step1417 p h) (sat_cons (step777 p h) (sat_nil p)))
def c1419 : List Lit := [(1497, true)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c1405, c823] c1419 (by decide) p (sat_cons (step1405 p h) (sat_cons (step823 p h) (sat_nil p)))
def c1420 : List Lit := [(3, true), (1498, true)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c1405, c824] c1420 (by decide) p (sat_cons (step1405 p h) (sat_cons (step824 p h) (sat_nil p)))
def c1421 : List Lit := [(1499, true)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c1419, c825] c1421 (by decide) p (sat_cons (step1419 p h) (sat_cons (step825 p h) (sat_nil p)))
def c1422 : List Lit := [(1, true), (1500, true)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c1419, c827] c1422 (by decide) p (sat_cons (step1419 p h) (sat_cons (step827 p h) (sat_nil p)))
def c1423 : List Lit := [(1506, false), (1511, true)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c1421, c838] c1423 (by decide) p (sat_cons (step1421 p h) (sat_cons (step838 p h) (sat_nil p)))
def c1424 : List Lit := [(1507, false), (1512, true)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c1421, c839] c1424 (by decide) p (sat_cons (step1421 p h) (sat_cons (step839 p h) (sat_nil p)))
def c1425 : List Lit := [(1508, false), (1513, true)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c1421, c840] c1425 (by decide) p (sat_cons (step1421 p h) (sat_cons (step840 p h) (sat_nil p)))
def c1426 : List Lit := [(1511, true)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c1423, c841, c835, c1422, c829, c1401] c1426 (by decide) p (sat_cons (step1423 p h) (sat_cons (step841 p h) (sat_cons (step835 p h) (sat_cons (step1422 p h) (sat_cons (step829 p h) (sat_cons (step1401 p h) (sat_nil p)))))))
def c1427 : List Lit := [(1596, true)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c682, c975, c978, c968, c954, c965, c966, c952, c201, c199] c1427 (by decide) p (sat_cons (step682 p h) (sat_cons (step975 p h) (sat_cons (step978 p h) (sat_cons (step968 p h) (sat_cons (step954 p h) (sat_cons (step965 p h) (sat_cons (step966 p h) (sat_cons (step952 p h) (sat_cons (step201 p h) (sat_cons (step199 p h) (sat_nil p)))))))))))
def c1428 : List Lit := [(42, false), (43, false), (41, false)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c674, c143, c145] c1428 (by decide) p (sat_cons (step674 p h) (sat_cons (step143 p h) (sat_cons (step145 p h) (sat_nil p))))
def c1429 : List Lit := [(1568, true)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c926, c928, c923, c924, c920, c1428] c1429 (by decide) p (sat_cons (step926 p h) (sat_cons (step928 p h) (sat_cons (step923 p h) (sat_cons (step924 p h) (sat_cons (step920 p h) (sat_cons (step1428 p h) (sat_nil p)))))))
def c1430 : List Lit := [(1572, true)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c1429, c933] c1430 (by decide) p (sat_cons (step1429 p h) (sat_cons (step933 p h) (sat_nil p)))
def c1431 : List Lit := [(1597, true), (1580, false)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c682, c956, c982, c979, c957, c968, c952, c965, c966, c201, c199] c1431 (by decide) p (sat_cons (step682 p h) (sat_cons (step956 p h) (sat_cons (step982 p h) (sat_cons (step979 p h) (sat_cons (step957 p h) (sat_cons (step968 p h) (sat_cons (step952 p h) (sat_cons (step965 p h) (sat_cons (step966 p h) (sat_cons (step201 p h) (sat_cons (step199 p h) (sat_nil p))))))))))))
def c1432 : List Lit := [(1525, true), (24, false), (42, false)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c862, c863, c70] c1432 (by decide) p (sat_cons (step862 p h) (sat_cons (step863 p h) (sat_cons (step70 p h) (sat_nil p))))
def c1433 : List Lit := [(1560, true), (37, false)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c673, c912, c914, c909, c910, c906, c907, c124, c139, c102, c137] c1433 (by decide) p (sat_cons (step673 p h) (sat_cons (step912 p h) (sat_cons (step914 p h) (sat_cons (step909 p h) (sat_cons (step910 p h) (sat_cons (step906 p h) (sat_cons (step907 p h) (sat_cons (step124 p h) (sat_cons (step139 p h) (sat_cons (step102 p h) (sat_cons (step137 p h) (sat_nil p))))))))))))
def c1434 : List Lit := [(1556, true), (36, false), (37, false)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c670, c906, c907, c139, c102, c106] c1434 (by decide) p (sat_cons (step670 p h) (sat_cons (step906 p h) (sat_cons (step907 p h) (sat_cons (step139 p h) (sat_cons (step102 p h) (sat_cons (step106 p h) (sat_nil p)))))))
def c1435 : List Lit := [(1513, true), (13, true), (1, true), (4, false), (36, false)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c830, c833, c1422, c843, c846, c834, c828, c832, c1420, c6] c1435 (by decide) p (sat_cons (step830 p h) (sat_cons (step833 p h) (sat_cons (step1422 p h) (sat_cons (step843 p h) (sat_cons (step846 p h) (sat_cons (step834 p h) (sat_cons (step828 p h) (sat_cons (step832 p h) (sat_cons (step1420 p h) (sat_cons (step6 p h) (sat_nil p)))))))))))
def c1436 : List Lit := [(19, false), (54, false), (14, true), (144, true), (17, true)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c664, c55, c56, c405, c62] c1436 (by decide) p (sat_cons (step664 p h) (sat_cons (step55 p h) (sat_cons (step56 p h) (sat_cons (step405 p h) (sat_cons (step62 p h) (sat_nil p))))))
def c1437 : List Lit := [(1680, false), (1695, true), (1669, false), (1651, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c691, c1075, c1081, c1154, c1104, c1133, c1128, c1107, c1160, c1099, c1082, c1086, c275, c1076, c1059, c1070, c1056, c269] c1437 (by decide) p (sat_cons (step691 p h) (sat_cons (step1075 p h) (sat_cons (step1081 p h) (sat_cons (step1154 p h) (sat_cons (step1104 p h) (sat_cons (step1133 p h) (sat_cons (step1128 p h) (sat_cons (step1107 p h) (sat_cons (step1160 p h) (sat_cons (step1099 p h) (sat_cons (step1082 p h) (sat_cons (step1086 p h) (sat_cons (step275 p h) (sat_cons (step1076 p h) (sat_cons (step1059 p h) (sat_cons (step1070 p h) (sat_cons (step1056 p h) (sat_cons (step269 p h) (sat_nil p)))))))))))))))))))
def c1438 : List Lit := [(26, false), (27, true), (102, true), (1717, false), (1726, true)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c667, c1196, c1205, c1217, c76, c78, c1357, c1183, c1190, c1191, c1213, c1185, c1208, c472, c1198] c1438 (by decide) p (sat_cons (step667 p h) (sat_cons (step1196 p h) (sat_cons (step1205 p h) (sat_cons (step1217 p h) (sat_cons (step76 p h) (sat_cons (step78 p h) (sat_cons (step1357 p h) (sat_cons (step1183 p h) (sat_cons (step1190 p h) (sat_cons (step1191 p h) (sat_cons (step1213 p h) (sat_cons (step1185 p h) (sat_cons (step1208 p h) (sat_cons (step472 p h) (sat_cons (step1198 p h) (sat_nil p))))))))))))))))
def c1439 : List Lit := [(1709, true), (1707, true)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c697, c1183, c1182, c1185, c1186, c451, c458, c462] c1439 (by decide) p (sat_cons (step697 p h) (sat_cons (step1183 p h) (sat_cons (step1182 p h) (sat_cons (step1185 p h) (sat_cons (step1186 p h) (sat_cons (step451 p h) (sat_cons (step458 p h) (sat_cons (step462 p h) (sat_nil p)))))))))
def c1440 : List Lit := [(1711, true)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c1188, c1190, c1439] c1440 (by decide) p (sat_cons (step1188 p h) (sat_cons (step1190 p h) (sat_cons (step1439 p h) (sat_nil p))))
def c1441 : List Lit := [(1723, true)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c1440, c1210] c1441 (by decide) p (sat_cons (step1440 p h) (sat_cons (step1210 p h) (sat_nil p)))
def c1442 : List Lit := [(97, false), (96, true), (94, false), (100, false)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c697, c451, c462] c1442 (by decide) p (sat_cons (step697 p h) (sat_cons (step451 p h) (sat_cons (step462 p h) (sat_nil p))))
def c1443 : List Lit := [(1749, true), (122, true), (113, true)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c706, c1246, c1248, c1232, c1234, c1262, c1265, c1249, c1251, c1235, c1237, c1247, c1242, c1243, c1233, c1229, c629, c563, c627] c1443 (by decide) p (sat_cons (step706 p h) (sat_cons (step1246 p h) (sat_cons (step1248 p h) (sat_cons (step1232 p h) (sat_cons (step1234 p h) (sat_cons (step1262 p h) (sat_cons (step1265 p h) (sat_cons (step1249 p h) (sat_cons (step1251 p h) (sat_cons (step1235 p h) (sat_cons (step1237 p h) (sat_cons (step1247 p h) (sat_cons (step1242 p h) (sat_cons (step1243 p h) (sat_cons (step1233 p h) (sat_cons (step1229 p h) (sat_cons (step629 p h) (sat_cons (step563 p h) (sat_cons (step627 p h) (sat_nil p))))))))))))))))))))
def c1444 : List Lit := [(1744, true), (109, false), (114, false), (122, true)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c706, c1246, c1249, c1251, c1247, c1242, c1243, c629, c563, c627] c1444 (by decide) p (sat_cons (step706 p h) (sat_cons (step1246 p h) (sat_cons (step1249 p h) (sat_cons (step1251 p h) (sat_cons (step1247 p h) (sat_cons (step1242 p h) (sat_cons (step1243 p h) (sat_cons (step629 p h) (sat_cons (step563 p h) (sat_cons (step627 p h) (sat_nil p)))))))))))
def c1445 : List Lit := [(1739, true), (123, false), (109, false), (114, false)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c706, c1242, c1243, c629, c563, c627] c1445 (by decide) p (sat_cons (step706 p h) (sat_cons (step1242 p h) (sat_cons (step1243 p h) (sat_cons (step629 p h) (sat_cons (step563 p h) (sat_cons (step627 p h) (sat_nil p)))))))
def c1446 : List Lit := [(105, false), (1731, true), (114, false), (90, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c705, c1229, c1228, c560, c598, c620] c1446 (by decide) p (sat_cons (step705 p h) (sat_cons (step1229 p h) (sat_cons (step1228 p h) (sat_cons (step560 p h) (sat_cons (step598 p h) (sat_cons (step620 p h) (sat_nil p)))))))
def c1447 : List Lit := [(119, false), (123, false), (107, false), (109, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c707, c580, c633, c634, c1398] c1447 (by decide) p (sat_cons (step707 p h) (sat_cons (step580 p h) (sat_cons (step633 p h) (sat_cons (step634 p h) (sat_cons (step1398 p h) (sat_nil p))))))
def c1448 : List Lit := [(36, false), (18, false), (28, false), (1522, true)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c53, c52, c852, c848, c857] c1448 (by decide) p (sat_cons (step53 p h) (sat_cons (step52 p h) (sat_cons (step852 p h) (sat_cons (step848 p h) (sat_cons (step857 p h) (sat_nil p))))))
def c1449 : List Lit := [(1504, false), (1512, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c1424, c833, c836, c842, c829, c1422, c1401] c1449 (by decide) p (sat_cons (step1424 p h) (sat_cons (step833 p h) (sat_cons (step836 p h) (sat_cons (step842 p h) (sat_cons (step829 p h) (sat_cons (step1422 p h) (sat_cons (step1401 p h) (sat_nil p))))))))
def c1450 : List Lit := [(28, false), (1522, true), (27, true), (13, false)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c668, c86, c47, c45, c852, c848, c857] c1450 (by decide) p (sat_cons (step668 p h) (sat_cons (step86 p h) (sat_cons (step47 p h) (sat_cons (step45 p h) (sat_cons (step852 p h) (sat_cons (step848 p h) (sat_cons (step857 p h) (sat_nil p))))))))
def c1451 : List Lit := [(37, false), (1557, true), (32, false), (15, false)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c101, c100, c908] c1451 (by decide) p (sat_cons (step101 p h) (sat_cons (step100 p h) (sat_cons (step908 p h) (sat_nil p))))
def c1452 : List Lit := [(1556, true), (32, false), (15, false)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c906, c907, c99] c1452 (by decide) p (sat_cons (step906 p h) (sat_cons (step907 p h) (sat_cons (step99 p h) (sat_nil p))))
def c1453 : List Lit := [(107, false), (1676, true), (110, false), (85, false), (13, false)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c328, c1381, c1114] c1453 (by decide) p (sat_cons (step328 p h) (sat_cons (step1381 p h) (sat_cons (step1114 p h) (sat_nil p))))
def c1454 : List Lit := [(1707, true), (101, false), (100, false)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c697, c1182, c1183, c459, c451, c462] c1454 (by decide) p (sat_cons (step697 p h) (sat_cons (step1182 p h) (sat_cons (step1183 p h) (sat_cons (step459 p h) (sat_cons (step451 p h) (sat_cons (step462 p h) (sat_nil p)))))))
def c1455 : List Lit := [(84, true), (81, true), (1687, true), (1676, true), (1678, false), (85, false), (13, false)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c1113, c1114, c1122, c323, c1134, c1103, c1105] c1455 (by decide) p (sat_cons (step1113 p h) (sat_cons (step1114 p h) (sat_cons (step1122 p h) (sat_cons (step323 p h) (sat_cons (step1134 p h) (sat_cons (step1103 p h) (sat_cons (step1105 p h) (sat_nil p))))))))
def c1456 : List Lit := [(81, true), (1687, true), (13, false), (1676, true), (1678, false), (85, false)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c1455, c326, c322, c1112, c1103, c1122, c1105, c1134] c1456 (by decide) p (sat_cons (step1455 p h) (sat_cons (step326 p h) (sat_cons (step322 p h) (sat_cons (step1112 p h) (sat_cons (step1103 p h) (sat_cons (step1122 p h) (sat_cons (step1105 p h) (sat_cons (step1134 p h) (sat_nil p)))))))))
def c1457 : List Lit := [(1525, true), (29, true)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c666, c862, c74, c73, c1358, c863] c1457 (by decide) p (sat_cons (step666 p h) (sat_cons (step862 p h) (sat_cons (step74 p h) (sat_cons (step73 p h) (sat_cons (step1358 p h) (sat_cons (step863 p h) (sat_nil p)))))))
def c1458 : List Lit := [(83, false), (1676, true), (85, false), (13, false)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c322, c323, c1114] c1458 (by decide) p (sat_cons (step322 p h) (sat_cons (step323 p h) (sat_cons (step1114 p h) (sat_nil p))))
def c1459 : List Lit := [(48, false), (1676, true), (85, false), (13, false)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c319, c318, c1114] c1459 (by decide) p (sat_cons (step319 p h) (sat_cons (step318 p h) (sat_cons (step1114 p h) (sat_nil p))))
def c1460 : List Lit := [(1575, false), (1687, false), (70, true), (1760, false), (1544, false), (1580, false)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c1350, c685, c678, c1067, c1075, c1081, c1155, c1319, c1345, c1025, c1431, c1003, c1004, c1024, c985, c1344, c958, c1326, c1162, c1082, c1086, c1078, c1076, c1059, c1061, c1069, c1070, c1071, c1056, c1057, c1053, c1054, c241, c217, c223, c251, c952, c953, c957, c208, c983, c175, c970, c187, c963] c1460 (by decide) p (sat_cons (step1350 p h) (sat_cons (step685 p h) (sat_cons (step678 p h) (sat_cons (step1067 p h) (sat_cons (step1075 p h) (sat_cons (step1081 p h) (sat_cons (step1155 p h) (sat_cons (step1319 p h) (sat_cons (step1345 p h) (sat_cons (step1025 p h) (sat_cons (step1431 p h) (sat_cons (step1003 p h) (sat_cons (step1004 p h) (sat_cons (step1024 p h) (sat_cons (step985 p h) (sat_cons (step1344 p h) (sat_cons (step958 p h) (sat_cons (step1326 p h) (sat_cons (step1162 p h) (sat_cons (step1082 p h) (sat_cons (step1086 p h) (sat_cons (step1078 p h) (sat_cons (step1076 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1069 p h) (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1053 p h) (sat_cons (step1054 p h) (sat_cons (step241 p h) (sat_cons (step217 p h) (sat_cons (step223 p h) (sat_cons (step251 p h) (sat_cons (step952 p h) (sat_cons (step953 p h) (sat_cons (step957 p h) (sat_cons (step208 p h) (sat_cons (step983 p h) (sat_cons (step175 p h) (sat_cons (step970 p h) (sat_cons (step187 p h) (sat_cons (step963 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c1461 : List Lit := [(1675, true), (85, false), (13, false)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c1112, c1113, c326] c1461 (by decide) p (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step326 p h) (sat_nil p))))
def c1462 : List Lit := [(81, true), (1651, false), (1697, true), (1676, true), (83, true), (1678, false), (85, false), (13, false)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c691, c1461, c1122, c1075, c1081, c1156, c1139, c1456, c1103, c1162, c1108, c1082, c1086, c1099, c1076, c1059, c275, c1070, c1056, c269] c1462 (by decide) p (sat_cons (step691 p h) (sat_cons (step1461 p h) (sat_cons (step1122 p h) (sat_cons (step1075 p h) (sat_cons (step1081 p h) (sat_cons (step1156 p h) (sat_cons (step1139 p h) (sat_cons (step1456 p h) (sat_cons (step1103 p h) (sat_cons (step1162 p h) (sat_cons (step1108 p h) (sat_cons (step1082 p h) (sat_cons (step1086 p h) (sat_cons (step1099 p h) (sat_cons (step1076 p h) (sat_cons (step1059 p h) (sat_cons (step275 p h) (sat_cons (step1070 p h) (sat_cons (step1056 p h) (sat_cons (step269 p h) (sat_nil p)))))))))))))))))))))
def c1463 : List Lit := [(1660, true), (81, false), (1668, true), (70, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c690, c692, c1067, c1075, c1082, c1086, c1078, c1076, c1059, c1061, c1069, c1070, c1071, c1056, c1057, c1054, c241, c272, c269, c1100, c280, c276, c279] c1463 (by decide) p (sat_cons (step690 p h) (sat_cons (step692 p h) (sat_cons (step1067 p h) (sat_cons (step1075 p h) (sat_cons (step1082 p h) (sat_cons (step1086 p h) (sat_cons (step1078 p h) (sat_cons (step1076 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1069 p h) (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1054 p h) (sat_cons (step241 p h) (sat_cons (step272 p h) (sat_cons (step269 p h) (sat_cons (step1100 p h) (sat_cons (step280 p h) (sat_cons (step276 p h) (sat_cons (step279 p h) (sat_nil p))))))))))))))))))))))))
end B112E186
