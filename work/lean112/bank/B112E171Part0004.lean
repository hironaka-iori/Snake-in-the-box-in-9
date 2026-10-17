import B112E171Part0003
namespace B112E171
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1312 : List Lit := [(72, true), (68, true), (56, true), (73, false)]
theorem step1312 (p : Nat → Bool) (h : Constraints p) : clause p c1312 = true :=
  Snake9.LocalRup.prove_clause [c426, c298] c1312 (by decide) p (sat_cons (step426 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1313 : List Lit := [(73, false), (68, true), (56, true), (71, true)]
theorem step1313 (p : Nat → Bool) (h : Constraints p) : clause p c1313 = true :=
  Snake9.LocalRup.prove_clause [c426, c299] c1313 (by decide) p (sat_cons (step426 p h) (sat_cons (step299 p h) (sat_nil p)))
def c1314 : List Lit := [(74, false), (66, true), (57, true)]
theorem step1314 (p : Nat → Bool) (h : Constraints p) : clause p c1314 = true :=
  Snake9.LocalRup.prove_clause [c427, c301] c1314 (by decide) p (sat_cons (step427 p h) (sat_cons (step301 p h) (sat_nil p)))
def c1315 : List Lit := [(75, false), (77, true), (78, true)]
theorem step1315 (p : Nat → Bool) (h : Constraints p) : clause p c1315 = true :=
  Snake9.LocalRup.prove_clause [c428, c303] c1315 (by decide) p (sat_cons (step428 p h) (sat_cons (step303 p h) (sat_nil p)))
def c1316 : List Lit := [(80, false), (79, true)]
theorem step1316 (p : Nat → Bool) (h : Constraints p) : clause p c1316 = true :=
  Snake9.LocalRup.prove_clause [c429, c319] c1316 (by decide) p (sat_cons (step429 p h) (sat_cons (step319 p h) (sat_nil p)))
def c1317 : List Lit := [(80, false), (72, true)]
theorem step1317 (p : Nat → Bool) (h : Constraints p) : clause p c1317 = true :=
  Snake9.LocalRup.prove_clause [c429, c320] c1317 (by decide) p (sat_cons (step429 p h) (sat_cons (step320 p h) (sat_nil p)))
def c1318 : List Lit := [(81, false), (77, true), (78, true)]
theorem step1318 (p : Nat → Bool) (h : Constraints p) : clause p c1318 = true :=
  Snake9.LocalRup.prove_clause [c430, c324] c1318 (by decide) p (sat_cons (step430 p h) (sat_cons (step324 p h) (sat_nil p)))
def c1319 : List Lit := [(11, true), (82, false), (44, true), (83, true)]
theorem step1319 (p : Nat → Bool) (h : Constraints p) : clause p c1319 = true :=
  Snake9.LocalRup.prove_clause [c431, c328] c1319 (by decide) p (sat_cons (step431 p h) (sat_cons (step328 p h) (sat_nil p)))
def c1320 : List Lit := [(89, true), (90, false), (56, true), (88, true)]
theorem step1320 (p : Nat → Bool) (h : Constraints p) : clause p c1320 = true :=
  Snake9.LocalRup.prove_clause [c434, c363] c1320 (by decide) p (sat_cons (step434 p h) (sat_cons (step363 p h) (sat_nil p)))
def c1321 : List Lit := [(91, false), (83, true), (57, true)]
theorem step1321 (p : Nat → Bool) (h : Constraints p) : clause p c1321 = true :=
  Snake9.LocalRup.prove_clause [c435, c366] c1321 (by decide) p (sat_cons (step435 p h) (sat_cons (step366 p h) (sat_nil p)))
def c1322 : List Lit := [(94, true), (92, false), (95, true)]
theorem step1322 (p : Nat → Bool) (h : Constraints p) : clause p c1322 = true :=
  Snake9.LocalRup.prove_clause [c436, c368] c1322 (by decide) p (sat_cons (step436 p h) (sat_cons (step368 p h) (sat_nil p)))
def c1323 : List Lit := [(99, false), (103, true)]
theorem step1323 (p : Nat → Bool) (h : Constraints p) : clause p c1323 = true :=
  Snake9.LocalRup.prove_clause [c439, c375] c1323 (by decide) p (sat_cons (step439 p h) (sat_cons (step375 p h) (sat_nil p)))
def c1324 : List Lit := [(107, false), (109, true)]
theorem step1324 (p : Nat → Bool) (h : Constraints p) : clause p c1324 = true :=
  Snake9.LocalRup.prove_clause [c443, c384] c1324 (by decide) p (sat_cons (step443 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1325 : List Lit := [(118, false), (119, false)]
theorem step1325 (p : Nat → Bool) (h : Constraints p) : clause p c1325 = true :=
  Snake9.LocalRup.prove_clause [c1094, c451] c1325 (by decide) p (sat_cons (step1094 p h) (sat_cons (step451 p h) (sat_nil p)))
def c1326 : List Lit := [(231, false), (237, false)]
theorem step1326 (p : Nat → Bool) (h : Constraints p) : clause p c1326 = true :=
  Snake9.LocalRup.prove_clause [c1082, c457] c1326 (by decide) p (sat_cons (step1082 p h) (sat_cons (step457 p h) (sat_nil p)))
def c1327 : List Lit := [(239, false), (251, false)]
theorem step1327 (p : Nat → Bool) (h : Constraints p) : clause p c1327 = true :=
  Snake9.LocalRup.prove_clause [c1072, c468] c1327 (by decide) p (sat_cons (step1072 p h) (sat_cons (step468 p h) (sat_nil p)))
def c1328 : List Lit := [(257, false), (263, false)]
theorem step1328 (p : Nat → Bool) (h : Constraints p) : clause p c1328 = true :=
  Snake9.LocalRup.prove_clause [c1081, c479] c1328 (by decide) p (sat_cons (step1081 p h) (sat_cons (step479 p h) (sat_nil p)))
def c1329 : List Lit := [(265, false), (277, false)]
theorem step1329 (p : Nat → Bool) (h : Constraints p) : clause p c1329 = true :=
  Snake9.LocalRup.prove_clause [c1071, c488] c1329 (by decide) p (sat_cons (step1071 p h) (sat_cons (step488 p h) (sat_nil p)))
def c1330 : List Lit := [(253, false), (279, false)]
theorem step1330 (p : Nat → Bool) (h : Constraints p) : clause p c1330 = true :=
  Snake9.LocalRup.prove_clause [c1064, c493] c1330 (by decide) p (sat_cons (step1064 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1331 : List Lit := [(285, false), (291, false)]
theorem step1331 (p : Nat → Bool) (h : Constraints p) : clause p c1331 = true :=
  Snake9.LocalRup.prove_clause [c1080, c508] c1331 (by decide) p (sat_cons (step1080 p h) (sat_cons (step508 p h) (sat_nil p)))
def c1332 : List Lit := [(319, false), (331, false)]
theorem step1332 (p : Nat → Bool) (h : Constraints p) : clause p c1332 = true :=
  Snake9.LocalRup.prove_clause [c1069, c536] c1332 (by decide) p (sat_cons (step1069 p h) (sat_cons (step536 p h) (sat_nil p)))
def c1333 : List Lit := [(307, false), (333, false)]
theorem step1333 (p : Nat → Bool) (h : Constraints p) : clause p c1333 = true :=
  Snake9.LocalRup.prove_clause [c1063, c540] c1333 (by decide) p (sat_cons (step1063 p h) (sat_cons (step540 p h) (sat_nil p)))
def c1334 : List Lit := [(281, false), (335, false)]
theorem step1334 (p : Nat → Bool) (h : Constraints p) : clause p c1334 = true :=
  Snake9.LocalRup.prove_clause [c1060, c545] c1334 (by decide) p (sat_cons (step1060 p h) (sat_cons (step545 p h) (sat_nil p)))
def c1335 : List Lit := [(172, false), (339, false)]
theorem step1335 (p : Nat → Bool) (h : Constraints p) : clause p c1335 = true :=
  Snake9.LocalRup.prove_clause [c1087, c550] c1335 (by decide) p (sat_cons (step1087 p h) (sat_cons (step550 p h) (sat_nil p)))
def c1336 : List Lit := [(341, false), (347, false)]
theorem step1336 (p : Nat → Bool) (h : Constraints p) : clause p c1336 = true :=
  Snake9.LocalRup.prove_clause [c1079, c555] c1336 (by decide) p (sat_cons (step1079 p h) (sat_cons (step555 p h) (sat_nil p)))
def c1337 : List Lit := [(182, false), (183, false)]
theorem step1337 (p : Nat → Bool) (h : Constraints p) : clause p c1337 = true :=
  Snake9.LocalRup.prove_clause [c1092, c561] c1337 (by decide) p (sat_cons (step1092 p h) (sat_cons (step561 p h) (sat_nil p)))
def c1338 : List Lit := [(355, false), (357, false)]
theorem step1338 (p : Nat → Bool) (h : Constraints p) : clause p c1338 = true :=
  Snake9.LocalRup.prove_clause [c1086, c565] c1338 (by decide) p (sat_cons (step1086 p h) (sat_cons (step565 p h) (sat_nil p)))
def c1339 : List Lit := [(353, false), (359, false)]
theorem step1339 (p : Nat → Bool) (h : Constraints p) : clause p c1339 = true :=
  Snake9.LocalRup.prove_clause [c1078, c570] c1339 (by decide) p (sat_cons (step1078 p h) (sat_cons (step570 p h) (sat_nil p)))
def c1340 : List Lit := [(349, false), (361, false)]
theorem step1340 (p : Nat → Bool) (h : Constraints p) : clause p c1340 = true :=
  Snake9.LocalRup.prove_clause [c1068, c574] c1340 (by decide) p (sat_cons (step1068 p h) (sat_cons (step574 p h) (sat_nil p)))
def c1341 : List Lit := [(367, false), (373, false)]
theorem step1341 (p : Nat → Bool) (h : Constraints p) : clause p c1341 = true :=
  Snake9.LocalRup.prove_clause [c1077, c587] c1341 (by decide) p (sat_cons (step1077 p h) (sat_cons (step587 p h) (sat_nil p)))
def c1342 : List Lit := [(379, false), (385, false)]
theorem step1342 (p : Nat → Bool) (h : Constraints p) : clause p c1342 = true :=
  Snake9.LocalRup.prove_clause [c1076, c595] c1342 (by decide) p (sat_cons (step1076 p h) (sat_cons (step595 p h) (sat_nil p)))
def c1343 : List Lit := [(375, false), (387, false)]
theorem step1343 (p : Nat → Bool) (h : Constraints p) : clause p c1343 = true :=
  Snake9.LocalRup.prove_clause [c1067, c599] c1343 (by decide) p (sat_cons (step1067 p h) (sat_cons (step599 p h) (sat_nil p)))
def c1344 : List Lit := [(389, false), (363, false)]
theorem step1344 (p : Nat → Bool) (h : Constraints p) : clause p c1344 = true :=
  Snake9.LocalRup.prove_clause [c1062, c604] c1344 (by decide) p (sat_cons (step1062 p h) (sat_cons (step604 p h) (sat_nil p)))
def c1345 : List Lit := [(395, false), (401, false)]
theorem step1345 (p : Nat → Bool) (h : Constraints p) : clause p c1345 = true :=
  Snake9.LocalRup.prove_clause [c1075, c614] c1345 (by decide) p (sat_cons (step1075 p h) (sat_cons (step614 p h) (sat_nil p)))
def c1346 : List Lit := [(403, false), (415, false)]
theorem step1346 (p : Nat → Bool) (h : Constraints p) : clause p c1346 = true :=
  Snake9.LocalRup.prove_clause [c1066, c628] c1346 (by decide) p (sat_cons (step1066 p h) (sat_cons (step628 p h) (sat_nil p)))
def c1347 : List Lit := [(417, false), (445, false)]
theorem step1347 (p : Nat → Bool) (h : Constraints p) : clause p c1347 = true :=
  Snake9.LocalRup.prove_clause [c1061, c656] c1347 (by decide) p (sat_cons (step1061 p h) (sat_cons (step656 p h) (sat_nil p)))
def c1348 : List Lit := [(391, false), (447, false)]
theorem step1348 (p : Nat → Bool) (h : Constraints p) : clause p c1348 = true :=
  Snake9.LocalRup.prove_clause [c1059, c661] c1348 (by decide) p (sat_cons (step1059 p h) (sat_cons (step661 p h) (sat_nil p)))
def c1349 : List Lit := [(337, false), (449, false)]
theorem step1349 (p : Nat → Bool) (h : Constraints p) : clause p c1349 = true :=
  Snake9.LocalRup.prove_clause [c666, c664] c1349 (by decide) p (sat_cons (step666 p h) (sat_cons (step664 p h) (sat_nil p)))
def c1350 : List Lit := [(1399, true), (1387, false)]
theorem step1350 (p : Nat → Bool) (h : Constraints p) : clause p c1350 = true :=
  Snake9.LocalRup.prove_clause [c1177, c716] c1350 (by decide) p (sat_cons (step1177 p h) (sat_cons (step716 p h) (sat_nil p)))
def c1351 : List Lit := [(1388, false), (1400, true)]
theorem step1351 (p : Nat → Bool) (h : Constraints p) : clause p c1351 = true :=
  Snake9.LocalRup.prove_clause [c1177, c718] c1351 (by decide) p (sat_cons (step1177 p h) (sat_cons (step718 p h) (sat_nil p)))
def c1352 : List Lit := [(1407, true), (1379, false)]
theorem step1352 (p : Nat → Bool) (h : Constraints p) : clause p c1352 = true :=
  Snake9.LocalRup.prove_clause [c1178, c724] c1352 (by decide) p (sat_cons (step1178 p h) (sat_cons (step724 p h) (sat_nil p)))
def c1353 : List Lit := [(1380, false), (1408, true)]
theorem step1353 (p : Nat → Bool) (h : Constraints p) : clause p c1353 = true :=
  Snake9.LocalRup.prove_clause [c1178, c727] c1353 (by decide) p (sat_cons (step1178 p h) (sat_cons (step727 p h) (sat_nil p)))
def c1354 : List Lit := [(1381, false), (1409, true)]
theorem step1354 (p : Nat → Bool) (h : Constraints p) : clause p c1354 = true :=
  Snake9.LocalRup.prove_clause [c1178, c730] c1354 (by decide) p (sat_cons (step1178 p h) (sat_cons (step730 p h) (sat_nil p)))
def c1355 : List Lit := [(1382, false), (1410, true)]
theorem step1355 (p : Nat → Bool) (h : Constraints p) : clause p c1355 = true :=
  Snake9.LocalRup.prove_clause [c1178, c732] c1355 (by decide) p (sat_cons (step1178 p h) (sat_cons (step732 p h) (sat_nil p)))
def c1356 : List Lit := [(1461, true), (1453, false)]
theorem step1356 (p : Nat → Bool) (h : Constraints p) : clause p c1356 = true :=
  Snake9.LocalRup.prove_clause [c1124, c803] c1356 (by decide) p (sat_cons (step1124 p h) (sat_cons (step803 p h) (sat_nil p)))
def c1357 : List Lit := [(1462, true), (1454, false)]
theorem step1357 (p : Nat → Bool) (h : Constraints p) : clause p c1357 = true :=
  Snake9.LocalRup.prove_clause [c1124, c804] c1357 (by decide) p (sat_cons (step1124 p h) (sat_cons (step804 p h) (sat_nil p)))
def c1358 : List Lit := [(1463, true), (1455, false)]
theorem step1358 (p : Nat → Bool) (h : Constraints p) : clause p c1358 = true :=
  Snake9.LocalRup.prove_clause [c1124, c805] c1358 (by decide) p (sat_cons (step1124 p h) (sat_cons (step805 p h) (sat_nil p)))
def c1359 : List Lit := [(1456, false), (1464, true)]
theorem step1359 (p : Nat → Bool) (h : Constraints p) : clause p c1359 = true :=
  Snake9.LocalRup.prove_clause [c1124, c806] c1359 (by decide) p (sat_cons (step1124 p h) (sat_cons (step806 p h) (sat_nil p)))
def c1360 : List Lit := [(1457, false), (1465, true)]
theorem step1360 (p : Nat → Bool) (h : Constraints p) : clause p c1360 = true :=
  Snake9.LocalRup.prove_clause [c1124, c807] c1360 (by decide) p (sat_cons (step1124 p h) (sat_cons (step807 p h) (sat_nil p)))
def c1361 : List Lit := [(1458, false), (1466, true)]
theorem step1361 (p : Nat → Bool) (h : Constraints p) : clause p c1361 = true :=
  Snake9.LocalRup.prove_clause [c1124, c808] c1361 (by decide) p (sat_cons (step1124 p h) (sat_cons (step808 p h) (sat_nil p)))
def c1362 : List Lit := [(1461, true), (1433, false)]
theorem step1362 (p : Nat → Bool) (h : Constraints p) : clause p c1362 = true :=
  Snake9.LocalRup.prove_clause [c1096, c809] c1362 (by decide) p (sat_cons (step1096 p h) (sat_cons (step809 p h) (sat_nil p)))
def c1363 : List Lit := [(1462, true), (1434, false)]
theorem step1363 (p : Nat → Bool) (h : Constraints p) : clause p c1363 = true :=
  Snake9.LocalRup.prove_clause [c1096, c816] c1363 (by decide) p (sat_cons (step1096 p h) (sat_cons (step816 p h) (sat_nil p)))
def c1364 : List Lit := [(1479, true), (1463, false)]
theorem step1364 (p : Nat → Bool) (h : Constraints p) : clause p c1364 = true :=
  Snake9.LocalRup.prove_clause [c1179, c823] c1364 (by decide) p (sat_cons (step1179 p h) (sat_cons (step823 p h) (sat_nil p)))
def c1365 : List Lit := [(1480, true), (1464, false)]
theorem step1365 (p : Nat → Bool) (h : Constraints p) : clause p c1365 = true :=
  Snake9.LocalRup.prove_clause [c1179, c824] c1365 (by decide) p (sat_cons (step1179 p h) (sat_cons (step824 p h) (sat_nil p)))
def c1366 : List Lit := [(1481, true), (1465, false)]
theorem step1366 (p : Nat → Bool) (h : Constraints p) : clause p c1366 = true :=
  Snake9.LocalRup.prove_clause [c1179, c825] c1366 (by decide) p (sat_cons (step1179 p h) (sat_cons (step825 p h) (sat_nil p)))
def c1367 : List Lit := [(1482, true), (1466, false)]
theorem step1367 (p : Nat → Bool) (h : Constraints p) : clause p c1367 = true :=
  Snake9.LocalRup.prove_clause [c1179, c826] c1367 (by decide) p (sat_cons (step1179 p h) (sat_cons (step826 p h) (sat_nil p)))
def c1368 : List Lit := [(1483, true), (1467, false)]
theorem step1368 (p : Nat → Bool) (h : Constraints p) : clause p c1368 = true :=
  Snake9.LocalRup.prove_clause [c1179, c827] c1368 (by decide) p (sat_cons (step1179 p h) (sat_cons (step827 p h) (sat_nil p)))
def c1369 : List Lit := [(1478, true), (1408, false)]
theorem step1369 (p : Nat → Bool) (h : Constraints p) : clause p c1369 = true :=
  Snake9.LocalRup.prove_clause [c1125, c835] c1369 (by decide) p (sat_cons (step1125 p h) (sat_cons (step835 p h) (sat_nil p)))
def c1370 : List Lit := [(1479, true), (1409, false)]
theorem step1370 (p : Nat → Bool) (h : Constraints p) : clause p c1370 = true :=
  Snake9.LocalRup.prove_clause [c1125, c842] c1370 (by decide) p (sat_cons (step1125 p h) (sat_cons (step842 p h) (sat_nil p)))
def c1371 : List Lit := [(1480, true), (1410, false)]
theorem step1371 (p : Nat → Bool) (h : Constraints p) : clause p c1371 = true :=
  Snake9.LocalRup.prove_clause [c1125, c848] c1371 (by decide) p (sat_cons (step1125 p h) (sat_cons (step848 p h) (sat_nil p)))
def c1372 : List Lit := [(1504, false), (1532, true)]
theorem step1372 (p : Nat → Bool) (h : Constraints p) : clause p c1372 = true :=
  Snake9.LocalRup.prove_clause [c1097, c930] c1372 (by decide) p (sat_cons (step1097 p h) (sat_cons (step930 p h) (sat_nil p)))
def c1373 : List Lit := [(1505, false), (1533, true)]
theorem step1373 (p : Nat → Bool) (h : Constraints p) : clause p c1373 = true :=
  Snake9.LocalRup.prove_clause [c1097, c936] c1373 (by decide) p (sat_cons (step1097 p h) (sat_cons (step936 p h) (sat_nil p)))
def c1374 : List Lit := [(1506, false), (1534, true)]
theorem step1374 (p : Nat → Bool) (h : Constraints p) : clause p c1374 = true :=
  Snake9.LocalRup.prove_clause [c1097, c940] c1374 (by decide) p (sat_cons (step1097 p h) (sat_cons (step940 p h) (sat_nil p)))
def c1375 : List Lit := [(1507, false), (1535, true)]
theorem step1375 (p : Nat → Bool) (h : Constraints p) : clause p c1375 = true :=
  Snake9.LocalRup.prove_clause [c1097, c943] c1375 (by decide) p (sat_cons (step1097 p h) (sat_cons (step943 p h) (sat_nil p)))
end B112E171
