import B112E207Inputs
namespace B112E207
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1347 : List Lit := [(105, true)]
theorem step1347 (p : Nat → Bool) (h : Constraints p) : clause p c1347 = true :=
  Snake9.LocalRup.prove_clause [c600, c599] c1347 (by decide) p (sat_cons (step600 p h) (sat_cons (step599 p h) (sat_nil p)))
def c1348 : List Lit := [(222, true), (110, true)]
theorem step1348 (p : Nat → Bool) (h : Constraints p) : clause p c1348 = true :=
  Snake9.LocalRup.prove_clause [c1347, c601] c1348 (by decide) p (sat_cons (step1347 p h) (sat_cons (step601 p h) (sat_nil p)))
def c1349 : List Lit := [(36, false)]
theorem step1349 (p : Nat → Bool) (h : Constraints p) : clause p c1349 = true :=
  Snake9.LocalRup.prove_clause [c641, c161] c1349 (by decide) p (sat_cons (step641 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1350 : List Lit := [(42, false)]
theorem step1350 (p : Nat → Bool) (h : Constraints p) : clause p c1350 = true :=
  Snake9.LocalRup.prove_clause [c644, c177] c1350 (by decide) p (sat_cons (step644 p h) (sat_cons (step177 p h) (sat_nil p)))
def c1351 : List Lit := [(44, false)]
theorem step1351 (p : Nat → Bool) (h : Constraints p) : clause p c1351 = true :=
  Snake9.LocalRup.prove_clause [c645, c179] c1351 (by decide) p (sat_cons (step645 p h) (sat_cons (step179 p h) (sat_nil p)))
def c1352 : List Lit := [(462, false)]
theorem step1352 (p : Nat → Bool) (h : Constraints p) : clause p c1352 = true :=
  Snake9.LocalRup.prove_clause [c901, c898] c1352 (by decide) p (sat_cons (step901 p h) (sat_cons (step898 p h) (sat_nil p)))
def c1353 : List Lit := [(348, false)]
theorem step1353 (p : Nat → Bool) (h : Constraints p) : clause p c1353 = true :=
  Snake9.LocalRup.prove_clause [c901, c900] c1353 (by decide) p (sat_cons (step901 p h) (sat_cons (step900 p h) (sat_nil p)))
def c1354 : List Lit := [(460, false)]
theorem step1354 (p : Nat → Bool) (h : Constraints p) : clause p c1354 = true :=
  Snake9.LocalRup.prove_clause [c1352, c894] c1354 (by decide) p (sat_cons (step1352 p h) (sat_cons (step894 p h) (sat_nil p)))
def c1355 : List Lit := [(404, false)]
theorem step1355 (p : Nat → Bool) (h : Constraints p) : clause p c1355 = true :=
  Snake9.LocalRup.prove_clause [c1352, c897] c1355 (by decide) p (sat_cons (step1352 p h) (sat_cons (step897 p h) (sat_nil p)))
def c1356 : List Lit := [(346, false)]
theorem step1356 (p : Nat → Bool) (h : Constraints p) : clause p c1356 = true :=
  Snake9.LocalRup.prove_clause [c1353, c778] c1356 (by decide) p (sat_cons (step1353 p h) (sat_cons (step778 p h) (sat_nil p)))
def c1357 : List Lit := [(290, false)]
theorem step1357 (p : Nat → Bool) (h : Constraints p) : clause p c1357 = true :=
  Snake9.LocalRup.prove_clause [c1353, c781] c1357 (by decide) p (sat_cons (step1353 p h) (sat_cons (step781 p h) (sat_nil p)))
def c1358 : List Lit := [(430, false)]
theorem step1358 (p : Nat → Bool) (h : Constraints p) : clause p c1358 = true :=
  Snake9.LocalRup.prove_clause [c1354, c892] c1358 (by decide) p (sat_cons (step1354 p h) (sat_cons (step892 p h) (sat_nil p)))
def c1359 : List Lit := [(402, false)]
theorem step1359 (p : Nat → Bool) (h : Constraints p) : clause p c1359 = true :=
  Snake9.LocalRup.prove_clause [c1355, c837] c1359 (by decide) p (sat_cons (step1355 p h) (sat_cons (step837 p h) (sat_nil p)))
def c1360 : List Lit := [(374, false)]
theorem step1360 (p : Nat → Bool) (h : Constraints p) : clause p c1360 = true :=
  Snake9.LocalRup.prove_clause [c1355, c840] c1360 (by decide) p (sat_cons (step1355 p h) (sat_cons (step840 p h) (sat_nil p)))
def c1361 : List Lit := [(344, false)]
theorem step1361 (p : Nat → Bool) (h : Constraints p) : clause p c1361 = true :=
  Snake9.LocalRup.prove_clause [c1356, c773] c1361 (by decide) p (sat_cons (step1356 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1362 : List Lit := [(316, false)]
theorem step1362 (p : Nat → Bool) (h : Constraints p) : clause p c1362 = true :=
  Snake9.LocalRup.prove_clause [c1356, c776] c1362 (by decide) p (sat_cons (step1356 p h) (sat_cons (step776 p h) (sat_nil p)))
def c1363 : List Lit := [(288, false)]
theorem step1363 (p : Nat → Bool) (h : Constraints p) : clause p c1363 = true :=
  Snake9.LocalRup.prove_clause [c1357, c723] c1363 (by decide) p (sat_cons (step1357 p h) (sat_cons (step723 p h) (sat_nil p)))
def c1364 : List Lit := [(260, false)]
theorem step1364 (p : Nat → Bool) (h : Constraints p) : clause p c1364 = true :=
  Snake9.LocalRup.prove_clause [c1357, c726] c1364 (by decide) p (sat_cons (step1357 p h) (sat_cons (step726 p h) (sat_nil p)))
def c1365 : List Lit := [(428, false)]
theorem step1365 (p : Nat → Bool) (h : Constraints p) : clause p c1365 = true :=
  Snake9.LocalRup.prove_clause [c1358, c867] c1365 (by decide) p (sat_cons (step1358 p h) (sat_cons (step867 p h) (sat_nil p)))
def c1366 : List Lit := [(416, false)]
theorem step1366 (p : Nat → Bool) (h : Constraints p) : clause p c1366 = true :=
  Snake9.LocalRup.prove_clause [c1358, c870] c1366 (by decide) p (sat_cons (step1358 p h) (sat_cons (step870 p h) (sat_nil p)))
def c1367 : List Lit := [(400, false)]
theorem step1367 (p : Nat → Bool) (h : Constraints p) : clause p c1367 = true :=
  Snake9.LocalRup.prove_clause [c1359, c833] c1367 (by decide) p (sat_cons (step1359 p h) (sat_cons (step833 p h) (sat_nil p)))
def c1368 : List Lit := [(386, false)]
theorem step1368 (p : Nat → Bool) (h : Constraints p) : clause p c1368 = true :=
  Snake9.LocalRup.prove_clause [c1359, c835] c1368 (by decide) p (sat_cons (step1359 p h) (sat_cons (step835 p h) (sat_nil p)))
def c1369 : List Lit := [(372, false)]
theorem step1369 (p : Nat → Bool) (h : Constraints p) : clause p c1369 = true :=
  Snake9.LocalRup.prove_clause [c1360, c806] c1369 (by decide) p (sat_cons (step1360 p h) (sat_cons (step806 p h) (sat_nil p)))
def c1370 : List Lit := [(360, false)]
theorem step1370 (p : Nat → Bool) (h : Constraints p) : clause p c1370 = true :=
  Snake9.LocalRup.prove_clause [c1360, c809] c1370 (by decide) p (sat_cons (step1360 p h) (sat_cons (step809 p h) (sat_nil p)))
def c1371 : List Lit := [(342, false)]
theorem step1371 (p : Nat → Bool) (h : Constraints p) : clause p c1371 = true :=
  Snake9.LocalRup.prove_clause [c1361, c768] c1371 (by decide) p (sat_cons (step1361 p h) (sat_cons (step768 p h) (sat_nil p)))
def c1372 : List Lit := [(328, false)]
theorem step1372 (p : Nat → Bool) (h : Constraints p) : clause p c1372 = true :=
  Snake9.LocalRup.prove_clause [c1361, c771] c1372 (by decide) p (sat_cons (step1361 p h) (sat_cons (step771 p h) (sat_nil p)))
def c1373 : List Lit := [(314, false)]
theorem step1373 (p : Nat → Bool) (h : Constraints p) : clause p c1373 = true :=
  Snake9.LocalRup.prove_clause [c1362, c746] c1373 (by decide) p (sat_cons (step1362 p h) (sat_cons (step746 p h) (sat_nil p)))
def c1374 : List Lit := [(302, false)]
theorem step1374 (p : Nat → Bool) (h : Constraints p) : clause p c1374 = true :=
  Snake9.LocalRup.prove_clause [c1362, c749] c1374 (by decide) p (sat_cons (step1362 p h) (sat_cons (step749 p h) (sat_nil p)))
def c1375 : List Lit := [(286, false)]
theorem step1375 (p : Nat → Bool) (h : Constraints p) : clause p c1375 = true :=
  Snake9.LocalRup.prove_clause [c1363, c718] c1375 (by decide) p (sat_cons (step1363 p h) (sat_cons (step718 p h) (sat_nil p)))
def c1376 : List Lit := [(272, false)]
theorem step1376 (p : Nat → Bool) (h : Constraints p) : clause p c1376 = true :=
  Snake9.LocalRup.prove_clause [c1363, c721] c1376 (by decide) p (sat_cons (step1363 p h) (sat_cons (step721 p h) (sat_nil p)))
def c1377 : List Lit := [(258, false)]
theorem step1377 (p : Nat → Bool) (h : Constraints p) : clause p c1377 = true :=
  Snake9.LocalRup.prove_clause [c1364, c695] c1377 (by decide) p (sat_cons (step1364 p h) (sat_cons (step695 p h) (sat_nil p)))
def c1378 : List Lit := [(246, false)]
theorem step1378 (p : Nat → Bool) (h : Constraints p) : clause p c1378 = true :=
  Snake9.LocalRup.prove_clause [c1364, c698] c1378 (by decide) p (sat_cons (step1364 p h) (sat_cons (step698 p h) (sat_nil p)))
def c1379 : List Lit := [(426, false)]
theorem step1379 (p : Nat → Bool) (h : Constraints p) : clause p c1379 = true :=
  Snake9.LocalRup.prove_clause [c1365, c863] c1379 (by decide) p (sat_cons (step1365 p h) (sat_cons (step863 p h) (sat_nil p)))
def c1380 : List Lit := [(414, false)]
theorem step1380 (p : Nat → Bool) (h : Constraints p) : clause p c1380 = true :=
  Snake9.LocalRup.prove_clause [c1366, c850] c1380 (by decide) p (sat_cons (step1366 p h) (sat_cons (step850 p h) (sat_nil p)))
def c1381 : List Lit := [(392, false)]
theorem step1381 (p : Nat → Bool) (h : Constraints p) : clause p c1381 = true :=
  Snake9.LocalRup.prove_clause [c1367, c831] c1381 (by decide) p (sat_cons (step1367 p h) (sat_cons (step831 p h) (sat_nil p)))
def c1382 : List Lit := [(378, false)]
theorem step1382 (p : Nat → Bool) (h : Constraints p) : clause p c1382 = true :=
  Snake9.LocalRup.prove_clause [c1368, c819] c1382 (by decide) p (sat_cons (step1368 p h) (sat_cons (step819 p h) (sat_nil p)))
def c1383 : List Lit := [(370, false)]
theorem step1383 (p : Nat → Bool) (h : Constraints p) : clause p c1383 = true :=
  Snake9.LocalRup.prove_clause [c1369, c803] c1383 (by decide) p (sat_cons (step1369 p h) (sat_cons (step803 p h) (sat_nil p)))
def c1384 : List Lit := [(358, false)]
theorem step1384 (p : Nat → Bool) (h : Constraints p) : clause p c1384 = true :=
  Snake9.LocalRup.prove_clause [c1370, c790] c1384 (by decide) p (sat_cons (step1370 p h) (sat_cons (step790 p h) (sat_nil p)))
def c1385 : List Lit := [(326, false)]
theorem step1385 (p : Nat → Bool) (h : Constraints p) : clause p c1385 = true :=
  Snake9.LocalRup.prove_clause [c1372, c758] c1385 (by decide) p (sat_cons (step1372 p h) (sat_cons (step758 p h) (sat_nil p)))
def c1386 : List Lit := [(306, false)]
theorem step1386 (p : Nat → Bool) (h : Constraints p) : clause p c1386 = true :=
  Snake9.LocalRup.prove_clause [c1373, c744] c1386 (by decide) p (sat_cons (step1373 p h) (sat_cons (step744 p h) (sat_nil p)))
def c1387 : List Lit := [(278, false)]
theorem step1387 (p : Nat → Bool) (h : Constraints p) : clause p c1387 = true :=
  Snake9.LocalRup.prove_clause [c1375, c716] c1387 (by decide) p (sat_cons (step1375 p h) (sat_cons (step716 p h) (sat_nil p)))
def c1388 : List Lit := [(244, false)]
theorem step1388 (p : Nat → Bool) (h : Constraints p) : clause p c1388 = true :=
  Snake9.LocalRup.prove_clause [c1378, c683] c1388 (by decide) p (sat_cons (step1378 p h) (sat_cons (step683 p h) (sat_nil p)))
def c1389 : List Lit := [(422, false)]
theorem step1389 (p : Nat → Bool) (h : Constraints p) : clause p c1389 = true :=
  Snake9.LocalRup.prove_clause [c1379, c861] c1389 (by decide) p (sat_cons (step1379 p h) (sat_cons (step861 p h) (sat_nil p)))
def c1390 : List Lit := [(388, false)]
theorem step1390 (p : Nat → Bool) (h : Constraints p) : clause p c1390 = true :=
  Snake9.LocalRup.prove_clause [c1381, c826] c1390 (by decide) p (sat_cons (step1381 p h) (sat_cons (step826 p h) (sat_nil p)))
def c1391 : List Lit := [(376, false)]
theorem step1391 (p : Nat → Bool) (h : Constraints p) : clause p c1391 = true :=
  Snake9.LocalRup.prove_clause [c1382, c814] c1391 (by decide) p (sat_cons (step1382 p h) (sat_cons (step814 p h) (sat_nil p)))
def c1392 : List Lit := [(368, false)]
theorem step1392 (p : Nat → Bool) (h : Constraints p) : clause p c1392 = true :=
  Snake9.LocalRup.prove_clause [c1383, c799] c1392 (by decide) p (sat_cons (step1383 p h) (sat_cons (step799 p h) (sat_nil p)))
def c1393 : List Lit := [(354, false)]
theorem step1393 (p : Nat → Bool) (h : Constraints p) : clause p c1393 = true :=
  Snake9.LocalRup.prove_clause [c1384, c788] c1393 (by decide) p (sat_cons (step1384 p h) (sat_cons (step788 p h) (sat_nil p)))
def c1394 : List Lit := [(324, false)]
theorem step1394 (p : Nat → Bool) (h : Constraints p) : clause p c1394 = true :=
  Snake9.LocalRup.prove_clause [c1385, c756] c1394 (by decide) p (sat_cons (step1385 p h) (sat_cons (step756 p h) (sat_nil p)))
def c1395 : List Lit := [(304, false)]
theorem step1395 (p : Nat → Bool) (h : Constraints p) : clause p c1395 = true :=
  Snake9.LocalRup.prove_clause [c1386, c737] c1395 (by decide) p (sat_cons (step1386 p h) (sat_cons (step737 p h) (sat_nil p)))
def c1396 : List Lit := [(240, false)]
theorem step1396 (p : Nat → Bool) (h : Constraints p) : clause p c1396 = true :=
  Snake9.LocalRup.prove_clause [c1388, c681] c1396 (by decide) p (sat_cons (step1388 p h) (sat_cons (step681 p h) (sat_nil p)))
def c1397 : List Lit := [(75, false), (1551, true)]
theorem step1397 (p : Nat → Bool) (h : Constraints p) : clause p c1397 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1155, c1152, c1153, c1157, c1150, c463, c1149, c481, c477, c472, c812] c1397 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1155 p h) (sat_cons (step1152 p h) (sat_cons (step1153 p h) (sat_cons (step1157 p h) (sat_cons (step1150 p h) (sat_cons (step463 p h) (sat_cons (step1149 p h) (sat_cons (step481 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step812 p h) (sat_nil p)))))))))))))
def c1398 : List Lit := [(75, true), (1576, true)]
theorem step1398 (p : Nat → Bool) (h : Constraints p) : clause p c1398 = true :=
  Snake9.LocalRup.prove_clause [c659, c1205, c499, c1184, c1185, c1203, c1179, c1194, c1186, c1187, c495, c500] c1398 (by decide) p (sat_cons (step659 p h) (sat_cons (step1205 p h) (sat_cons (step499 p h) (sat_cons (step1184 p h) (sat_cons (step1185 p h) (sat_cons (step1203 p h) (sat_cons (step1179 p h) (sat_cons (step1194 p h) (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step495 p h) (sat_cons (step500 p h) (sat_nil p)))))))))))))
def c1399 : List Lit := [(1583, true)]
theorem step1399 (p : Nat → Bool) (h : Constraints p) : clause p c1399 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1212, c1398, c1397, c1163, c1167, c1209, c1144, c1199, c1202, c1141, c1142, c1194, c1182, c1186, c1187, c1179, c1180, c432, c500, c486, c491] c1399 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1212 p h) (sat_cons (step1398 p h) (sat_cons (step1397 p h) (sat_cons (step1163 p h) (sat_cons (step1167 p h) (sat_cons (step1209 p h) (sat_cons (step1144 p h) (sat_cons (step1199 p h) (sat_cons (step1202 p h) (sat_cons (step1141 p h) (sat_cons (step1142 p h) (sat_cons (step1194 p h) (sat_cons (step1182 p h) (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step1179 p h) (sat_cons (step1180 p h) (sat_cons (step432 p h) (sat_cons (step500 p h) (sat_cons (step486 p h) (sat_cons (step491 p h) (sat_nil p)))))))))))))))))))))))
def c1400 : List Lit := [(1567, true), (1562, true)]
theorem step1400 (p : Nat → Bool) (h : Constraints p) : clause p c1400 = true :=
  Snake9.LocalRup.prove_clause [c1390, c1180, c1179, c1186, c1187, c500, c486, c492, c490, c821] c1400 (by decide) p (sat_cons (step1390 p h) (sat_cons (step1180 p h) (sat_cons (step1179 p h) (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step500 p h) (sat_cons (step486 p h) (sat_cons (step492 p h) (sat_cons (step490 p h) (sat_cons (step821 p h) (sat_nil p)))))))))))
def c1401 : List Lit := [(1485, true), (50, false), (166, true), (1569, true)]
theorem step1401 (p : Nat → Bool) (h : Constraints p) : clause p c1401 = true :=
  Snake9.LocalRup.prove_clause [c1190, c1189, c1040, c1041, c262, c519, c219, c228, c244] c1401 (by decide) p (sat_cons (step1190 p h) (sat_cons (step1189 p h) (sat_cons (step1040 p h) (sat_cons (step1041 p h) (sat_cons (step262 p h) (sat_cons (step519 p h) (sat_cons (step219 p h) (sat_cons (step228 p h) (sat_cons (step244 p h) (sat_nil p))))))))))
def c1402 : List Lit := [(50, true), (1502, true)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true :=
  Snake9.LocalRup.prove_clause [c1075, c1047, c1044, c1045, c1046, c1049, c1071, c1040, c1041, c1060, c1062, c1057, c1054, c1055, c230, c357, c292, c349] c1402 (by decide) p (sat_cons (step1075 p h) (sat_cons (step1047 p h) (sat_cons (step1044 p h) (sat_cons (step1045 p h) (sat_cons (step1046 p h) (sat_cons (step1049 p h) (sat_cons (step1071 p h) (sat_cons (step1040 p h) (sat_cons (step1041 p h) (sat_cons (step1060 p h) (sat_cons (step1062 p h) (sat_cons (step1057 p h) (sat_cons (step1054 p h) (sat_cons (step1055 p h) (sat_cons (step230 p h) (sat_cons (step357 p h) (sat_cons (step292 p h) (sat_cons (step349 p h) (sat_nil p)))))))))))))))))))
def c1403 : List Lit := [(58, true), (1502, true)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1068, c1061, c1058, c1059, c1060, c1063, c1071, c1054, c1055, c1046, c1048, c237, c356, c1043, c1041, c349, c292] c1403 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1068 p h) (sat_cons (step1061 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step1060 p h) (sat_cons (step1063 p h) (sat_cons (step1071 p h) (sat_cons (step1054 p h) (sat_cons (step1055 p h) (sat_cons (step1046 p h) (sat_cons (step1048 p h) (sat_cons (step237 p h) (sat_cons (step356 p h) (sat_cons (step1043 p h) (sat_cons (step1041 p h) (sat_cons (step349 p h) (sat_cons (step292 p h) (sat_nil p)))))))))))))))))))
def c1404 : List Lit := [(1478, true)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c1030, c1033, c1024, c1026, c1013, c1022, c1018, c1019, c1010, c1011, c174, c171, c168] c1404 (by decide) p (sat_cons (step1030 p h) (sat_cons (step1033 p h) (sat_cons (step1024 p h) (sat_cons (step1026 p h) (sat_cons (step1013 p h) (sat_cons (step1022 p h) (sat_cons (step1018 p h) (sat_cons (step1019 p h) (sat_cons (step1010 p h) (sat_cons (step1011 p h) (sat_cons (step174 p h) (sat_cons (step171 p h) (sat_cons (step168 p h) (sat_nil p))))))))))))))
def c1405 : List Lit := [(1497, true), (1502, true)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.LocalRup.prove_clause [c1075, c1051, c1403, c1402, c1060, c1062, c1057, c1054, c1055, c237, c356, c349, c404, c408, c1040, c1042, c1049, c292, c1043] c1405 (by decide) p (sat_cons (step1075 p h) (sat_cons (step1051 p h) (sat_cons (step1403 p h) (sat_cons (step1402 p h) (sat_cons (step1060 p h) (sat_cons (step1062 p h) (sat_cons (step1057 p h) (sat_cons (step1054 p h) (sat_cons (step1055 p h) (sat_cons (step237 p h) (sat_cons (step356 p h) (sat_cons (step349 p h) (sat_cons (step404 p h) (sat_cons (step408 p h) (sat_cons (step1040 p h) (sat_cons (step1042 p h) (sat_cons (step1049 p h) (sat_cons (step292 p h) (sat_cons (step1043 p h) (sat_nil p))))))))))))))))))))
def c1406 : List Lit := [(60, false), (1502, true)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1405, c1071, c1048, c1040, c1041, c228, c1403, c408, c404] c1406 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1405 p h) (sat_cons (step1071 p h) (sat_cons (step1048 p h) (sat_cons (step1040 p h) (sat_cons (step1041 p h) (sat_cons (step228 p h) (sat_cons (step1403 p h) (sat_cons (step408 p h) (sat_cons (step404 p h) (sat_nil p)))))))))))
def c1407 : List Lit := [(1502, true)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.LocalRup.prove_clause [c1068, c1402, c1405, c1071, c1046, c1048, c1043, c1040, c1041, c228, c1406, c1057, c1063, c1054, c1055, c355, c349, c292] c1407 (by decide) p (sat_cons (step1068 p h) (sat_cons (step1402 p h) (sat_cons (step1405 p h) (sat_cons (step1071 p h) (sat_cons (step1046 p h) (sat_cons (step1048 p h) (sat_cons (step1043 p h) (sat_cons (step1040 p h) (sat_cons (step1041 p h) (sat_cons (step228 p h) (sat_cons (step1406 p h) (sat_cons (step1057 p h) (sat_cons (step1063 p h) (sat_cons (step1054 p h) (sat_cons (step1055 p h) (sat_cons (step355 p h) (sat_cons (step349 p h) (sat_cons (step292 p h) (sat_nil p)))))))))))))))))))
def c1408 : List Lit := [(1511, true)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1404, c1089] c1408 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1404 p h) (sat_cons (step1089 p h) (sat_nil p))))
def c1409 : List Lit := [(76, true), (1553, true), (359, false), (51, true), (54, true), (72, true)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c1360, c1355, c807, c839, c834, c818, c813, c811, c808, c802, c798, c796, c456, c473, c1149, c1154, c1159] c1409 (by decide) p (sat_cons (step1360 p h) (sat_cons (step1355 p h) (sat_cons (step807 p h) (sat_cons (step839 p h) (sat_cons (step834 p h) (sat_cons (step818 p h) (sat_cons (step813 p h) (sat_cons (step811 p h) (sat_cons (step808 p h) (sat_cons (step802 p h) (sat_cons (step798 p h) (sat_cons (step796 p h) (sat_cons (step456 p h) (sat_cons (step473 p h) (sat_cons (step1149 p h) (sat_cons (step1154 p h) (sat_cons (step1159 p h) (sat_nil p))))))))))))))))))
def c1410 : List Lit := [(71, false), (75, false), (188, true), (51, true), (57, false)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c479, c456] c1410 (by decide) p (sat_cons (step479 p h) (sat_cons (step456 p h) (sat_nil p)))
end B112E207
