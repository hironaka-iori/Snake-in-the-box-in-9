import B112E088Part0002
namespace B112E088
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1352 : List Lit := [(1394, false), (29, true), (1478, false), (1449, false), (1419, false), (1508, true), (41, true)]
theorem step1352 (p : Nat → Bool) (h : Constraints p) : clause p c1352 = true :=
  Snake9.LocalRup.prove_clause [c780, c803, c878, c924, c762, c699, c702, c755, c1267, c919, c775, c885, c781, c808] c1352 (by decide) p (sat_cons (step780 p h) (sat_cons (step803 p h) (sat_cons (step878 p h) (sat_cons (step924 p h) (sat_cons (step762 p h) (sat_cons (step699 p h) (sat_cons (step702 p h) (sat_cons (step755 p h) (sat_cons (step1267 p h) (sat_cons (step919 p h) (sat_cons (step775 p h) (sat_cons (step885 p h) (sat_cons (step781 p h) (sat_cons (step808 p h) (sat_nil p)))))))))))))))
def c1353 : List Lit := [(1478, false), (1449, false), (1508, true), (17, false), (41, true), (28, true), (39, false)]
theorem step1353 (p : Nat → Bool) (h : Constraints p) : clause p c1353 = true :=
  Snake9.LocalRup.prove_clause [c719, c722, c1343, c735, c748, c912, c891, c813, c1349, c723, c1257, c1273, c725, c721, c717, c135, c780, c782, c803, c878, c924, c1350, c1352, c740, c694, c1351, c692] c1353 (by decide) p (sat_cons (step719 p h) (sat_cons (step722 p h) (sat_cons (step1343 p h) (sat_cons (step735 p h) (sat_cons (step748 p h) (sat_cons (step912 p h) (sat_cons (step891 p h) (sat_cons (step813 p h) (sat_cons (step1349 p h) (sat_cons (step723 p h) (sat_cons (step1257 p h) (sat_cons (step1273 p h) (sat_cons (step725 p h) (sat_cons (step721 p h) (sat_cons (step717 p h) (sat_cons (step135 p h) (sat_cons (step780 p h) (sat_cons (step782 p h) (sat_cons (step803 p h) (sat_cons (step878 p h) (sat_cons (step924 p h) (sat_cons (step1350 p h) (sat_cons (step1352 p h) (sat_cons (step740 p h) (sat_cons (step694 p h) (sat_cons (step1351 p h) (sat_cons (step692 p h) (sat_nil p))))))))))))))))))))))))))))
def c1354 : List Lit := [(1421, false), (29, true), (1449, false), (1508, true), (1477, false)]
theorem step1354 (p : Nat → Bool) (h : Constraints p) : clause p c1354 = true :=
  Snake9.LocalRup.prove_clause [c780, c803, c877, c931, c750, c757, c924, c1222, c884, c775, c808, c781] c1354 (by decide) p (sat_cons (step780 p h) (sat_cons (step803 p h) (sat_cons (step877 p h) (sat_cons (step931 p h) (sat_cons (step750 p h) (sat_cons (step757 p h) (sat_cons (step924 p h) (sat_cons (step1222 p h) (sat_cons (step884 p h) (sat_cons (step775 p h) (sat_cons (step808 p h) (sat_cons (step781 p h) (sat_nil p)))))))))))))
def c1355 : List Lit := [(1415, true), (45, false), (28, true)]
theorem step1355 (p : Nat → Bool) (h : Constraints p) : clause p c1355 = true :=
  Snake9.LocalRup.prove_clause [c1257, c1238] c1355 (by decide) p (sat_cons (step1257 p h) (sat_cons (step1238 p h) (sat_nil p)))
def c1356 : List Lit := [(1422, false), (1430, true), (1449, false), (1508, true), (47, true)]
theorem step1356 (p : Nat → Bool) (h : Constraints p) : clause p c1356 = true :=
  Snake9.LocalRup.prove_clause [c751, c758, c931, c1222, c775, c1280, c778] c1356 (by decide) p (sat_cons (step751 p h) (sat_cons (step758 p h) (sat_cons (step931 p h) (sat_cons (step1222 p h) (sat_cons (step775 p h) (sat_cons (step1280 p h) (sat_cons (step778 p h) (sat_nil p))))))))
def c1357 : List Lit := [(26, false), (29, false), (1416, true), (45, false), (28, true)]
theorem step1357 (p : Nat → Bool) (h : Constraints p) : clause p c1357 = true :=
  Snake9.LocalRup.prove_clause [c141, c138, c721, c717, c726] c1357 (by decide) p (sat_cons (step141 p h) (sat_cons (step138 p h) (sat_cons (step721 p h) (sat_cons (step717 p h) (sat_cons (step726 p h) (sat_nil p))))))
def c1358 : List Lit := [(26, true), (1459, true), (47, true), (162, true)]
theorem step1358 (p : Nat → Bool) (h : Constraints p) : clause p c1358 = true :=
  Snake9.LocalRup.prove_clause [c493, c817, c816, c333, c332, c193, c336] c1358 (by decide) p (sat_cons (step493 p h) (sat_cons (step817 p h) (sat_cons (step816 p h) (sat_cons (step333 p h) (sat_cons (step332 p h) (sat_cons (step193 p h) (sat_cons (step336 p h) (sat_nil p))))))))
def c1359 : List Lit := [(7, true), (2, true), (3, false), (37, true)]
theorem step1359 (p : Nat → Bool) (h : Constraints p) : clause p c1359 = true :=
  Snake9.LocalRup.prove_clause [c476, c14] c1359 (by decide) p (sat_cons (step476 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1360 : List Lit := [(1, true), (37, true), (7, true), (3, false)]
theorem step1360 (p : Nat → Bool) (h : Constraints p) : clause p c1360 = true :=
  Snake9.LocalRup.prove_clause [c476, c15] c1360 (by decide) p (sat_cons (step476 p h) (sat_cons (step15 p h) (sat_nil p)))
def c1361 : List Lit := [(2, true), (1, true), (3, false), (37, true)]
theorem step1361 (p : Nat → Bool) (h : Constraints p) : clause p c1361 = true :=
  Snake9.LocalRup.prove_clause [c476, c16] c1361 (by decide) p (sat_cons (step476 p h) (sat_cons (step16 p h) (sat_nil p)))
def c1362 : List Lit := [(7, true), (2, true), (1, true), (3, false)]
theorem step1362 (p : Nat → Bool) (h : Constraints p) : clause p c1362 = true :=
  Snake9.LocalRup.prove_clause [c476, c17] c1362 (by decide) p (sat_cons (step476 p h) (sat_cons (step17 p h) (sat_nil p)))
def c1363 : List Lit := [(5, false), (7, true), (41, true), (4, true)]
theorem step1363 (p : Nat → Bool) (h : Constraints p) : clause p c1363 = true :=
  Snake9.LocalRup.prove_clause [c477, c24] c1363 (by decide) p (sat_cons (step477 p h) (sat_cons (step24 p h) (sat_nil p)))
def c1364 : List Lit := [(7, true), (1, true), (41, true), (5, false)]
theorem step1364 (p : Nat → Bool) (h : Constraints p) : clause p c1364 = true :=
  Snake9.LocalRup.prove_clause [c477, c25] c1364 (by decide) p (sat_cons (step477 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1365 : List Lit := [(5, false), (1, true), (41, true), (4, true)]
theorem step1365 (p : Nat → Bool) (h : Constraints p) : clause p c1365 = true :=
  Snake9.LocalRup.prove_clause [c477, c26] c1365 (by decide) p (sat_cons (step477 p h) (sat_cons (step26 p h) (sat_nil p)))
def c1366 : List Lit := [(7, true), (1, true), (5, false), (4, true)]
theorem step1366 (p : Nat → Bool) (h : Constraints p) : clause p c1366 = true :=
  Snake9.LocalRup.prove_clause [c477, c27] c1366 (by decide) p (sat_cons (step477 p h) (sat_cons (step27 p h) (sat_nil p)))
def c1367 : List Lit := [(7, true), (2, true), (6, false)]
theorem step1367 (p : Nat → Bool) (h : Constraints p) : clause p c1367 = true :=
  Snake9.LocalRup.prove_clause [c478, c29] c1367 (by decide) p (sat_cons (step478 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1368 : List Lit := [(9, false), (10, true)]
theorem step1368 (p : Nat → Bool) (h : Constraints p) : clause p c1368 = true :=
  Snake9.LocalRup.prove_clause [c479, c36] c1368 (by decide) p (sat_cons (step479 p h) (sat_cons (step36 p h) (sat_nil p)))
def c1369 : List Lit := [(12, true), (15, true), (17, true), (14, true), (13, false)]
theorem step1369 (p : Nat → Bool) (h : Constraints p) : clause p c1369 = true :=
  Snake9.LocalRup.prove_clause [c480, c49] c1369 (by decide) p (sat_cons (step480 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1370 : List Lit := [(37, true), (22, true), (15, true), (16, false)]
theorem step1370 (p : Nat → Bool) (h : Constraints p) : clause p c1370 = true :=
  Snake9.LocalRup.prove_clause [c481, c71] c1370 (by decide) p (sat_cons (step481 p h) (sat_cons (step71 p h) (sat_nil p)))
def c1371 : List Lit := [(37, true), (22, true), (14, true), (16, false)]
theorem step1371 (p : Nat → Bool) (h : Constraints p) : clause p c1371 = true :=
  Snake9.LocalRup.prove_clause [c481, c72] c1371 (by decide) p (sat_cons (step481 p h) (sat_cons (step72 p h) (sat_nil p)))
def c1372 : List Lit := [(15, true), (37, true), (14, true), (16, false)]
theorem step1372 (p : Nat → Bool) (h : Constraints p) : clause p c1372 = true :=
  Snake9.LocalRup.prove_clause [c481, c73] c1372 (by decide) p (sat_cons (step481 p h) (sat_cons (step73 p h) (sat_nil p)))
def c1373 : List Lit := [(22, true), (15, true), (16, false), (14, true)]
theorem step1373 (p : Nat → Bool) (h : Constraints p) : clause p c1373 = true :=
  Snake9.LocalRup.prove_clause [c481, c74] c1373 (by decide) p (sat_cons (step481 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1374 : List Lit := [(22, true), (19, false), (18, true), (41, true), (17, true)]
theorem step1374 (p : Nat → Bool) (h : Constraints p) : clause p c1374 = true :=
  Snake9.LocalRup.prove_clause [c482, c98] c1374 (by decide) p (sat_cons (step482 p h) (sat_cons (step98 p h) (sat_nil p)))
def c1375 : List Lit := [(14, true), (22, true), (19, false), (18, true), (41, true)]
theorem step1375 (p : Nat → Bool) (h : Constraints p) : clause p c1375 = true :=
  Snake9.LocalRup.prove_clause [c482, c99] c1375 (by decide) p (sat_cons (step482 p h) (sat_cons (step99 p h) (sat_nil p)))
def c1376 : List Lit := [(14, true), (19, false), (17, true), (22, true), (41, true)]
theorem step1376 (p : Nat → Bool) (h : Constraints p) : clause p c1376 = true :=
  Snake9.LocalRup.prove_clause [c482, c100] c1376 (by decide) p (sat_cons (step482 p h) (sat_cons (step100 p h) (sat_nil p)))
def c1377 : List Lit := [(14, true), (19, false), (41, true), (17, true), (18, true)]
theorem step1377 (p : Nat → Bool) (h : Constraints p) : clause p c1377 = true :=
  Snake9.LocalRup.prove_clause [c482, c101] c1377 (by decide) p (sat_cons (step482 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1378 : List Lit := [(14, true), (22, true), (18, true), (19, false), (17, true)]
theorem step1378 (p : Nat → Bool) (h : Constraints p) : clause p c1378 = true :=
  Snake9.LocalRup.prove_clause [c482, c102] c1378 (by decide) p (sat_cons (step482 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1379 : List Lit := [(20, false), (22, true), (17, true), (30, true)]
theorem step1379 (p : Nat → Bool) (h : Constraints p) : clause p c1379 = true :=
  Snake9.LocalRup.prove_clause [c483, c106] c1379 (by decide) p (sat_cons (step483 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1380 : List Lit := [(20, false), (22, true), (30, true), (15, true)]
theorem step1380 (p : Nat → Bool) (h : Constraints p) : clause p c1380 = true :=
  Snake9.LocalRup.prove_clause [c483, c107] c1380 (by decide) p (sat_cons (step483 p h) (sat_cons (step107 p h) (sat_nil p)))
def c1381 : List Lit := [(20, false), (15, true), (17, true), (30, true)]
theorem step1381 (p : Nat → Bool) (h : Constraints p) : clause p c1381 = true :=
  Snake9.LocalRup.prove_clause [c483, c108] c1381 (by decide) p (sat_cons (step483 p h) (sat_cons (step108 p h) (sat_nil p)))
def c1382 : List Lit := [(15, true), (20, false), (17, true), (22, true)]
theorem step1382 (p : Nat → Bool) (h : Constraints p) : clause p c1382 = true :=
  Snake9.LocalRup.prove_clause [c483, c109] c1382 (by decide) p (sat_cons (step483 p h) (sat_cons (step109 p h) (sat_nil p)))
def c1383 : List Lit := [(24, true), (23, false), (26, true)]
theorem step1383 (p : Nat → Bool) (h : Constraints p) : clause p c1383 = true :=
  Snake9.LocalRup.prove_clause [c484, c124] c1383 (by decide) p (sat_cons (step484 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1384 : List Lit := [(12, true), (23, false), (26, true)]
theorem step1384 (p : Nat → Bool) (h : Constraints p) : clause p c1384 = true :=
  Snake9.LocalRup.prove_clause [c484, c125] c1384 (by decide) p (sat_cons (step484 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1385 : List Lit := [(24, true), (12, true), (23, false)]
theorem step1385 (p : Nat → Bool) (h : Constraints p) : clause p c1385 = true :=
  Snake9.LocalRup.prove_clause [c484, c126] c1385 (by decide) p (sat_cons (step484 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1386 : List Lit := [(91, true), (44, true), (24, true), (25, false)]
theorem step1386 (p : Nat → Bool) (h : Constraints p) : clause p c1386 = true :=
  Snake9.LocalRup.prove_clause [c485, c132] c1386 (by decide) p (sat_cons (step485 p h) (sat_cons (step132 p h) (sat_nil p)))
def c1387 : List Lit := [(91, true), (14, true), (24, true), (25, false)]
theorem step1387 (p : Nat → Bool) (h : Constraints p) : clause p c1387 = true :=
  Snake9.LocalRup.prove_clause [c485, c133] c1387 (by decide) p (sat_cons (step485 p h) (sat_cons (step133 p h) (sat_nil p)))
def c1388 : List Lit := [(44, true), (14, true), (24, true), (25, false)]
theorem step1388 (p : Nat → Bool) (h : Constraints p) : clause p c1388 = true :=
  Snake9.LocalRup.prove_clause [c485, c134] c1388 (by decide) p (sat_cons (step485 p h) (sat_cons (step134 p h) (sat_nil p)))
def c1389 : List Lit := [(31, true), (26, true), (27, false)]
theorem step1389 (p : Nat → Bool) (h : Constraints p) : clause p c1389 = true :=
  Snake9.LocalRup.prove_clause [c486, c146] c1389 (by decide) p (sat_cons (step486 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1390 : List Lit := [(24, true), (31, true), (27, false)]
theorem step1390 (p : Nat → Bool) (h : Constraints p) : clause p c1390 = true :=
  Snake9.LocalRup.prove_clause [c486, c147] c1390 (by decide) p (sat_cons (step486 p h) (sat_cons (step147 p h) (sat_nil p)))
def c1391 : List Lit := [(24, true), (27, false), (26, true)]
theorem step1391 (p : Nat → Bool) (h : Constraints p) : clause p c1391 = true :=
  Snake9.LocalRup.prove_clause [c486, c148] c1391 (by decide) p (sat_cons (step486 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1392 : List Lit := [(30, true), (28, false), (49, true)]
theorem step1392 (p : Nat → Bool) (h : Constraints p) : clause p c1392 = true :=
  Snake9.LocalRup.prove_clause [c487, c150] c1392 (by decide) p (sat_cons (step487 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1393 : List Lit := [(28, false), (17, true), (49, true)]
theorem step1393 (p : Nat → Bool) (h : Constraints p) : clause p c1393 = true :=
  Snake9.LocalRup.prove_clause [c487, c151] c1393 (by decide) p (sat_cons (step487 p h) (sat_cons (step151 p h) (sat_nil p)))
def c1394 : List Lit := [(30, true), (28, false), (17, true)]
theorem step1394 (p : Nat → Bool) (h : Constraints p) : clause p c1394 = true :=
  Snake9.LocalRup.prove_clause [c487, c152] c1394 (by decide) p (sat_cons (step487 p h) (sat_cons (step152 p h) (sat_nil p)))
def c1395 : List Lit := [(31, true), (30, true), (29, false)]
theorem step1395 (p : Nat → Bool) (h : Constraints p) : clause p c1395 = true :=
  Snake9.LocalRup.prove_clause [c488, c154] c1395 (by decide) p (sat_cons (step488 p h) (sat_cons (step154 p h) (sat_nil p)))
def c1396 : List Lit := [(31, true), (26, true), (29, false)]
theorem step1396 (p : Nat → Bool) (h : Constraints p) : clause p c1396 = true :=
  Snake9.LocalRup.prove_clause [c488, c155] c1396 (by decide) p (sat_cons (step488 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1397 : List Lit := [(26, true), (30, true), (29, false)]
theorem step1397 (p : Nat → Bool) (h : Constraints p) : clause p c1397 = true :=
  Snake9.LocalRup.prove_clause [c488, c156] c1397 (by decide) p (sat_cons (step488 p h) (sat_cons (step156 p h) (sat_nil p)))
def c1398 : List Lit := [(99, true), (34, true), (38, true), (32, false)]
theorem step1398 (p : Nat → Bool) (h : Constraints p) : clause p c1398 = true :=
  Snake9.LocalRup.prove_clause [c489, c171] c1398 (by decide) p (sat_cons (step489 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1399 : List Lit := [(99, true), (12, true), (32, false), (38, true)]
theorem step1399 (p : Nat → Bool) (h : Constraints p) : clause p c1399 = true :=
  Snake9.LocalRup.prove_clause [c489, c172] c1399 (by decide) p (sat_cons (step489 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1400 : List Lit := [(12, true), (34, true), (32, false), (38, true)]
theorem step1400 (p : Nat → Bool) (h : Constraints p) : clause p c1400 = true :=
  Snake9.LocalRup.prove_clause [c489, c173] c1400 (by decide) p (sat_cons (step489 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1401 : List Lit := [(43, true), (37, true), (36, false)]
theorem step1401 (p : Nat → Bool) (h : Constraints p) : clause p c1401 = true :=
  Snake9.LocalRup.prove_clause [c490, c205] c1401 (by decide) p (sat_cons (step490 p h) (sat_cons (step205 p h) (sat_nil p)))
def c1402 : List Lit := [(43, true), (36, false), (34, true)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true :=
  Snake9.LocalRup.prove_clause [c490, c206] c1402 (by decide) p (sat_cons (step490 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1403 : List Lit := [(37, true), (36, false), (34, true)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true :=
  Snake9.LocalRup.prove_clause [c490, c207] c1403 (by decide) p (sat_cons (step490 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1404 : List Lit := [(41, true), (49, true), (38, true), (39, false)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c491, c258] c1404 (by decide) p (sat_cons (step491 p h) (sat_cons (step258 p h) (sat_nil p)))
def c1405 : List Lit := [(49, true), (17, true), (41, true), (39, false)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.LocalRup.prove_clause [c491, c259] c1405 (by decide) p (sat_cons (step491 p h) (sat_cons (step259 p h) (sat_nil p)))
def c1406 : List Lit := [(49, true), (17, true), (39, false), (38, true)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c491, c260] c1406 (by decide) p (sat_cons (step491 p h) (sat_cons (step260 p h) (sat_nil p)))
def c1407 : List Lit := [(41, true), (17, true), (39, false), (38, true)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.LocalRup.prove_clause [c491, c261] c1407 (by decide) p (sat_cons (step491 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1408 : List Lit := [(106, true), (34, true), (42, false), (38, true)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c492, c318] c1408 (by decide) p (sat_cons (step492 p h) (sat_cons (step318 p h) (sat_nil p)))
def c1409 : List Lit := [(43, true), (34, true), (42, false), (38, true)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c492, c319] c1409 (by decide) p (sat_cons (step492 p h) (sat_cons (step319 p h) (sat_nil p)))
def c1410 : List Lit := [(34, true), (46, true), (45, false)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c493, c331] c1410 (by decide) p (sat_cons (step493 p h) (sat_cons (step331 p h) (sat_nil p)))
def c1411 : List Lit := [(26, true), (46, true), (45, false)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c493, c332] c1411 (by decide) p (sat_cons (step493 p h) (sat_cons (step332 p h) (sat_nil p)))
def c1412 : List Lit := [(26, true), (34, true), (45, false)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c493, c333] c1412 (by decide) p (sat_cons (step493 p h) (sat_cons (step333 p h) (sat_nil p)))
def c1413 : List Lit := [(52, true), (47, false), (37, true), (46, true)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c494, c339] c1413 (by decide) p (sat_cons (step494 p h) (sat_cons (step339 p h) (sat_nil p)))
def c1414 : List Lit := [(44, true), (47, false), (37, true), (46, true)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c494, c340] c1414 (by decide) p (sat_cons (step494 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1415 : List Lit := [(48, false), (49, true), (50, true)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c495, c341] c1415 (by decide) p (sat_cons (step495 p h) (sat_cons (step341 p h) (sat_nil p)))
end B112E088
