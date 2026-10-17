import B112E078Part0002
namespace B112E078
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1404 : List Lit := [(8, false), (3, true), (45, true)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c539, c36] c1404 (by decide) p (sat_cons (step539 p h) (sat_cons (step36 p h) (sat_nil p)))
def c1405 : List Lit := [(9, true), (8, false), (3, true)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.LocalRup.prove_clause [c539, c37] c1405 (by decide) p (sat_cons (step539 p h) (sat_cons (step37 p h) (sat_nil p)))
def c1406 : List Lit := [(12, true), (10, true), (11, false)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c540, c51] c1406 (by decide) p (sat_cons (step540 p h) (sat_cons (step51 p h) (sat_nil p)))
def c1407 : List Lit := [(12, true), (3, true), (11, false)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.LocalRup.prove_clause [c540, c52] c1407 (by decide) p (sat_cons (step540 p h) (sat_cons (step52 p h) (sat_nil p)))
def c1408 : List Lit := [(13, false), (18, true)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c541, c58] c1408 (by decide) p (sat_cons (step541 p h) (sat_cons (step58 p h) (sat_nil p)))
def c1409 : List Lit := [(13, false), (12, true)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c541, c59] c1409 (by decide) p (sat_cons (step541 p h) (sat_cons (step59 p h) (sat_nil p)))
def c1410 : List Lit := [(16, true), (15, true), (14, false), (54, true)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c542, c61] c1410 (by decide) p (sat_cons (step542 p h) (sat_cons (step61 p h) (sat_nil p)))
def c1411 : List Lit := [(10, true), (16, true), (14, false), (54, true)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c542, c62] c1411 (by decide) p (sat_cons (step542 p h) (sat_cons (step62 p h) (sat_nil p)))
def c1412 : List Lit := [(15, true), (10, true), (14, false), (54, true)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c542, c63] c1412 (by decide) p (sat_cons (step542 p h) (sat_cons (step63 p h) (sat_nil p)))
def c1413 : List Lit := [(15, true), (10, true), (14, false), (16, true)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c542, c64] c1413 (by decide) p (sat_cons (step542 p h) (sat_cons (step64 p h) (sat_nil p)))
def c1414 : List Lit := [(18, true), (17, false), (16, true)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c543, c80] c1414 (by decide) p (sat_cons (step543 p h) (sat_cons (step80 p h) (sat_nil p)))
def c1415 : List Lit := [(15, true), (16, true), (17, false)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c543, c82] c1415 (by decide) p (sat_cons (step543 p h) (sat_cons (step82 p h) (sat_nil p)))
def c1416 : List Lit := [(23, true), (40, true), (20, false)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c544, c95] c1416 (by decide) p (sat_cons (step544 p h) (sat_cons (step95 p h) (sat_nil p)))
def c1417 : List Lit := [(19, true), (40, true), (20, false)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c544, c96] c1417 (by decide) p (sat_cons (step544 p h) (sat_cons (step96 p h) (sat_nil p)))
def c1418 : List Lit := [(19, true), (23, true), (20, false)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c544, c97] c1418 (by decide) p (sat_cons (step544 p h) (sat_cons (step97 p h) (sat_nil p)))
def c1419 : List Lit := [(21, true), (88, true), (22, false), (28, true), (23, true)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c545, c107] c1419 (by decide) p (sat_cons (step545 p h) (sat_cons (step107 p h) (sat_nil p)))
def c1420 : List Lit := [(19, true), (88, true), (22, false), (28, true), (23, true)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c545, c108] c1420 (by decide) p (sat_cons (step545 p h) (sat_cons (step108 p h) (sat_nil p)))
def c1421 : List Lit := [(21, true), (88, true), (28, true), (22, false), (19, true)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c545, c109] c1421 (by decide) p (sat_cons (step545 p h) (sat_cons (step109 p h) (sat_nil p)))
def c1422 : List Lit := [(21, true), (19, true), (28, true), (23, true), (22, false)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c545, c110] c1422 (by decide) p (sat_cons (step545 p h) (sat_cons (step110 p h) (sat_nil p)))
def c1423 : List Lit := [(33, true), (43, true), (25, false), (91, true)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c546, c124] c1423 (by decide) p (sat_cons (step546 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1424 : List Lit := [(43, true), (24, true), (25, false), (91, true)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c546, c125] c1424 (by decide) p (sat_cons (step546 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1425 : List Lit := [(33, true), (24, true), (25, false), (91, true)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c546, c126] c1425 (by decide) p (sat_cons (step546 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1426 : List Lit := [(43, true), (33, true), (24, true), (25, false)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c546, c127] c1426 (by decide) p (sat_cons (step546 p h) (sat_cons (step127 p h) (sat_nil p)))
def c1427 : List Lit := [(34, true), (24, true), (44, true), (26, false), (28, true)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c547, c130] c1427 (by decide) p (sat_cons (step547 p h) (sat_cons (step130 p h) (sat_nil p)))
def c1428 : List Lit := [(34, true), (44, true), (28, true), (26, false), (19, true)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c547, c131] c1428 (by decide) p (sat_cons (step547 p h) (sat_cons (step131 p h) (sat_nil p)))
def c1429 : List Lit := [(44, true), (24, true), (34, true), (26, false), (19, true)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c547, c132] c1429 (by decide) p (sat_cons (step547 p h) (sat_cons (step132 p h) (sat_nil p)))
def c1430 : List Lit := [(24, true), (44, true), (26, false), (28, true), (19, true)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c547, c133] c1430 (by decide) p (sat_cons (step547 p h) (sat_cons (step133 p h) (sat_nil p)))
def c1431 : List Lit := [(28, true), (27, false), (45, true), (24, true)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c548, c136] c1431 (by decide) p (sat_cons (step548 p h) (sat_cons (step136 p h) (sat_nil p)))
def c1432 : List Lit := [(21, true), (28, true), (27, false), (45, true)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c548, c137] c1432 (by decide) p (sat_cons (step548 p h) (sat_cons (step137 p h) (sat_nil p)))
def c1433 : List Lit := [(21, true), (27, false), (24, true), (45, true)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c548, c138] c1433 (by decide) p (sat_cons (step548 p h) (sat_cons (step138 p h) (sat_nil p)))
def c1434 : List Lit := [(21, true), (24, true), (28, true), (27, false)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c548, c139] c1434 (by decide) p (sat_cons (step548 p h) (sat_cons (step139 p h) (sat_nil p)))
def c1435 : List Lit := [(31, true), (29, true), (30, false)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c549, c146] c1435 (by decide) p (sat_cons (step549 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1436 : List Lit := [(31, true), (21, true), (30, false)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c549, c147] c1436 (by decide) p (sat_cons (step549 p h) (sat_cons (step147 p h) (sat_nil p)))
def c1437 : List Lit := [(21, true), (29, true), (30, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c549, c148] c1437 (by decide) p (sat_cons (step549 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1438 : List Lit := [(23, true), (36, true), (32, false)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c550, c152] c1438 (by decide) p (sat_cons (step550 p h) (sat_cons (step152 p h) (sat_nil p)))
def c1439 : List Lit := [(23, true), (31, true), (32, false)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c550, c153] c1439 (by decide) p (sat_cons (step550 p h) (sat_cons (step153 p h) (sat_nil p)))
def c1440 : List Lit := [(36, true), (35, false), (34, true)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c551, c159] c1440 (by decide) p (sat_cons (step551 p h) (sat_cons (step159 p h) (sat_nil p)))
def c1441 : List Lit := [(36, true), (33, true), (35, false)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c551, c160] c1441 (by decide) p (sat_cons (step551 p h) (sat_cons (step160 p h) (sat_nil p)))
def c1442 : List Lit := [(33, true), (35, false), (34, true)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c551, c161] c1442 (by decide) p (sat_cons (step551 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1443 : List Lit := [(50, true), (43, true), (41, true), (40, true), (38, false)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c552, c169] c1443 (by decide) p (sat_cons (step552 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1444 : List Lit := [(43, true), (37, true), (38, false), (41, true), (50, true)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c552, c170] c1444 (by decide) p (sat_cons (step552 p h) (sat_cons (step170 p h) (sat_nil p)))
def c1445 : List Lit := [(38, false), (43, true), (50, true), (37, true), (40, true)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c552, c171] c1445 (by decide) p (sat_cons (step552 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1446 : List Lit := [(37, true), (40, true), (50, true), (38, false), (41, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c552, c172] c1446 (by decide) p (sat_cons (step552 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1447 : List Lit := [(37, true), (43, true), (38, false), (40, true), (41, true)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c552, c173] c1447 (by decide) p (sat_cons (step552 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1448 : List Lit := [(40, true), (48, true), (42, false), (41, true)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c553, c237] c1448 (by decide) p (sat_cons (step553 p h) (sat_cons (step237 p h) (sat_nil p)))
def c1449 : List Lit := [(23, true), (48, true), (42, false), (41, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c553, c238] c1449 (by decide) p (sat_cons (step553 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1450 : List Lit := [(23, true), (40, true), (42, false), (48, true)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c553, c239] c1450 (by decide) p (sat_cons (step553 p h) (sat_cons (step239 p h) (sat_nil p)))
def c1451 : List Lit := [(23, true), (40, true), (42, false), (41, true)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c553, c240] c1451 (by decide) p (sat_cons (step553 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1452 : List Lit := [(43, true), (58, true), (45, true), (46, false), (48, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c554, c298] c1452 (by decide) p (sat_cons (step554 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1453 : List Lit := [(48, true), (58, true), (45, true), (46, false), (41, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c554, c299] c1453 (by decide) p (sat_cons (step554 p h) (sat_cons (step299 p h) (sat_nil p)))
def c1454 : List Lit := [(58, true), (43, true), (41, true), (46, false), (45, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c554, c300] c1454 (by decide) p (sat_cons (step554 p h) (sat_cons (step300 p h) (sat_nil p)))
def c1455 : List Lit := [(43, true), (48, true), (41, true), (45, true), (46, false)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c554, c301] c1455 (by decide) p (sat_cons (step554 p h) (sat_cons (step301 p h) (sat_nil p)))
def c1456 : List Lit := [(51, true), (50, true), (52, false)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c555, c340] c1456 (by decide) p (sat_cons (step555 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1457 : List Lit := [(51, true), (40, true), (52, false)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c555, c341] c1457 (by decide) p (sat_cons (step555 p h) (sat_cons (step341 p h) (sat_nil p)))
def c1458 : List Lit := [(50, true), (40, true), (52, false)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c555, c342] c1458 (by decide) p (sat_cons (step555 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1459 : List Lit := [(114, true), (59, true), (53, false)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c556, c343] c1459 (by decide) p (sat_cons (step556 p h) (sat_cons (step343 p h) (sat_nil p)))
def c1460 : List Lit := [(114, true), (51, true), (53, false)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c556, c344] c1460 (by decide) p (sat_cons (step556 p h) (sat_cons (step344 p h) (sat_nil p)))
def c1461 : List Lit := [(51, true), (59, true), (53, false)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c556, c345] c1461 (by decide) p (sat_cons (step556 p h) (sat_cons (step345 p h) (sat_nil p)))
def c1462 : List Lit := [(16, true), (51, true), (44, true), (54, true), (56, false), (59, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c557, c380] c1462 (by decide) p (sat_cons (step557 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1463 : List Lit := [(16, true), (54, true), (59, true), (44, true), (56, false), (34, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c557, c381] c1463 (by decide) p (sat_cons (step557 p h) (sat_cons (step381 p h) (sat_nil p)))
def c1464 : List Lit := [(16, true), (51, true), (44, true), (54, true), (34, true), (56, false)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c557, c382] c1464 (by decide) p (sat_cons (step557 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1465 : List Lit := [(54, true), (58, true), (57, false), (59, true)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c558, c384] c1465 (by decide) p (sat_cons (step558 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1466 : List Lit := [(58, true), (59, true), (57, false), (45, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c558, c385] c1466 (by decide) p (sat_cons (step558 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1467 : List Lit := [(54, true), (59, true), (45, true), (57, false)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c558, c386] c1467 (by decide) p (sat_cons (step558 p h) (sat_cons (step386 p h) (sat_nil p)))
end B112E078
