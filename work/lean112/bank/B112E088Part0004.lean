import B112E088Part0003
namespace B112E088
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1416 : List Lit := [(48, false), (50, true), (38, true)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c495, c342] c1416 (by decide) p (sat_cons (step495 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1417 : List Lit := [(48, false), (49, true), (38, true)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c495, c343] c1417 (by decide) p (sat_cons (step495 p h) (sat_cons (step343 p h) (sat_nil p)))
def c1418 : List Lit := [(49, true), (41, true), (52, true), (51, false), (50, true)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c496, c361] c1418 (by decide) p (sat_cons (step496 p h) (sat_cons (step361 p h) (sat_nil p)))
def c1419 : List Lit := [(44, true), (52, true), (41, true), (50, true), (51, false)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c496, c362] c1419 (by decide) p (sat_cons (step496 p h) (sat_cons (step362 p h) (sat_nil p)))
def c1420 : List Lit := [(44, true), (52, true), (49, true), (51, false), (41, true)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c496, c363] c1420 (by decide) p (sat_cons (step496 p h) (sat_cons (step363 p h) (sat_nil p)))
def c1421 : List Lit := [(49, true), (44, true), (41, true), (51, false), (50, true)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c496, c364] c1421 (by decide) p (sat_cons (step496 p h) (sat_cons (step364 p h) (sat_nil p)))
def c1422 : List Lit := [(54, false), (170, true)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c1162, c366] c1422 (by decide) p (sat_cons (step1162 p h) (sat_cons (step366 p h) (sat_nil p)))
def c1423 : List Lit := [(56, false), (65, true)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c498, c368] c1423 (by decide) p (sat_cons (step498 p h) (sat_cons (step368 p h) (sat_nil p)))
def c1424 : List Lit := [(56, false), (60, true)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c498, c369] c1424 (by decide) p (sat_cons (step498 p h) (sat_cons (step369 p h) (sat_nil p)))
def c1425 : List Lit := [(57, false), (58, true)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c499, c370] c1425 (by decide) p (sat_cons (step499 p h) (sat_cons (step370 p h) (sat_nil p)))
def c1426 : List Lit := [(57, false), (54, true)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c499, c371] c1426 (by decide) p (sat_cons (step499 p h) (sat_cons (step371 p h) (sat_nil p)))
def c1427 : List Lit := [(59, false), (60, true)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c500, c375] c1427 (by decide) p (sat_cons (step500 p h) (sat_cons (step375 p h) (sat_nil p)))
def c1428 : List Lit := [(59, false), (58, true)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c500, c376] c1428 (by decide) p (sat_cons (step500 p h) (sat_cons (step376 p h) (sat_nil p)))
def c1429 : List Lit := [(62, true), (61, false), (53, true), (83, true)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c501, c381] c1429 (by decide) p (sat_cons (step501 p h) (sat_cons (step381 p h) (sat_nil p)))
def c1430 : List Lit := [(63, false), (65, true)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c502, c383] c1430 (by decide) p (sat_cons (step502 p h) (sat_cons (step383 p h) (sat_nil p)))
def c1431 : List Lit := [(63, false), (62, true)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c502, c384] c1431 (by decide) p (sat_cons (step502 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1432 : List Lit := [(69, false), (72, true)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c504, c394] c1432 (by decide) p (sat_cons (step504 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1433 : List Lit := [(69, false), (68, true)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c504, c395] c1433 (by decide) p (sat_cons (step504 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1434 : List Lit := [(71, false), (67, true)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c505, c399] c1434 (by decide) p (sat_cons (step505 p h) (sat_cons (step399 p h) (sat_nil p)))
def c1435 : List Lit := [(75, false), (68, true)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c506, c402] c1435 (by decide) p (sat_cons (step506 p h) (sat_cons (step402 p h) (sat_nil p)))
def c1436 : List Lit := [(78, false), (70, true)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c507, c403] c1436 (by decide) p (sat_cons (step507 p h) (sat_cons (step403 p h) (sat_nil p)))
def c1437 : List Lit := [(85, false), (89, true)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c508, c415] c1437 (by decide) p (sat_cons (step508 p h) (sat_cons (step415 p h) (sat_nil p)))
def c1438 : List Lit := [(85, false), (84, true)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c508, c416] c1438 (by decide) p (sat_cons (step508 p h) (sat_cons (step416 p h) (sat_nil p)))
def c1439 : List Lit := [(86, true), (83, true), (87, false)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c509, c422] c1439 (by decide) p (sat_cons (step509 p h) (sat_cons (step422 p h) (sat_nil p)))
def c1440 : List Lit := [(86, true), (87, false), (17, true)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c509, c423] c1440 (by decide) p (sat_cons (step509 p h) (sat_cons (step423 p h) (sat_nil p)))
def c1441 : List Lit := [(83, true), (87, false), (17, true)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c509, c424] c1441 (by decide) p (sat_cons (step509 p h) (sat_cons (step424 p h) (sat_nil p)))
def c1442 : List Lit := [(86, true), (84, true), (88, false), (89, true)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c510, c425] c1442 (by decide) p (sat_cons (step510 p h) (sat_cons (step425 p h) (sat_nil p)))
def c1443 : List Lit := [(94, false), (98, true), (93, true)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c511, c433] c1443 (by decide) p (sat_cons (step511 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1444 : List Lit := [(91, true), (94, false), (93, true)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c511, c435] c1444 (by decide) p (sat_cons (step511 p h) (sat_cons (step435 p h) (sat_nil p)))
def c1445 : List Lit := [(95, false), (96, true)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c512, c436] c1445 (by decide) p (sat_cons (step512 p h) (sat_cons (step436 p h) (sat_nil p)))
def c1446 : List Lit := [(95, false), (86, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c512, c437] c1446 (by decide) p (sat_cons (step512 p h) (sat_cons (step437 p h) (sat_nil p)))
def c1447 : List Lit := [(91, true), (97, false), (98, true)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c513, c440] c1447 (by decide) p (sat_cons (step513 p h) (sat_cons (step440 p h) (sat_nil p)))
def c1448 : List Lit := [(102, true), (103, false), (37, true)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c514, c453] c1448 (by decide) p (sat_cons (step514 p h) (sat_cons (step453 p h) (sat_nil p)))
def c1449 : List Lit := [(101, true), (103, false), (37, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c514, c454] c1449 (by decide) p (sat_cons (step514 p h) (sat_cons (step454 p h) (sat_nil p)))
def c1450 : List Lit := [(101, true), (104, true), (105, false)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c515, c457] c1450 (by decide) p (sat_cons (step515 p h) (sat_cons (step457 p h) (sat_nil p)))
def c1451 : List Lit := [(104, true), (105, false), (41, true)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c515, c458] c1451 (by decide) p (sat_cons (step515 p h) (sat_cons (step458 p h) (sat_nil p)))
def c1452 : List Lit := [(101, true), (105, false), (41, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c515, c459] c1452 (by decide) p (sat_cons (step515 p h) (sat_cons (step459 p h) (sat_nil p)))
def c1453 : List Lit := [(114, true), (107, false), (106, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c516, c463] c1453 (by decide) p (sat_cons (step516 p h) (sat_cons (step463 p h) (sat_nil p)))
def c1454 : List Lit := [(102, true), (107, false), (114, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c516, c464] c1454 (by decide) p (sat_cons (step516 p h) (sat_cons (step464 p h) (sat_nil p)))
def c1455 : List Lit := [(110, true), (108, false), (109, true)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c517, c465] c1455 (by decide) p (sat_cons (step517 p h) (sat_cons (step465 p h) (sat_nil p)))
def c1456 : List Lit := [(110, true), (99, true), (108, false)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c517, c466] c1456 (by decide) p (sat_cons (step517 p h) (sat_cons (step466 p h) (sat_nil p)))
def c1457 : List Lit := [(99, true), (108, false), (109, true)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c517, c467] c1457 (by decide) p (sat_cons (step517 p h) (sat_cons (step467 p h) (sat_nil p)))
def c1458 : List Lit := [(111, false), (110, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c518, c471] c1458 (by decide) p (sat_cons (step518 p h) (sat_cons (step471 p h) (sat_nil p)))
def c1459 : List Lit := [(114, true), (112, false), (49, true)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c519, c472] c1459 (by decide) p (sat_cons (step519 p h) (sat_cons (step472 p h) (sat_nil p)))
def c1460 : List Lit := [(117, false), (233, false)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c1182, c523] c1460 (by decide) p (sat_cons (step1182 p h) (sat_cons (step523 p h) (sat_nil p)))
def c1461 : List Lit := [(235, false), (241, false)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c1178, c530] c1461 (by decide) p (sat_cons (step1178 p h) (sat_cons (step530 p h) (sat_nil p)))
def c1462 : List Lit := [(249, false), (251, false)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c1181, c540] c1462 (by decide) p (sat_cons (step1181 p h) (sat_cons (step540 p h) (sat_nil p)))
def c1463 : List Lit := [(243, false), (255, false)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c1174, c547] c1463 (by decide) p (sat_cons (step1174 p h) (sat_cons (step547 p h) (sat_nil p)))
def c1464 : List Lit := [(257, false), (283, false)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c1169, c565] c1464 (by decide) p (sat_cons (step1169 p h) (sat_cons (step565 p h) (sat_nil p)))
def c1465 : List Lit := [(146, false), (287, false)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c1180, c570] c1465 (by decide) p (sat_cons (step1180 p h) (sat_cons (step570 p h) (sat_nil p)))
def c1466 : List Lit := [(169, false), (170, false)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c1183, c597] c1466 (by decide) p (sat_cons (step1183 p h) (sat_cons (step597 p h) (sat_nil p)))
def c1467 : List Lit := [(329, false), (335, false)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c1175, c604] c1467 (by decide) p (sat_cons (step1175 p h) (sat_cons (step604 p h) (sat_nil p)))
def c1468 : List Lit := [(311, false), (339, false)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c1168, c613] c1468 (by decide) p (sat_cons (step1168 p h) (sat_cons (step613 p h) (sat_nil p)))
def c1469 : List Lit := [(285, false), (341, false)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c1165, c618] c1469 (by decide) p (sat_cons (step1165 p h) (sat_cons (step618 p h) (sat_nil p)))
def c1470 : List Lit := [(369, false), (397, false)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c1167, c644] c1470 (by decide) p (sat_cons (step1167 p h) (sat_cons (step644 p h) (sat_nil p)))
def c1471 : List Lit := [(411, false), (423, false)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c1170, c660] c1471 (by decide) p (sat_cons (step1170 p h) (sat_cons (step660 p h) (sat_nil p)))
def c1472 : List Lit := [(425, false), (453, false)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c1166, c672] c1472 (by decide) p (sat_cons (step1166 p h) (sat_cons (step672 p h) (sat_nil p)))
def c1473 : List Lit := [(399, false), (455, false)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c1164, c677] c1473 (by decide) p (sat_cons (step1164 p h) (sat_cons (step677 p h) (sat_nil p)))
def c1474 : List Lit := [(343, false), (457, false)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c682, c680] c1474 (by decide) p (sat_cons (step682 p h) (sat_cons (step680 p h) (sat_nil p)))
def c1475 : List Lit := [(1493, false), (1428, false)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c1315, c927] c1475 (by decide) p (sat_cons (step1315 p h) (sat_cons (step927 p h) (sat_nil p)))
def c1476 : List Lit := [(1491, false), (1430, false)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c1315, c938] c1476 (by decide) p (sat_cons (step1315 p h) (sat_cons (step938 p h) (sat_nil p)))
def c1477 : List Lit := [(1520, false), (1533, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c1219, c966] c1477 (by decide) p (sat_cons (step1219 p h) (sat_cons (step966 p h) (sat_nil p)))
def c1478 : List Lit := [(1564, true), (1554, false)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c1220, c996] c1478 (by decide) p (sat_cons (step1220 p h) (sat_cons (step996 p h) (sat_nil p)))
def c1479 : List Lit := [(1564, true), (1553, false)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c1295, c998] c1479 (by decide) p (sat_cons (step1295 p h) (sat_cons (step998 p h) (sat_nil p)))
end B112E088
