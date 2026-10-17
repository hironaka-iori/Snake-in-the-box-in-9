import B112E203Part0002
namespace B112E203
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1465 : List Lit := [(60, true), (45, true), (49, true), (50, true), (48, false)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c540, c199] c1465 (by decide) p (sat_cons (step540 p h) (sat_cons (step199 p h) (sat_nil p)))
def c1466 : List Lit := [(48, false), (50, true), (45, true), (55, true), (49, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c540, c200] c1466 (by decide) p (sat_cons (step540 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1467 : List Lit := [(51, false), (49, true), (62, true), (57, true), (50, true), (89, true)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c541, c251] c1467 (by decide) p (sat_cons (step541 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1468 : List Lit := [(55, true), (53, true), (57, true), (56, false)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c542, c289] c1468 (by decide) p (sat_cons (step542 p h) (sat_cons (step289 p h) (sat_nil p)))
def c1469 : List Lit := [(50, true), (55, true), (56, false), (57, true)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c542, c290] c1469 (by decide) p (sat_cons (step542 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1470 : List Lit := [(53, true), (50, true), (56, false), (57, true)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c542, c291] c1470 (by decide) p (sat_cons (step542 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1471 : List Lit := [(50, true), (55, true), (53, true), (56, false)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c542, c292] c1471 (by decide) p (sat_cons (step542 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1472 : List Lit := [(60, true), (58, true), (62, true), (61, false)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c543, c366] c1472 (by decide) p (sat_cons (step543 p h) (sat_cons (step366 p h) (sat_nil p)))
def c1473 : List Lit := [(49, true), (58, true), (62, true), (61, false)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c543, c367] c1473 (by decide) p (sat_cons (step543 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1474 : List Lit := [(60, true), (49, true), (58, true), (61, false)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c543, c368] c1474 (by decide) p (sat_cons (step543 p h) (sat_cons (step368 p h) (sat_nil p)))
def c1475 : List Lit := [(66, true), (63, true), (64, false)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c544, c376] c1475 (by decide) p (sat_cons (step544 p h) (sat_cons (step376 p h) (sat_nil p)))
def c1476 : List Lit := [(66, true), (58, true), (64, false)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c544, c377] c1476 (by decide) p (sat_cons (step544 p h) (sat_cons (step377 p h) (sat_nil p)))
def c1477 : List Lit := [(63, true), (58, true), (64, false)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c544, c378] c1477 (by decide) p (sat_cons (step544 p h) (sat_cons (step378 p h) (sat_nil p)))
def c1478 : List Lit := [(82, true), (53, true), (100, true), (65, false), (66, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c545, c380] c1478 (by decide) p (sat_cons (step545 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1479 : List Lit := [(82, true), (100, true), (53, true), (65, false), (63, true)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c545, c381] c1479 (by decide) p (sat_cons (step545 p h) (sat_cons (step381 p h) (sat_nil p)))
def c1480 : List Lit := [(66, true), (62, true), (67, false)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c546, c392] c1480 (by decide) p (sat_cons (step546 p h) (sat_cons (step392 p h) (sat_nil p)))
def c1481 : List Lit := [(67, false), (66, true), (57, true)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c546, c393] c1481 (by decide) p (sat_cons (step546 p h) (sat_cons (step393 p h) (sat_nil p)))
def c1482 : List Lit := [(67, false), (62, true), (57, true)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c546, c394] c1482 (by decide) p (sat_cons (step546 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1483 : List Lit := [(69, true), (72, true), (68, false)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c547, c395] c1483 (by decide) p (sat_cons (step547 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1484 : List Lit := [(72, true), (45, true), (68, false)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c547, c396] c1484 (by decide) p (sat_cons (step547 p h) (sat_cons (step396 p h) (sat_nil p)))
def c1485 : List Lit := [(69, true), (45, true), (68, false)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c547, c397] c1485 (by decide) p (sat_cons (step547 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1486 : List Lit := [(71, true), (70, false), (81, true)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c548, c404] c1486 (by decide) p (sat_cons (step548 p h) (sat_cons (step404 p h) (sat_nil p)))
def c1487 : List Lit := [(70, false), (50, true), (81, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c548, c405] c1487 (by decide) p (sat_cons (step548 p h) (sat_cons (step405 p h) (sat_nil p)))
def c1488 : List Lit := [(71, true), (70, false), (50, true)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c548, c406] c1488 (by decide) p (sat_cons (step548 p h) (sat_cons (step406 p h) (sat_nil p)))
def c1489 : List Lit := [(69, true), (73, false), (75, true), (74, true)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c549, c414] c1489 (by decide) p (sat_cons (step549 p h) (sat_cons (step414 p h) (sat_nil p)))
def c1490 : List Lit := [(69, true), (73, false), (72, true), (74, true)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c549, c415] c1490 (by decide) p (sat_cons (step549 p h) (sat_cons (step415 p h) (sat_nil p)))
def c1491 : List Lit := [(74, true), (75, true), (76, false), (57, true)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c550, c424] c1491 (by decide) p (sat_cons (step550 p h) (sat_cons (step424 p h) (sat_nil p)))
def c1492 : List Lit := [(75, true), (76, false), (57, true), (71, true)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c550, c425] c1492 (by decide) p (sat_cons (step550 p h) (sat_cons (step425 p h) (sat_nil p)))
def c1493 : List Lit := [(76, false), (71, true), (57, true), (74, true)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c550, c426] c1493 (by decide) p (sat_cons (step550 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1494 : List Lit := [(79, true), (69, true), (77, false)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c551, c428] c1494 (by decide) p (sat_cons (step551 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1495 : List Lit := [(79, true), (77, false), (58, true)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c551, c429] c1495 (by decide) p (sat_cons (step551 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1496 : List Lit := [(69, true), (77, false), (58, true)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c551, c430] c1496 (by decide) p (sat_cons (step551 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1497 : List Lit := [(78, false), (82, true), (81, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c552, c432] c1497 (by decide) p (sat_cons (step552 p h) (sat_cons (step432 p h) (sat_nil p)))
def c1498 : List Lit := [(79, true), (78, false), (81, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c552, c433] c1498 (by decide) p (sat_cons (step552 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1499 : List Lit := [(80, false), (81, true), (60, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c553, c436] c1499 (by decide) p (sat_cons (step553 p h) (sat_cons (step436 p h) (sat_nil p)))
def c1500 : List Lit := [(84, false), (83, true)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c554, c446] c1500 (by decide) p (sat_cons (step554 p h) (sat_cons (step446 p h) (sat_nil p)))
def c1501 : List Lit := [(84, false), (75, true)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c554, c447] c1501 (by decide) p (sat_cons (step554 p h) (sat_cons (step447 p h) (sat_nil p)))
def c1502 : List Lit := [(83, true), (85, false), (81, true)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c555, c449] c1502 (by decide) p (sat_cons (step555 p h) (sat_cons (step449 p h) (sat_nil p)))
def c1503 : List Lit := [(85, false), (82, true), (81, true)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c555, c450] c1503 (by decide) p (sat_cons (step555 p h) (sat_cons (step450 p h) (sat_nil p)))
def c1504 : List Lit := [(95, true), (86, false), (90, true), (45, true), (87, true)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c556, c451] c1504 (by decide) p (sat_cons (step556 p h) (sat_cons (step451 p h) (sat_nil p)))
def c1505 : List Lit := [(95, true), (15, true), (86, false), (90, true), (45, true)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c556, c452] c1505 (by decide) p (sat_cons (step556 p h) (sat_cons (step452 p h) (sat_nil p)))
def c1506 : List Lit := [(95, true), (15, true), (86, false), (87, true), (45, true)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c556, c453] c1506 (by decide) p (sat_cons (step556 p h) (sat_cons (step453 p h) (sat_nil p)))
def c1507 : List Lit := [(15, true), (86, false), (45, true), (90, true), (87, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c556, c454] c1507 (by decide) p (sat_cons (step556 p h) (sat_cons (step454 p h) (sat_nil p)))
def c1508 : List Lit := [(99, true), (50, true), (89, true), (88, false)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c557, c459] c1508 (by decide) p (sat_cons (step557 p h) (sat_cons (step459 p h) (sat_nil p)))
def c1509 : List Lit := [(99, true), (50, true), (88, false), (18, true)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c557, c460] c1509 (by decide) p (sat_cons (step557 p h) (sat_cons (step460 p h) (sat_nil p)))
def c1510 : List Lit := [(91, false), (93, true), (87, true), (92, true), (90, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c558, c468] c1510 (by decide) p (sat_cons (step558 p h) (sat_cons (step468 p h) (sat_nil p)))
def c1511 : List Lit := [(94, false), (93, true), (89, true), (57, true)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c559, c472] c1511 (by decide) p (sat_cons (step559 p h) (sat_cons (step472 p h) (sat_nil p)))
def c1512 : List Lit := [(94, false), (92, true), (57, true), (89, true)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c559, c473] c1512 (by decide) p (sat_cons (step559 p h) (sat_cons (step473 p h) (sat_nil p)))
def c1513 : List Lit := [(98, true), (96, false), (95, true), (87, true)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c560, c477] c1513 (by decide) p (sat_cons (step560 p h) (sat_cons (step477 p h) (sat_nil p)))
def c1514 : List Lit := [(96, false), (98, true), (95, true), (58, true)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c560, c478] c1514 (by decide) p (sat_cons (step560 p h) (sat_cons (step478 p h) (sat_nil p)))
def c1515 : List Lit := [(96, false), (98, true), (87, true), (58, true)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c560, c479] c1515 (by decide) p (sat_cons (step560 p h) (sat_cons (step479 p h) (sat_nil p)))
def c1516 : List Lit := [(96, false), (95, true), (87, true), (58, true)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c560, c480] c1516 (by decide) p (sat_cons (step560 p h) (sat_cons (step480 p h) (sat_nil p)))
def c1517 : List Lit := [(95, true), (97, false), (99, true), (100, true)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c561, c481] c1517 (by decide) p (sat_cons (step561 p h) (sat_cons (step481 p h) (sat_nil p)))
def c1518 : List Lit := [(95, true), (98, true), (97, false), (99, true)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c561, c482] c1518 (by decide) p (sat_cons (step561 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1519 : List Lit := [(93, true), (31, true), (102, false)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c562, c489] c1519 (by decide) p (sat_cons (step562 p h) (sat_cons (step489 p h) (sat_nil p)))
def c1520 : List Lit := [(103, false), (101, true), (100, true)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c563, c491] c1520 (by decide) p (sat_cons (step563 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1521 : List Lit := [(103, false), (101, true), (99, true)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c563, c492] c1521 (by decide) p (sat_cons (step563 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1522 : List Lit := [(99, true), (103, false), (100, true)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c563, c493] c1522 (by decide) p (sat_cons (step563 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1523 : List Lit := [(113, true), (43, true), (106, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c564, c497] c1523 (by decide) p (sat_cons (step564 p h) (sat_cons (step497 p h) (sat_nil p)))
def c1524 : List Lit := [(106, false), (107, true), (43, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c564, c498] c1524 (by decide) p (sat_cons (step564 p h) (sat_cons (step498 p h) (sat_nil p)))
def c1525 : List Lit := [(109, false), (108, true)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c565, c503] c1525 (by decide) p (sat_cons (step565 p h) (sat_cons (step503 p h) (sat_nil p)))
def c1526 : List Lit := [(109, false), (107, true)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c565, c504] c1526 (by decide) p (sat_cons (step565 p h) (sat_cons (step504 p h) (sat_nil p)))
def c1527 : List Lit := [(110, false), (112, true)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c566, c505] c1527 (by decide) p (sat_cons (step566 p h) (sat_cons (step505 p h) (sat_nil p)))
def c1528 : List Lit := [(113, true), (114, true), (111, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c567, c507] c1528 (by decide) p (sat_cons (step567 p h) (sat_cons (step507 p h) (sat_nil p)))
end B112E203
