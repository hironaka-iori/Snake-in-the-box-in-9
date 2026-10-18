import B112E213Part0003
namespace B112E213
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1460 : List Lit := [(28, true), (29, true), (34, true), (30, false)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c523, c200] c1460 (by decide) p (sat_cons (step523 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1461 : List Lit := [(18, true), (29, true), (30, false), (34, true)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c523, c201] c1461 (by decide) p (sat_cons (step523 p h) (sat_cons (step201 p h) (sat_nil p)))
def c1462 : List Lit := [(28, true), (34, true), (18, true), (30, false)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c523, c202] c1462 (by decide) p (sat_cons (step523 p h) (sat_cons (step202 p h) (sat_nil p)))
def c1463 : List Lit := [(18, true), (28, true), (30, false), (29, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c523, c203] c1463 (by decide) p (sat_cons (step523 p h) (sat_cons (step203 p h) (sat_nil p)))
def c1464 : List Lit := [(31, true), (36, true), (35, false), (32, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c524, c249] c1464 (by decide) p (sat_cons (step524 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1465 : List Lit := [(36, true), (23, true), (32, true), (35, false)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c524, c250] c1465 (by decide) p (sat_cons (step524 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1466 : List Lit := [(31, true), (23, true), (35, false), (32, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c524, c251] c1466 (by decide) p (sat_cons (step524 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1467 : List Lit := [(36, true), (34, true), (37, false)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c525, c257] c1467 (by decide) p (sat_cons (step525 p h) (sat_cons (step257 p h) (sat_nil p)))
def c1468 : List Lit := [(36, true), (26, true), (37, false)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c525, c258] c1468 (by decide) p (sat_cons (step525 p h) (sat_cons (step258 p h) (sat_nil p)))
def c1469 : List Lit := [(34, true), (26, true), (37, false)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c525, c259] c1469 (by decide) p (sat_cons (step525 p h) (sat_cons (step259 p h) (sat_nil p)))
def c1470 : List Lit := [(41, true), (48, true), (40, false)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c526, c274] c1470 (by decide) p (sat_cons (step526 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1471 : List Lit := [(38, true), (40, false), (48, true)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c526, c275] c1471 (by decide) p (sat_cons (step526 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1472 : List Lit := [(41, true), (38, true), (40, false)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c526, c276] c1472 (by decide) p (sat_cons (step526 p h) (sat_cons (step276 p h) (sat_nil p)))
def c1473 : List Lit := [(45, true), (44, false), (53, true)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c527, c290] c1473 (by decide) p (sat_cons (step527 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1474 : List Lit := [(43, true), (44, false), (53, true)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c527, c291] c1474 (by decide) p (sat_cons (step527 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1475 : List Lit := [(45, true), (43, true), (44, false)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c527, c292] c1475 (by decide) p (sat_cons (step527 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1476 : List Lit := [(38, true), (50, true), (46, false), (48, true)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c528, c296] c1476 (by decide) p (sat_cons (step528 p h) (sat_cons (step296 p h) (sat_nil p)))
def c1477 : List Lit := [(47, true), (38, true), (46, false), (48, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c528, c297] c1477 (by decide) p (sat_cons (step528 p h) (sat_cons (step297 p h) (sat_nil p)))
def c1478 : List Lit := [(47, true), (48, true), (49, false)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c529, c334] c1478 (by decide) p (sat_cons (step529 p h) (sat_cons (step334 p h) (sat_nil p)))
def c1479 : List Lit := [(41, true), (48, true), (49, false)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c529, c335] c1479 (by decide) p (sat_cons (step529 p h) (sat_cons (step335 p h) (sat_nil p)))
def c1480 : List Lit := [(41, true), (47, true), (49, false)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c529, c336] c1480 (by decide) p (sat_cons (step529 p h) (sat_cons (step336 p h) (sat_nil p)))
def c1481 : List Lit := [(51, false), (48, true), (71, true)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c530, c339] c1481 (by decide) p (sat_cons (step530 p h) (sat_cons (step339 p h) (sat_nil p)))
def c1482 : List Lit := [(54, true), (48, true), (51, false)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c530, c340] c1482 (by decide) p (sat_cons (step530 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1483 : List Lit := [(54, true), (52, false), (53, true)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c531, c342] c1483 (by decide) p (sat_cons (step531 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1484 : List Lit := [(54, true), (50, true), (52, false)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c531, c343] c1484 (by decide) p (sat_cons (step531 p h) (sat_cons (step343 p h) (sat_nil p)))
def c1485 : List Lit := [(50, true), (52, false), (53, true)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c531, c344] c1485 (by decide) p (sat_cons (step531 p h) (sat_cons (step344 p h) (sat_nil p)))
def c1486 : List Lit := [(45, true), (55, false), (53, true)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c532, c367] c1486 (by decide) p (sat_cons (step532 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1487 : List Lit := [(58, true), (61, true), (56, false), (38, true), (57, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c533, c368] c1487 (by decide) p (sat_cons (step533 p h) (sat_cons (step368 p h) (sat_nil p)))
def c1488 : List Lit := [(58, true), (61, true), (57, true), (15, true), (56, false)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c533, c369] c1488 (by decide) p (sat_cons (step533 p h) (sat_cons (step369 p h) (sat_nil p)))
def c1489 : List Lit := [(58, true), (61, true), (38, true), (15, true), (56, false)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c533, c370] c1489 (by decide) p (sat_cons (step533 p h) (sat_cons (step370 p h) (sat_nil p)))
def c1490 : List Lit := [(61, true), (57, true), (15, true), (56, false), (38, true)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c533, c371] c1490 (by decide) p (sat_cons (step533 p h) (sat_cons (step371 p h) (sat_nil p)))
def c1491 : List Lit := [(58, true), (57, true), (56, false), (38, true), (15, true)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c533, c372] c1491 (by decide) p (sat_cons (step533 p h) (sat_cons (step372 p h) (sat_nil p)))
def c1492 : List Lit := [(58, true), (68, true), (59, false), (65, true)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c534, c385] c1492 (by decide) p (sat_cons (step534 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1493 : List Lit := [(58, true), (60, true), (59, false), (65, true)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c534, c386] c1493 (by decide) p (sat_cons (step534 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1494 : List Lit := [(63, true), (70, true), (61, true), (57, true), (62, false)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c535, c399] c1494 (by decide) p (sat_cons (step535 p h) (sat_cons (step399 p h) (sat_nil p)))
def c1495 : List Lit := [(63, true), (43, true), (70, true), (61, true), (62, false)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c535, c400] c1495 (by decide) p (sat_cons (step535 p h) (sat_cons (step400 p h) (sat_nil p)))
def c1496 : List Lit := [(70, true), (43, true), (57, true), (61, true), (62, false)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c535, c401] c1496 (by decide) p (sat_cons (step535 p h) (sat_cons (step401 p h) (sat_nil p)))
def c1497 : List Lit := [(58, true), (61, true), (65, true), (64, false)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c536, c407] c1497 (by decide) p (sat_cons (step536 p h) (sat_cons (step407 p h) (sat_nil p)))
def c1498 : List Lit := [(65, true), (61, true), (23, true), (64, false)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c536, c408] c1498 (by decide) p (sat_cons (step536 p h) (sat_cons (step408 p h) (sat_nil p)))
def c1499 : List Lit := [(58, true), (65, true), (23, true), (64, false)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c536, c409] c1499 (by decide) p (sat_cons (step536 p h) (sat_cons (step409 p h) (sat_nil p)))
def c1500 : List Lit := [(61, true), (58, true), (23, true), (64, false)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c536, c410] c1500 (by decide) p (sat_cons (step536 p h) (sat_cons (step410 p h) (sat_nil p)))
def c1501 : List Lit := [(68, true), (66, false), (29, true), (71, true)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c537, c418] c1501 (by decide) p (sat_cons (step537 p h) (sat_cons (step418 p h) (sat_nil p)))
def c1502 : List Lit := [(66, false), (71, true), (48, true), (29, true)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c537, c419] c1502 (by decide) p (sat_cons (step537 p h) (sat_cons (step419 p h) (sat_nil p)))
def c1503 : List Lit := [(68, true), (66, false), (48, true), (29, true)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c537, c420] c1503 (by decide) p (sat_cons (step537 p h) (sat_cons (step420 p h) (sat_nil p)))
def c1504 : List Lit := [(68, true), (67, true), (69, false)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c538, c423] c1504 (by decide) p (sat_cons (step538 p h) (sat_cons (step423 p h) (sat_nil p)))
def c1505 : List Lit := [(68, true), (60, true), (69, false)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c538, c424] c1505 (by decide) p (sat_cons (step538 p h) (sat_cons (step424 p h) (sat_nil p)))
def c1506 : List Lit := [(63, true), (70, true), (71, true), (72, false)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c539, c433] c1506 (by decide) p (sat_cons (step539 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1507 : List Lit := [(70, true), (72, false), (71, true), (34, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c539, c434] c1507 (by decide) p (sat_cons (step539 p h) (sat_cons (step434 p h) (sat_nil p)))
def c1508 : List Lit := [(63, true), (72, false), (34, true), (71, true)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c539, c435] c1508 (by decide) p (sat_cons (step539 p h) (sat_cons (step435 p h) (sat_nil p)))
def c1509 : List Lit := [(63, true), (70, true), (72, false), (34, true)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c539, c436] c1509 (by decide) p (sat_cons (step539 p h) (sat_cons (step436 p h) (sat_nil p)))
def c1510 : List Lit := [(70, true), (73, false), (53, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c540, c438] c1510 (by decide) p (sat_cons (step540 p h) (sat_cons (step438 p h) (sat_nil p)))
def c1511 : List Lit := [(15, true), (78, true), (74, false)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c541, c442] c1511 (by decide) p (sat_cons (step541 p h) (sat_cons (step442 p h) (sat_nil p)))
def c1512 : List Lit := [(75, true), (15, true), (74, false)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c541, c443] c1512 (by decide) p (sat_cons (step541 p h) (sat_cons (step443 p h) (sat_nil p)))
def c1513 : List Lit := [(82, true), (86, true), (76, false)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c542, c446] c1513 (by decide) p (sat_cons (step542 p h) (sat_cons (step446 p h) (sat_nil p)))
def c1514 : List Lit := [(77, true), (86, true), (76, false)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c542, c447] c1514 (by decide) p (sat_cons (step542 p h) (sat_cons (step447 p h) (sat_nil p)))
def c1515 : List Lit := [(88, true), (80, true), (79, false), (75, true)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c543, c454] c1515 (by decide) p (sat_cons (step543 p h) (sat_cons (step454 p h) (sat_nil p)))
def c1516 : List Lit := [(82, true), (78, true), (81, false)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c544, c456] c1516 (by decide) p (sat_cons (step544 p h) (sat_cons (step456 p h) (sat_nil p)))
def c1517 : List Lit := [(82, true), (23, true), (81, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c544, c457] c1517 (by decide) p (sat_cons (step544 p h) (sat_cons (step457 p h) (sat_nil p)))
def c1518 : List Lit := [(78, true), (23, true), (81, false)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c544, c458] c1518 (by decide) p (sat_cons (step544 p h) (sat_cons (step458 p h) (sat_nil p)))
def c1519 : List Lit := [(86, true), (89, true), (83, false)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c545, c461] c1519 (by decide) p (sat_cons (step545 p h) (sat_cons (step461 p h) (sat_nil p)))
def c1520 : List Lit := [(89, true), (29, true), (83, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c545, c462] c1520 (by decide) p (sat_cons (step545 p h) (sat_cons (step462 p h) (sat_nil p)))
def c1521 : List Lit := [(86, true), (29, true), (83, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c545, c463] c1521 (by decide) p (sat_cons (step545 p h) (sat_cons (step463 p h) (sat_nil p)))
def c1522 : List Lit := [(85, true), (86, true), (84, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c546, c464] c1522 (by decide) p (sat_cons (step546 p h) (sat_cons (step464 p h) (sat_nil p)))
def c1523 : List Lit := [(31, true), (86, true), (84, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c546, c465] c1523 (by decide) p (sat_cons (step546 p h) (sat_cons (step465 p h) (sat_nil p)))
end B112E213
