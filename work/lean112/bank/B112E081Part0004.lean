import B112E081Part0003
namespace B112E081
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1450 : List Lit := [(72, true), (63, true), (51, true), (52, false), (58, true), (50, true)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c554, c260] c1450 (by decide) p (sat_cons (step554 p h) (sat_cons (step260 p h) (sat_nil p)))
def c1451 : List Lit := [(56, true), (54, true), (57, false), (58, true)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c555, c301] c1451 (by decide) p (sat_cons (step555 p h) (sat_cons (step301 p h) (sat_nil p)))
def c1452 : List Lit := [(56, true), (51, true), (58, true), (57, false)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c555, c302] c1452 (by decide) p (sat_cons (step555 p h) (sat_cons (step302 p h) (sat_nil p)))
def c1453 : List Lit := [(51, true), (54, true), (57, false), (58, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c555, c303] c1453 (by decide) p (sat_cons (step555 p h) (sat_cons (step303 p h) (sat_nil p)))
def c1454 : List Lit := [(56, true), (51, true), (57, false), (54, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c555, c304] c1454 (by decide) p (sat_cons (step555 p h) (sat_cons (step304 p h) (sat_nil p)))
def c1455 : List Lit := [(61, true), (62, false), (59, true), (63, true)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c556, c384] c1455 (by decide) p (sat_cons (step556 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1456 : List Lit := [(62, false), (59, true), (50, true), (63, true)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c556, c385] c1456 (by decide) p (sat_cons (step556 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1457 : List Lit := [(61, true), (62, false), (50, true), (59, true)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c556, c386] c1457 (by decide) p (sat_cons (step556 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1458 : List Lit := [(64, true), (67, true), (65, false)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c557, c395] c1458 (by decide) p (sat_cons (step557 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1459 : List Lit := [(65, false), (67, true), (59, true)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c557, c396] c1459 (by decide) p (sat_cons (step557 p h) (sat_cons (step396 p h) (sat_nil p)))
def c1460 : List Lit := [(64, true), (65, false), (59, true)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c557, c397] c1460 (by decide) p (sat_cons (step557 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1461 : List Lit := [(83, true), (66, false), (54, true), (67, true), (100, true)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c558, c400] c1461 (by decide) p (sat_cons (step558 p h) (sat_cons (step400 p h) (sat_nil p)))
def c1462 : List Lit := [(83, true), (66, false), (54, true), (64, true), (100, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c558, c401] c1462 (by decide) p (sat_cons (step558 p h) (sat_cons (step401 p h) (sat_nil p)))
def c1463 : List Lit := [(67, true), (100, true), (54, true), (64, true), (66, false)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c558, c402] c1463 (by decide) p (sat_cons (step558 p h) (sat_cons (step402 p h) (sat_nil p)))
def c1464 : List Lit := [(83, true), (66, false), (64, true), (54, true), (67, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c558, c403] c1464 (by decide) p (sat_cons (step558 p h) (sat_cons (step403 p h) (sat_nil p)))
def c1465 : List Lit := [(63, true), (67, true), (68, false)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c559, c415] c1465 (by decide) p (sat_cons (step559 p h) (sat_cons (step415 p h) (sat_nil p)))
def c1466 : List Lit := [(67, true), (68, false), (58, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c559, c416] c1466 (by decide) p (sat_cons (step559 p h) (sat_cons (step416 p h) (sat_nil p)))
def c1467 : List Lit := [(63, true), (68, false), (58, true)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c559, c417] c1467 (by decide) p (sat_cons (step559 p h) (sat_cons (step417 p h) (sat_nil p)))
def c1468 : List Lit := [(73, true), (70, true), (69, false)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c560, c419] c1468 (by decide) p (sat_cons (step560 p h) (sat_cons (step419 p h) (sat_nil p)))
def c1469 : List Lit := [(73, true), (69, false), (46, true)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c560, c420] c1469 (by decide) p (sat_cons (step560 p h) (sat_cons (step420 p h) (sat_nil p)))
def c1470 : List Lit := [(70, true), (69, false), (46, true)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c560, c421] c1470 (by decide) p (sat_cons (step560 p h) (sat_cons (step421 p h) (sat_nil p)))
def c1471 : List Lit := [(82, true), (72, true), (71, false)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c561, c428] c1471 (by decide) p (sat_cons (step561 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1472 : List Lit := [(82, true), (51, true), (71, false)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c561, c429] c1472 (by decide) p (sat_cons (step561 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1473 : List Lit := [(72, true), (51, true), (71, false)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c561, c430] c1473 (by decide) p (sat_cons (step561 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1474 : List Lit := [(76, true), (73, true), (75, true), (74, false)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c562, c438] c1474 (by decide) p (sat_cons (step562 p h) (sat_cons (step438 p h) (sat_nil p)))
def c1475 : List Lit := [(76, true), (70, true), (74, false), (75, true)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c562, c439] c1475 (by decide) p (sat_cons (step562 p h) (sat_cons (step439 p h) (sat_nil p)))
def c1476 : List Lit := [(73, true), (70, true), (74, false), (75, true)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c562, c440] c1476 (by decide) p (sat_cons (step562 p h) (sat_cons (step440 p h) (sat_nil p)))
def c1477 : List Lit := [(76, true), (77, false), (72, true), (58, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c563, c446] c1477 (by decide) p (sat_cons (step563 p h) (sat_cons (step446 p h) (sat_nil p)))
def c1478 : List Lit := [(77, false), (75, true), (58, true), (72, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c563, c447] c1478 (by decide) p (sat_cons (step563 p h) (sat_cons (step447 p h) (sat_nil p)))
def c1479 : List Lit := [(80, true), (70, true), (78, false)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c564, c449] c1479 (by decide) p (sat_cons (step564 p h) (sat_cons (step449 p h) (sat_nil p)))
def c1480 : List Lit := [(80, true), (59, true), (78, false)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c564, c450] c1480 (by decide) p (sat_cons (step564 p h) (sat_cons (step450 p h) (sat_nil p)))
def c1481 : List Lit := [(70, true), (59, true), (78, false)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c564, c451] c1481 (by decide) p (sat_cons (step564 p h) (sat_cons (step451 p h) (sat_nil p)))
def c1482 : List Lit := [(83, true), (82, true), (79, false)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c565, c452] c1482 (by decide) p (sat_cons (step565 p h) (sat_cons (step452 p h) (sat_nil p)))
def c1483 : List Lit := [(80, true), (79, false), (82, true)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c565, c453] c1483 (by decide) p (sat_cons (step565 p h) (sat_cons (step453 p h) (sat_nil p)))
def c1484 : List Lit := [(61, true), (81, false), (82, true)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c566, c458] c1484 (by decide) p (sat_cons (step566 p h) (sat_cons (step458 p h) (sat_nil p)))
def c1485 : List Lit := [(85, false), (84, true)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c567, c465] c1485 (by decide) p (sat_cons (step567 p h) (sat_cons (step465 p h) (sat_nil p)))
def c1486 : List Lit := [(85, false), (76, true)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c567, c466] c1486 (by decide) p (sat_cons (step567 p h) (sat_cons (step466 p h) (sat_nil p)))
def c1487 : List Lit := [(88, true), (91, true), (87, false), (46, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c569, c468] c1487 (by decide) p (sat_cons (step569 p h) (sat_cons (step468 p h) (sat_nil p)))
def c1488 : List Lit := [(91, true), (87, false), (16, true), (46, true)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c569, c469] c1488 (by decide) p (sat_cons (step569 p h) (sat_cons (step469 p h) (sat_nil p)))
def c1489 : List Lit := [(88, true), (87, false), (46, true), (16, true)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c569, c470] c1489 (by decide) p (sat_cons (step569 p h) (sat_cons (step470 p h) (sat_nil p)))
def c1490 : List Lit := [(99, true), (51, true), (90, true), (89, false)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c570, c478] c1490 (by decide) p (sat_cons (step570 p h) (sat_cons (step478 p h) (sat_nil p)))
def c1491 : List Lit := [(99, true), (90, true), (19, true), (89, false)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c570, c479] c1491 (by decide) p (sat_cons (step570 p h) (sat_cons (step479 p h) (sat_nil p)))
def c1492 : List Lit := [(99, true), (51, true), (19, true), (89, false)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c570, c480] c1492 (by decide) p (sat_cons (step570 p h) (sat_cons (step480 p h) (sat_nil p)))
def c1493 : List Lit := [(94, true), (91, true), (92, false), (88, true), (93, true)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c571, c490] c1493 (by decide) p (sat_cons (step571 p h) (sat_cons (step490 p h) (sat_nil p)))
def c1494 : List Lit := [(94, true), (93, true), (95, false), (90, true)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c572, c497] c1494 (by decide) p (sat_cons (step572 p h) (sat_cons (step497 p h) (sat_nil p)))
def c1495 : List Lit := [(94, true), (93, true), (95, false), (58, true)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c572, c498] c1495 (by decide) p (sat_cons (step572 p h) (sat_cons (step498 p h) (sat_nil p)))
def c1496 : List Lit := [(94, true), (90, true), (58, true), (95, false)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c572, c499] c1496 (by decide) p (sat_cons (step572 p h) (sat_cons (step499 p h) (sat_nil p)))
def c1497 : List Lit := [(90, true), (95, false), (93, true), (58, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c572, c500] c1497 (by decide) p (sat_cons (step572 p h) (sat_cons (step500 p h) (sat_nil p)))
def c1498 : List Lit := [(98, true), (88, true), (96, false)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c573, c501] c1498 (by decide) p (sat_cons (step573 p h) (sat_cons (step501 p h) (sat_nil p)))
def c1499 : List Lit := [(98, true), (59, true), (96, false)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c573, c502] c1499 (by decide) p (sat_cons (step573 p h) (sat_cons (step502 p h) (sat_nil p)))
def c1500 : List Lit := [(88, true), (59, true), (96, false)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c573, c503] c1500 (by decide) p (sat_cons (step573 p h) (sat_cons (step503 p h) (sat_nil p)))
def c1501 : List Lit := [(99, true), (100, true), (97, false)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c574, c504] c1501 (by decide) p (sat_cons (step574 p h) (sat_cons (step504 p h) (sat_nil p)))
def c1502 : List Lit := [(98, true), (100, true), (97, false)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c574, c505] c1502 (by decide) p (sat_cons (step574 p h) (sat_cons (step505 p h) (sat_nil p)))
def c1503 : List Lit := [(99, true), (98, true), (97, false)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c574, c506] c1503 (by decide) p (sat_cons (step574 p h) (sat_cons (step506 p h) (sat_nil p)))
def c1504 : List Lit := [(101, true), (32, true), (102, false)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c575, c518] c1504 (by decide) p (sat_cons (step575 p h) (sat_cons (step518 p h) (sat_nil p)))
def c1505 : List Lit := [(94, true), (32, true), (102, false)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c575, c519] c1505 (by decide) p (sat_cons (step575 p h) (sat_cons (step519 p h) (sat_nil p)))
def c1506 : List Lit := [(100, true), (101, true), (103, false)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c576, c521] c1506 (by decide) p (sat_cons (step576 p h) (sat_cons (step521 p h) (sat_nil p)))
def c1507 : List Lit := [(99, true), (100, true), (103, false)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c576, c522] c1507 (by decide) p (sat_cons (step576 p h) (sat_cons (step522 p h) (sat_nil p)))
def c1508 : List Lit := [(110, false), (112, true)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c578, c527] c1508 (by decide) p (sat_cons (step578 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1509 : List Lit := [(121, false), (122, false)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c1213, c583] c1509 (by decide) p (sat_cons (step1213 p h) (sat_cons (step583 p h) (sat_nil p)))
def c1510 : List Lit := [(239, false), (241, false)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c1212, c587] c1510 (by decide) p (sat_cons (step1212 p h) (sat_cons (step587 p h) (sat_nil p)))
def c1511 : List Lit := [(237, false), (243, false)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c1209, c592] c1511 (by decide) p (sat_cons (step1209 p h) (sat_cons (step592 p h) (sat_nil p)))
def c1512 : List Lit := [(251, false), (253, false)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c1211, c598] c1512 (by decide) p (sat_cons (step1211 p h) (sat_cons (step598 p h) (sat_nil p)))
def c1513 : List Lit := [(245, false), (257, false)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c1205, c604] c1513 (by decide) p (sat_cons (step1205 p h) (sat_cons (step604 p h) (sat_nil p)))
end B112E081
