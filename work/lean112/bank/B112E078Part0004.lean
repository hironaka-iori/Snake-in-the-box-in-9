import B112E078Part0003
namespace B112E078
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1468 : List Lit := [(54, true), (58, true), (57, false), (45, true)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c558, c387] c1468 (by decide) p (sat_cons (step558 p h) (sat_cons (step387 p h) (sat_nil p)))
def c1469 : List Lit := [(63, false), (64, true)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c559, c403] c1469 (by decide) p (sat_cons (step559 p h) (sat_cons (step403 p h) (sat_nil p)))
def c1470 : List Lit := [(63, false), (62, true)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c559, c404] c1470 (by decide) p (sat_cons (step559 p h) (sat_cons (step404 p h) (sat_nil p)))
def c1471 : List Lit := [(66, false), (65, true)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c560, c407] c1471 (by decide) p (sat_cons (step560 p h) (sat_cons (step407 p h) (sat_nil p)))
def c1472 : List Lit := [(69, true), (70, false), (74, true)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c561, c412] c1472 (by decide) p (sat_cons (step561 p h) (sat_cons (step412 p h) (sat_nil p)))
def c1473 : List Lit := [(72, false), (76, true)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c562, c415] c1473 (by decide) p (sat_cons (step562 p h) (sat_cons (step415 p h) (sat_nil p)))
def c1474 : List Lit := [(72, false), (71, true)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c562, c416] c1474 (by decide) p (sat_cons (step562 p h) (sat_cons (step416 p h) (sat_nil p)))
def c1475 : List Lit := [(62, true), (74, true), (73, false)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c563, c417] c1475 (by decide) p (sat_cons (step563 p h) (sat_cons (step417 p h) (sat_nil p)))
def c1476 : List Lit := [(83, true), (75, false), (74, true)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c564, c424] c1476 (by decide) p (sat_cons (step564 p h) (sat_cons (step424 p h) (sat_nil p)))
def c1477 : List Lit := [(79, false), (78, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c565, c429] c1477 (by decide) p (sat_cons (step565 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1478 : List Lit := [(79, false), (77, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c565, c430] c1478 (by decide) p (sat_cons (step565 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1479 : List Lit := [(82, false), (84, true)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c566, c432] c1479 (by decide) p (sat_cons (step566 p h) (sat_cons (step432 p h) (sat_nil p)))
def c1480 : List Lit := [(82, false), (83, true)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c566, c433] c1480 (by decide) p (sat_cons (step566 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1481 : List Lit := [(87, true), (85, true), (86, false), (91, true)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c567, c440] c1481 (by decide) p (sat_cons (step567 p h) (sat_cons (step440 p h) (sat_nil p)))
def c1482 : List Lit := [(88, true), (23, true), (93, true), (89, false)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c568, c447] c1482 (by decide) p (sat_cons (step568 p h) (sat_cons (step447 p h) (sat_nil p)))
def c1483 : List Lit := [(88, true), (23, true), (89, false), (87, true)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c568, c448] c1483 (by decide) p (sat_cons (step568 p h) (sat_cons (step448 p h) (sat_nil p)))
def c1484 : List Lit := [(85, true), (24, true), (91, true), (90, false)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c569, c450] c1484 (by decide) p (sat_cons (step569 p h) (sat_cons (step450 p h) (sat_nil p)))
def c1485 : List Lit := [(100, true), (92, false), (91, true), (87, true)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c570, c461] c1485 (by decide) p (sat_cons (step570 p h) (sat_cons (step461 p h) (sat_nil p)))
def c1486 : List Lit := [(93, true), (92, false), (91, true), (87, true)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c570, c462] c1486 (by decide) p (sat_cons (step570 p h) (sat_cons (step462 p h) (sat_nil p)))
def c1487 : List Lit := [(96, false), (95, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c571, c466] c1487 (by decide) p (sat_cons (step571 p h) (sat_cons (step466 p h) (sat_nil p)))
def c1488 : List Lit := [(96, false), (94, true)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c571, c467] c1488 (by decide) p (sat_cons (step571 p h) (sat_cons (step467 p h) (sat_nil p)))
def c1489 : List Lit := [(99, false), (101, true)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c572, c470] c1489 (by decide) p (sat_cons (step572 p h) (sat_cons (step470 p h) (sat_nil p)))
def c1490 : List Lit := [(99, false), (100, true)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c572, c471] c1490 (by decide) p (sat_cons (step572 p h) (sat_cons (step471 p h) (sat_nil p)))
def c1491 : List Lit := [(102, true), (108, true), (103, false)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c573, c480] c1491 (by decide) p (sat_cons (step573 p h) (sat_cons (step480 p h) (sat_nil p)))
def c1492 : List Lit := [(40, true), (108, true), (103, false)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c573, c481] c1492 (by decide) p (sat_cons (step573 p h) (sat_cons (step481 p h) (sat_nil p)))
def c1493 : List Lit := [(102, true), (40, true), (103, false)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c573, c482] c1493 (by decide) p (sat_cons (step573 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1494 : List Lit := [(104, true), (113, true), (105, false), (87, true)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c574, c484] c1494 (by decide) p (sat_cons (step574 p h) (sat_cons (step484 p h) (sat_nil p)))
def c1495 : List Lit := [(113, true), (41, true), (87, true), (105, false)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c574, c486] c1495 (by decide) p (sat_cons (step574 p h) (sat_cons (step486 p h) (sat_nil p)))
def c1496 : List Lit := [(104, true), (41, true), (87, true), (105, false)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c574, c487] c1496 (by decide) p (sat_cons (step574 p h) (sat_cons (step487 p h) (sat_nil p)))
def c1497 : List Lit := [(117, true), (108, true), (106, false), (91, true), (74, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c575, c489] c1497 (by decide) p (sat_cons (step575 p h) (sat_cons (step489 p h) (sat_nil p)))
def c1498 : List Lit := [(74, true), (43, true), (117, true), (106, false), (91, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c575, c490] c1498 (by decide) p (sat_cons (step575 p h) (sat_cons (step490 p h) (sat_nil p)))
def c1499 : List Lit := [(74, true), (43, true), (108, true), (106, false), (91, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c575, c491] c1499 (by decide) p (sat_cons (step575 p h) (sat_cons (step491 p h) (sat_nil p)))
def c1500 : List Lit := [(110, true), (108, true), (107, false), (44, true)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c576, c492] c1500 (by decide) p (sat_cons (step576 p h) (sat_cons (step492 p h) (sat_nil p)))
def c1501 : List Lit := [(110, true), (102, true), (107, false), (44, true)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c576, c493] c1501 (by decide) p (sat_cons (step576 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1502 : List Lit := [(102, true), (108, true), (107, false), (44, true)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c576, c494] c1502 (by decide) p (sat_cons (step576 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1503 : List Lit := [(110, true), (104, true), (109, false)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c577, c500] c1503 (by decide) p (sat_cons (step577 p h) (sat_cons (step500 p h) (sat_nil p)))
def c1504 : List Lit := [(110, true), (109, false), (45, true)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c577, c501] c1504 (by decide) p (sat_cons (step577 p h) (sat_cons (step501 p h) (sat_nil p)))
def c1505 : List Lit := [(104, true), (109, false), (45, true)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c577, c502] c1505 (by decide) p (sat_cons (step577 p h) (sat_cons (step502 p h) (sat_nil p)))
def c1506 : List Lit := [(111, true), (104, true), (113, true), (112, false)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c578, c512] c1506 (by decide) p (sat_cons (step578 p h) (sat_cons (step512 p h) (sat_nil p)))
def c1507 : List Lit := [(119, true), (114, true), (115, false)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c579, c520] c1507 (by decide) p (sat_cons (step579 p h) (sat_cons (step520 p h) (sat_nil p)))
def c1508 : List Lit := [(119, true), (113, true), (115, false)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c579, c521] c1508 (by decide) p (sat_cons (step579 p h) (sat_cons (step521 p h) (sat_nil p)))
def c1509 : List Lit := [(114, true), (113, true), (115, false)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c579, c522] c1509 (by decide) p (sat_cons (step579 p h) (sat_cons (step522 p h) (sat_nil p)))
def c1510 : List Lit := [(117, true), (111, true), (116, false)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c580, c523] c1510 (by decide) p (sat_cons (step580 p h) (sat_cons (step523 p h) (sat_nil p)))
def c1511 : List Lit := [(117, true), (54, true), (116, false)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c580, c524] c1511 (by decide) p (sat_cons (step580 p h) (sat_cons (step524 p h) (sat_nil p)))
def c1512 : List Lit := [(54, true), (111, true), (116, false)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c580, c525] c1512 (by decide) p (sat_cons (step580 p h) (sat_cons (step525 p h) (sat_nil p)))
def c1513 : List Lit := [(119, true), (108, true), (118, false)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c581, c531] c1513 (by decide) p (sat_cons (step581 p h) (sat_cons (step531 p h) (sat_nil p)))
def c1514 : List Lit := [(117, true), (108, true), (118, false)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c581, c532] c1514 (by decide) p (sat_cons (step581 p h) (sat_cons (step532 p h) (sat_nil p)))
def c1515 : List Lit := [(120, false), (239, false)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c1230, c585] c1515 (by decide) p (sat_cons (step1230 p h) (sat_cons (step585 p h) (sat_nil p)))
def c1516 : List Lit := [(128, false), (129, false)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c1232, c590] c1516 (by decide) p (sat_cons (step1232 p h) (sat_cons (step590 p h) (sat_nil p)))
def c1517 : List Lit := [(253, false), (259, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c1225, c597] c1517 (by decide) p (sat_cons (step1225 p h) (sat_cons (step597 p h) (sat_nil p)))
def c1518 : List Lit := [(249, false), (261, false)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c1222, c602] c1518 (by decide) p (sat_cons (step1222 p h) (sat_cons (step602 p h) (sat_nil p)))
def c1519 : List Lit := [(137, false), (138, false)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c1231, c607] c1519 (by decide) p (sat_cons (step1231 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1520 : List Lit := [(269, false), (271, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c1228, c611] c1520 (by decide) p (sat_cons (step1228 p h) (sat_cons (step611 p h) (sat_nil p)))
def c1521 : List Lit := [(267, false), (273, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c1224, c616] c1521 (by decide) p (sat_cons (step1224 p h) (sat_cons (step616 p h) (sat_nil p)))
def c1522 : List Lit := [(275, false), (289, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c1221, c623] c1522 (by decide) p (sat_cons (step1221 p h) (sat_cons (step623 p h) (sat_nil p)))
def c1523 : List Lit := [(263, false), (291, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c1218, c628] c1523 (by decide) p (sat_cons (step1218 p h) (sat_cons (step628 p h) (sat_nil p)))
def c1524 : List Lit := [(293, false), (351, false)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c1215, c666] c1524 (by decide) p (sat_cons (step1215 p h) (sat_cons (step666 p h) (sat_nil p)))
def c1525 : List Lit := [(359, false), (361, false)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c1227, c671] c1525 (by decide) p (sat_cons (step1227 p h) (sat_cons (step671 p h) (sat_nil p)))
def c1526 : List Lit := [(449, false), (463, false)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1219, c718] c1526 (by decide) p (sat_cons (step1219 p h) (sat_cons (step718 p h) (sat_nil p)))
def c1527 : List Lit := [(437, false), (465, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c1216, c722] c1527 (by decide) p (sat_cons (step1216 p h) (sat_cons (step722 p h) (sat_nil p)))
def c1528 : List Lit := [(353, false), (469, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c731, c729] c1528 (by decide) p (sat_cons (step731 p h) (sat_cons (step729 p h) (sat_nil p)))
def c1529 : List Lit := [(1488, true), (1480, false)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c1349, c811] c1529 (by decide) p (sat_cons (step1349 p h) (sat_cons (step811 p h) (sat_nil p)))
def c1530 : List Lit := [(1481, false), (1489, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c1349, c812] c1530 (by decide) p (sat_cons (step1349 p h) (sat_cons (step812 p h) (sat_nil p)))
def c1531 : List Lit := [(1482, false), (1490, true)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c1349, c813] c1531 (by decide) p (sat_cons (step1349 p h) (sat_cons (step813 p h) (sat_nil p)))
end B112E078
