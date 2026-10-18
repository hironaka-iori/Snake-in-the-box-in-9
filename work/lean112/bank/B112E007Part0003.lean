import B112E007Part0002
namespace B112E007
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1492 : List Lit := [(58, false), (57, false), (94, false)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c1300, c222] c1492 (by decide) p (sat_cons (step1300 p h) (sat_cons (step222 p h) (sat_nil p)))
def c1493 : List Lit := [(58, false), (60, false)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c1300, c233, c229] c1493 (by decide) p (sat_cons (step1300 p h) (sat_cons (step233 p h) (sat_cons (step229 p h) (sat_nil p))))
def c1494 : List Lit := [(179, false), (58, false)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c233, c230] c1494 (by decide) p (sat_cons (step233 p h) (sat_cons (step230 p h) (sat_nil p)))
def c1495 : List Lit := [(63, false), (68, true), (65, true)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c576, c235] c1495 (by decide) p (sat_cons (step576 p h) (sat_cons (step235 p h) (sat_nil p)))
def c1496 : List Lit := [(63, false), (65, true), (64, true)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c576, c236] c1496 (by decide) p (sat_cons (step576 p h) (sat_cons (step236 p h) (sat_nil p)))
def c1497 : List Lit := [(72, true), (66, false), (65, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c577, c249] c1497 (by decide) p (sat_cons (step577 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1498 : List Lit := [(66, false), (67, true), (65, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c577, c250] c1498 (by decide) p (sat_cons (step577 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1499 : List Lit := [(72, true), (70, false), (68, true), (52, true), (77, true), (106, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c579, c280] c1499 (by decide) p (sat_cons (step579 p h) (sat_cons (step280 p h) (sat_nil p)))
def c1500 : List Lit := [(52, true), (77, true), (70, false), (106, true), (68, true), (65, true)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c579, c281] c1500 (by decide) p (sat_cons (step579 p h) (sat_cons (step281 p h) (sat_nil p)))
def c1501 : List Lit := [(71, false), (72, true)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c580, c282] c1501 (by decide) p (sat_cons (step580 p h) (sat_cons (step282 p h) (sat_nil p)))
def c1502 : List Lit := [(71, false), (68, true)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c580, c283] c1502 (by decide) p (sat_cons (step580 p h) (sat_cons (step283 p h) (sat_nil p)))
def c1503 : List Lit := [(77, true), (55, true), (65, true), (73, false)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c581, c291] c1503 (by decide) p (sat_cons (step581 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1504 : List Lit := [(12, true), (55, true), (73, false), (65, true)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c581, c292] c1504 (by decide) p (sat_cons (step581 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1505 : List Lit := [(75, false), (74, true)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c582, c295] c1505 (by decide) p (sat_cons (step582 p h) (sat_cons (step295 p h) (sat_nil p)))
def c1506 : List Lit := [(75, false), (67, true)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c582, c296] c1506 (by decide) p (sat_cons (step582 p h) (sat_cons (step296 p h) (sat_nil p)))
def c1507 : List Lit := [(78, false), (77, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c583, c305] c1507 (by decide) p (sat_cons (step583 p h) (sat_cons (step305 p h) (sat_nil p)))
def c1508 : List Lit := [(78, false), (76, true)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c583, c306] c1508 (by decide) p (sat_cons (step583 p h) (sat_cons (step306 p h) (sat_nil p)))
def c1509 : List Lit := [(79, false), (76, true)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c584, c307] c1509 (by decide) p (sat_cons (step584 p h) (sat_cons (step307 p h) (sat_nil p)))
def c1510 : List Lit := [(79, false), (74, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c584, c308] c1510 (by decide) p (sat_cons (step584 p h) (sat_cons (step308 p h) (sat_nil p)))
def c1511 : List Lit := [(98, true), (81, true), (90, true), (21, true), (88, false), (86, true), (106, true)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c589, c403] c1511 (by decide) p (sat_cons (step589 p h) (sat_cons (step403 p h) (sat_nil p)))
def c1512 : List Lit := [(98, true), (21, true), (88, false), (52, true), (81, true), (86, true), (106, true)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c589, c404] c1512 (by decide) p (sat_cons (step589 p h) (sat_cons (step404 p h) (sat_nil p)))
def c1513 : List Lit := [(89, false), (90, true), (86, true)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c590, c406] c1513 (by decide) p (sat_cons (step590 p h) (sat_cons (step406 p h) (sat_nil p)))
def c1514 : List Lit := [(89, false), (83, true), (86, true)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c590, c407] c1514 (by decide) p (sat_cons (step590 p h) (sat_cons (step407 p h) (sat_nil p)))
def c1515 : List Lit := [(95, false), (94, true), (92, true), (93, true)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c592, c455] c1515 (by decide) p (sat_cons (step592 p h) (sat_cons (step455 p h) (sat_nil p)))
def c1516 : List Lit := [(95, false), (94, true), (92, true), (85, true)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c592, c456] c1516 (by decide) p (sat_cons (step592 p h) (sat_cons (step456 p h) (sat_nil p)))
def c1517 : List Lit := [(98, true), (86, true), (97, true), (115, true), (96, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c593, c467] c1517 (by decide) p (sat_cons (step593 p h) (sat_cons (step467 p h) (sat_nil p)))
def c1518 : List Lit := [(99, false), (97, true), (92, true)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c594, c481] c1518 (by decide) p (sat_cons (step594 p h) (sat_cons (step481 p h) (sat_nil p)))
def c1519 : List Lit := [(100, false), (97, true)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c595, c482] c1519 (by decide) p (sat_cons (step595 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1520 : List Lit := [(100, false), (93, true)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c595, c483] c1520 (by decide) p (sat_cons (step595 p h) (sat_cons (step483 p h) (sat_nil p)))
def c1521 : List Lit := [(102, true), (65, true), (101, false), (106, true)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c596, c488] c1521 (by decide) p (sat_cons (step596 p h) (sat_cons (step488 p h) (sat_nil p)))
def c1522 : List Lit := [(81, true), (65, true), (106, true), (101, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c596, c489] c1522 (by decide) p (sat_cons (step596 p h) (sat_cons (step489 p h) (sat_nil p)))
def c1523 : List Lit := [(102, true), (65, true), (81, true), (101, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c596, c490] c1523 (by decide) p (sat_cons (step596 p h) (sat_cons (step490 p h) (sat_nil p)))
def c1524 : List Lit := [(105, true), (109, true), (108, false)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c599, c514] c1524 (by decide) p (sat_cons (step599 p h) (sat_cons (step514 p h) (sat_nil p)))
def c1525 : List Lit := [(108, false), (105, true), (104, true)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c599, c515] c1525 (by decide) p (sat_cons (step599 p h) (sat_cons (step515 p h) (sat_nil p)))
def c1526 : List Lit := [(113, true), (115, true), (110, false)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c600, c520] c1526 (by decide) p (sat_cons (step600 p h) (sat_cons (step520 p h) (sat_nil p)))
def c1527 : List Lit := [(112, false), (92, true), (111, true)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c601, c526] c1527 (by decide) p (sat_cons (step601 p h) (sat_cons (step526 p h) (sat_nil p)))
def c1528 : List Lit := [(102, true), (112, false), (92, true)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c601, c527] c1528 (by decide) p (sat_cons (step601 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1529 : List Lit := [(118, false), (109, true)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c604, c543] c1529 (by decide) p (sat_cons (step604 p h) (sat_cons (step543 p h) (sat_nil p)))
def c1530 : List Lit := [(138, false), (139, false)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c1333, c625] c1530 (by decide) p (sat_cons (step1333 p h) (sat_cons (step625 p h) (sat_nil p)))
def c1531 : List Lit := [(265, false), (271, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c1323, c631] c1531 (by decide) p (sat_cons (step1323 p h) (sat_cons (step631 p h) (sat_nil p)))
def c1532 : List Lit := [(281, false), (283, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c1330, c640] c1532 (by decide) p (sat_cons (step1330 p h) (sat_cons (step640 p h) (sat_nil p)))
def c1533 : List Lit := [(279, false), (285, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1322, c644] c1533 (by decide) p (sat_cons (step1322 p h) (sat_cons (step644 p h) (sat_nil p)))
def c1534 : List Lit := [(273, false), (287, false)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1313, c648] c1534 (by decide) p (sat_cons (step1313 p h) (sat_cons (step648 p h) (sat_nil p)))
def c1535 : List Lit := [(261, false), (289, false)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1306, c653] c1535 (by decide) p (sat_cons (step1306 p h) (sat_cons (step653 p h) (sat_nil p)))
def c1536 : List Lit := [(303, false), (315, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1312, c675] c1536 (by decide) p (sat_cons (step1312 p h) (sat_cons (step675 p h) (sat_nil p)))
def c1537 : List Lit := [(321, false), (327, false)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1320, c682] c1537 (by decide) p (sat_cons (step1320 p h) (sat_cons (step682 p h) (sat_nil p)))
def c1538 : List Lit := [(169, false), (170, false)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1332, c685] c1538 (by decide) p (sat_cons (step1332 p h) (sat_cons (step685 p h) (sat_nil p)))
def c1539 : List Lit := [(331, false), (333, false)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1328, c689] c1539 (by decide) p (sat_cons (step1328 p h) (sat_cons (step689 p h) (sat_nil p)))
def c1540 : List Lit := [(335, false), (341, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1319, c697] c1540 (by decide) p (sat_cons (step1319 p h) (sat_cons (step697 p h) (sat_nil p)))
def c1541 : List Lit := [(329, false), (343, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1311, c702] c1541 (by decide) p (sat_cons (step1311 p h) (sat_cons (step702 p h) (sat_nil p)))
def c1542 : List Lit := [(317, false), (345, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1305, c707] c1542 (by decide) p (sat_cons (step1305 p h) (sat_cons (step707 p h) (sat_nil p)))
def c1543 : List Lit := [(291, false), (347, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1302, c712] c1543 (by decide) p (sat_cons (step1302 p h) (sat_cons (step712 p h) (sat_nil p)))
def c1544 : List Lit := [(361, false), (373, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1310, c736] c1544 (by decide) p (sat_cons (step1310 p h) (sat_cons (step736 p h) (sat_nil p)))
def c1545 : List Lit := [(387, false), (401, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1309, c756] c1545 (by decide) p (sat_cons (step1309 p h) (sat_cons (step756 p h) (sat_nil p)))
def c1546 : List Lit := [(375, false), (403, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1304, c760] c1546 (by decide) p (sat_cons (step1304 p h) (sat_cons (step760 p h) (sat_nil p)))
def c1547 : List Lit := [(409, false), (415, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1316, c773] c1547 (by decide) p (sat_cons (step1316 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1548 : List Lit := [(417, false), (431, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1308, c784] c1548 (by decide) p (sat_cons (step1308 p h) (sat_cons (step784 p h) (sat_nil p)))
def c1549 : List Lit := [(437, false), (443, false)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1315, c794] c1549 (by decide) p (sat_cons (step1315 p h) (sat_cons (step794 p h) (sat_nil p)))
def c1550 : List Lit := [(447, false), (449, false)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1325, c799] c1550 (by decide) p (sat_cons (step1325 p h) (sat_cons (step799 p h) (sat_nil p)))
def c1551 : List Lit := [(453, false), (455, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1324, c804] c1551 (by decide) p (sat_cons (step1324 p h) (sat_cons (step804 p h) (sat_nil p)))
def c1552 : List Lit := [(451, false), (457, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1314, c808] c1552 (by decide) p (sat_cons (step1314 p h) (sat_cons (step808 p h) (sat_nil p)))
def c1553 : List Lit := [(445, false), (459, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1307, c813] c1553 (by decide) p (sat_cons (step1307 p h) (sat_cons (step813 p h) (sat_nil p)))
def c1554 : List Lit := [(433, false), (461, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1303, c818] c1554 (by decide) p (sat_cons (step1303 p h) (sat_cons (step818 p h) (sat_nil p)))
def c1555 : List Lit := [(405, false), (463, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1301, c823] c1555 (by decide) p (sat_cons (step1301 p h) (sat_cons (step823 p h) (sat_nil p)))
end B112E007
