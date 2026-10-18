import B112E257Inputs
namespace B112E257
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1518 : List Lit := [(96, true)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c503, c502] c1518 (by decide) p (sat_cons (step503 p h) (sat_cons (step502 p h) (sat_nil p)))
def c1519 : List Lit := [(212, true), (113, true)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c1518, c504] c1519 (by decide) p (sat_cons (step1518 p h) (sat_cons (step504 p h) (sat_nil p)))
def c1520 : List Lit := [(108, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c604, c529] c1520 (by decide) p (sat_cons (step604 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1521 : List Lit := [(112, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c607, c544] c1521 (by decide) p (sat_cons (step607 p h) (sat_cons (step544 p h) (sat_nil p)))
def c1522 : List Lit := [(458, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c800, c797] c1522 (by decide) p (sat_cons (step800 p h) (sat_cons (step797 p h) (sat_nil p)))
def c1523 : List Lit := [(344, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c800, c799] c1523 (by decide) p (sat_cons (step800 p h) (sat_cons (step799 p h) (sat_nil p)))
def c1524 : List Lit := [(456, false)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c1522, c794] c1524 (by decide) p (sat_cons (step1522 p h) (sat_cons (step794 p h) (sat_nil p)))
def c1525 : List Lit := [(342, false)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c1523, c715] c1525 (by decide) p (sat_cons (step1523 p h) (sat_cons (step715 p h) (sat_nil p)))
def c1526 : List Lit := [(286, false)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1523, c718] c1526 (by decide) p (sat_cons (step1523 p h) (sat_cons (step718 p h) (sat_nil p)))
def c1527 : List Lit := [(454, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c1524, c789] c1527 (by decide) p (sat_cons (step1524 p h) (sat_cons (step789 p h) (sat_nil p)))
def c1528 : List Lit := [(426, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c1524, c792] c1528 (by decide) p (sat_cons (step1524 p h) (sat_cons (step792 p h) (sat_nil p)))
def c1529 : List Lit := [(340, false)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c1525, c710] c1529 (by decide) p (sat_cons (step1525 p h) (sat_cons (step710 p h) (sat_nil p)))
def c1530 : List Lit := [(312, false)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c1525, c713] c1530 (by decide) p (sat_cons (step1525 p h) (sat_cons (step713 p h) (sat_nil p)))
def c1531 : List Lit := [(284, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c1526, c658] c1531 (by decide) p (sat_cons (step1526 p h) (sat_cons (step658 p h) (sat_nil p)))
def c1532 : List Lit := [(258, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c1526, c661] c1532 (by decide) p (sat_cons (step1526 p h) (sat_cons (step661 p h) (sat_nil p)))
def c1533 : List Lit := [(412, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1528, c773] c1533 (by decide) p (sat_cons (step1528 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1534 : List Lit := [(310, false)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1530, c686] c1534 (by decide) p (sat_cons (step1530 p h) (sat_cons (step686 p h) (sat_nil p)))
def c1535 : List Lit := [(298, false)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1530, c689] c1535 (by decide) p (sat_cons (step1530 p h) (sat_cons (step689 p h) (sat_nil p)))
def c1536 : List Lit := [(270, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1531, c656] c1536 (by decide) p (sat_cons (step1531 p h) (sat_cons (step656 p h) (sat_nil p)))
def c1537 : List Lit := [(256, false)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1532, c631] c1537 (by decide) p (sat_cons (step1532 p h) (sat_cons (step631 p h) (sat_nil p)))
def c1538 : List Lit := [(244, false)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1532, c634] c1538 (by decide) p (sat_cons (step1532 p h) (sat_cons (step634 p h) (sat_nil p)))
def c1539 : List Lit := [(302, false)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1534, c684] c1539 (by decide) p (sat_cons (step1534 p h) (sat_cons (step684 p h) (sat_nil p)))
def c1540 : List Lit := [(296, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1535, c671] c1540 (by decide) p (sat_cons (step1535 p h) (sat_cons (step671 p h) (sat_nil p)))
def c1541 : List Lit := [(268, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1536, c643] c1541 (by decide) p (sat_cons (step1536 p h) (sat_cons (step643 p h) (sat_nil p)))
def c1542 : List Lit := [(254, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1537, c627] c1542 (by decide) p (sat_cons (step1537 p h) (sat_cons (step627 p h) (sat_nil p)))
def c1543 : List Lit := [(252, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1542, c625] c1543 (by decide) p (sat_cons (step1542 p h) (sat_cons (step625 p h) (sat_nil p)))
def c1544 : List Lit := [(994, true)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1520, c1228] c1544 (by decide) p (sat_cons (step1520 p h) (sat_cons (step1228 p h) (sat_nil p)))
def c1545 : List Lit := [(996, true)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1544, c1229] c1545 (by decide) p (sat_cons (step1544 p h) (sat_cons (step1229 p h) (sat_nil p)))
def c1546 : List Lit := [(992, false), (997, true)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1544, c1230] c1546 (by decide) p (sat_cons (step1544 p h) (sat_cons (step1230 p h) (sat_nil p)))
def c1547 : List Lit := [(993, false), (998, true)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1544, c1232] c1547 (by decide) p (sat_cons (step1544 p h) (sat_cons (step1232 p h) (sat_nil p)))
def c1548 : List Lit := [(1000, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1233] c1548 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1233 p h) (sat_nil p)))
def c1549 : List Lit := [(111, true), (1001, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1234] c1549 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1234 p h) (sat_nil p)))
def c1550 : List Lit := [(1004, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1548, c1238] c1550 (by decide) p (sat_cons (step1548 p h) (sat_cons (step1238 p h) (sat_nil p)))
def c1551 : List Lit := [(1002, false), (1005, true)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1548, c1239] c1551 (by decide) p (sat_cons (step1548 p h) (sat_cons (step1239 p h) (sat_nil p)))
def c1552 : List Lit := [(1009, true)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1545, c1550, c1243] c1552 (by decide) p (sat_cons (step1545 p h) (sat_cons (step1550 p h) (sat_cons (step1243 p h) (sat_nil p))))
def c1553 : List Lit := [(1005, false), (1010, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1545, c1244] c1553 (by decide) p (sat_cons (step1545 p h) (sat_cons (step1244 p h) (sat_nil p)))
def c1554 : List Lit := [(1006, false), (1011, true)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1545, c1245] c1554 (by decide) p (sat_cons (step1545 p h) (sat_cons (step1245 p h) (sat_nil p)))
def c1555 : List Lit := [(1007, false), (1012, true)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1545, c1246] c1555 (by decide) p (sat_cons (step1545 p h) (sat_cons (step1246 p h) (sat_nil p)))
def c1556 : List Lit := [(997, false), (1010, true)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1247] c1556 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1247 p h) (sat_nil p)))
def c1557 : List Lit := [(998, false), (1011, true)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1250] c1557 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1250 p h) (sat_nil p)))
def c1558 : List Lit := [(1017, true)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1252] c1558 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1252 p h) (sat_nil p)))
def c1559 : List Lit := [(985, false), (1018, true)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1256] c1559 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1256 p h) (sat_nil p)))
def c1560 : List Lit := [(986, false), (1019, true)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1260] c1560 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1260 p h) (sat_nil p)))
def c1561 : List Lit := [(987, false), (1020, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1263] c1561 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1263 p h) (sat_nil p)))
def c1562 : List Lit := [(988, false), (1021, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1267] c1562 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1267 p h) (sat_nil p)))
def c1563 : List Lit := [(960, false), (1035, true)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1558, c1283] c1563 (by decide) p (sat_cons (step1558 p h) (sat_cons (step1283 p h) (sat_nil p)))
def c1564 : List Lit := [(110, false), (114, true), (226, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c598, c1521, c535, c536, c497, c1515] c1564 (by decide) p (sat_cons (step598 p h) (sat_cons (step1521 p h) (sat_cons (step535 p h) (sat_cons (step536 p h) (sat_cons (step497 p h) (sat_cons (step1515 p h) (sat_nil p)))))))
def c1565 : List Lit := [(1616, true), (110, true), (115, true)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1524, c1522, c592, c597, c1445, c1442, c1449, c1453, c1454, c1452, c1450, c1439, c1444, c1446, c1434, c1435, c532, c556, c780, c782, c783, c785, c788, c791, c796, c771, c772, c752, c769, c760, c750, c768, c758, c748, c767, c757, c747, c508, c494, c744, c470, c492, c473] c1565 (by decide) p (sat_cons (step1524 p h) (sat_cons (step1522 p h) (sat_cons (step592 p h) (sat_cons (step597 p h) (sat_cons (step1445 p h) (sat_cons (step1442 p h) (sat_cons (step1449 p h) (sat_cons (step1453 p h) (sat_cons (step1454 p h) (sat_cons (step1452 p h) (sat_cons (step1450 p h) (sat_cons (step1439 p h) (sat_cons (step1444 p h) (sat_cons (step1446 p h) (sat_cons (step1434 p h) (sat_cons (step1435 p h) (sat_cons (step532 p h) (sat_cons (step556 p h) (sat_cons (step780 p h) (sat_cons (step782 p h) (sat_cons (step783 p h) (sat_cons (step785 p h) (sat_cons (step788 p h) (sat_cons (step791 p h) (sat_cons (step796 p h) (sat_cons (step771 p h) (sat_cons (step772 p h) (sat_cons (step752 p h) (sat_cons (step769 p h) (sat_cons (step760 p h) (sat_cons (step750 p h) (sat_cons (step768 p h) (sat_cons (step758 p h) (sat_cons (step748 p h) (sat_cons (step767 p h) (sat_cons (step757 p h) (sat_cons (step747 p h) (sat_cons (step508 p h) (sat_cons (step494 p h) (sat_cons (step744 p h) (sat_cons (step470 p h) (sat_cons (step492 p h) (sat_cons (step473 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c1566 : List Lit := [(397, true), (1554, true), (91, true)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c750, c751, c748, c739, c747, c737, c744, c736, c473, c464, c1403, c1400, c1406] c1566 (by decide) p (sat_cons (step750 p h) (sat_cons (step751 p h) (sat_cons (step748 p h) (sat_cons (step739 p h) (sat_cons (step747 p h) (sat_cons (step737 p h) (sat_cons (step744 p h) (sat_cons (step736 p h) (sat_cons (step473 p h) (sat_cons (step464 p h) (sat_cons (step1403 p h) (sat_cons (step1400 p h) (sat_cons (step1406 p h) (sat_nil p))))))))))))))
def c1567 : List Lit := [(1554, true), (89, true), (457, true), (73, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.TreeRup.prove_clause [c608, c597, c595, c600, c593, c602, c601, c609, c594, c598, c793, c788, c785, c783, c782, c780, c790, c771, c770, c765, c764, c1519, c545, c556, c795, c752, c751, c739, c737, c736, c464, c1400, c750, c749, c742, c741, c748, c747, c743, c746, c745, c772, c761, c755, c754, c760, c759, c756, c786, c777, c776, c775, c784, c779, c778, c766, c1407, c1566, c1406, c1401, c492, c1402, c467, c530, c475, c476, c481, c513, c471, c484, c517, c489, c523, c516, c526, c519, c480, c548, c477, c1564, c499, c496] c1567 (by decide) p (sat_cons (step608 p h) (sat_cons (step597 p h) (sat_cons (step595 p h) (sat_cons (step600 p h) (sat_cons (step593 p h) (sat_cons (step602 p h) (sat_cons (step601 p h) (sat_cons (step609 p h) (sat_cons (step594 p h) (sat_cons (step598 p h) (sat_cons (step793 p h) (sat_cons (step788 p h) (sat_cons (step785 p h) (sat_cons (step783 p h) (sat_cons (step782 p h) (sat_cons (step780 p h) (sat_cons (step790 p h) (sat_cons (step771 p h) (sat_cons (step770 p h) (sat_cons (step765 p h) (sat_cons (step764 p h) (sat_cons (step1519 p h) (sat_cons (step545 p h) (sat_cons (step556 p h) (sat_cons (step795 p h) (sat_cons (step752 p h) (sat_cons (step751 p h) (sat_cons (step739 p h) (sat_cons (step737 p h) (sat_cons (step736 p h) (sat_cons (step464 p h) (sat_cons (step1400 p h) (sat_cons (step750 p h) (sat_cons (step749 p h) (sat_cons (step742 p h) (sat_cons (step741 p h) (sat_cons (step748 p h) (sat_cons (step747 p h) (sat_cons (step743 p h) (sat_cons (step746 p h) (sat_cons (step745 p h) (sat_cons (step772 p h) (sat_cons (step761 p h) (sat_cons (step755 p h) (sat_cons (step754 p h) (sat_cons (step760 p h) (sat_cons (step759 p h) (sat_cons (step756 p h) (sat_cons (step786 p h) (sat_cons (step777 p h) (sat_cons (step776 p h) (sat_cons (step775 p h) (sat_cons (step784 p h) (sat_cons (step779 p h) (sat_cons (step778 p h) (sat_cons (step766 p h) (sat_cons (step1407 p h) (sat_cons (step1566 p h) (sat_cons (step1406 p h) (sat_cons (step1401 p h) (sat_cons (step492 p h) (sat_cons (step1402 p h) (sat_cons (step467 p h) (sat_cons (step530 p h) (sat_cons (step475 p h) (sat_cons (step476 p h) (sat_cons (step481 p h) (sat_cons (step513 p h) (sat_cons (step471 p h) (sat_cons (step484 p h) (sat_cons (step517 p h) (sat_cons (step489 p h) (sat_cons (step523 p h) (sat_cons (step516 p h) (sat_cons (step526 p h) (sat_cons (step519 p h) (sat_cons (step480 p h) (sat_cons (step548 p h) (sat_cons (step477 p h) (sat_cons (step1564 p h) (sat_cons (step499 p h) (sat_cons (step496 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1568 : List Lit := [(84, false), (93, true), (92, false), (89, true), (457, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.TreeRup.prove_clause [c608, c597, c592, c599, c591, c595, c602, c600, c593, c601, c594, c793, c790, c772, c761, c755, c754, c795, c752, c750, c749, c742, c741, c771, c770, c765, c763, c769, c768, c767, c748, c747, c744, c760, c758, c757, c495, c493, c474, c469, c507, c510, c506, c466, c467, c481, c484, c523, c764, c1519, c545, c788, c785, c783, c782, c780, c556, c530, c743, c746, c745, c759, c756, c786, c777, c776, c775, c766, c475, c476, c513, c471, c517, c489, c516, c519, c480, c499, c477] c1568 (by decide) p (sat_cons (step608 p h) (sat_cons (step597 p h) (sat_cons (step592 p h) (sat_cons (step599 p h) (sat_cons (step591 p h) (sat_cons (step595 p h) (sat_cons (step602 p h) (sat_cons (step600 p h) (sat_cons (step593 p h) (sat_cons (step601 p h) (sat_cons (step594 p h) (sat_cons (step793 p h) (sat_cons (step790 p h) (sat_cons (step772 p h) (sat_cons (step761 p h) (sat_cons (step755 p h) (sat_cons (step754 p h) (sat_cons (step795 p h) (sat_cons (step752 p h) (sat_cons (step750 p h) (sat_cons (step749 p h) (sat_cons (step742 p h) (sat_cons (step741 p h) (sat_cons (step771 p h) (sat_cons (step770 p h) (sat_cons (step765 p h) (sat_cons (step763 p h) (sat_cons (step769 p h) (sat_cons (step768 p h) (sat_cons (step767 p h) (sat_cons (step748 p h) (sat_cons (step747 p h) (sat_cons (step744 p h) (sat_cons (step760 p h) (sat_cons (step758 p h) (sat_cons (step757 p h) (sat_cons (step495 p h) (sat_cons (step493 p h) (sat_cons (step474 p h) (sat_cons (step469 p h) (sat_cons (step507 p h) (sat_cons (step510 p h) (sat_cons (step506 p h) (sat_cons (step466 p h) (sat_cons (step467 p h) (sat_cons (step481 p h) (sat_cons (step484 p h) (sat_cons (step523 p h) (sat_cons (step764 p h) (sat_cons (step1519 p h) (sat_cons (step545 p h) (sat_cons (step788 p h) (sat_cons (step785 p h) (sat_cons (step783 p h) (sat_cons (step782 p h) (sat_cons (step780 p h) (sat_cons (step556 p h) (sat_cons (step530 p h) (sat_cons (step743 p h) (sat_cons (step746 p h) (sat_cons (step745 p h) (sat_cons (step759 p h) (sat_cons (step756 p h) (sat_cons (step786 p h) (sat_cons (step777 p h) (sat_cons (step776 p h) (sat_cons (step775 p h) (sat_cons (step766 p h) (sat_cons (step475 p h) (sat_cons (step476 p h) (sat_cons (step513 p h) (sat_cons (step471 p h) (sat_cons (step517 p h) (sat_cons (step489 p h) (sat_cons (step516 p h) (sat_cons (step519 p h) (sat_cons (step480 p h) (sat_cons (step499 p h) (sat_cons (step477 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1569 : List Lit := [(110, true), (92, false), (1628, true), (89, true), (457, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c608, c598, c593, c600, c601, c594, c793, c790, c771, c770, c765, c764, c1519, c545, c788, c785, c783, c782, c780, c556, c530, c1434, c531, c795, c752, c750, c748, c746, c745, c772, c760, c759, c756, c786, c777, c776, c775, c766, c496, c1444, c1451, c1568, c472, c514, c491, c518, c1422, c515, c1438, c479, c1440, c478, c1425, c1456, c501, c1460, c1426, c1432, c1429] c1569 (by decide) p (sat_cons (step608 p h) (sat_cons (step598 p h) (sat_cons (step593 p h) (sat_cons (step600 p h) (sat_cons (step601 p h) (sat_cons (step594 p h) (sat_cons (step793 p h) (sat_cons (step790 p h) (sat_cons (step771 p h) (sat_cons (step770 p h) (sat_cons (step765 p h) (sat_cons (step764 p h) (sat_cons (step1519 p h) (sat_cons (step545 p h) (sat_cons (step788 p h) (sat_cons (step785 p h) (sat_cons (step783 p h) (sat_cons (step782 p h) (sat_cons (step780 p h) (sat_cons (step556 p h) (sat_cons (step530 p h) (sat_cons (step1434 p h) (sat_cons (step531 p h) (sat_cons (step795 p h) (sat_cons (step752 p h) (sat_cons (step750 p h) (sat_cons (step748 p h) (sat_cons (step746 p h) (sat_cons (step745 p h) (sat_cons (step772 p h) (sat_cons (step760 p h) (sat_cons (step759 p h) (sat_cons (step756 p h) (sat_cons (step786 p h) (sat_cons (step777 p h) (sat_cons (step776 p h) (sat_cons (step775 p h) (sat_cons (step766 p h) (sat_cons (step496 p h) (sat_cons (step1444 p h) (sat_cons (step1451 p h) (sat_cons (step1568 p h) (sat_cons (step472 p h) (sat_cons (step514 p h) (sat_cons (step491 p h) (sat_cons (step518 p h) (sat_cons (step1422 p h) (sat_cons (step515 p h) (sat_cons (step1438 p h) (sat_cons (step479 p h) (sat_cons (step1440 p h) (sat_cons (step478 p h) (sat_cons (step1425 p h) (sat_cons (step1456 p h) (sat_cons (step501 p h) (sat_cons (step1460 p h) (sat_cons (step1426 p h) (sat_cons (step1432 p h) (sat_cons (step1429 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1570 : List Lit := [(92, false), (1628, true), (89, true), (457, true), (75, true), (73, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.TreeRup.prove_clause [c608, c597, c592, c599, c591, c595, c602, c609, c1521, c598, c593, c594, c600, c601, c793, c788, c785, c783, c782, c780, c790, c771, c770, c765, c764, c1519, c545, c556, c795, c752, c750, c749, c742, c741, c748, c747, c744, c743, c746, c745, c772, c761, c755, c754, c760, c758, c757, c763, c769, c768, c767, c786, c777, c776, c775, c784, c779, c778, c781, c766, c495, c530, c493, c474, c469, c507, c510, c506, c466, c467, c481, c484, c523, c1569, c1564, c548, c1517, c555, c537, c526, c497, c471, c500, c476, c478, c514, c479, c518, c515] c1570 (by decide) p (sat_cons (step608 p h) (sat_cons (step597 p h) (sat_cons (step592 p h) (sat_cons (step599 p h) (sat_cons (step591 p h) (sat_cons (step595 p h) (sat_cons (step602 p h) (sat_cons (step609 p h) (sat_cons (step1521 p h) (sat_cons (step598 p h) (sat_cons (step593 p h) (sat_cons (step594 p h) (sat_cons (step600 p h) (sat_cons (step601 p h) (sat_cons (step793 p h) (sat_cons (step788 p h) (sat_cons (step785 p h) (sat_cons (step783 p h) (sat_cons (step782 p h) (sat_cons (step780 p h) (sat_cons (step790 p h) (sat_cons (step771 p h) (sat_cons (step770 p h) (sat_cons (step765 p h) (sat_cons (step764 p h) (sat_cons (step1519 p h) (sat_cons (step545 p h) (sat_cons (step556 p h) (sat_cons (step795 p h) (sat_cons (step752 p h) (sat_cons (step750 p h) (sat_cons (step749 p h) (sat_cons (step742 p h) (sat_cons (step741 p h) (sat_cons (step748 p h) (sat_cons (step747 p h) (sat_cons (step744 p h) (sat_cons (step743 p h) (sat_cons (step746 p h) (sat_cons (step745 p h) (sat_cons (step772 p h) (sat_cons (step761 p h) (sat_cons (step755 p h) (sat_cons (step754 p h) (sat_cons (step760 p h) (sat_cons (step758 p h) (sat_cons (step757 p h) (sat_cons (step763 p h) (sat_cons (step769 p h) (sat_cons (step768 p h) (sat_cons (step767 p h) (sat_cons (step786 p h) (sat_cons (step777 p h) (sat_cons (step776 p h) (sat_cons (step775 p h) (sat_cons (step784 p h) (sat_cons (step779 p h) (sat_cons (step778 p h) (sat_cons (step781 p h) (sat_cons (step766 p h) (sat_cons (step495 p h) (sat_cons (step530 p h) (sat_cons (step493 p h) (sat_cons (step474 p h) (sat_cons (step469 p h) (sat_cons (step507 p h) (sat_cons (step510 p h) (sat_cons (step506 p h) (sat_cons (step466 p h) (sat_cons (step467 p h) (sat_cons (step481 p h) (sat_cons (step484 p h) (sat_cons (step523 p h) (sat_cons (step1569 p h) (sat_cons (step1564 p h) (sat_cons (step548 p h) (sat_cons (step1517 p h) (sat_cons (step555 p h) (sat_cons (step537 p h) (sat_cons (step526 p h) (sat_cons (step497 p h) (sat_cons (step471 p h) (sat_cons (step500 p h) (sat_cons (step476 p h) (sat_cons (step478 p h) (sat_cons (step514 p h) (sat_cons (step479 p h) (sat_cons (step518 p h) (sat_cons (step515 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1571 : List Lit := [(1600, false), (1616, true), (98, true), (455, true)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c608, c1457, c1435, c788, c785, c783, c782, c780, c790, c771, c770, c765, c764, c1519, c545, c556, c1440, c1441, c1455, c1436, c1448, c532, c1443] c1571 (by decide) p (sat_cons (step608 p h) (sat_cons (step1457 p h) (sat_cons (step1435 p h) (sat_cons (step788 p h) (sat_cons (step785 p h) (sat_cons (step783 p h) (sat_cons (step782 p h) (sat_cons (step780 p h) (sat_cons (step790 p h) (sat_cons (step771 p h) (sat_cons (step770 p h) (sat_cons (step765 p h) (sat_cons (step764 p h) (sat_cons (step1519 p h) (sat_cons (step545 p h) (sat_cons (step556 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1455 p h) (sat_cons (step1436 p h) (sat_cons (step1448 p h) (sat_cons (step532 p h) (sat_cons (step1443 p h) (sat_nil p))))))))))))))))))))))))
def c1572 : List Lit := [(1546, false), (1650, true), (1540, false), (89, true), (457, true), (75, true), (73, true)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.TreeRup.prove_clause [c597, c592, c599, c591, c595, c602, c609, c1567, c795, c752, c751, c739, c737, c736, c464, c750, c749, c742, c741, c748, c747, c744, c793, c790, c772, c761, c755, c754, c771, c770, c765, c763, c769, c768, c767, c788, c786, c777, c776, c774, c785, c784, c779, c778, c1414, c1420, c1468, c1570, c492, c1427, c473, c470, c1403, c508, c509, c505, c465, c1428, c468, c1430, c482, c1401, c485, c1408, c524, c1423, c1415, c1424, c1421, c1431, c1469, c1459, c1571, c1437, c521, c522, c1516, c548, c1565, c1564] c1572 (by decide) p (sat_cons (step597 p h) (sat_cons (step592 p h) (sat_cons (step599 p h) (sat_cons (step591 p h) (sat_cons (step595 p h) (sat_cons (step602 p h) (sat_cons (step609 p h) (sat_cons (step1567 p h) (sat_cons (step795 p h) (sat_cons (step752 p h) (sat_cons (step751 p h) (sat_cons (step739 p h) (sat_cons (step737 p h) (sat_cons (step736 p h) (sat_cons (step464 p h) (sat_cons (step750 p h) (sat_cons (step749 p h) (sat_cons (step742 p h) (sat_cons (step741 p h) (sat_cons (step748 p h) (sat_cons (step747 p h) (sat_cons (step744 p h) (sat_cons (step793 p h) (sat_cons (step790 p h) (sat_cons (step772 p h) (sat_cons (step761 p h) (sat_cons (step755 p h) (sat_cons (step754 p h) (sat_cons (step771 p h) (sat_cons (step770 p h) (sat_cons (step765 p h) (sat_cons (step763 p h) (sat_cons (step769 p h) (sat_cons (step768 p h) (sat_cons (step767 p h) (sat_cons (step788 p h) (sat_cons (step786 p h) (sat_cons (step777 p h) (sat_cons (step776 p h) (sat_cons (step774 p h) (sat_cons (step785 p h) (sat_cons (step784 p h) (sat_cons (step779 p h) (sat_cons (step778 p h) (sat_cons (step1414 p h) (sat_cons (step1420 p h) (sat_cons (step1468 p h) (sat_cons (step1570 p h) (sat_cons (step492 p h) (sat_cons (step1427 p h) (sat_cons (step473 p h) (sat_cons (step470 p h) (sat_cons (step1403 p h) (sat_cons (step508 p h) (sat_cons (step509 p h) (sat_cons (step505 p h) (sat_cons (step465 p h) (sat_cons (step1428 p h) (sat_cons (step468 p h) (sat_cons (step1430 p h) (sat_cons (step482 p h) (sat_cons (step1401 p h) (sat_cons (step485 p h) (sat_cons (step1408 p h) (sat_cons (step524 p h) (sat_cons (step1423 p h) (sat_cons (step1415 p h) (sat_cons (step1424 p h) (sat_cons (step1421 p h) (sat_cons (step1431 p h) (sat_cons (step1469 p h) (sat_cons (step1459 p h) (sat_cons (step1571 p h) (sat_cons (step1437 p h) (sat_cons (step521 p h) (sat_cons (step522 p h) (sat_cons (step1516 p h) (sat_cons (step548 p h) (sat_cons (step1565 p h) (sat_cons (step1564 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1573 : List Lit := [(1616, true), (105, true), (98, true), (455, true), (73, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c609, c788, c786, c777, c776, c774, c785, c784, c779, c778, c1571, c1437, c521, c522, c1516, c548, c1565, c1564] c1573 (by decide) p (sat_cons (step609 p h) (sat_cons (step788 p h) (sat_cons (step786 p h) (sat_cons (step777 p h) (sat_cons (step776 p h) (sat_cons (step774 p h) (sat_cons (step785 p h) (sat_cons (step784 p h) (sat_cons (step779 p h) (sat_cons (step778 p h) (sat_cons (step1571 p h) (sat_cons (step1437 p h) (sat_cons (step521 p h) (sat_cons (step522 p h) (sat_cons (step1516 p h) (sat_cons (step548 p h) (sat_cons (step1565 p h) (sat_cons (step1564 p h) (sat_nil p)))))))))))))))))))
def c1574 : List Lit := [(457, true), (1627, true), (92, true), (73, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c597, c592, c599, c591, c595, c602, c1427, c492, c793, c795, c790, c752, c771, c772, c750, c769, c770, c761, c748, c749, c768, c765, c755, c747, c742, c767, c763, c754, c744, c741, c473, c470, c508, c509, c505, c465, c1428, c468, c1430, c482, c485, c524, c1423, c1573, c1424, c1459, c1431] c1574 (by decide) p (sat_cons (step597 p h) (sat_cons (step592 p h) (sat_cons (step599 p h) (sat_cons (step591 p h) (sat_cons (step595 p h) (sat_cons (step602 p h) (sat_cons (step1427 p h) (sat_cons (step492 p h) (sat_cons (step793 p h) (sat_cons (step795 p h) (sat_cons (step790 p h) (sat_cons (step752 p h) (sat_cons (step771 p h) (sat_cons (step772 p h) (sat_cons (step750 p h) (sat_cons (step769 p h) (sat_cons (step770 p h) (sat_cons (step761 p h) (sat_cons (step748 p h) (sat_cons (step749 p h) (sat_cons (step768 p h) (sat_cons (step765 p h) (sat_cons (step755 p h) (sat_cons (step747 p h) (sat_cons (step742 p h) (sat_cons (step767 p h) (sat_cons (step763 p h) (sat_cons (step754 p h) (sat_cons (step744 p h) (sat_cons (step741 p h) (sat_cons (step473 p h) (sat_cons (step470 p h) (sat_cons (step508 p h) (sat_cons (step509 p h) (sat_cons (step505 p h) (sat_cons (step465 p h) (sat_cons (step1428 p h) (sat_cons (step468 p h) (sat_cons (step1430 p h) (sat_cons (step482 p h) (sat_cons (step485 p h) (sat_cons (step524 p h) (sat_cons (step1423 p h) (sat_cons (step1573 p h) (sat_cons (step1424 p h) (sat_cons (step1459 p h) (sat_cons (step1431 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c1575 : List Lit := [(89, true), (103, false), (104, false), (90, false), (455, true), (92, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c608, c593, c605, c788, c786, c777, c776, c775, c518, c785, c783, c782, c780, c790, c771, c770, c765, c764, c1519, c545, c556, c772, c760, c759, c756, c491, c489, c472, c525, c512, c533] c1575 (by decide) p (sat_cons (step608 p h) (sat_cons (step593 p h) (sat_cons (step605 p h) (sat_cons (step788 p h) (sat_cons (step786 p h) (sat_cons (step777 p h) (sat_cons (step776 p h) (sat_cons (step775 p h) (sat_cons (step518 p h) (sat_cons (step785 p h) (sat_cons (step783 p h) (sat_cons (step782 p h) (sat_cons (step780 p h) (sat_cons (step790 p h) (sat_cons (step771 p h) (sat_cons (step770 p h) (sat_cons (step765 p h) (sat_cons (step764 p h) (sat_cons (step1519 p h) (sat_cons (step545 p h) (sat_cons (step556 p h) (sat_cons (step772 p h) (sat_cons (step760 p h) (sat_cons (step759 p h) (sat_cons (step756 p h) (sat_cons (step491 p h) (sat_cons (step489 p h) (sat_cons (step472 p h) (sat_cons (step525 p h) (sat_cons (step512 p h) (sat_cons (step533 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1576 : List Lit := [(19, false), (124, true), (8, false), (24, false), (32, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c127, c111, c38] c1576 (by decide) p (sat_cons (step127 p h) (sat_cons (step111 p h) (sat_cons (step38 p h) (sat_nil p))))
def c1577 : List Lit := [(27, false), (143, true), (8, false), (24, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c152, c147] c1577 (by decide) p (sat_cons (step152 p h) (sat_cons (step147 p h) (sat_nil p)))
def c1578 : List Lit := [(84, false), (100, false), (103, false), (200, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c512, c475] c1578 (by decide) p (sat_cons (step512 p h) (sat_cons (step475 p h) (sat_nil p)))
def c1579 : List Lit := [(92, false), (106, false), (116, false)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1524, c531, c494, c556, c757, c780, c758, c782, c760, c783, c772, c785, c791] c1579 (by decide) p (sat_cons (step1524 p h) (sat_cons (step531 p h) (sat_cons (step494 p h) (sat_cons (step556 p h) (sat_cons (step757 p h) (sat_cons (step780 p h) (sat_cons (step758 p h) (sat_cons (step782 p h) (sat_cons (step760 p h) (sat_cons (step783 p h) (sat_cons (step772 p h) (sat_cons (step785 p h) (sat_cons (step791 p h) (sat_nil p))))))))))))))
def c1580 : List Lit := [(109, true), (92, false), (116, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1524, c556, c494, c780, c757, c782, c758, c783, c760, c785, c772, c791] c1580 (by decide) p (sat_cons (step1524 p h) (sat_cons (step556 p h) (sat_cons (step494 p h) (sat_cons (step780 p h) (sat_cons (step757 p h) (sat_cons (step782 p h) (sat_cons (step758 p h) (sat_cons (step783 p h) (sat_cons (step760 p h) (sat_cons (step785 p h) (sat_cons (step772 p h) (sat_cons (step791 p h) (sat_nil p)))))))))))))
def c1581 : List Lit := [(1483, true), (172, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1373, c1374, c1372, c1368, c1369, c1370, c1371, c1367, c1365, c305, c231, c315] c1581 (by decide) p (sat_cons (step1373 p h) (sat_cons (step1374 p h) (sat_cons (step1372 p h) (sat_cons (step1368 p h) (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step1371 p h) (sat_cons (step1367 p h) (sat_cons (step1365 p h) (sat_cons (step305 p h) (sat_cons (step231 p h) (sat_cons (step315 p h) (sat_nil p)))))))))))))
end B112E257
