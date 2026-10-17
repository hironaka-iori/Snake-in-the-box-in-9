import B112E258Inputs
namespace B112E258
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1498 : List Lit := [(5, false)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c640, c8] c1498 (by decide) p (sat_cons (step640 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1499 : List Lit := [(107, false)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c688, c572] c1499 (by decide) p (sat_cons (step688 p h) (sat_cons (step572 p h) (sat_nil p)))
def c1500 : List Lit := [(482, false)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c919, c916] c1500 (by decide) p (sat_cons (step919 p h) (sat_cons (step916 p h) (sat_nil p)))
def c1501 : List Lit := [(362, false)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c919, c918] c1501 (by decide) p (sat_cons (step919 p h) (sat_cons (step918 p h) (sat_nil p)))
def c1502 : List Lit := [(480, false)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c1500, c912] c1502 (by decide) p (sat_cons (step1500 p h) (sat_cons (step912 p h) (sat_nil p)))
def c1503 : List Lit := [(420, false)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c1500, c915] c1503 (by decide) p (sat_cons (step1500 p h) (sat_cons (step915 p h) (sat_nil p)))
def c1504 : List Lit := [(360, false)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c1501, c806] c1504 (by decide) p (sat_cons (step1501 p h) (sat_cons (step806 p h) (sat_nil p)))
def c1505 : List Lit := [(302, false)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c1501, c809] c1505 (by decide) p (sat_cons (step1501 p h) (sat_cons (step809 p h) (sat_nil p)))
def c1506 : List Lit := [(478, false)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c1502, c907] c1506 (by decide) p (sat_cons (step1502 p h) (sat_cons (step907 p h) (sat_nil p)))
def c1507 : List Lit := [(448, false)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c1502, c910] c1507 (by decide) p (sat_cons (step1502 p h) (sat_cons (step910 p h) (sat_nil p)))
def c1508 : List Lit := [(390, false)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c1503, c854] c1508 (by decide) p (sat_cons (step1503 p h) (sat_cons (step854 p h) (sat_nil p)))
def c1509 : List Lit := [(358, false)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c1504, c801] c1509 (by decide) p (sat_cons (step1504 p h) (sat_cons (step801 p h) (sat_nil p)))
def c1510 : List Lit := [(330, false)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c1504, c804] c1510 (by decide) p (sat_cons (step1504 p h) (sat_cons (step804 p h) (sat_nil p)))
def c1511 : List Lit := [(300, false)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c1505, c747] c1511 (by decide) p (sat_cons (step1505 p h) (sat_cons (step747 p h) (sat_nil p)))
def c1512 : List Lit := [(272, false)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c1505, c750] c1512 (by decide) p (sat_cons (step1505 p h) (sat_cons (step750 p h) (sat_nil p)))
def c1513 : List Lit := [(476, false)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c1506, c903] c1513 (by decide) p (sat_cons (step1506 p h) (sat_cons (step903 p h) (sat_nil p)))
def c1514 : List Lit := [(446, false)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c1507, c878] c1514 (by decide) p (sat_cons (step1507 p h) (sat_cons (step878 p h) (sat_nil p)))
def c1515 : List Lit := [(388, false)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c1508, c833] c1515 (by decide) p (sat_cons (step1508 p h) (sat_cons (step833 p h) (sat_nil p)))
def c1516 : List Lit := [(356, false)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c1509, c797] c1516 (by decide) p (sat_cons (step1509 p h) (sat_cons (step797 p h) (sat_nil p)))
def c1517 : List Lit := [(328, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c1510, c772] c1517 (by decide) p (sat_cons (step1510 p h) (sat_cons (step772 p h) (sat_nil p)))
def c1518 : List Lit := [(314, false)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c1510, c775] c1518 (by decide) p (sat_cons (step1510 p h) (sat_cons (step775 p h) (sat_nil p)))
def c1519 : List Lit := [(284, false)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c1511, c745] c1519 (by decide) p (sat_cons (step1511 p h) (sat_cons (step745 p h) (sat_nil p)))
def c1520 : List Lit := [(256, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c1512, c720] c1520 (by decide) p (sat_cons (step1512 p h) (sat_cons (step720 p h) (sat_nil p)))
def c1521 : List Lit := [(468, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c1513, c901] c1521 (by decide) p (sat_cons (step1513 p h) (sat_cons (step901 p h) (sat_nil p)))
def c1522 : List Lit := [(444, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c1514, c874] c1522 (by decide) p (sat_cons (step1514 p h) (sat_cons (step874 p h) (sat_nil p)))
def c1523 : List Lit := [(380, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c1515, c831] c1523 (by decide) p (sat_cons (step1515 p h) (sat_cons (step831 p h) (sat_nil p)))
def c1524 : List Lit := [(320, false)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c1517, c770] c1524 (by decide) p (sat_cons (step1517 p h) (sat_cons (step770 p h) (sat_nil p)))
def c1525 : List Lit := [(312, false)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c1518, c759] c1525 (by decide) p (sat_cons (step1518 p h) (sat_cons (step759 p h) (sat_nil p)))
def c1526 : List Lit := [(282, false)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c1519, c728] c1526 (by decide) p (sat_cons (step1519 p h) (sat_cons (step728 p h) (sat_nil p)))
def c1527 : List Lit := [(254, false)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c1520, c705] c1527 (by decide) p (sat_cons (step1520 p h) (sat_cons (step705 p h) (sat_nil p)))
def c1528 : List Lit := [(466, false)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c1521, c893] c1528 (by decide) p (sat_cons (step1521 p h) (sat_cons (step893 p h) (sat_nil p)))
def c1529 : List Lit := [(278, false)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c1526, c726] c1529 (by decide) p (sat_cons (step1526 p h) (sat_cons (step726 p h) (sat_nil p)))
def c1530 : List Lit := [(123, true), (125, true), (126, true), (128, true), (129, true), (131, true), (132, true), (133, true), (136, true), (138, true), (141, true), (142, true), (145, true), (146, true), (148, true), (149, true), (152, true), (154, true), (156, true), (158, true), (160, true), (162, true), (164, true), (167, true), (168, true), (170, true), (171, true), (175, true), (176, true), (178, true), (179, true), (181, true), (182, true), (184, true), (186, true), (190, true), (192, true), (193, true), (194, true), (196, true), (197, true), (198, true), (202, true), (205, true), (209, true), (211, true), (213, true), (214, true), (217, true), (218, true), (219, true), (222, true), (223, true), (225, true), (226, true), (228, true), (231, true), (232, true), (236, true), (237, true), (239, true), (240, true), (243, true), (244, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c639, c640, c641, c642, c643, c644, c645, c646, c647, c648, c649, c650, c651, c652, c653, c654, c655, c656, c657, c658, c659, c660, c661, c662, c663, c664, c665, c666, c667, c668, c669, c670, c671, c672, c673, c674, c675, c676, c677, c678, c679, c680, c681, c682, c683, c684, c685, c686, c687, c688, c689, c690, c691, c692, c693, c694, c695, c920] c1530 (by decide) p (sat_cons (step639 p h) (sat_cons (step640 p h) (sat_cons (step641 p h) (sat_cons (step642 p h) (sat_cons (step643 p h) (sat_cons (step644 p h) (sat_cons (step645 p h) (sat_cons (step646 p h) (sat_cons (step647 p h) (sat_cons (step648 p h) (sat_cons (step649 p h) (sat_cons (step650 p h) (sat_cons (step651 p h) (sat_cons (step652 p h) (sat_cons (step653 p h) (sat_cons (step654 p h) (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step657 p h) (sat_cons (step658 p h) (sat_cons (step659 p h) (sat_cons (step660 p h) (sat_cons (step661 p h) (sat_cons (step662 p h) (sat_cons (step663 p h) (sat_cons (step664 p h) (sat_cons (step665 p h) (sat_cons (step666 p h) (sat_cons (step667 p h) (sat_cons (step668 p h) (sat_cons (step669 p h) (sat_cons (step670 p h) (sat_cons (step671 p h) (sat_cons (step672 p h) (sat_cons (step673 p h) (sat_cons (step674 p h) (sat_cons (step675 p h) (sat_cons (step676 p h) (sat_cons (step677 p h) (sat_cons (step678 p h) (sat_cons (step679 p h) (sat_cons (step680 p h) (sat_cons (step681 p h) (sat_cons (step682 p h) (sat_cons (step683 p h) (sat_cons (step684 p h) (sat_cons (step685 p h) (sat_cons (step686 p h) (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step689 p h) (sat_cons (step690 p h) (sat_cons (step691 p h) (sat_cons (step692 p h) (sat_cons (step693 p h) (sat_cons (step694 p h) (sat_cons (step695 p h) (sat_cons (step920 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1531 : List Lit := [(1501, true)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c1498, c921] c1531 (by decide) p (sat_cons (step1498 p h) (sat_cons (step921 p h) (sat_nil p)))
def c1532 : List Lit := [(8, true), (1502, true)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c1498, c922] c1532 (by decide) p (sat_cons (step1498 p h) (sat_cons (step922 p h) (sat_nil p)))
def c1533 : List Lit := [(1503, true)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1531, c923] c1533 (by decide) p (sat_cons (step1531 p h) (sat_cons (step923 p h) (sat_nil p)))
def c1534 : List Lit := [(2, true), (1504, true)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1531, c925] c1534 (by decide) p (sat_cons (step1531 p h) (sat_cons (step925 p h) (sat_nil p)))
def c1535 : List Lit := [(1514, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1533, c941] c1535 (by decide) p (sat_cons (step1533 p h) (sat_cons (step941 p h) (sat_nil p)))
def c1536 : List Lit := [(1510, false), (1515, true)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1533, c942] c1536 (by decide) p (sat_cons (step1533 p h) (sat_cons (step942 p h) (sat_nil p)))
def c1537 : List Lit := [(1511, false), (1516, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1533, c943] c1537 (by decide) p (sat_cons (step1533 p h) (sat_cons (step943 p h) (sat_nil p)))
def c1538 : List Lit := [(1512, false), (1517, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1533, c944] c1538 (by decide) p (sat_cons (step1533 p h) (sat_cons (step944 p h) (sat_nil p)))
def c1539 : List Lit := [(1513, false), (1518, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1533, c945] c1539 (by decide) p (sat_cons (step1533 p h) (sat_cons (step945 p h) (sat_nil p)))
def c1540 : List Lit := [(1541, true)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1535, c994] c1540 (by decide) p (sat_cons (step1535 p h) (sat_cons (step994 p h) (sat_nil p)))
def c1541 : List Lit := [(1534, false), (1542, true)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1535, c995] c1541 (by decide) p (sat_cons (step1535 p h) (sat_cons (step995 p h) (sat_nil p)))
def c1542 : List Lit := [(1535, false), (1543, true)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1535, c996] c1542 (by decide) p (sat_cons (step1535 p h) (sat_cons (step996 p h) (sat_nil p)))
def c1543 : List Lit := [(1536, false), (1544, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1535, c997] c1543 (by decide) p (sat_cons (step1535 p h) (sat_cons (step997 p h) (sat_nil p)))
def c1544 : List Lit := [(1537, false), (1545, true)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1535, c998] c1544 (by decide) p (sat_cons (step1535 p h) (sat_cons (step998 p h) (sat_nil p)))
def c1545 : List Lit := [(1538, false), (1546, true)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1535, c999] c1545 (by decide) p (sat_cons (step1535 p h) (sat_cons (step999 p h) (sat_nil p)))
def c1546 : List Lit := [(1539, false), (1547, true)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1535, c1000] c1546 (by decide) p (sat_cons (step1535 p h) (sat_cons (step1000 p h) (sat_nil p)))
def c1547 : List Lit := [(1600, false), (1616, true)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1540, c1115] c1547 (by decide) p (sat_cons (step1540 p h) (sat_cons (step1115 p h) (sat_nil p)))
def c1548 : List Lit := [(1601, false), (1617, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1540, c1116] c1548 (by decide) p (sat_cons (step1540 p h) (sat_cons (step1116 p h) (sat_nil p)))
def c1549 : List Lit := [(1602, false), (1618, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1540, c1117] c1549 (by decide) p (sat_cons (step1540 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c1550 : List Lit := [(1603, false), (1619, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1540, c1118] c1550 (by decide) p (sat_cons (step1540 p h) (sat_cons (step1118 p h) (sat_nil p)))
def c1551 : List Lit := [(1604, false), (1620, true)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1540, c1119] c1551 (by decide) p (sat_cons (step1540 p h) (sat_cons (step1119 p h) (sat_nil p)))
def c1552 : List Lit := [(1706, true)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1325] c1552 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1325 p h) (sat_nil p)))
def c1553 : List Lit := [(108, true), (1707, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1499, c1326] c1553 (by decide) p (sat_cons (step1499 p h) (sat_cons (step1326 p h) (sat_nil p)))
def c1554 : List Lit := [(1710, true)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1330] c1554 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1330 p h) (sat_nil p)))
def c1555 : List Lit := [(1708, false), (1711, true)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1331] c1555 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1331 p h) (sat_nil p)))
def c1556 : List Lit := [(1709, false), (1712, true)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1552, c1332] c1556 (by decide) p (sat_cons (step1552 p h) (sat_cons (step1332 p h) (sat_nil p)))
def c1557 : List Lit := [(1722, true)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1348] c1557 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1348 p h) (sat_nil p)))
def c1558 : List Lit := [(1718, false), (1723, true)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1349] c1558 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1349 p h) (sat_nil p)))
def c1559 : List Lit := [(1719, false), (1724, true)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1350] c1559 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1350 p h) (sat_nil p)))
def c1560 : List Lit := [(1720, false), (1725, true)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1351] c1560 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1351 p h) (sat_nil p)))
def c1561 : List Lit := [(1702, false), (1734, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1557, c1376] c1561 (by decide) p (sat_cons (step1557 p h) (sat_cons (step1376 p h) (sat_nil p)))
end B112E258
