import B112E047Inputs
namespace B112E047
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1543 : List Lit := [(60, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c281, c280] c1543 (by decide) p (sat_cons (step281 p h) (sat_cons (step280 p h) (sat_nil p)))
def c1544 : List Lit := [(466, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c989, c986] c1544 (by decide) p (sat_cons (step989 p h) (sat_cons (step986 p h) (sat_nil p)))
def c1545 : List Lit := [(350, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c989, c988] c1545 (by decide) p (sat_cons (step989 p h) (sat_cons (step988 p h) (sat_nil p)))
def c1546 : List Lit := [(464, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1544, c982] c1546 (by decide) p (sat_cons (step1544 p h) (sat_cons (step982 p h) (sat_nil p)))
def c1547 : List Lit := [(406, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1544, c985] c1547 (by decide) p (sat_cons (step1544 p h) (sat_cons (step985 p h) (sat_nil p)))
def c1548 : List Lit := [(348, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1545, c855] c1548 (by decide) p (sat_cons (step1545 p h) (sat_cons (step855 p h) (sat_nil p)))
def c1549 : List Lit := [(292, false)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1545, c858] c1549 (by decide) p (sat_cons (step1545 p h) (sat_cons (step858 p h) (sat_nil p)))
def c1550 : List Lit := [(462, false)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1546, c977] c1550 (by decide) p (sat_cons (step1546 p h) (sat_cons (step977 p h) (sat_nil p)))
def c1551 : List Lit := [(434, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1546, c980] c1551 (by decide) p (sat_cons (step1546 p h) (sat_cons (step980 p h) (sat_nil p)))
def c1552 : List Lit := [(404, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1547, c910] c1552 (by decide) p (sat_cons (step1547 p h) (sat_cons (step910 p h) (sat_nil p)))
def c1553 : List Lit := [(376, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1547, c913] c1553 (by decide) p (sat_cons (step1547 p h) (sat_cons (step913 p h) (sat_nil p)))
def c1554 : List Lit := [(346, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1548, c850] c1554 (by decide) p (sat_cons (step1548 p h) (sat_cons (step850 p h) (sat_nil p)))
def c1555 : List Lit := [(318, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1548, c853] c1555 (by decide) p (sat_cons (step1548 p h) (sat_cons (step853 p h) (sat_nil p)))
def c1556 : List Lit := [(290, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1549, c793] c1556 (by decide) p (sat_cons (step1549 p h) (sat_cons (step793 p h) (sat_nil p)))
def c1557 : List Lit := [(262, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1549, c796] c1557 (by decide) p (sat_cons (step1549 p h) (sat_cons (step796 p h) (sat_nil p)))
def c1558 : List Lit := [(460, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1550, c972] c1558 (by decide) p (sat_cons (step1550 p h) (sat_cons (step972 p h) (sat_nil p)))
def c1559 : List Lit := [(446, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1550, c975] c1559 (by decide) p (sat_cons (step1550 p h) (sat_cons (step975 p h) (sat_nil p)))
def c1560 : List Lit := [(432, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1551, c942] c1560 (by decide) p (sat_cons (step1551 p h) (sat_cons (step942 p h) (sat_nil p)))
def c1561 : List Lit := [(418, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1551, c945] c1561 (by decide) p (sat_cons (step1551 p h) (sat_cons (step945 p h) (sat_nil p)))
def c1562 : List Lit := [(402, false)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1552, c905] c1562 (by decide) p (sat_cons (step1552 p h) (sat_cons (step905 p h) (sat_nil p)))
def c1563 : List Lit := [(388, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1552, c908] c1563 (by decide) p (sat_cons (step1552 p h) (sat_cons (step908 p h) (sat_nil p)))
def c1564 : List Lit := [(374, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1553, c880] c1564 (by decide) p (sat_cons (step1553 p h) (sat_cons (step880 p h) (sat_nil p)))
def c1565 : List Lit := [(362, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1553, c883] c1565 (by decide) p (sat_cons (step1553 p h) (sat_cons (step883 p h) (sat_nil p)))
def c1566 : List Lit := [(344, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1554, c846] c1566 (by decide) p (sat_cons (step1554 p h) (sat_cons (step846 p h) (sat_nil p)))
def c1567 : List Lit := [(316, false)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c1555, c817] c1567 (by decide) p (sat_cons (step1555 p h) (sat_cons (step817 p h) (sat_nil p)))
def c1568 : List Lit := [(304, false)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1555, c820] c1568 (by decide) p (sat_cons (step1555 p h) (sat_cons (step820 p h) (sat_nil p)))
def c1569 : List Lit := [(288, false)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1556, c788] c1569 (by decide) p (sat_cons (step1556 p h) (sat_cons (step788 p h) (sat_nil p)))
def c1570 : List Lit := [(274, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1556, c791] c1570 (by decide) p (sat_cons (step1556 p h) (sat_cons (step791 p h) (sat_nil p)))
def c1571 : List Lit := [(260, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1557, c759] c1571 (by decide) p (sat_cons (step1557 p h) (sat_cons (step759 p h) (sat_nil p)))
def c1572 : List Lit := [(248, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1557, c762] c1572 (by decide) p (sat_cons (step1557 p h) (sat_cons (step762 p h) (sat_nil p)))
def c1573 : List Lit := [(458, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1558, c968] c1573 (by decide) p (sat_cons (step1558 p h) (sat_cons (step968 p h) (sat_nil p)))
def c1574 : List Lit := [(444, false)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1559, c955] c1574 (by decide) p (sat_cons (step1559 p h) (sat_cons (step955 p h) (sat_nil p)))
def c1575 : List Lit := [(430, false)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c1560, c937] c1575 (by decide) p (sat_cons (step1560 p h) (sat_cons (step937 p h) (sat_nil p)))
def c1576 : List Lit := [(424, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1560, c940] c1576 (by decide) p (sat_cons (step1560 p h) (sat_cons (step940 p h) (sat_nil p)))
def c1577 : List Lit := [(416, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c1561, c923] c1577 (by decide) p (sat_cons (step1561 p h) (sat_cons (step923 p h) (sat_nil p)))
def c1578 : List Lit := [(380, false)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c1563, c894] c1578 (by decide) p (sat_cons (step1563 p h) (sat_cons (step894 p h) (sat_nil p)))
def c1579 : List Lit := [(372, false)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c1564, c876] c1579 (by decide) p (sat_cons (step1564 p h) (sat_cons (step876 p h) (sat_nil p)))
def c1580 : List Lit := [(360, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c1565, c867] c1580 (by decide) p (sat_cons (step1565 p h) (sat_cons (step867 p h) (sat_nil p)))
def c1581 : List Lit := [(342, false)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c1566, c841] c1581 (by decide) p (sat_cons (step1566 p h) (sat_cons (step841 p h) (sat_nil p)))
def c1582 : List Lit := [(336, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c1566, c844] c1582 (by decide) p (sat_cons (step1566 p h) (sat_cons (step844 p h) (sat_nil p)))
def c1583 : List Lit := [(314, false)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c1567, c814] c1583 (by decide) p (sat_cons (step1567 p h) (sat_cons (step814 p h) (sat_nil p)))
def c1584 : List Lit := [(280, false)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c1569, c786] c1584 (by decide) p (sat_cons (step1569 p h) (sat_cons (step786 p h) (sat_nil p)))
def c1585 : List Lit := [(272, false)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c1570, c771] c1585 (by decide) p (sat_cons (step1570 p h) (sat_cons (step771 p h) (sat_nil p)))
def c1586 : List Lit := [(258, false)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c1571, c757] c1586 (by decide) p (sat_cons (step1571 p h) (sat_cons (step757 p h) (sat_nil p)))
def c1587 : List Lit := [(246, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c1572, c746] c1587 (by decide) p (sat_cons (step1572 p h) (sat_cons (step746 p h) (sat_nil p)))
def c1588 : List Lit := [(420, false)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c1576, c930] c1588 (by decide) p (sat_cons (step1576 p h) (sat_cons (step930 p h) (sat_nil p)))
def c1589 : List Lit := [(412, false)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c1577, c921] c1589 (by decide) p (sat_cons (step1577 p h) (sat_cons (step921 p h) (sat_nil p)))
def c1590 : List Lit := [(378, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c1578, c888] c1590 (by decide) p (sat_cons (step1578 p h) (sat_cons (step888 p h) (sat_nil p)))
def c1591 : List Lit := [(332, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c1582, c834] c1591 (by decide) p (sat_cons (step1582 p h) (sat_cons (step834 p h) (sat_nil p)))
def c1592 : List Lit := [(270, false)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c1585, c769] c1592 (by decide) p (sat_cons (step1585 p h) (sat_cons (step769 p h) (sat_nil p)))
def c1593 : List Lit := [(254, false)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c1586, c755] c1593 (by decide) p (sat_cons (step1586 p h) (sat_cons (step755 p h) (sat_nil p)))
def c1594 : List Lit := [(121, true), (123, true), (125, true), (129, true), (130, true), (132, true), (135, true), (138, true), (139, true), (141, true), (143, true), (144, true), (146, true), (149, true), (152, true), (154, true), (155, true), (158, true), (160, true), (161, true), (164, true), (165, true), (169, true), (170, true), (172, true), (174, true), (176, true), (178, true), (181, true), (182, true), (184, true), (185, true), (189, true), (191, true), (193, true), (194, true), (198, true), (200, true), (202, true), (203, true), (207, true), (209, true), (210, true), (211, true), (214, true), (215, true), (219, true), (221, true), (222, true), (223, true), (226, true), (228, true), (229, true), (231, true), (233, true), (235, true)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.TreeRup.prove_clause [c677, c678, c679, c680, c681, c682, c683, c684, c685, c686, c687, c688, c689, c690, c691, c692, c693, c694, c695, c696, c697, c698, c699, c700, c701, c702, c703, c704, c705, c706, c707, c708, c709, c710, c711, c712, c713, c714, c715, c716, c717, c718, c719, c720, c721, c722, c723, c724, c725, c726, c727, c728, c729, c730, c731, c732, c733, c734, c735, c736, c737, c990] c1594 (by decide) p (sat_cons (step677 p h) (sat_cons (step678 p h) (sat_cons (step679 p h) (sat_cons (step680 p h) (sat_cons (step681 p h) (sat_cons (step682 p h) (sat_cons (step683 p h) (sat_cons (step684 p h) (sat_cons (step685 p h) (sat_cons (step686 p h) (sat_cons (step687 p h) (sat_cons (step688 p h) (sat_cons (step689 p h) (sat_cons (step690 p h) (sat_cons (step691 p h) (sat_cons (step692 p h) (sat_cons (step693 p h) (sat_cons (step694 p h) (sat_cons (step695 p h) (sat_cons (step696 p h) (sat_cons (step697 p h) (sat_cons (step698 p h) (sat_cons (step699 p h) (sat_cons (step700 p h) (sat_cons (step701 p h) (sat_cons (step702 p h) (sat_cons (step703 p h) (sat_cons (step704 p h) (sat_cons (step705 p h) (sat_cons (step706 p h) (sat_cons (step707 p h) (sat_cons (step708 p h) (sat_cons (step709 p h) (sat_cons (step710 p h) (sat_cons (step711 p h) (sat_cons (step712 p h) (sat_cons (step713 p h) (sat_cons (step714 p h) (sat_cons (step715 p h) (sat_cons (step716 p h) (sat_cons (step717 p h) (sat_cons (step718 p h) (sat_cons (step719 p h) (sat_cons (step720 p h) (sat_cons (step721 p h) (sat_cons (step722 p h) (sat_cons (step723 p h) (sat_cons (step724 p h) (sat_cons (step725 p h) (sat_cons (step726 p h) (sat_cons (step727 p h) (sat_cons (step728 p h) (sat_cons (step729 p h) (sat_cons (step730 p h) (sat_cons (step731 p h) (sat_cons (step732 p h) (sat_cons (step733 p h) (sat_cons (step734 p h) (sat_cons (step735 p h) (sat_cons (step736 p h) (sat_cons (step737 p h) (sat_cons (step990 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1595 : List Lit := [(1602, true)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c1289, c1293, c1281, c1283, c1270, c1279, c1275, c1276, c1267, c1268, c428, c491, c479, c496] c1595 (by decide) p (sat_cons (step1289 p h) (sat_cons (step1293 p h) (sat_cons (step1281 p h) (sat_cons (step1283 p h) (sat_cons (step1270 p h) (sat_cons (step1279 p h) (sat_cons (step1275 p h) (sat_cons (step1276 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step428 p h) (sat_cons (step491 p h) (sat_cons (step479 p h) (sat_cons (step496 p h) (sat_nil p)))))))))))))))
def c1596 : List Lit := [(1609, true)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c1595, c1307] c1596 (by decide) p (sat_cons (step1595 p h) (sat_cons (step1307 p h) (sat_nil p)))
def c1597 : List Lit := [(1582, true)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c1580, c1250, c1254, c1242, c1244, c1231, c1233, c1239, c1236, c1237, c1228, c1229, c282, c317, c302, c286, c308, c861, c862, c865] c1597 (by decide) p (sat_cons (step1580 p h) (sat_cons (step1250 p h) (sat_cons (step1254 p h) (sat_cons (step1242 p h) (sat_cons (step1244 p h) (sat_cons (step1231 p h) (sat_cons (step1233 p h) (sat_cons (step1239 p h) (sat_cons (step1236 p h) (sat_cons (step1237 p h) (sat_cons (step1228 p h) (sat_cons (step1229 p h) (sat_cons (step282 p h) (sat_cons (step317 p h) (sat_cons (step302 p h) (sat_cons (step286 p h) (sat_cons (step308 p h) (sat_cons (step861 p h) (sat_cons (step862 p h) (sat_cons (step865 p h) (sat_nil p)))))))))))))))))))))
def c1598 : List Lit := [(1610, true)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c1597, c1595, c1310] c1598 (by decide) p (sat_cons (step1597 p h) (sat_cons (step1595 p h) (sat_cons (step1310 p h) (sat_nil p))))
def c1599 : List Lit := [(1589, true), (1598, true)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c1283, c1276, c1275, c1281, c1279, c1267, c1268, c428, c491, c479, c496] c1599 (by decide) p (sat_cons (step1283 p h) (sat_cons (step1276 p h) (sat_cons (step1275 p h) (sat_cons (step1281 p h) (sat_cons (step1279 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step428 p h) (sat_cons (step491 p h) (sat_cons (step479 p h) (sat_cons (step496 p h) (sat_nil p))))))))))))
def c1600 : List Lit := [(83, false), (1598, true), (1590, true)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c1283, c1276, c1281, c1279, c425, c428, c1269] c1600 (by decide) p (sat_cons (step1283 p h) (sat_cons (step1276 p h) (sat_cons (step1281 p h) (sat_cons (step1279 p h) (sat_cons (step425 p h) (sat_cons (step428 p h) (sat_cons (step1269 p h) (sat_nil p))))))))
def c1601 : List Lit := [(89, true), (93, false), (1603, true), (1446, true)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c1544, c989, c1543, c678, c1290, c1282, c1279, c1280, c1281, c1284, c1294, c1276, c1270, c549, c1267, c1268, c429, c414, c439, c896, c897, c902, c904, c909, c983, c984, c987, c978, c856, c943, c794, c922, c760, c920, c745, c917, c743, c547, c740, c267, c3, c993, c12] c1601 (by decide) p (sat_cons (step1544 p h) (sat_cons (step989 p h) (sat_cons (step1543 p h) (sat_cons (step678 p h) (sat_cons (step1290 p h) (sat_cons (step1282 p h) (sat_cons (step1279 p h) (sat_cons (step1280 p h) (sat_cons (step1281 p h) (sat_cons (step1284 p h) (sat_cons (step1294 p h) (sat_cons (step1276 p h) (sat_cons (step1270 p h) (sat_cons (step549 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step429 p h) (sat_cons (step414 p h) (sat_cons (step439 p h) (sat_cons (step896 p h) (sat_cons (step897 p h) (sat_cons (step902 p h) (sat_cons (step904 p h) (sat_cons (step909 p h) (sat_cons (step983 p h) (sat_cons (step984 p h) (sat_cons (step987 p h) (sat_cons (step978 p h) (sat_cons (step856 p h) (sat_cons (step943 p h) (sat_cons (step794 p h) (sat_cons (step922 p h) (sat_cons (step760 p h) (sat_cons (step920 p h) (sat_cons (step745 p h) (sat_cons (step917 p h) (sat_cons (step743 p h) (sat_cons (step547 p h) (sat_cons (step740 p h) (sat_cons (step267 p h) (sat_cons (step3 p h) (sat_cons (step993 p h) (sat_cons (step12 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c1602 : List Lit := [(85, false), (80, false), (82, false), (83, true), (89, false)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c491, c479, c496] c1602 (by decide) p (sat_cons (step491 p h) (sat_cons (step479 p h) (sat_cons (step496 p h) (sat_nil p))))
def c1603 : List Lit := [(84, false), (91, false), (80, false), (83, true), (93, false), (1446, true)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c1544, c989, c1543, c678, c549, c414, c439, c896, c897, c902, c904, c909, c983, c984, c987, c978, c856, c943, c794, c922, c760, c920, c745, c917, c743, c547, c740, c267, c3, c993, c12] c1603 (by decide) p (sat_cons (step1544 p h) (sat_cons (step989 p h) (sat_cons (step1543 p h) (sat_cons (step678 p h) (sat_cons (step549 p h) (sat_cons (step414 p h) (sat_cons (step439 p h) (sat_cons (step896 p h) (sat_cons (step897 p h) (sat_cons (step902 p h) (sat_cons (step904 p h) (sat_cons (step909 p h) (sat_cons (step983 p h) (sat_cons (step984 p h) (sat_cons (step987 p h) (sat_cons (step978 p h) (sat_cons (step856 p h) (sat_cons (step943 p h) (sat_cons (step794 p h) (sat_cons (step922 p h) (sat_cons (step760 p h) (sat_cons (step920 p h) (sat_cons (step745 p h) (sat_cons (step917 p h) (sat_cons (step743 p h) (sat_cons (step547 p h) (sat_cons (step740 p h) (sat_cons (step267 p h) (sat_cons (step3 p h) (sat_cons (step993 p h) (sat_cons (step12 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1604 : List Lit := [(83, false), (1603, true)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c1298, c1271, c1290, c1600, c1294, c1270, c1267, c1268, c422, c423, c1276, c1279, c1284] c1604 (by decide) p (sat_cons (step1298 p h) (sat_cons (step1271 p h) (sat_cons (step1290 p h) (sat_cons (step1600 p h) (sat_cons (step1294 p h) (sat_cons (step1270 p h) (sat_cons (step1267 p h) (sat_cons (step1268 p h) (sat_cons (step422 p h) (sat_cons (step423 p h) (sat_cons (step1276 p h) (sat_cons (step1279 p h) (sat_cons (step1284 p h) (sat_nil p))))))))))))))
def c1605 : List Lit := [(7, true), (123, true), (1446, true)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c678, c3, c993, c12] c1605 (by decide) p (sat_cons (step678 p h) (sat_cons (step3 p h) (sat_cons (step993 p h) (sat_cons (step12 p h) (sat_nil p)))))
def c1606 : List Lit := [(1519, true), (170, true), (87, true), (80, false)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c1132, c1133, c249, c232] c1606 (by decide) p (sat_cons (step1132 p h) (sat_cons (step1133 p h) (sat_cons (step249 p h) (sat_cons (step232 p h) (sat_nil p)))))
end B112E047
