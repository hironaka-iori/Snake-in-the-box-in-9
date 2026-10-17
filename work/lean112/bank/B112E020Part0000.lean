import B112E020Inputs
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1612 : List Lit := [(1, true)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c5, c4] c1612 (by decide) p (sat_cons (step5 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1613 : List Lit := [(9, false), (28, false), (44, false)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c1612, c24] c1613 (by decide) p (sat_cons (step1612 p h) (sat_cons (step24 p h) (sat_nil p)))
def c1614 : List Lit := [(13, false)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c775, c49] c1614 (by decide) p (sat_cons (step775 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1615 : List Lit := [(490, false)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c1015, c1012] c1615 (by decide) p (sat_cons (step1015 p h) (sat_cons (step1012 p h) (sat_nil p)))
def c1616 : List Lit := [(368, false)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c1015, c1014] c1616 (by decide) p (sat_cons (step1015 p h) (sat_cons (step1014 p h) (sat_nil p)))
def c1617 : List Lit := [(488, false)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1008] c1617 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1008 p h) (sat_nil p)))
def c1618 : List Lit := [(428, false)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1011] c1618 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1011 p h) (sat_nil p)))
def c1619 : List Lit := [(366, false)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c1616, c916] c1619 (by decide) p (sat_cons (step1616 p h) (sat_cons (step916 p h) (sat_nil p)))
def c1620 : List Lit := [(306, false)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c1616, c919] c1620 (by decide) p (sat_cons (step1616 p h) (sat_cons (step919 p h) (sat_nil p)))
def c1621 : List Lit := [(486, false)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1003] c1621 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1003 p h) (sat_nil p)))
def c1622 : List Lit := [(456, false)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c1617, c1006] c1622 (by decide) p (sat_cons (step1617 p h) (sat_cons (step1006 p h) (sat_nil p)))
def c1623 : List Lit := [(426, false)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c1618, c958] c1623 (by decide) p (sat_cons (step1618 p h) (sat_cons (step958 p h) (sat_nil p)))
def c1624 : List Lit := [(364, false)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c1619, c911] c1624 (by decide) p (sat_cons (step1619 p h) (sat_cons (step911 p h) (sat_nil p)))
def c1625 : List Lit := [(334, false)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c1619, c914] c1625 (by decide) p (sat_cons (step1619 p h) (sat_cons (step914 p h) (sat_nil p)))
def c1626 : List Lit := [(304, false)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c1620, c862] c1626 (by decide) p (sat_cons (step1620 p h) (sat_cons (step862 p h) (sat_nil p)))
def c1627 : List Lit := [(276, false)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c1620, c865] c1627 (by decide) p (sat_cons (step1620 p h) (sat_cons (step865 p h) (sat_nil p)))
def c1628 : List Lit := [(484, false)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c1621, c999] c1628 (by decide) p (sat_cons (step1621 p h) (sat_cons (step999 p h) (sat_nil p)))
def c1629 : List Lit := [(454, false)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c1622, c978] c1629 (by decide) p (sat_cons (step1622 p h) (sat_cons (step978 p h) (sat_nil p)))
def c1630 : List Lit := [(424, false)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c1623, c955] c1630 (by decide) p (sat_cons (step1623 p h) (sat_cons (step955 p h) (sat_nil p)))
def c1631 : List Lit := [(362, false)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c1624, c906] c1631 (by decide) p (sat_cons (step1624 p h) (sat_cons (step906 p h) (sat_nil p)))
def c1632 : List Lit := [(348, false)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c1624, c909] c1632 (by decide) p (sat_cons (step1624 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1633 : List Lit := [(318, false)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c1625, c888] c1633 (by decide) p (sat_cons (step1625 p h) (sat_cons (step888 p h) (sat_nil p)))
def c1634 : List Lit := [(288, false)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c1626, c860] c1634 (by decide) p (sat_cons (step1626 p h) (sat_cons (step860 p h) (sat_nil p)))
def c1635 : List Lit := [(260, false)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c1627, c844] c1635 (by decide) p (sat_cons (step1627 p h) (sat_cons (step844 p h) (sat_nil p)))
def c1636 : List Lit := [(446, false)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c1629, c976] c1636 (by decide) p (sat_cons (step1629 p h) (sat_cons (step976 p h) (sat_nil p)))
def c1637 : List Lit := [(310, false)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c1633, c874] c1637 (by decide) p (sat_cons (step1633 p h) (sat_cons (step874 p h) (sat_nil p)))
def c1638 : List Lit := [(286, false)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c1634, c852] c1638 (by decide) p (sat_cons (step1634 p h) (sat_cons (step852 p h) (sat_nil p)))
def c1639 : List Lit := [(252, false)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c1635, c832] c1639 (by decide) p (sat_cons (step1635 p h) (sat_cons (step832 p h) (sat_nil p)))
def c1640 : List Lit := [(442, false)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c1636, c971] c1640 (by decide) p (sat_cons (step1636 p h) (sat_cons (step971 p h) (sat_nil p)))
def c1641 : List Lit := [(1517, true)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1047] c1641 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1047 p h) (sat_nil p)))
def c1642 : List Lit := [(15, true), (1518, true)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c1614, c1048] c1642 (by decide) p (sat_cons (step1614 p h) (sat_cons (step1048 p h) (sat_nil p)))
def c1643 : List Lit := [(1521, true)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c1641, c1052] c1643 (by decide) p (sat_cons (step1641 p h) (sat_cons (step1052 p h) (sat_nil p)))
def c1644 : List Lit := [(1519, false), (1522, true)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c1641, c1053] c1644 (by decide) p (sat_cons (step1641 p h) (sat_cons (step1053 p h) (sat_nil p)))
def c1645 : List Lit := [(1520, false), (1523, true)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c1641, c1054] c1645 (by decide) p (sat_cons (step1641 p h) (sat_cons (step1054 p h) (sat_nil p)))
def c1646 : List Lit := [(1530, false), (1535, true)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c1643, c1072] c1646 (by decide) p (sat_cons (step1643 p h) (sat_cons (step1072 p h) (sat_nil p)))
def c1647 : List Lit := [(1531, false), (1536, true)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c1643, c1073] c1647 (by decide) p (sat_cons (step1643 p h) (sat_cons (step1073 p h) (sat_nil p)))
def c1648 : List Lit := [(1659, true)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c802, c1290, c1294, c1282, c1284, c1268, c1270, c1280, c1276, c1277, c1265, c1262, c407, c424, c365, c422] c1648 (by decide) p (sat_cons (step802 p h) (sat_cons (step1290 p h) (sat_cons (step1294 p h) (sat_cons (step1282 p h) (sat_cons (step1284 p h) (sat_cons (step1268 p h) (sat_cons (step1270 p h) (sat_cons (step1280 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step1265 p h) (sat_cons (step1262 p h) (sat_cons (step407 p h) (sat_cons (step424 p h) (sat_cons (step365 p h) (sat_cons (step422 p h) (sat_nil p)))))))))))))))))
def c1649 : List Lit := [(18, false), (1525, true)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c777, c1059, c1058, c68, c107] c1649 (by decide) p (sat_cons (step777 p h) (sat_cons (step1059 p h) (sat_cons (step1058 p h) (sat_cons (step68 p h) (sat_cons (step107 p h) (sat_nil p))))))
def c1650 : List Lit := [(18, true), (1535, true)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c776, c1079, c1645, c1049, c1051, c1644, c1056, c1075, c1642, c1064, c1061, c1062, c63, c134, c59] c1650 (by decide) p (sat_cons (step776 p h) (sat_cons (step1079 p h) (sat_cons (step1645 p h) (sat_cons (step1049 p h) (sat_cons (step1051 p h) (sat_cons (step1644 p h) (sat_cons (step1056 p h) (sat_cons (step1075 p h) (sat_cons (step1642 p h) (sat_cons (step1064 p h) (sat_cons (step1061 p h) (sat_cons (step1062 p h) (sat_cons (step63 p h) (sat_cons (step134 p h) (sat_cons (step59 p h) (sat_nil p))))))))))))))))
def c1651 : List Lit := [(1535, true)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c777, c1646, c1650, c69, c1649, c1066, c1067, c1075, c1061, c1644, c65, c1050] c1651 (by decide) p (sat_cons (step777 p h) (sat_cons (step1646 p h) (sat_cons (step1650 p h) (sat_cons (step69 p h) (sat_cons (step1649 p h) (sat_cons (step1066 p h) (sat_cons (step1067 p h) (sat_cons (step1075 p h) (sat_cons (step1061 p h) (sat_cons (step1644 p h) (sat_cons (step65 p h) (sat_cons (step1050 p h) (sat_nil p)))))))))))))
def c1652 : List Lit := [(1691, true)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c1648, c1351] c1652 (by decide) p (sat_cons (step1648 p h) (sat_cons (step1351 p h) (sat_nil p)))
def c1653 : List Lit := [(1568, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c788, c1129, c1131, c1126, c1127, c1123, c199, c201] c1653 (by decide) p (sat_cons (step788 p h) (sat_cons (step1129 p h) (sat_cons (step1131 p h) (sat_cons (step1126 p h) (sat_cons (step1127 p h) (sat_cons (step1123 p h) (sat_cons (step199 p h) (sat_cons (step201 p h) (sat_nil p)))))))))
def c1654 : List Lit := [(1596, true)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c793, c1180, c1184, c1174, c1158, c1160, c1167, c1155, c1156, c1152, c1153, c238, c262, c223, c258] c1654 (by decide) p (sat_cons (step793 p h) (sat_cons (step1180 p h) (sat_cons (step1184 p h) (sat_cons (step1174 p h) (sat_cons (step1158 p h) (sat_cons (step1160 p h) (sat_cons (step1167 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1152 p h) (sat_cons (step1153 p h) (sat_cons (step238 p h) (sat_cons (step262 p h) (sat_cons (step223 p h) (sat_cons (step258 p h) (sat_nil p))))))))))))))))
def c1655 : List Lit := [(1560, true), (1584, true)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c791, c1158, c1155, c1156, c1160, c1153, c232, c1115, c1117, c1112, c1110, c214, c246, c249, c1557] c1655 (by decide) p (sat_cons (step791 p h) (sat_cons (step1158 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1160 p h) (sat_cons (step1153 p h) (sat_cons (step232 p h) (sat_cons (step1115 p h) (sat_cons (step1117 p h) (sat_cons (step1112 p h) (sat_cons (step1110 p h) (sat_cons (step214 p h) (sat_cons (step246 p h) (sat_cons (step249 p h) (sat_cons (step1557 p h) (sat_nil p))))))))))))))))
def c1656 : List Lit := [(1661, true), (73, true), (1643, false), (45, false)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c799, c1279, c1282, c1270, c1296, c1300, c1283, c1285, c1271, c1281, c1276, c1265, c1266, c424, c355, c369, c380] c1656 (by decide) p (sat_cons (step799 p h) (sat_cons (step1279 p h) (sat_cons (step1282 p h) (sat_cons (step1270 p h) (sat_cons (step1296 p h) (sat_cons (step1300 p h) (sat_cons (step1283 p h) (sat_cons (step1285 p h) (sat_cons (step1271 p h) (sat_cons (step1281 p h) (sat_cons (step1276 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step424 p h) (sat_cons (step355 p h) (sat_cons (step369 p h) (sat_cons (step380 p h) (sat_nil p))))))))))))))))))
def c1657 : List Lit := [(1645, true), (68, false), (69, false), (45, false)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c799, c1265, c1266, c424, c355, c369, c380] c1657 (by decide) p (sat_cons (step799 p h) (sat_cons (step1265 p h) (sat_cons (step1266 p h) (sat_cons (step424 p h) (sat_cons (step355 p h) (sat_cons (step369 p h) (sat_cons (step380 p h) (sat_nil p))))))))
def c1658 : List Lit := [(49, false), (1584, true)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c793, c1158, c1155, c1156, c1160, c1153, c232, c1152, c262, c223, c258] c1658 (by decide) p (sat_cons (step793 p h) (sat_cons (step1158 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1160 p h) (sat_cons (step1153 p h) (sat_cons (step232 p h) (sat_cons (step1152 p h) (sat_cons (step262 p h) (sat_cons (step223 p h) (sat_cons (step258 p h) (sat_nil p))))))))))))
def c1659 : List Lit := [(1748, true), (119, false), (66, false), (1731, false)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1460, c1456, c1432, c1443, c1426, c1441, c690] c1659 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1460 p h) (sat_cons (step1456 p h) (sat_cons (step1432 p h) (sat_cons (step1443 p h) (sat_cons (step1426 p h) (sat_cons (step1441 p h) (sat_cons (step690 p h) (sat_nil p)))))))))
def c1660 : List Lit := [(1709, false), (115, false), (1724, true), (118, false)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1386, c1389, c1412, c1380, c1399, c653, c1397] c1660 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1386 p h) (sat_cons (step1389 p h) (sat_cons (step1412 p h) (sat_cons (step1380 p h) (sat_cons (step1399 p h) (sat_cons (step653 p h) (sat_cons (step1397 p h) (sat_nil p)))))))))
def c1661 : List Lit := [(94, false), (115, false), (1758, true), (118, false), (1731, false)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c653, c655, c656, c1397, c1426, c1438, c1399, c1432, c1445, c1407, c1461, c1480] c1661 (by decide) p (sat_cons (step653 p h) (sat_cons (step655 p h) (sat_cons (step656 p h) (sat_cons (step1397 p h) (sat_cons (step1426 p h) (sat_cons (step1438 p h) (sat_cons (step1399 p h) (sat_cons (step1432 p h) (sat_cons (step1445 p h) (sat_cons (step1407 p h) (sat_cons (step1461 p h) (sat_cons (step1480 p h) (sat_nil p)))))))))))))
def c1662 : List Lit := [(115, false), (1724, true), (1758, true), (118, false), (1731, false)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c1661, c1380, c1388, c1411, c1412, c1480, c1399, c1397, c658, c659, c1426, c1438, c1432, c1445, c1461] c1662 (by decide) p (sat_cons (step1661 p h) (sat_cons (step1380 p h) (sat_cons (step1388 p h) (sat_cons (step1411 p h) (sat_cons (step1412 p h) (sat_cons (step1480 p h) (sat_cons (step1399 p h) (sat_cons (step1397 p h) (sat_cons (step658 p h) (sat_cons (step659 p h) (sat_cons (step1426 p h) (sat_cons (step1438 p h) (sat_cons (step1432 p h) (sat_cons (step1445 p h) (sat_cons (step1461 p h) (sat_nil p))))))))))))))))
def c1663 : List Lit := [(1719, true), (115, true)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c816, c1399, c1401, c1396, c1397, c1393, c537, c540] c1663 (by decide) p (sat_cons (step816 p h) (sat_cons (step1399 p h) (sat_cons (step1401 p h) (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step1393 p h) (sat_cons (step537 p h) (sat_cons (step540 p h) (sat_nil p)))))))))
def c1664 : List Lit := [(1717, true), (1748, true), (115, true)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c816, c1396, c1397, c537, c546, c547, c1423, c1438, c1431, c1445, c1456] c1664 (by decide) p (sat_cons (step816 p h) (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step537 p h) (sat_cons (step546 p h) (sat_cons (step547 p h) (sat_cons (step1423 p h) (sat_cons (step1438 p h) (sat_cons (step1431 p h) (sat_cons (step1445 p h) (sat_cons (step1456 p h) (sat_nil p))))))))))))
def c1665 : List Lit := [(104, false), (1711, false), (115, true), (1758, true)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c816, c1663, c1412, c1486, c1664, c537, c538, c1597, c1393, c1402, c1413, c1492, c1451, c1455, c1445, c1431, c1438, c1423, c548] c1665 (by decide) p (sat_cons (step816 p h) (sat_cons (step1663 p h) (sat_cons (step1412 p h) (sat_cons (step1486 p h) (sat_cons (step1664 p h) (sat_cons (step537 p h) (sat_cons (step538 p h) (sat_cons (step1597 p h) (sat_cons (step1393 p h) (sat_cons (step1402 p h) (sat_cons (step1413 p h) (sat_cons (step1492 p h) (sat_cons (step1451 p h) (sat_cons (step1455 p h) (sat_cons (step1445 p h) (sat_cons (step1431 p h) (sat_cons (step1438 p h) (sat_cons (step1423 p h) (sat_cons (step548 p h) (sat_nil p))))))))))))))))))))
def c1666 : List Lit := [(1741, true), (1707, false), (115, true), (1758, true), (118, false)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c822, c1663, c1440, c1441, c746, c684, c680, c681, c1384, c1426, c1389, c1429, c1417, c1455, c1492] c1666 (by decide) p (sat_cons (step822 p h) (sat_cons (step1663 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step746 p h) (sat_cons (step684 p h) (sat_cons (step680 p h) (sat_cons (step681 p h) (sat_cons (step1384 p h) (sat_cons (step1426 p h) (sat_cons (step1389 p h) (sat_cons (step1429 p h) (sat_cons (step1417 p h) (sat_cons (step1455 p h) (sat_cons (step1492 p h) (sat_nil p))))))))))))))))
def c1667 : List Lit := [(1707, false), (115, true), (1758, true), (118, false)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c817, c1663, c1388, c1412, c1486, c1452, c1665, c1666, c1443, c1446, c1451, c1456, c1438, c1492, c1429, c1431, c1413, c1427, c1423, c1400, c1398, c609, c549, c552] c1667 (by decide) p (sat_cons (step817 p h) (sat_cons (step1663 p h) (sat_cons (step1388 p h) (sat_cons (step1412 p h) (sat_cons (step1486 p h) (sat_cons (step1452 p h) (sat_cons (step1665 p h) (sat_cons (step1666 p h) (sat_cons (step1443 p h) (sat_cons (step1446 p h) (sat_cons (step1451 p h) (sat_cons (step1456 p h) (sat_cons (step1438 p h) (sat_cons (step1492 p h) (sat_cons (step1429 p h) (sat_cons (step1431 p h) (sat_cons (step1413 p h) (sat_cons (step1427 p h) (sat_cons (step1423 p h) (sat_cons (step1400 p h) (sat_cons (step1398 p h) (sat_cons (step609 p h) (sat_cons (step549 p h) (sat_cons (step552 p h) (sat_nil p)))))))))))))))))))))))))
def c1668 : List Lit := [(1743, false), (1748, true), (104, true), (1711, false), (1758, true)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c817, c1397, c1451, c1456, c1492, c1429, c1431, c1413, c1427, c1423, c1400, c1402, c1398, c1393, c609, c543, c552] c1668 (by decide) p (sat_cons (step817 p h) (sat_cons (step1397 p h) (sat_cons (step1451 p h) (sat_cons (step1456 p h) (sat_cons (step1492 p h) (sat_cons (step1429 p h) (sat_cons (step1431 p h) (sat_cons (step1413 p h) (sat_cons (step1427 p h) (sat_cons (step1423 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1398 p h) (sat_cons (step1393 p h) (sat_cons (step609 p h) (sat_cons (step543 p h) (sat_cons (step552 p h) (sat_nil p))))))))))))))))))
def c1669 : List Lit := [(115, true), (1758, true), (118, false)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c812, c822, c1663, c1667, c1380, c1381, c498, c513, c1383, c1386, c1665, c1412, c1486, c1668, c1443, c1440, c1441, c746, c684, c680, c681, c1385, c1426, c1387, c1429, c1417, c1455, c1492] c1669 (by decide) p (sat_cons (step812 p h) (sat_cons (step822 p h) (sat_cons (step1663 p h) (sat_cons (step1667 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step498 p h) (sat_cons (step513 p h) (sat_cons (step1383 p h) (sat_cons (step1386 p h) (sat_cons (step1665 p h) (sat_cons (step1412 p h) (sat_cons (step1486 p h) (sat_cons (step1668 p h) (sat_cons (step1443 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step746 p h) (sat_cons (step684 p h) (sat_cons (step680 p h) (sat_cons (step681 p h) (sat_cons (step1385 p h) (sat_cons (step1426 p h) (sat_cons (step1387 p h) (sat_cons (step1429 p h) (sat_cons (step1417 p h) (sat_cons (step1455 p h) (sat_cons (step1492 p h) (sat_nil p)))))))))))))))))))))))))))))
def c1670 : List Lit := [(1743, true), (1758, true), (118, false)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c815, c1669, c1443, c1445, c1440, c1438, c660, c656, c659, c1426, c1380, c1397, c1429, c1388, c1399, c1455, c1412, c1492, c1486, c1413, c1417, c1460, c1402, c1389, c1430, c1394, c1383, c1428, c521, c743, c519] c1670 (by decide) p (sat_cons (step815 p h) (sat_cons (step1669 p h) (sat_cons (step1443 p h) (sat_cons (step1445 p h) (sat_cons (step1440 p h) (sat_cons (step1438 p h) (sat_cons (step660 p h) (sat_cons (step656 p h) (sat_cons (step659 p h) (sat_cons (step1426 p h) (sat_cons (step1380 p h) (sat_cons (step1397 p h) (sat_cons (step1429 p h) (sat_cons (step1388 p h) (sat_cons (step1399 p h) (sat_cons (step1455 p h) (sat_cons (step1412 p h) (sat_cons (step1492 p h) (sat_cons (step1486 p h) (sat_cons (step1413 p h) (sat_cons (step1417 p h) (sat_cons (step1460 p h) (sat_cons (step1402 p h) (sat_cons (step1389 p h) (sat_cons (step1430 p h) (sat_cons (step1394 p h) (sat_cons (step1383 p h) (sat_cons (step1428 p h) (sat_cons (step521 p h) (sat_cons (step743 p h) (sat_cons (step519 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1671 : List Lit := [(104, true), (1724, true), (1758, true), (118, false)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c817, c1669, c1662, c1423, c1408, c1400, c1670, c1397, c1398, c1399, c1402, c1407, c1412, c1393, c1480, c1388, c543, c1461, c1380, c552, c1430, c655, c609, c1428] c1671 (by decide) p (sat_cons (step817 p h) (sat_cons (step1669 p h) (sat_cons (step1662 p h) (sat_cons (step1423 p h) (sat_cons (step1408 p h) (sat_cons (step1400 p h) (sat_cons (step1670 p h) (sat_cons (step1397 p h) (sat_cons (step1398 p h) (sat_cons (step1399 p h) (sat_cons (step1402 p h) (sat_cons (step1407 p h) (sat_cons (step1412 p h) (sat_cons (step1393 p h) (sat_cons (step1480 p h) (sat_cons (step1388 p h) (sat_cons (step543 p h) (sat_cons (step1461 p h) (sat_cons (step1380 p h) (sat_cons (step552 p h) (sat_cons (step1430 p h) (sat_cons (step655 p h) (sat_cons (step609 p h) (sat_cons (step1428 p h) (sat_nil p)))))))))))))))))))))))))
def c1672 : List Lit := [(1724, true), (115, false), (1758, true), (118, false)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c816, c1662, c1423, c1424, c1671, c653, c1380, c1388, c1412, c1399, c1401, c1396, c1393, c546, c523, c539] c1672 (by decide) p (sat_cons (step816 p h) (sat_cons (step1662 p h) (sat_cons (step1423 p h) (sat_cons (step1424 p h) (sat_cons (step1671 p h) (sat_cons (step653 p h) (sat_cons (step1380 p h) (sat_cons (step1388 p h) (sat_cons (step1412 p h) (sat_cons (step1399 p h) (sat_cons (step1401 p h) (sat_cons (step1396 p h) (sat_cons (step1393 p h) (sat_cons (step546 p h) (sat_cons (step523 p h) (sat_cons (step539 p h) (sat_nil p)))))))))))))))))
def c1673 : List Lit := [(1758, true), (118, false)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c1669, c1670, c1672, c1486, c1456, c1429, c1426, c655, c658, c1380, c1668, c1388] c1673 (by decide) p (sat_cons (step1669 p h) (sat_cons (step1670 p h) (sat_cons (step1672 p h) (sat_cons (step1486 p h) (sat_cons (step1456 p h) (sat_cons (step1429 p h) (sat_cons (step1426 p h) (sat_cons (step655 p h) (sat_cons (step658 p h) (sat_cons (step1380 p h) (sat_cons (step1668 p h) (sat_cons (step1388 p h) (sat_nil p)))))))))))))
def c1674 : List Lit := [(123, true), (117, true), (121, false), (122, true), (107, false)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c823, c721, c723, c1603] c1674 (by decide) p (sat_cons (step823 p h) (sat_cons (step721 p h) (sat_cons (step723 p h) (sat_cons (step1603 p h) (sat_nil p)))))
def c1675 : List Lit := [(28, false), (25, false), (16, false), (24, false)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c776, c110, c111, c60] c1675 (by decide) p (sat_cons (step776 p h) (sat_cons (step110 p h) (sat_cons (step111 p h) (sat_cons (step60 p h) (sat_nil p)))))
end B112E020
