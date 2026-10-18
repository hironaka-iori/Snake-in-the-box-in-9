import B112E097Inputs
namespace B112E097
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1595 : List Lit := [(88, false), (55, false), (86, false)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c57, c359] c1595 (by decide) p (sat_cons (step57 p h) (sat_cons (step359 p h) (sat_nil p)))
def c1596 : List Lit := [(88, false), (55, false), (89, false)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c57, c360] c1596 (by decide) p (sat_cons (step57 p h) (sat_cons (step360 p h) (sat_nil p)))
def c1597 : List Lit := [(88, false), (55, false), (97, false)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c57, c361] c1597 (by decide) p (sat_cons (step57 p h) (sat_cons (step361 p h) (sat_nil p)))
def c1598 : List Lit := [(88, false), (55, false), (111, false)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c57, c362] c1598 (by decide) p (sat_cons (step57 p h) (sat_cons (step362 p h) (sat_nil p)))
def c1599 : List Lit := [(88, false), (86, false), (89, false)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c57, c363] c1599 (by decide) p (sat_cons (step57 p h) (sat_cons (step363 p h) (sat_nil p)))
def c1600 : List Lit := [(88, false), (86, false), (97, false)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c57, c364] c1600 (by decide) p (sat_cons (step57 p h) (sat_cons (step364 p h) (sat_nil p)))
def c1601 : List Lit := [(88, false), (86, false), (111, false)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c57, c365] c1601 (by decide) p (sat_cons (step57 p h) (sat_cons (step365 p h) (sat_nil p)))
def c1602 : List Lit := [(88, false), (89, false), (97, false)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c57, c366] c1602 (by decide) p (sat_cons (step57 p h) (sat_cons (step366 p h) (sat_nil p)))
def c1603 : List Lit := [(88, false), (89, false), (111, false)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c57, c367] c1603 (by decide) p (sat_cons (step57 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1604 : List Lit := [(88, false), (97, false), (111, false)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c57, c368] c1604 (by decide) p (sat_cons (step57 p h) (sat_cons (step368 p h) (sat_nil p)))
def c1605 : List Lit := [(1, false)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c688, c1] c1605 (by decide) p (sat_cons (step688 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1606 : List Lit := [(3, false)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c689, c4] c1606 (by decide) p (sat_cons (step689 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1607 : List Lit := [(4, false)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c690, c5] c1607 (by decide) p (sat_cons (step690 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1608 : List Lit := [(486, false)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c920, c917] c1608 (by decide) p (sat_cons (step920 p h) (sat_cons (step917 p h) (sat_nil p)))
def c1609 : List Lit := [(366, false)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c920, c919] c1609 (by decide) p (sat_cons (step920 p h) (sat_cons (step919 p h) (sat_nil p)))
def c1610 : List Lit := [(484, false)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c1608, c913] c1610 (by decide) p (sat_cons (step1608 p h) (sat_cons (step913 p h) (sat_nil p)))
def c1611 : List Lit := [(424, false)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c1608, c916] c1611 (by decide) p (sat_cons (step1608 p h) (sat_cons (step916 p h) (sat_nil p)))
def c1612 : List Lit := [(364, false)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c1609, c831] c1612 (by decide) p (sat_cons (step1609 p h) (sat_cons (step831 p h) (sat_nil p)))
def c1613 : List Lit := [(304, false)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c1609, c834] c1613 (by decide) p (sat_cons (step1609 p h) (sat_cons (step834 p h) (sat_nil p)))
def c1614 : List Lit := [(482, false)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c1610, c908] c1614 (by decide) p (sat_cons (step1610 p h) (sat_cons (step908 p h) (sat_nil p)))
def c1615 : List Lit := [(452, false)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c1610, c911] c1615 (by decide) p (sat_cons (step1610 p h) (sat_cons (step911 p h) (sat_nil p)))
def c1616 : List Lit := [(422, false)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c1611, c869] c1616 (by decide) p (sat_cons (step1611 p h) (sat_cons (step869 p h) (sat_nil p)))
def c1617 : List Lit := [(394, false)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c1611, c872] c1617 (by decide) p (sat_cons (step1611 p h) (sat_cons (step872 p h) (sat_nil p)))
def c1618 : List Lit := [(362, false)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c1612, c827] c1618 (by decide) p (sat_cons (step1612 p h) (sat_cons (step827 p h) (sat_nil p)))
def c1619 : List Lit := [(332, false)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c1612, c829] c1619 (by decide) p (sat_cons (step1612 p h) (sat_cons (step829 p h) (sat_nil p)))
def c1620 : List Lit := [(274, false)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c1613, c788] c1620 (by decide) p (sat_cons (step1613 p h) (sat_cons (step788 p h) (sat_nil p)))
def c1621 : List Lit := [(480, false)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c1614, c905] c1621 (by decide) p (sat_cons (step1614 p h) (sat_cons (step905 p h) (sat_nil p)))
def c1622 : List Lit := [(436, false)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c1615, c893] c1622 (by decide) p (sat_cons (step1615 p h) (sat_cons (step893 p h) (sat_nil p)))
def c1623 : List Lit := [(406, false)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c1616, c867] c1623 (by decide) p (sat_cons (step1616 p h) (sat_cons (step867 p h) (sat_nil p)))
def c1624 : List Lit := [(378, false)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c1617, c852] c1624 (by decide) p (sat_cons (step1617 p h) (sat_cons (step852 p h) (sat_nil p)))
def c1625 : List Lit := [(360, false)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c1618, c824] c1625 (by decide) p (sat_cons (step1618 p h) (sat_cons (step824 p h) (sat_nil p)))
def c1626 : List Lit := [(272, false)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c1620, c763] c1626 (by decide) p (sat_cons (step1620 p h) (sat_cons (step763 p h) (sat_nil p)))
def c1627 : List Lit := [(258, false)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c1620, c766] c1627 (by decide) p (sat_cons (step1620 p h) (sat_cons (step766 p h) (sat_nil p)))
def c1628 : List Lit := [(434, false)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c1622, c881] c1628 (by decide) p (sat_cons (step1622 p h) (sat_cons (step881 p h) (sat_nil p)))
def c1629 : List Lit := [(376, false)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c1624, c841] c1629 (by decide) p (sat_cons (step1624 p h) (sat_cons (step841 p h) (sat_nil p)))
def c1630 : List Lit := [(358, false)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c1625, c821] c1630 (by decide) p (sat_cons (step1625 p h) (sat_cons (step821 p h) (sat_nil p)))
def c1631 : List Lit := [(270, false)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c1626, c760] c1631 (by decide) p (sat_cons (step1626 p h) (sat_cons (step760 p h) (sat_nil p)))
def c1632 : List Lit := [(372, false)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c1629, c839] c1632 (by decide) p (sat_cons (step1629 p h) (sat_cons (step839 p h) (sat_nil p)))
def c1633 : List Lit := [(834, true)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c1606, c1607, c921] c1633 (by decide) p (sat_cons (step1606 p h) (sat_cons (step1607 p h) (sat_cons (step921 p h) (sat_nil p))))
def c1634 : List Lit := [(836, true)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c1633, c922] c1634 (by decide) p (sat_cons (step1633 p h) (sat_cons (step922 p h) (sat_nil p)))
def c1635 : List Lit := [(837, true)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1633, c923] c1635 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1633 p h) (sat_cons (step923 p h) (sat_nil p))))
def c1636 : List Lit := [(843, false), (849, true)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c1634, c937] c1636 (by decide) p (sat_cons (step1634 p h) (sat_cons (step937 p h) (sat_nil p)))
def c1637 : List Lit := [(848, true)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c1635, c938] c1637 (by decide) p (sat_cons (step1635 p h) (sat_cons (step938 p h) (sat_nil p)))
def c1638 : List Lit := [(842, false), (849, true)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c1635, c939] c1638 (by decide) p (sat_cons (step1635 p h) (sat_cons (step939 p h) (sat_nil p)))
def c1639 : List Lit := [(843, false), (850, true)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c1635, c940] c1639 (by decide) p (sat_cons (step1635 p h) (sat_cons (step940 p h) (sat_nil p)))
def c1640 : List Lit := [(844, false), (851, true)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c1635, c941] c1640 (by decide) p (sat_cons (step1635 p h) (sat_cons (step941 p h) (sat_nil p)))
def c1641 : List Lit := [(879, true)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c1637, c978] c1641 (by decide) p (sat_cons (step1637 p h) (sat_cons (step978 p h) (sat_nil p)))
def c1642 : List Lit := [(869, false), (880, true)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c1637, c979] c1642 (by decide) p (sat_cons (step1637 p h) (sat_cons (step979 p h) (sat_nil p)))
def c1643 : List Lit := [(870, false), (881, true)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c1637, c980] c1643 (by decide) p (sat_cons (step1637 p h) (sat_cons (step980 p h) (sat_nil p)))
def c1644 : List Lit := [(871, false), (882, true)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c1637, c981] c1644 (by decide) p (sat_cons (step1637 p h) (sat_cons (step981 p h) (sat_nil p)))
def c1645 : List Lit := [(872, false), (883, true)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c1637, c982] c1645 (by decide) p (sat_cons (step1637 p h) (sat_cons (step982 p h) (sat_nil p)))
def c1646 : List Lit := [(873, false), (884, true)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c1637, c983] c1646 (by decide) p (sat_cons (step1637 p h) (sat_cons (step983 p h) (sat_nil p)))
def c1647 : List Lit := [(941, false), (959, true)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c1641, c1100] c1647 (by decide) p (sat_cons (step1641 p h) (sat_cons (step1100 p h) (sat_nil p)))
def c1648 : List Lit := [(942, false), (960, true)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c1641, c1101] c1648 (by decide) p (sat_cons (step1641 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c1649 : List Lit := [(943, false), (961, true)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c1641, c1102] c1649 (by decide) p (sat_cons (step1641 p h) (sat_cons (step1102 p h) (sat_nil p)))
def c1650 : List Lit := [(1645, true)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c1632, c1507, c1508, c1505, c1506, c1501, c1504, c1502, c1503, c1499, c1500, c285, c272, c279, c277, c837] c1650 (by decide) p (sat_cons (step1632 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step1505 p h) (sat_cons (step1506 p h) (sat_cons (step1501 p h) (sat_cons (step1504 p h) (sat_cons (step1502 p h) (sat_cons (step1503 p h) (sat_cons (step1499 p h) (sat_cons (step1500 p h) (sat_cons (step285 p h) (sat_cons (step272 p h) (sat_cons (step279 p h) (sat_cons (step277 p h) (sat_cons (step837 p h) (sat_nil p)))))))))))))))))
def c1651 : List Lit := [(861, true), (23, false), (24, false)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c951, c952, c1545] c1651 (by decide) p (sat_cons (step951 p h) (sat_cons (step952 p h) (sat_cons (step1545 p h) (sat_nil p))))
def c1652 : List Lit := [(1067, true)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c740, c1327, c1329, c1324, c1325, c1321, c1322, c687, c624, c631] c1652 (by decide) p (sat_cons (step740 p h) (sat_cons (step1327 p h) (sat_cons (step1329 p h) (sat_cons (step1324 p h) (sat_cons (step1325 p h) (sat_cons (step1321 p h) (sat_cons (step1322 p h) (sat_cons (step687 p h) (sat_cons (step624 p h) (sat_cons (step631 p h) (sat_nil p)))))))))))
def c1653 : List Lit := [(1071, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1335] c1653 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1335 p h) (sat_nil p)))
def c1654 : List Lit := [(1072, true), (115, true)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c1652, c740, c1322, c1336, c1338, c1332, c1330, c1313, c1323, c1324, c1325, c1310, c687, c623, c631] c1654 (by decide) p (sat_cons (step1652 p h) (sat_cons (step740 p h) (sat_cons (step1322 p h) (sat_cons (step1336 p h) (sat_cons (step1338 p h) (sat_cons (step1332 p h) (sat_cons (step1330 p h) (sat_cons (step1313 p h) (sat_cons (step1323 p h) (sat_cons (step1324 p h) (sat_cons (step1325 p h) (sat_cons (step1310 p h) (sat_cons (step687 p h) (sat_cons (step623 p h) (sat_cons (step631 p h) (sat_nil p))))))))))))))))
def c1655 : List Lit := [(1043, true), (1055, true), (114, false)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c734, c1308, c1307, c1279, c1281, c1276, c1277, c1273, c1274, c532, c484, c475, c445] c1655 (by decide) p (sat_cons (step734 p h) (sat_cons (step1308 p h) (sat_cons (step1307 p h) (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step532 p h) (sat_cons (step484 p h) (sat_cons (step475 p h) (sat_cons (step445 p h) (sat_nil p))))))))))))))
def c1656 : List Lit := [(1011, true), (92, false), (1001, false), (89, true), (114, false)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c1186, c1194, c1199, c1203, c1195, c1174, c1187, c1171, c401] c1656 (by decide) p (sat_cons (step1186 p h) (sat_cons (step1194 p h) (sat_cons (step1199 p h) (sat_cons (step1203 p h) (sat_cons (step1195 p h) (sat_cons (step1174 p h) (sat_cons (step1187 p h) (sat_cons (step1171 p h) (sat_cons (step401 p h) (sat_nil p))))))))))
def c1657 : List Lit := [(106, false), (107, true), (109, false), (1040, true), (111, false)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c736, c591, c557, c482, c484, c1275] c1657 (by decide) p (sat_cons (step736 p h) (sat_cons (step591 p h) (sat_cons (step557 p h) (sat_cons (step482 p h) (sat_cons (step484 p h) (sat_cons (step1275 p h) (sat_nil p)))))))
def c1658 : List Lit := [(107, true), (109, false), (1044, true), (102, true), (111, false)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c734, c1284, c1657, c1277, c1282, c1273, c1274, c445, c480] c1658 (by decide) p (sat_cons (step734 p h) (sat_cons (step1284 p h) (sat_cons (step1657 p h) (sat_cons (step1277 p h) (sat_cons (step1282 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step445 p h) (sat_cons (step480 p h) (sat_nil p))))))))))
end B112E097
