import B112E024Part0003
namespace B112E024
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1618 : List Lit := [(27, true), (101, true), (99, false), (100, true)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c620, c500] c1618 (by decide) p (sat_cons (step620 p h) (sat_cons (step500 p h) (sat_nil p)))
def c1619 : List Lit := [(27, true), (101, true), (99, false), (88, true)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c620, c501] c1619 (by decide) p (sat_cons (step620 p h) (sat_cons (step501 p h) (sat_nil p)))
def c1620 : List Lit := [(27, true), (100, true), (99, false), (88, true)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c620, c502] c1620 (by decide) p (sat_cons (step620 p h) (sat_cons (step502 p h) (sat_nil p)))
def c1621 : List Lit := [(101, true), (100, true), (102, false), (95, true), (103, true)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c621, c516] c1621 (by decide) p (sat_cons (step621 p h) (sat_cons (step516 p h) (sat_nil p)))
def c1622 : List Lit := [(100, true), (95, true), (103, true), (90, true), (102, false)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c621, c517] c1622 (by decide) p (sat_cons (step621 p h) (sat_cons (step517 p h) (sat_nil p)))
def c1623 : List Lit := [(101, true), (100, true), (102, false), (90, true), (95, true)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c621, c518] c1623 (by decide) p (sat_cons (step621 p h) (sat_cons (step518 p h) (sat_nil p)))
def c1624 : List Lit := [(113, true), (109, true), (82, true), (105, false)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c622, c526] c1624 (by decide) p (sat_cons (step622 p h) (sat_cons (step526 p h) (sat_nil p)))
def c1625 : List Lit := [(113, true), (104, true), (82, true), (105, false)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c622, c527] c1625 (by decide) p (sat_cons (step622 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1626 : List Lit := [(104, true), (109, true), (105, false), (82, true)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c622, c528] c1626 (by decide) p (sat_cons (step622 p h) (sat_cons (step528 p h) (sat_nil p)))
def c1627 : List Lit := [(112, true), (106, true), (107, false)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c623, c532] c1627 (by decide) p (sat_cons (step623 p h) (sat_cons (step532 p h) (sat_nil p)))
def c1628 : List Lit := [(112, true), (107, false), (87, true)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c623, c533] c1628 (by decide) p (sat_cons (step623 p h) (sat_cons (step533 p h) (sat_nil p)))
def c1629 : List Lit := [(106, true), (107, false), (87, true)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c623, c534] c1629 (by decide) p (sat_cons (step623 p h) (sat_cons (step534 p h) (sat_nil p)))
def c1630 : List Lit := [(104, true), (109, true), (108, false)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c624, c535] c1630 (by decide) p (sat_cons (step624 p h) (sat_cons (step535 p h) (sat_nil p)))
def c1631 : List Lit := [(109, true), (108, false), (88, true)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c624, c536] c1631 (by decide) p (sat_cons (step624 p h) (sat_cons (step536 p h) (sat_nil p)))
def c1632 : List Lit := [(104, true), (108, false), (88, true)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c624, c537] c1632 (by decide) p (sat_cons (step624 p h) (sat_cons (step537 p h) (sat_nil p)))
def c1633 : List Lit := [(109, true), (38, true), (71, true), (90, true), (110, false)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c625, c545] c1633 (by decide) p (sat_cons (step625 p h) (sat_cons (step545 p h) (sat_nil p)))
def c1634 : List Lit := [(120, true), (112, true), (111, false)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c626, c546] c1634 (by decide) p (sat_cons (step626 p h) (sat_cons (step546 p h) (sat_nil p)))
def c1635 : List Lit := [(120, true), (109, true), (111, false)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c626, c547] c1635 (by decide) p (sat_cons (step626 p h) (sat_cons (step547 p h) (sat_nil p)))
def c1636 : List Lit := [(109, true), (112, true), (111, false)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c626, c548] c1636 (by decide) p (sat_cons (step626 p h) (sat_cons (step548 p h) (sat_nil p)))
def c1637 : List Lit := [(114, true), (113, true), (115, false)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c627, c558] c1637 (by decide) p (sat_cons (step627 p h) (sat_cons (step558 p h) (sat_nil p)))
def c1638 : List Lit := [(114, true), (95, true), (115, false)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c627, c559] c1638 (by decide) p (sat_cons (step627 p h) (sat_cons (step559 p h) (sat_nil p)))
def c1639 : List Lit := [(113, true), (95, true), (115, false)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c627, c560] c1639 (by decide) p (sat_cons (step627 p h) (sat_cons (step560 p h) (sat_nil p)))
def c1640 : List Lit := [(114, true), (121, true), (117, false), (106, true)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c628, c568] c1640 (by decide) p (sat_cons (step628 p h) (sat_cons (step568 p h) (sat_nil p)))
def c1641 : List Lit := [(114, true), (118, false), (101, true), (121, true)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c629, c571] c1641 (by decide) p (sat_cons (step629 p h) (sat_cons (step571 p h) (sat_nil p)))
def c1642 : List Lit := [(118, false), (121, true), (101, true), (46, true)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c629, c573] c1642 (by decide) p (sat_cons (step629 p h) (sat_cons (step573 p h) (sat_nil p)))
def c1643 : List Lit := [(121, true), (116, true), (119, false)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c630, c575] c1643 (by decide) p (sat_cons (step630 p h) (sat_cons (step575 p h) (sat_nil p)))
def c1644 : List Lit := [(289, false), (291, false)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c1380, c659] c1644 (by decide) p (sat_cons (step1380 p h) (sat_cons (step659 p h) (sat_nil p)))
def c1645 : List Lit := [(287, false), (293, false)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c1378, c662] c1645 (by decide) p (sat_cons (step1378 p h) (sat_cons (step662 p h) (sat_nil p)))
def c1646 : List Lit := [(281, false), (295, false)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c1375, c666] c1646 (by decide) p (sat_cons (step1375 p h) (sat_cons (step666 p h) (sat_nil p)))
def c1647 : List Lit := [(269, false), (297, false)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c1370, c670] c1647 (by decide) p (sat_cons (step1370 p h) (sat_cons (step670 p h) (sat_nil p)))
def c1648 : List Lit := [(331, false), (337, false)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c1377, c688] c1648 (by decide) p (sat_cons (step1377 p h) (sat_cons (step688 p h) (sat_nil p)))
def c1649 : List Lit := [(339, false), (353, false)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c1374, c697] c1649 (by decide) p (sat_cons (step1374 p h) (sat_cons (step697 p h) (sat_nil p)))
def c1650 : List Lit := [(327, false), (355, false)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c1369, c702] c1650 (by decide) p (sat_cons (step1369 p h) (sat_cons (step702 p h) (sat_nil p)))
def c1651 : List Lit := [(299, false), (357, false)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c1366, c706] c1651 (by decide) p (sat_cons (step1366 p h) (sat_cons (step706 p h) (sat_nil p)))
def c1652 : List Lit := [(371, false), (385, false)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c1373, c727] c1652 (by decide) p (sat_cons (step1373 p h) (sat_cons (step727 p h) (sat_nil p)))
def c1653 : List Lit := [(399, false), (413, false)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c1372, c741] c1653 (by decide) p (sat_cons (step1372 p h) (sat_cons (step741 p h) (sat_nil p)))
def c1654 : List Lit := [(387, false), (415, false)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c1368, c745] c1654 (by decide) p (sat_cons (step1368 p h) (sat_cons (step745 p h) (sat_nil p)))
def c1655 : List Lit := [(429, false), (443, false)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c1371, c762] c1655 (by decide) p (sat_cons (step1371 p h) (sat_cons (step762 p h) (sat_nil p)))
def c1656 : List Lit := [(445, false), (473, false)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c1367, c773] c1656 (by decide) p (sat_cons (step1367 p h) (sat_cons (step773 p h) (sat_nil p)))
def c1657 : List Lit := [(417, false), (475, false)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c1365, c778] c1657 (by decide) p (sat_cons (step1365 p h) (sat_cons (step778 p h) (sat_nil p)))
def c1658 : List Lit := [(359, false), (477, false)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c783, c781] c1658 (by decide) p (sat_cons (step783 p h) (sat_cons (step781 p h) (sat_nil p)))
def c1659 : List Lit := [(1483, false), (1492, true)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c1396, c863] c1659 (by decide) p (sat_cons (step1396 p h) (sat_cons (step863 p h) (sat_nil p)))
def c1660 : List Lit := [(1481, false), (1491, true)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c1399, c865] c1660 (by decide) p (sat_cons (step1399 p h) (sat_cons (step865 p h) (sat_nil p)))
def c1661 : List Lit := [(1482, false), (1492, true)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c1399, c866] c1661 (by decide) p (sat_cons (step1399 p h) (sat_cons (step866 p h) (sat_nil p)))
def c1662 : List Lit := [(1483, false), (1493, true)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c1399, c867] c1662 (by decide) p (sat_cons (step1399 p h) (sat_cons (step867 p h) (sat_nil p)))
def c1663 : List Lit := [(1480, false), (1491, true)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c1506, c869] c1663 (by decide) p (sat_cons (step1506 p h) (sat_cons (step869 p h) (sat_nil p)))
def c1664 : List Lit := [(1492, true), (1481, false)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c1506, c870] c1664 (by decide) p (sat_cons (step1506 p h) (sat_cons (step870 p h) (sat_nil p)))
def c1665 : List Lit := [(1482, false), (1493, true)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c1506, c871] c1665 (by decide) p (sat_cons (step1506 p h) (sat_cons (step871 p h) (sat_nil p)))
def c1666 : List Lit := [(1483, false), (1494, true)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c1506, c872] c1666 (by decide) p (sat_cons (step1506 p h) (sat_cons (step872 p h) (sat_nil p)))
def c1667 : List Lit := [(1484, false), (1495, true)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c1506, c873] c1667 (by decide) p (sat_cons (step1506 p h) (sat_cons (step873 p h) (sat_nil p)))
def c1668 : List Lit := [(1491, true), (1459, false)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c1397, c874] c1668 (by decide) p (sat_cons (step1397 p h) (sat_cons (step874 p h) (sat_nil p)))
def c1669 : List Lit := [(1556, false), (1575, true)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c1400, c998] c1669 (by decide) p (sat_cons (step1400 p h) (sat_cons (step998 p h) (sat_nil p)))
def c1670 : List Lit := [(1553, false), (1573, true)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c1507, c999] c1670 (by decide) p (sat_cons (step1507 p h) (sat_cons (step999 p h) (sat_nil p)))
def c1671 : List Lit := [(1574, true), (1554, false)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c1507, c1000] c1671 (by decide) p (sat_cons (step1507 p h) (sat_cons (step1000 p h) (sat_nil p)))
def c1672 : List Lit := [(1555, false), (1575, true)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c1507, c1001] c1672 (by decide) p (sat_cons (step1507 p h) (sat_cons (step1001 p h) (sat_nil p)))
def c1673 : List Lit := [(1556, false), (1576, true)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c1507, c1002] c1673 (by decide) p (sat_cons (step1507 p h) (sat_cons (step1002 p h) (sat_nil p)))
def c1674 : List Lit := [(1557, false), (1577, true)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c1507, c1003] c1674 (by decide) p (sat_cons (step1507 p h) (sat_cons (step1003 p h) (sat_nil p)))
def c1675 : List Lit := [(1694, true), (1689, false)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c1423, c1220] c1675 (by decide) p (sat_cons (step1423 p h) (sat_cons (step1220 p h) (sat_nil p)))
def c1676 : List Lit := [(1690, false), (1695, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c1423, c1221] c1676 (by decide) p (sat_cons (step1423 p h) (sat_cons (step1221 p h) (sat_nil p)))
def c1677 : List Lit := [(1702, true), (1669, false)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1230] c1677 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1230 p h) (sat_nil p)))
def c1678 : List Lit := [(1703, true), (1670, false)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1235] c1678 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1235 p h) (sat_nil p)))
def c1679 : List Lit := [(1671, false), (1704, true)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1240] c1679 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1240 p h) (sat_nil p)))
def c1680 : List Lit := [(1672, false), (1705, true)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1246] c1680 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1246 p h) (sat_nil p)))
def c1681 : List Lit := [(1673, false), (1706, true)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1251] c1681 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1251 p h) (sat_nil p)))
end B112E024
