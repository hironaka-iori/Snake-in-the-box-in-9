import B112E026Part0003
namespace B112E026
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1658 : List Lit := [(90, true), (71, true), (38, true), (110, false), (109, true)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c680, c589] c1658 (by decide) p (sat_cons (step680 p h) (sat_cons (step589 p h) (sat_nil p)))
def c1659 : List Lit := [(120, true), (111, false), (112, true)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c681, c591] c1659 (by decide) p (sat_cons (step681 p h) (sat_cons (step591 p h) (sat_nil p)))
def c1660 : List Lit := [(120, true), (111, false), (109, true)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c681, c592] c1660 (by decide) p (sat_cons (step681 p h) (sat_cons (step592 p h) (sat_nil p)))
def c1661 : List Lit := [(109, true), (112, true), (111, false)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c681, c593] c1661 (by decide) p (sat_cons (step681 p h) (sat_cons (step593 p h) (sat_nil p)))
def c1662 : List Lit := [(114, true), (113, true), (115, false)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c682, c605] c1662 (by decide) p (sat_cons (step682 p h) (sat_cons (step605 p h) (sat_nil p)))
def c1663 : List Lit := [(114, true), (115, false), (95, true)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c682, c606] c1663 (by decide) p (sat_cons (step682 p h) (sat_cons (step606 p h) (sat_nil p)))
def c1664 : List Lit := [(113, true), (115, false), (95, true)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c682, c607] c1664 (by decide) p (sat_cons (step682 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1665 : List Lit := [(114, true), (121, true), (106, true), (117, false)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c683, c618] c1665 (by decide) p (sat_cons (step683 p h) (sat_cons (step618 p h) (sat_nil p)))
def c1666 : List Lit := [(114, true), (101, true), (121, true), (118, false)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c684, c620] c1666 (by decide) p (sat_cons (step684 p h) (sat_cons (step620 p h) (sat_nil p)))
def c1667 : List Lit := [(114, true), (46, true), (121, true), (118, false)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c684, c621] c1667 (by decide) p (sat_cons (step684 p h) (sat_cons (step621 p h) (sat_nil p)))
def c1668 : List Lit := [(121, true), (46, true), (118, false), (101, true)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c684, c622] c1668 (by decide) p (sat_cons (step684 p h) (sat_cons (step622 p h) (sat_nil p)))
def c1669 : List Lit := [(120, true), (121, true), (119, false)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c685, c624] c1669 (by decide) p (sat_cons (step685 p h) (sat_cons (step624 p h) (sat_nil p)))
def c1670 : List Lit := [(121, true), (116, true), (119, false)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c685, c625] c1670 (by decide) p (sat_cons (step685 p h) (sat_cons (step625 p h) (sat_nil p)))
def c1671 : List Lit := [(120, true), (116, true), (119, false)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c685, c626] c1671 (by decide) p (sat_cons (step685 p h) (sat_cons (step626 p h) (sat_nil p)))
def c1672 : List Lit := [(289, false), (291, false)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c1418, c706] c1672 (by decide) p (sat_cons (step1418 p h) (sat_cons (step706 p h) (sat_nil p)))
def c1673 : List Lit := [(331, false), (337, false)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c1416, c734] c1673 (by decide) p (sat_cons (step1416 p h) (sat_cons (step734 p h) (sat_nil p)))
def c1674 : List Lit := [(339, false), (353, false)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c1413, c744] c1674 (by decide) p (sat_cons (step1413 p h) (sat_cons (step744 p h) (sat_nil p)))
def c1675 : List Lit := [(327, false), (355, false)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c1408, c749] c1675 (by decide) p (sat_cons (step1408 p h) (sat_cons (step749 p h) (sat_nil p)))
def c1676 : List Lit := [(299, false), (357, false)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c1405, c753] c1676 (by decide) p (sat_cons (step1405 p h) (sat_cons (step753 p h) (sat_nil p)))
def c1677 : List Lit := [(391, false), (397, false)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c1415, c776] c1677 (by decide) p (sat_cons (step1415 p h) (sat_cons (step776 p h) (sat_nil p)))
def c1678 : List Lit := [(399, false), (413, false)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c1412, c782] c1678 (by decide) p (sat_cons (step1412 p h) (sat_cons (step782 p h) (sat_nil p)))
def c1679 : List Lit := [(387, false), (415, false)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c1407, c787] c1679 (by decide) p (sat_cons (step1407 p h) (sat_cons (step787 p h) (sat_nil p)))
def c1680 : List Lit := [(429, false), (443, false)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c1411, c806] c1680 (by decide) p (sat_cons (step1411 p h) (sat_cons (step806 p h) (sat_nil p)))
def c1681 : List Lit := [(457, false), (471, false)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c1410, c822] c1681 (by decide) p (sat_cons (step1410 p h) (sat_cons (step822 p h) (sat_nil p)))
def c1682 : List Lit := [(445, false), (473, false)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c1406, c826] c1682 (by decide) p (sat_cons (step1406 p h) (sat_cons (step826 p h) (sat_nil p)))
def c1683 : List Lit := [(417, false), (475, false)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c1404, c831] c1683 (by decide) p (sat_cons (step1404 p h) (sat_cons (step831 p h) (sat_nil p)))
def c1684 : List Lit := [(359, false), (477, false)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c836, c834] c1684 (by decide) p (sat_cons (step836 p h) (sat_cons (step834 p h) (sat_nil p)))
def c1685 : List Lit := [(1481, false), (1491, true)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c1435, c912] c1685 (by decide) p (sat_cons (step1435 p h) (sat_cons (step912 p h) (sat_nil p)))
def c1686 : List Lit := [(1482, false), (1492, true)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c1435, c913] c1686 (by decide) p (sat_cons (step1435 p h) (sat_cons (step913 p h) (sat_nil p)))
def c1687 : List Lit := [(1483, false), (1493, true)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c1435, c914] c1687 (by decide) p (sat_cons (step1435 p h) (sat_cons (step914 p h) (sat_nil p)))
def c1688 : List Lit := [(1479, false), (1490, true)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c1506, c916] c1688 (by decide) p (sat_cons (step1506 p h) (sat_cons (step916 p h) (sat_nil p)))
def c1689 : List Lit := [(1480, false), (1491, true)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c1506, c917] c1689 (by decide) p (sat_cons (step1506 p h) (sat_cons (step917 p h) (sat_nil p)))
def c1690 : List Lit := [(1481, false), (1492, true)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c1506, c918] c1690 (by decide) p (sat_cons (step1506 p h) (sat_cons (step918 p h) (sat_nil p)))
def c1691 : List Lit := [(1482, false), (1493, true)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c1506, c919] c1691 (by decide) p (sat_cons (step1506 p h) (sat_cons (step919 p h) (sat_nil p)))
def c1692 : List Lit := [(1483, false), (1494, true)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c1506, c920] c1692 (by decide) p (sat_cons (step1506 p h) (sat_cons (step920 p h) (sat_nil p)))
def c1693 : List Lit := [(1484, false), (1495, true)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c1506, c921] c1693 (by decide) p (sat_cons (step1506 p h) (sat_cons (step921 p h) (sat_nil p)))
def c1694 : List Lit := [(1519, true), (1506, false)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c1459, c961] c1694 (by decide) p (sat_cons (step1459 p h) (sat_cons (step961 p h) (sat_nil p)))
def c1695 : List Lit := [(1507, false), (1520, true)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c1459, c965] c1695 (by decide) p (sat_cons (step1459 p h) (sat_cons (step965 p h) (sat_nil p)))
def c1696 : List Lit := [(1508, false), (1521, true)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c1459, c968] c1696 (by decide) p (sat_cons (step1459 p h) (sat_cons (step968 p h) (sat_nil p)))
def c1697 : List Lit := [(1509, false), (1522, true)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c1459, c970] c1697 (by decide) p (sat_cons (step1459 p h) (sat_cons (step970 p h) (sat_nil p)))
def c1698 : List Lit := [(1530, false), (1543, true)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c1432, c1003] c1698 (by decide) p (sat_cons (step1432 p h) (sat_cons (step1003 p h) (sat_nil p)))
def c1699 : List Lit := [(1531, false), (1544, true)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c1432, c1007] c1699 (by decide) p (sat_cons (step1432 p h) (sat_cons (step1007 p h) (sat_nil p)))
def c1700 : List Lit := [(1532, false), (1545, true)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c1432, c1011] c1700 (by decide) p (sat_cons (step1432 p h) (sat_cons (step1011 p h) (sat_nil p)))
def c1701 : List Lit := [(1533, false), (1546, true)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c1432, c1014] c1701 (by decide) p (sat_cons (step1432 p h) (sat_cons (step1014 p h) (sat_nil p)))
def c1702 : List Lit := [(1552, true), (1543, false)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c1460, c1015] c1702 (by decide) p (sat_cons (step1460 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c1703 : List Lit := [(1553, true), (1544, false)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c1460, c1016] c1703 (by decide) p (sat_cons (step1460 p h) (sat_cons (step1016 p h) (sat_nil p)))
def c1704 : List Lit := [(1554, true), (1545, false)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c1460, c1017] c1704 (by decide) p (sat_cons (step1460 p h) (sat_cons (step1017 p h) (sat_nil p)))
def c1705 : List Lit := [(1546, false), (1555, true)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c1460, c1018] c1705 (by decide) p (sat_cons (step1460 p h) (sat_cons (step1018 p h) (sat_nil p)))
def c1706 : List Lit := [(1547, false), (1556, true)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c1460, c1019] c1706 (by decide) p (sat_cons (step1460 p h) (sat_cons (step1019 p h) (sat_nil p)))
def c1707 : List Lit := [(1519, false), (1552, true)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1020] c1707 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1020 p h) (sat_nil p)))
def c1708 : List Lit := [(1520, false), (1553, true)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1026] c1708 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1026 p h) (sat_nil p)))
def c1709 : List Lit := [(1521, false), (1554, true)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1032] c1709 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1032 p h) (sat_nil p)))
def c1710 : List Lit := [(1556, false), (1575, true)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c1507, c1040] c1710 (by decide) p (sat_cons (step1507 p h) (sat_cons (step1040 p h) (sat_nil p)))
def c1711 : List Lit := [(1573, false), (1731, false)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c1356, c1348] c1711 (by decide) p (sat_cons (step1356 p h) (sat_cons (step1348 p h) (sat_nil p)))
def c1712 : List Lit := [(1574, false), (1730, false)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c1356, c1349] c1712 (by decide) p (sat_cons (step1356 p h) (sat_cons (step1349 p h) (sat_nil p)))
def c1713 : List Lit := [(1575, false), (1729, false)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c1356, c1350] c1713 (by decide) p (sat_cons (step1356 p h) (sat_cons (step1350 p h) (sat_nil p)))
def c1714 : List Lit := [(1576, false), (1728, false)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c1356, c1351] c1714 (by decide) p (sat_cons (step1356 p h) (sat_cons (step1351 p h) (sat_nil p)))
def c1715 : List Lit := [(1577, false), (1727, false)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c1356, c1352] c1715 (by decide) p (sat_cons (step1356 p h) (sat_cons (step1352 p h) (sat_nil p)))
def c1716 : List Lit := [(1578, false), (1726, false)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c1356, c1353] c1716 (by decide) p (sat_cons (step1356 p h) (sat_cons (step1353 p h) (sat_nil p)))
def c1717 : List Lit := [(1579, false), (1725, false)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c1356, c1354] c1717 (by decide) p (sat_cons (step1356 p h) (sat_cons (step1354 p h) (sat_nil p)))
def c1718 : List Lit := [(1580, false), (1724, false)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c1356, c1355] c1718 (by decide) p (sat_cons (step1356 p h) (sat_cons (step1355 p h) (sat_nil p)))
def c1719 : List Lit := [(1480, true), (1465, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c871, c900, c897, c874, c885, c887, c1508, c879] c1719 (by decide) p (sat_cons (step871 p h) (sat_cons (step900 p h) (sat_cons (step897 p h) (sat_cons (step874 p h) (sat_cons (step885 p h) (sat_cons (step887 p h) (sat_cons (step1508 p h) (sat_cons (step879 p h) (sat_nil p)))))))))
def c1720 : List Lit := [(74, false), (1608, true), (61, false), (96, false)]
theorem step1720 (p : Nat → Bool) (h : Constraints p) : clause p c1720 = true :=
  Snake9.LocalRup.prove_clause [c1457, c241, c244, c245, c1085, c1073, c1077, c1093, c1082, c1108] c1720 (by decide) p (sat_cons (step1457 p h) (sat_cons (step241 p h) (sat_cons (step244 p h) (sat_cons (step245 p h) (sat_cons (step1085 p h) (sat_cons (step1073 p h) (sat_cons (step1077 p h) (sat_cons (step1093 p h) (sat_cons (step1082 p h) (sat_cons (step1108 p h) (sat_nil p)))))))))))
def c1721 : List Lit := [(1554, true), (1502, false), (1539, false)]
theorem step1721 (p : Nat → Bool) (h : Constraints p) : clause p c1721 = true :=
  Snake9.LocalRup.prove_clause [c938, c1694, c1000, c1027, c1022, c1695, c962, c1004, c939, c1436, c933, c953, c1512] c1721 (by decide) p (sat_cons (step938 p h) (sat_cons (step1694 p h) (sat_cons (step1000 p h) (sat_cons (step1027 p h) (sat_cons (step1022 p h) (sat_cons (step1695 p h) (sat_cons (step962 p h) (sat_cons (step1004 p h) (sat_cons (step939 p h) (sat_cons (step1436 p h) (sat_cons (step933 p h) (sat_cons (step953 p h) (sat_cons (step1512 p h) (sat_nil p))))))))))))))
end B112E026
