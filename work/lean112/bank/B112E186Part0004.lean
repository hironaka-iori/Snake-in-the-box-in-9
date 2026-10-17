import B112E186Part0003
namespace B112E186
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1656 : List Lit := [(96, true), (24, true), (98, false)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c698, c468] c1656 (by decide) p (sat_cons (step698 p h) (sat_cons (step468 p h) (sat_nil p)))
def c1657 : List Lit := [(104, true), (121, true), (89, true), (101, false), (99, true)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c699, c508] c1657 (by decide) p (sat_cons (step699 p h) (sat_cons (step508 p h) (sat_nil p)))
def c1658 : List Lit := [(104, true), (121, true), (101, false), (89, true), (96, true)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c699, c509] c1658 (by decide) p (sat_cons (step699 p h) (sat_cons (step509 p h) (sat_nil p)))
def c1659 : List Lit := [(121, true), (96, true), (99, true), (101, false), (89, true)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c699, c510] c1659 (by decide) p (sat_cons (step699 p h) (sat_cons (step510 p h) (sat_nil p)))
def c1660 : List Lit := [(104, true), (96, true), (99, true), (89, true), (101, false)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c699, c511] c1660 (by decide) p (sat_cons (step699 p h) (sat_cons (step511 p h) (sat_nil p)))
def c1661 : List Lit := [(103, true), (104, true), (102, false), (99, true)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c700, c512] c1661 (by decide) p (sat_cons (step700 p h) (sat_cons (step512 p h) (sat_nil p)))
def c1662 : List Lit := [(103, true), (90, true), (102, false), (104, true)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c700, c513] c1662 (by decide) p (sat_cons (step700 p h) (sat_cons (step513 p h) (sat_nil p)))
def c1663 : List Lit := [(104, true), (90, true), (99, true), (102, false)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c700, c514] c1663 (by decide) p (sat_cons (step700 p h) (sat_cons (step514 p h) (sat_nil p)))
def c1664 : List Lit := [(103, true), (90, true), (99, true), (102, false)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c700, c515] c1664 (by decide) p (sat_cons (step700 p h) (sat_cons (step515 p h) (sat_nil p)))
def c1665 : List Lit := [(110, true), (106, true), (107, false), (85, true)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c701, c556] c1665 (by decide) p (sat_cons (step701 p h) (sat_cons (step556 p h) (sat_nil p)))
def c1666 : List Lit := [(110, true), (106, true), (107, false), (67, true)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c701, c557] c1666 (by decide) p (sat_cons (step701 p h) (sat_cons (step557 p h) (sat_nil p)))
def c1667 : List Lit := [(110, true), (67, true), (107, false), (85, true)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c701, c558] c1667 (by decide) p (sat_cons (step701 p h) (sat_cons (step558 p h) (sat_nil p)))
def c1668 : List Lit := [(67, true), (106, true), (107, false), (85, true)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c701, c559] c1668 (by decide) p (sat_cons (step701 p h) (sat_cons (step559 p h) (sat_nil p)))
def c1669 : List Lit := [(108, true), (115, true), (109, false), (110, true)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c702, c567] c1669 (by decide) p (sat_cons (step702 p h) (sat_cons (step567 p h) (sat_nil p)))
def c1670 : List Lit := [(110, true), (115, true), (109, false), (106, true)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c702, c568] c1670 (by decide) p (sat_cons (step702 p h) (sat_cons (step568 p h) (sat_nil p)))
def c1671 : List Lit := [(108, true), (115, true), (109, false), (106, true)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c702, c569] c1671 (by decide) p (sat_cons (step702 p h) (sat_cons (step569 p h) (sat_nil p)))
def c1672 : List Lit := [(108, true), (110, true), (109, false), (106, true)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c702, c570] c1672 (by decide) p (sat_cons (step702 p h) (sat_cons (step570 p h) (sat_nil p)))
def c1673 : List Lit := [(120, true), (112, false), (88, true), (111, true)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c703, c602] c1673 (by decide) p (sat_cons (step703 p h) (sat_cons (step602 p h) (sat_nil p)))
def c1674 : List Lit := [(120, true), (112, false), (111, true), (35, true)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c703, c603] c1674 (by decide) p (sat_cons (step703 p h) (sat_cons (step603 p h) (sat_nil p)))
def c1675 : List Lit := [(120, true), (112, false), (35, true), (88, true)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c703, c604] c1675 (by decide) p (sat_cons (step703 p h) (sat_cons (step604 p h) (sat_nil p)))
def c1676 : List Lit := [(112, false), (111, true), (88, true), (35, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c703, c605] c1676 (by decide) p (sat_cons (step703 p h) (sat_cons (step605 p h) (sat_nil p)))
def c1677 : List Lit := [(121, true), (106, true), (111, true), (115, true), (113, false)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c704, c612] c1677 (by decide) p (sat_cons (step704 p h) (sat_cons (step612 p h) (sat_nil p)))
def c1678 : List Lit := [(121, true), (106, true), (89, true), (111, true), (113, false)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c704, c613] c1678 (by decide) p (sat_cons (step704 p h) (sat_cons (step613 p h) (sat_nil p)))
def c1679 : List Lit := [(115, true), (106, true), (113, false), (89, true), (111, true)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c704, c614] c1679 (by decide) p (sat_cons (step704 p h) (sat_cons (step614 p h) (sat_nil p)))
def c1680 : List Lit := [(115, true), (108, true), (114, false), (111, true)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c705, c617] c1680 (by decide) p (sat_cons (step705 p h) (sat_cons (step617 p h) (sat_nil p)))
def c1681 : List Lit := [(115, true), (90, true), (111, true), (114, false)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c705, c618] c1681 (by decide) p (sat_cons (step705 p h) (sat_cons (step618 p h) (sat_nil p)))
def c1682 : List Lit := [(115, true), (90, true), (108, true), (114, false)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c705, c619] c1682 (by decide) p (sat_cons (step705 p h) (sat_cons (step619 p h) (sat_nil p)))
def c1683 : List Lit := [(90, true), (111, true), (108, true), (114, false)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c705, c620] c1683 (by decide) p (sat_cons (step705 p h) (sat_cons (step620 p h) (sat_nil p)))
def c1684 : List Lit := [(118, true), (116, true), (117, false)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c706, c626] c1684 (by decide) p (sat_cons (step706 p h) (sat_cons (step626 p h) (sat_nil p)))
def c1685 : List Lit := [(118, true), (108, true), (117, false)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c706, c627] c1685 (by decide) p (sat_cons (step706 p h) (sat_cons (step627 p h) (sat_nil p)))
def c1686 : List Lit := [(108, true), (116, true), (117, false)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c706, c628] c1686 (by decide) p (sat_cons (step706 p h) (sat_cons (step628 p h) (sat_nil p)))
def c1687 : List Lit := [(118, true), (119, false), (124, true)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c707, c632] c1687 (by decide) p (sat_cons (step707 p h) (sat_cons (step632 p h) (sat_nil p)))
def c1688 : List Lit := [(110, true), (119, false), (124, true)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c707, c633] c1688 (by decide) p (sat_cons (step707 p h) (sat_cons (step633 p h) (sat_nil p)))
def c1689 : List Lit := [(110, true), (118, true), (119, false)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c707, c634] c1689 (by decide) p (sat_cons (step707 p h) (sat_cons (step634 p h) (sat_nil p)))
def c1690 : List Lit := [(121, true), (124, true), (122, false)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c708, c644] c1690 (by decide) p (sat_cons (step708 p h) (sat_cons (step644 p h) (sat_nil p)))
def c1691 : List Lit := [(120, true), (124, true), (122, false)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c708, c645] c1691 (by decide) p (sat_cons (step708 p h) (sat_cons (step645 p h) (sat_nil p)))
def c1692 : List Lit := [(121, true), (120, true), (122, false)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c708, c646] c1692 (by decide) p (sat_cons (step708 p h) (sat_cons (step646 p h) (sat_nil p)))
def c1693 : List Lit := [(293, false), (299, false)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c1416, c733] c1693 (by decide) p (sat_cons (step1416 p h) (sat_cons (step733 p h) (sat_nil p)))
def c1694 : List Lit := [(287, false), (301, false)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c1413, c737] c1694 (by decide) p (sat_cons (step1413 p h) (sat_cons (step737 p h) (sat_nil p)))
def c1695 : List Lit := [(275, false), (303, false)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c1410, c741] c1695 (by decide) p (sat_cons (step1410 p h) (sat_cons (step741 p h) (sat_nil p)))
def c1696 : List Lit := [(323, false), (329, false)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c1415, c753] c1696 (by decide) p (sat_cons (step1415 p h) (sat_cons (step753 p h) (sat_nil p)))
def c1697 : List Lit := [(317, false), (331, false)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c1412, c757] c1697 (by decide) p (sat_cons (step1412 p h) (sat_cons (step757 p h) (sat_nil p)))
def c1698 : List Lit := [(305, false), (365, false)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c1407, c768] c1698 (by decide) p (sat_cons (step1407 p h) (sat_cons (step768 p h) (sat_nil p)))
def c1699 : List Lit := [(196, false), (197, false)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c1418, c775] c1699 (by decide) p (sat_cons (step1418 p h) (sat_cons (step775 p h) (sat_nil p)))
def c1700 : List Lit := [(395, false), (425, false)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c1408, c799] c1700 (by decide) p (sat_cons (step1408 p h) (sat_cons (step799 p h) (sat_nil p)))
def c1701 : List Lit := [(367, false), (489, false)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c822, c820] c1701 (by decide) p (sat_cons (step822 p h) (sat_cons (step820 p h) (sat_nil p)))
def c1702 : List Lit := [(1534, false), (1544, true)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c1426, c890] c1702 (by decide) p (sat_cons (step1426 p h) (sat_cons (step890 p h) (sat_nil p)))
def c1703 : List Lit := [(1535, false), (1545, true)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c1426, c891] c1703 (by decide) p (sat_cons (step1426 p h) (sat_cons (step891 p h) (sat_nil p)))
def c1704 : List Lit := [(1536, false), (1546, true)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c1426, c892] c1704 (by decide) p (sat_cons (step1426 p h) (sat_cons (step892 p h) (sat_nil p)))
def c1705 : List Lit := [(1513, false), (1545, true)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c1507, c899] c1705 (by decide) p (sat_cons (step1507 p h) (sat_cons (step899 p h) (sat_nil p)))
def c1706 : List Lit := [(1514, false), (1546, true)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c1507, c903] c1706 (by decide) p (sat_cons (step1507 p h) (sat_cons (step903 p h) (sat_nil p)))
def c1707 : List Lit := [(1560, false), (1573, true)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c1429, c936] c1707 (by decide) p (sat_cons (step1429 p h) (sat_cons (step936 p h) (sat_nil p)))
def c1708 : List Lit := [(1561, false), (1574, true)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c1429, c939] c1708 (by decide) p (sat_cons (step1429 p h) (sat_cons (step939 p h) (sat_nil p)))
def c1709 : List Lit := [(1562, false), (1575, true)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c1429, c943] c1709 (by decide) p (sat_cons (step1429 p h) (sat_cons (step943 p h) (sat_nil p)))
def c1710 : List Lit := [(1563, false), (1576, true)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c1429, c946] c1710 (by decide) p (sat_cons (step1429 p h) (sat_cons (step946 p h) (sat_nil p)))
def c1711 : List Lit := [(1599, false), (1608, true)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c1430, c990] c1711 (by decide) p (sat_cons (step1430 p h) (sat_cons (step990 p h) (sat_nil p)))
def c1712 : List Lit := [(1600, false), (1609, true)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c1430, c991] c1712 (by decide) p (sat_cons (step1430 p h) (sat_cons (step991 p h) (sat_nil p)))
def c1713 : List Lit := [(1573, false), (1606, true)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c1427, c992] c1713 (by decide) p (sat_cons (step1427 p h) (sat_cons (step992 p h) (sat_nil p)))
def c1714 : List Lit := [(1607, true), (1574, false)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c1427, c997] c1714 (by decide) p (sat_cons (step1427 p h) (sat_cons (step997 p h) (sat_nil p)))
def c1715 : List Lit := [(1608, true), (1575, false)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1002] c1715 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1002 p h) (sat_nil p)))
def c1716 : List Lit := [(1609, true), (1576, false)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1007] c1716 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1007 p h) (sat_nil p)))
def c1717 : List Lit := [(1610, true), (1577, false)]
theorem step1717 (p : Nat → Bool) (h : Constraints p) : clause p c1717 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1012] c1717 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1012 p h) (sat_nil p)))
def c1718 : List Lit := [(1626, true), (1607, false)]
theorem step1718 (p : Nat → Bool) (h : Constraints p) : clause p c1718 = true :=
  Snake9.LocalRup.prove_clause [c1516, c1015] c1718 (by decide) p (sat_cons (step1516 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c1719 : List Lit := [(1627, true), (1608, false)]
theorem step1719 (p : Nat → Bool) (h : Constraints p) : clause p c1719 = true :=
  Snake9.LocalRup.prove_clause [c1516, c1016] c1719 (by decide) p (sat_cons (step1516 p h) (sat_cons (step1016 p h) (sat_nil p)))
end B112E186
