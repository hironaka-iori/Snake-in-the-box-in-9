import B112E036Inputs
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1645 : List Lit := [(20, true)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c406, c405] c1645 (by decide) p (sat_cons (step406 p h) (sat_cons (step405 p h) (sat_nil p)))
def c1646 : List Lit := [(25, false)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c779, c86] c1646 (by decide) p (sat_cons (step779 p h) (sat_cons (step86 p h) (sat_nil p)))
def c1647 : List Lit := [(26, false)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c780, c87] c1647 (by decide) p (sat_cons (step780 p h) (sat_cons (step87 p h) (sat_nil p)))
def c1648 : List Lit := [(506, false)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c995, c992] c1648 (by decide) p (sat_cons (step995 p h) (sat_cons (step992 p h) (sat_nil p)))
def c1649 : List Lit := [(380, false)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c995, c994] c1649 (by decide) p (sat_cons (step995 p h) (sat_cons (step994 p h) (sat_nil p)))
def c1650 : List Lit := [(504, false)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c1648, c988] c1650 (by decide) p (sat_cons (step1648 p h) (sat_cons (step988 p h) (sat_nil p)))
def c1651 : List Lit := [(442, false)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c1648, c991] c1651 (by decide) p (sat_cons (step1648 p h) (sat_cons (step991 p h) (sat_nil p)))
def c1652 : List Lit := [(378, false)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c1649, c897] c1652 (by decide) p (sat_cons (step1649 p h) (sat_cons (step897 p h) (sat_nil p)))
def c1653 : List Lit := [(316, false)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c1649, c900] c1653 (by decide) p (sat_cons (step1649 p h) (sat_cons (step900 p h) (sat_nil p)))
def c1654 : List Lit := [(502, false)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c1650, c983] c1654 (by decide) p (sat_cons (step1650 p h) (sat_cons (step983 p h) (sat_nil p)))
def c1655 : List Lit := [(472, false)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c1650, c986] c1655 (by decide) p (sat_cons (step1650 p h) (sat_cons (step986 p h) (sat_nil p)))
def c1656 : List Lit := [(410, false)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c1651, c934] c1656 (by decide) p (sat_cons (step1651 p h) (sat_cons (step934 p h) (sat_nil p)))
def c1657 : List Lit := [(376, false)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c1652, c893] c1657 (by decide) p (sat_cons (step1652 p h) (sat_cons (step893 p h) (sat_nil p)))
def c1658 : List Lit := [(314, false)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c1653, c862] c1658 (by decide) p (sat_cons (step1653 p h) (sat_cons (step862 p h) (sat_nil p)))
def c1659 : List Lit := [(486, false)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c1654, c981] c1659 (by decide) p (sat_cons (step1654 p h) (sat_cons (step981 p h) (sat_nil p)))
def c1660 : List Lit := [(470, false)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c1655, c956] c1660 (by decide) p (sat_cons (step1655 p h) (sat_cons (step956 p h) (sat_nil p)))
def c1661 : List Lit := [(394, false)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c1656, c920] c1661 (by decide) p (sat_cons (step1656 p h) (sat_cons (step920 p h) (sat_nil p)))
def c1662 : List Lit := [(360, false)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c1657, c891] c1662 (by decide) p (sat_cons (step1657 p h) (sat_cons (step891 p h) (sat_nil p)))
def c1663 : List Lit := [(312, false)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c1658, c858] c1663 (by decide) p (sat_cons (step1658 p h) (sat_cons (step858 p h) (sat_nil p)))
def c1664 : List Lit := [(484, false)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c1659, c967] c1664 (by decide) p (sat_cons (step1659 p h) (sat_cons (step967 p h) (sat_nil p)))
def c1665 : List Lit := [(468, false)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c1660, c952] c1665 (by decide) p (sat_cons (step1660 p h) (sat_cons (step952 p h) (sat_nil p)))
def c1666 : List Lit := [(392, false)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c1661, c909] c1666 (by decide) p (sat_cons (step1661 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1667 : List Lit := [(352, false)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c1662, c882] c1667 (by decide) p (sat_cons (step1662 p h) (sat_cons (step882 p h) (sat_nil p)))
def c1668 : List Lit := [(482, false)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c1664, c965] c1668 (by decide) p (sat_cons (step1664 p h) (sat_cons (step965 p h) (sat_nil p)))
def c1669 : List Lit := [(388, false)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c1666, c907] c1669 (by decide) p (sat_cons (step1666 p h) (sat_cons (step907 p h) (sat_nil p)))
def c1670 : List Lit := [(348, false)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c1667, c877] c1670 (by decide) p (sat_cons (step1667 p h) (sat_cons (step877 p h) (sat_nil p)))
def c1671 : List Lit := [(1580, true)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c1646, c1647, c1056] c1671 (by decide) p (sat_cons (step1646 p h) (sat_cons (step1647 p h) (sat_cons (step1056 p h) (sat_nil p))))
def c1672 : List Lit := [(1584, true)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c1671, c1060] c1672 (by decide) p (sat_cons (step1671 p h) (sat_cons (step1060 p h) (sat_nil p)))
def c1673 : List Lit := [(1581, false), (1585, true)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c1671, c1061] c1673 (by decide) p (sat_cons (step1671 p h) (sat_cons (step1061 p h) (sat_nil p)))
def c1674 : List Lit := [(1582, false), (1586, true)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c1671, c1062] c1674 (by decide) p (sat_cons (step1671 p h) (sat_cons (step1062 p h) (sat_nil p)))
def c1675 : List Lit := [(1575, false), (1589, true)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c1672, c1063] c1675 (by decide) p (sat_cons (step1672 p h) (sat_cons (step1063 p h) (sat_nil p)))
def c1676 : List Lit := [(1576, false), (1590, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c1672, c1066] c1676 (by decide) p (sat_cons (step1672 p h) (sat_cons (step1066 p h) (sat_nil p)))
def c1677 : List Lit := [(1577, false), (1591, true)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c1672, c1069] c1677 (by decide) p (sat_cons (step1672 p h) (sat_cons (step1069 p h) (sat_nil p)))
def c1678 : List Lit := [(1578, false), (1592, true)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c1672, c1072] c1678 (by decide) p (sat_cons (step1672 p h) (sat_cons (step1072 p h) (sat_nil p)))
def c1679 : List Lit := [(1719, true)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c805, c1300, c1302, c1297, c1298, c1294, c1295, c370, c376, c375] c1679 (by decide) p (sat_cons (step805 p h) (sat_cons (step1300 p h) (sat_cons (step1302 p h) (sat_cons (step1297 p h) (sat_cons (step1298 p h) (sat_cons (step1294 p h) (sat_cons (step1295 p h) (sat_cons (step370 p h) (sat_cons (step376 p h) (sat_cons (step375 p h) (sat_nil p)))))))))))
def c1680 : List Lit := [(1723, true)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c1679, c1307] c1680 (by decide) p (sat_cons (step1679 p h) (sat_cons (step1307 p h) (sat_nil p)))
def c1681 : List Lit := [(1711, true), (1656, true)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c798, c1195, c1286, c1288, c1284, c1281, c306, c307, c337, c1152, c1160, c1161, c1191, c1155, c1177, c302, c1172, c1169] c1681 (by decide) p (sat_cons (step798 p h) (sat_cons (step1195 p h) (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step1284 p h) (sat_cons (step1281 p h) (sat_cons (step306 p h) (sat_cons (step307 p h) (sat_cons (step337 p h) (sat_cons (step1152 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1191 p h) (sat_cons (step1155 p h) (sat_cons (step1177 p h) (sat_cons (step302 p h) (sat_cons (step1172 p h) (sat_cons (step1169 p h) (sat_nil p)))))))))))))))))))
def c1682 : List Lit := [(63, false), (67, false), (1656, true)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c798, c1195, c306, c307, c337, c1152, c1160, c1161, c1191, c1155, c1177, c302, c1172, c1169] c1682 (by decide) p (sat_cons (step798 p h) (sat_cons (step1195 p h) (sat_cons (step306 p h) (sat_cons (step307 p h) (sat_cons (step337 p h) (sat_cons (step1152 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1191 p h) (sat_cons (step1155 p h) (sat_cons (step1177 p h) (sat_cons (step302 p h) (sat_cons (step1172 p h) (sat_cons (step1169 p h) (sat_nil p)))))))))))))))
def c1683 : List Lit := [(57, false), (59, false), (55, false)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c796, c295, c293] c1683 (by decide) p (sat_cons (step796 p h) (sat_cons (step295 p h) (sat_cons (step293 p h) (sat_nil p))))
def c1684 : List Lit := [(1650, true)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c1177, c1180, c1172, c1174, c1167, c1170, c1683] c1684 (by decide) p (sat_cons (step1177 p h) (sat_cons (step1180 p h) (sat_cons (step1172 p h) (sat_cons (step1174 p h) (sat_cons (step1167 p h) (sat_cons (step1170 p h) (sat_cons (step1683 p h) (sat_nil p))))))))
def c1685 : List Lit := [(1655, true)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c1684, c1187] c1685 (by decide) p (sat_cons (step1684 p h) (sat_cons (step1187 p h) (sat_nil p)))
def c1686 : List Lit := [(1623, true), (1635, true)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c790, c1153, c1152, c1124, c1126, c1121, c1119, c227, c222, c219] c1686 (by decide) p (sat_cons (step790 p h) (sat_cons (step1153 p h) (sat_cons (step1152 p h) (sat_cons (step1124 p h) (sat_cons (step1126 p h) (sat_cons (step1121 p h) (sat_cons (step1119 p h) (sat_cons (step227 p h) (sat_cons (step222 p h) (sat_cons (step219 p h) (sat_nil p)))))))))))
def c1687 : List Lit := [(1775, true), (97, false), (38, false)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c1392, c1394, c1390, c1387, c548] c1687 (by decide) p (sat_cons (step1392 p h) (sat_cons (step1394 p h) (sat_cons (step1390 p h) (sat_cons (step1387 p h) (sat_cons (step548 p h) (sat_nil p))))))
def c1688 : List Lit := [(1808, true), (123, false), (125, true), (61, false)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c1456, c1459, c1461, c1457, c746] c1688 (by decide) p (sat_cons (step1456 p h) (sat_cons (step1459 p h) (sat_cons (step1461 p h) (sat_cons (step1457 p h) (sat_cons (step746 p h) (sat_nil p))))))
def c1689 : List Lit := [(69, true), (73, false), (37, false), (74, true)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c803, c357, c360, c1590] c1689 (by decide) p (sat_cons (step803 p h) (sat_cons (step357 p h) (sat_cons (step360 p h) (sat_cons (step1590 p h) (sat_nil p)))))
def c1690 : List Lit := [(1557, true), (50, false), (14, true)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c775, c1013, c1014, c60, c64] c1690 (by decide) p (sat_cons (step775 p h) (sat_cons (step1013 p h) (sat_cons (step1014 p h) (sat_cons (step60 p h) (sat_cons (step64 p h) (sat_nil p))))))
def c1691 : List Lit := [(1573, false), (1560, false), (1602, true), (1550, false)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c406, c1645, c1003, c1035, c1091, c1676, c1049, c1675, c1096, c1039, c1006, c997, c1051, c67, c1043] c1691 (by decide) p (sat_cons (step406 p h) (sat_cons (step1645 p h) (sat_cons (step1003 p h) (sat_cons (step1035 p h) (sat_cons (step1091 p h) (sat_cons (step1676 p h) (sat_cons (step1049 p h) (sat_cons (step1675 p h) (sat_cons (step1096 p h) (sat_cons (step1039 p h) (sat_cons (step1006 p h) (sat_cons (step997 p h) (sat_cons (step1051 p h) (sat_cons (step67 p h) (sat_cons (step1043 p h) (sat_nil p))))))))))))))))
def c1692 : List Lit := [(1560, false), (1602, true), (1550, false)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c1645, c406, c1691, c1047, c68, c70, c997, c1043, c1006, c1050, c1039, c1675, c1096] c1692 (by decide) p (sat_cons (step1645 p h) (sat_cons (step406 p h) (sat_cons (step1691 p h) (sat_cons (step1047 p h) (sat_cons (step68 p h) (sat_cons (step70 p h) (sat_cons (step997 p h) (sat_cons (step1043 p h) (sat_cons (step1006 p h) (sat_cons (step1050 p h) (sat_cons (step1039 p h) (sat_cons (step1675 p h) (sat_cons (step1096 p h) (sat_nil p))))))))))))))
def c1693 : List Lit := [(17, false), (1557, true), (83, false)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c775, c1014, c1013, c56, c63, c59] c1693 (by decide) p (sat_cons (step775 p h) (sat_cons (step1014 p h) (sat_cons (step1013 p h) (sat_cons (step56 p h) (sat_cons (step63 p h) (sat_cons (step59 p h) (sat_nil p)))))))
def c1694 : List Lit := [(1576, true), (17, true)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c406, c1645, c1044, c1053, c1051, c1045, c1047, c70] c1694 (by decide) p (sat_cons (step406 p h) (sat_cons (step1645 p h) (sat_cons (step1044 p h) (sat_cons (step1053 p h) (sat_cons (step1051 p h) (sat_cons (step1045 p h) (sat_cons (step1047 p h) (sat_cons (step70 p h) (sat_nil p)))))))))
def c1695 : List Lit := [(17, true), (4, true), (1600, true)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c406, c1645, c996, c1004, c1028, c1078, c1677, c1694, c1676, c1082, c1033, c1007, c998, c67, c68, c1045, c1047, c1054] c1695 (by decide) p (sat_cons (step406 p h) (sat_cons (step1645 p h) (sat_cons (step996 p h) (sat_cons (step1004 p h) (sat_cons (step1028 p h) (sat_cons (step1078 p h) (sat_cons (step1677 p h) (sat_cons (step1694 p h) (sat_cons (step1676 p h) (sat_cons (step1082 p h) (sat_cons (step1033 p h) (sat_cons (step1007 p h) (sat_cons (step998 p h) (sat_cons (step67 p h) (sat_cons (step68 p h) (sat_cons (step1045 p h) (sat_cons (step1047 p h) (sat_cons (step1054 p h) (sat_nil p)))))))))))))))))))
def c1696 : List Lit := [(1818, true), (95, true), (117, true), (1797, false), (1799, false), (1808, false), (1811, false)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c820, c1483, c1479, c1445, c1447, c1468, c1443, c1439, c1453, c702, c711] c1696 (by decide) p (sat_cons (step820 p h) (sat_cons (step1483 p h) (sat_cons (step1479 p h) (sat_cons (step1445 p h) (sat_cons (step1447 p h) (sat_cons (step1468 p h) (sat_cons (step1443 p h) (sat_cons (step1439 p h) (sat_cons (step1453 p h) (sat_cons (step702 p h) (sat_cons (step711 p h) (sat_nil p))))))))))))
def c1697 : List Lit := [(1560, true), (1547, true), (9, true)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c774, c997, c996, c1011, c1021, c1019, c1012, c1014, c42, c12, c47] c1697 (by decide) p (sat_cons (step774 p h) (sat_cons (step997 p h) (sat_cons (step996 p h) (sat_cons (step1011 p h) (sat_cons (step1021 p h) (sat_cons (step1019 p h) (sat_cons (step1012 p h) (sat_cons (step1014 p h) (sat_cons (step42 p h) (sat_cons (step12 p h) (sat_cons (step47 p h) (sat_nil p))))))))))))
def c1698 : List Lit := [(122, false), (101, false), (105, false), (112, false)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c823, c625, c733, c743] c1698 (by decide) p (sat_cons (step823 p h) (sat_cons (step625 p h) (sat_cons (step733 p h) (sat_cons (step743 p h) (sat_nil p)))))
def c1699 : List Lit := [(1602, true), (14, true), (1550, false), (9, true)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c775, c1011, c1018, c1692, c1019, c1697, c1013, c1014, c1006, c60, c1038, c63, c1091, c1694, c1676] c1699 (by decide) p (sat_cons (step775 p h) (sat_cons (step1011 p h) (sat_cons (step1018 p h) (sat_cons (step1692 p h) (sat_cons (step1019 p h) (sat_cons (step1697 p h) (sat_cons (step1013 p h) (sat_cons (step1014 p h) (sat_cons (step1006 p h) (sat_cons (step60 p h) (sat_cons (step1038 p h) (sat_cons (step63 p h) (sat_cons (step1091 p h) (sat_cons (step1694 p h) (sat_cons (step1676 p h) (sat_nil p))))))))))))))))
def c1700 : List Lit := [(1798, false), (93, false), (1818, true), (94, true), (1803, false)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c819, c1466, c1487, c1445, c1448, c1483, c1438, c1467, c699, c1460, c693] c1700 (by decide) p (sat_cons (step819 p h) (sat_cons (step1466 p h) (sat_cons (step1487 p h) (sat_cons (step1445 p h) (sat_cons (step1448 p h) (sat_cons (step1483 p h) (sat_cons (step1438 p h) (sat_cons (step1467 p h) (sat_cons (step699 p h) (sat_cons (step1460 p h) (sat_cons (step693 p h) (sat_nil p))))))))))))
def c1701 : List Lit := [(118, true), (1812, true), (255, true), (122, true)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c826, c1454, c766, c1471, c1458, c1460, c1455, c1456, c767, c760] c1701 (by decide) p (sat_cons (step826 p h) (sat_cons (step1454 p h) (sat_cons (step766 p h) (sat_cons (step1471 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step767 p h) (sat_cons (step760 p h) (sat_nil p)))))))))))
def c1702 : List Lit := [(1735, true), (102, true)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c806, c1328, c1330, c1326, c1322, c1323, c385, c386] c1702 (by decide) p (sat_cons (step806 p h) (sat_cons (step1328 p h) (sat_cons (step1330 p h) (sat_cons (step1326 p h) (sat_cons (step1322 p h) (sat_cons (step1323 p h) (sat_cons (step385 p h) (sat_cons (step386 p h) (sat_nil p)))))))))
def c1703 : List Lit := [(1712, true), (70, true), (66, false), (125, false)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c1283, c1287, c1289, c1285, c1280, c327] c1703 (by decide) p (sat_cons (step1283 p h) (sat_cons (step1287 p h) (sat_cons (step1289 p h) (sat_cons (step1285 p h) (sat_cons (step1280 p h) (sat_cons (step327 p h) (sat_nil p)))))))
def c1704 : List Lit := [(109, true), (1790, true), (1773, false), (108, false), (1779, false), (125, false)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c1392, c1421, c1410, c1403, c1405, c1409, c662, c1425, c1387, c1395] c1704 (by decide) p (sat_cons (step1392 p h) (sat_cons (step1421 p h) (sat_cons (step1410 p h) (sat_cons (step1403 p h) (sat_cons (step1405 p h) (sat_cons (step1409 p h) (sat_cons (step662 p h) (sat_cons (step1425 p h) (sat_cons (step1387 p h) (sat_cons (step1395 p h) (sat_nil p)))))))))))
def c1705 : List Lit := [(1790, true), (125, false), (1773, false), (108, false), (1779, false)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c1704, c664, c663, c1404, c1387, c1409, c1395, c1425] c1705 (by decide) p (sat_cons (step1704 p h) (sat_cons (step664 p h) (sat_cons (step663 p h) (sat_cons (step1404 p h) (sat_cons (step1387 p h) (sat_cons (step1409 p h) (sat_cons (step1395 p h) (sat_cons (step1425 p h) (sat_nil p)))))))))
def c1706 : List Lit := [(98, false), (74, true), (73, false), (111, false), (88, false)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c813, c803, c518, c567, c357, c416] c1706 (by decide) p (sat_cons (step813 p h) (sat_cons (step803 p h) (sat_cons (step518 p h) (sat_cons (step567 p h) (sat_cons (step357 p h) (sat_cons (step416 p h) (sat_nil p)))))))
def c1707 : List Lit := [(1781, true), (108, false), (125, false)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c1403, c1404, c664] c1707 (by decide) p (sat_cons (step1403 p h) (sat_cons (step1404 p h) (sat_cons (step664 p h) (sat_nil p))))
def c1708 : List Lit := [(98, true), (1791, true), (1773, false), (108, false), (1779, false), (125, false)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c1707, c1409, c1430, c1398, c1386, c1395, c1426, c1410, c1388, c662, c663, c1405] c1708 (by decide) p (sat_cons (step1707 p h) (sat_cons (step1409 p h) (sat_cons (step1430 p h) (sat_cons (step1398 p h) (sat_cons (step1386 p h) (sat_cons (step1395 p h) (sat_cons (step1426 p h) (sat_cons (step1410 p h) (sat_cons (step1388 p h) (sat_cons (step662 p h) (sat_cons (step663 p h) (sat_cons (step1405 p h) (sat_nil p)))))))))))))
end B112E036
