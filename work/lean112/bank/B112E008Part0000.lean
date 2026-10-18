import B112E008Inputs
namespace B112E008
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1607 : List Lit := [(27, true)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c129, c128] c1607 (by decide) p (sat_cons (step129 p h) (sat_cons (step128 p h) (sat_nil p)))
def c1608 : List Lit := [(13, false), (20, false)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c1607, c129, c130] c1608 (by decide) p (sat_cons (step1607 p h) (sat_cons (step129 p h) (sat_cons (step130 p h) (sat_nil p))))
def c1609 : List Lit := [(13, false), (25, false)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c1607, c129, c131] c1609 (by decide) p (sat_cons (step1607 p h) (sat_cons (step129 p h) (sat_cons (step131 p h) (sat_nil p))))
def c1610 : List Lit := [(20, false), (25, false)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c1607, c129, c132] c1610 (by decide) p (sat_cons (step1607 p h) (sat_cons (step129 p h) (sat_cons (step132 p h) (sat_nil p))))
def c1611 : List Lit := [(151, true), (13, true), (20, true), (25, true)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c1607, c133] c1611 (by decide) p (sat_cons (step1607 p h) (sat_cons (step133 p h) (sat_nil p)))
def c1612 : List Lit := [(24, false)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c761, c126] c1612 (by decide) p (sat_cons (step761 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1613 : List Lit := [(490, false)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c1016, c1013] c1613 (by decide) p (sat_cons (step1016 p h) (sat_cons (step1013 p h) (sat_nil p)))
def c1614 : List Lit := [(368, false)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c1016, c1015] c1614 (by decide) p (sat_cons (step1016 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c1615 : List Lit := [(488, false)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c1613, c1009] c1615 (by decide) p (sat_cons (step1613 p h) (sat_cons (step1009 p h) (sat_nil p)))
def c1616 : List Lit := [(428, false)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c1613, c1012] c1616 (by decide) p (sat_cons (step1613 p h) (sat_cons (step1012 p h) (sat_nil p)))
def c1617 : List Lit := [(366, false)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c1614, c903] c1617 (by decide) p (sat_cons (step1614 p h) (sat_cons (step903 p h) (sat_nil p)))
def c1618 : List Lit := [(306, false)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c1614, c906] c1618 (by decide) p (sat_cons (step1614 p h) (sat_cons (step906 p h) (sat_nil p)))
def c1619 : List Lit := [(486, false)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1004] c1619 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1004 p h) (sat_nil p)))
def c1620 : List Lit := [(456, false)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c1615, c1007] c1620 (by decide) p (sat_cons (step1615 p h) (sat_cons (step1007 p h) (sat_nil p)))
def c1621 : List Lit := [(426, false)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c1616, c949] c1621 (by decide) p (sat_cons (step1616 p h) (sat_cons (step949 p h) (sat_nil p)))
def c1622 : List Lit := [(396, false)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c1616, c952] c1622 (by decide) p (sat_cons (step1616 p h) (sat_cons (step952 p h) (sat_nil p)))
def c1623 : List Lit := [(364, false)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c1617, c898] c1623 (by decide) p (sat_cons (step1617 p h) (sat_cons (step898 p h) (sat_nil p)))
def c1624 : List Lit := [(334, false)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c1617, c901] c1624 (by decide) p (sat_cons (step1617 p h) (sat_cons (step901 p h) (sat_nil p)))
def c1625 : List Lit := [(304, false)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c1618, c854] c1625 (by decide) p (sat_cons (step1618 p h) (sat_cons (step854 p h) (sat_nil p)))
def c1626 : List Lit := [(276, false)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c1618, c857] c1626 (by decide) p (sat_cons (step1618 p h) (sat_cons (step857 p h) (sat_nil p)))
def c1627 : List Lit := [(484, false)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c1619, c999] c1627 (by decide) p (sat_cons (step1619 p h) (sat_cons (step999 p h) (sat_nil p)))
def c1628 : List Lit := [(470, false)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c1619, c1002] c1628 (by decide) p (sat_cons (step1619 p h) (sat_cons (step1002 p h) (sat_nil p)))
def c1629 : List Lit := [(454, false)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c1620, c971] c1629 (by decide) p (sat_cons (step1620 p h) (sat_cons (step971 p h) (sat_nil p)))
def c1630 : List Lit := [(440, false)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c1620, c974] c1630 (by decide) p (sat_cons (step1620 p h) (sat_cons (step974 p h) (sat_nil p)))
def c1631 : List Lit := [(394, false)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c1622, c926] c1631 (by decide) p (sat_cons (step1622 p h) (sat_cons (step926 p h) (sat_nil p)))
def c1632 : List Lit := [(380, false)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c1622, c929] c1632 (by decide) p (sat_cons (step1622 p h) (sat_cons (step929 p h) (sat_nil p)))
def c1633 : List Lit := [(348, false)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c1623, c896] c1633 (by decide) p (sat_cons (step1623 p h) (sat_cons (step896 p h) (sat_nil p)))
def c1634 : List Lit := [(332, false)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c1624, c876] c1634 (by decide) p (sat_cons (step1624 p h) (sat_cons (step876 p h) (sat_nil p)))
def c1635 : List Lit := [(318, false)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c1624, c879] c1635 (by decide) p (sat_cons (step1624 p h) (sat_cons (step879 p h) (sat_nil p)))
def c1636 : List Lit := [(302, false)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c1625, c849] c1636 (by decide) p (sat_cons (step1625 p h) (sat_cons (step849 p h) (sat_nil p)))
def c1637 : List Lit := [(288, false)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c1625, c852] c1637 (by decide) p (sat_cons (step1625 p h) (sat_cons (step852 p h) (sat_nil p)))
def c1638 : List Lit := [(260, false)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c1626, c825] c1638 (by decide) p (sat_cons (step1626 p h) (sat_cons (step825 p h) (sat_nil p)))
def c1639 : List Lit := [(476, false)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c1627, c997] c1639 (by decide) p (sat_cons (step1627 p h) (sat_cons (step997 p h) (sat_nil p)))
def c1640 : List Lit := [(462, false)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c1628, c985] c1640 (by decide) p (sat_cons (step1628 p h) (sat_cons (step985 p h) (sat_nil p)))
def c1641 : List Lit := [(452, false)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c1629, c968] c1641 (by decide) p (sat_cons (step1629 p h) (sat_cons (step968 p h) (sat_nil p)))
def c1642 : List Lit := [(340, false)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c1633, c889] c1642 (by decide) p (sat_cons (step1633 p h) (sat_cons (step889 p h) (sat_nil p)))
def c1643 : List Lit := [(300, false)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c1636, c845] c1643 (by decide) p (sat_cons (step1636 p h) (sat_cons (step845 p h) (sat_nil p)))
def c1644 : List Lit := [(280, false)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c1637, c834] c1644 (by decide) p (sat_cons (step1637 p h) (sat_cons (step834 p h) (sat_nil p)))
def c1645 : List Lit := [(258, false)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c1638, c814] c1645 (by decide) p (sat_cons (step1638 p h) (sat_cons (step814 p h) (sat_nil p)))
def c1646 : List Lit := [(472, false)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c1639, c992] c1646 (by decide) p (sat_cons (step1639 p h) (sat_cons (step992 p h) (sat_nil p)))
def c1647 : List Lit := [(338, false)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c1642, c884] c1647 (by decide) p (sat_cons (step1642 p h) (sat_cons (step884 p h) (sat_nil p)))
def c1648 : List Lit := [(298, false)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c1643, c843] c1648 (by decide) p (sat_cons (step1643 p h) (sat_cons (step843 p h) (sat_nil p)))
def c1649 : List Lit := [(1533, true)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1067] c1649 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1067 p h) (sat_nil p)))
def c1650 : List Lit := [(21, true), (1534, true)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1068] c1650 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1068 p h) (sat_nil p)))
def c1651 : List Lit := [(1537, true)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1070] c1651 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1070 p h) (sat_nil p)))
def c1652 : List Lit := [(1535, false), (1538, true)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c1649, c1071] c1652 (by decide) p (sat_cons (step1649 p h) (sat_cons (step1071 p h) (sat_nil p)))
def c1653 : List Lit := [(1529, false), (1542, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c1651, c1076] c1653 (by decide) p (sat_cons (step1651 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c1654 : List Lit := [(1530, false), (1543, true)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c1651, c1079] c1654 (by decide) p (sat_cons (step1651 p h) (sat_cons (step1079 p h) (sat_nil p)))
def c1655 : List Lit := [(1531, false), (1544, true)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c1651, c1082] c1655 (by decide) p (sat_cons (step1651 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c1656 : List Lit := [(1532, false), (1545, true)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c1651, c1085] c1656 (by decide) p (sat_cons (step1651 p h) (sat_cons (step1085 p h) (sat_nil p)))
def c1657 : List Lit := [(1659, true)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c782, c1299, c1301, c1297, c1293, c1294, c405, c402] c1657 (by decide) p (sat_cons (step782 p h) (sat_cons (step1299 p h) (sat_cons (step1301 p h) (sat_cons (step1297 p h) (sat_cons (step1293 p h) (sat_cons (step1294 p h) (sat_cons (step405 p h) (sat_cons (step402 p h) (sat_nil p)))))))))
def c1658 : List Lit := [(1663, true)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c1657, c1306] c1658 (by decide) p (sat_cons (step1657 p h) (sat_cons (step1306 p h) (sat_nil p)))
def c1659 : List Lit := [(1650, true)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c779, c1286, c1287, c391, c392, c1582] c1659 (by decide) p (sat_cons (step779 p h) (sat_cons (step1286 p h) (sat_cons (step1287 p h) (sat_cons (step391 p h) (sat_cons (step392 p h) (sat_cons (step1582 p h) (sat_nil p)))))))
def c1660 : List Lit := [(1652, true)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c1659, c1289] c1660 (by decide) p (sat_cons (step1659 p h) (sat_cons (step1289 p h) (sat_nil p)))
def c1661 : List Lit := [(1664, true)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c1660, c1657, c1307] c1661 (by decide) p (sat_cons (step1660 p h) (sat_cons (step1657 p h) (sat_cons (step1307 p h) (sat_nil p))))
def c1662 : List Lit := [(1600, true), (60, false)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c778, c1189, c1191, c1186, c1187, c1183, c1184, c371, c377, c346, c388] c1662 (by decide) p (sat_cons (step778 p h) (sat_cons (step1189 p h) (sat_cons (step1191 p h) (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step1183 p h) (sat_cons (step1184 p h) (sat_cons (step371 p h) (sat_cons (step377 p h) (sat_cons (step346 p h) (sat_cons (step388 p h) (sat_nil p))))))))))))
def c1663 : List Lit := [(1592, true)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c771, c1175, c1177, c1172, c1173, c1169, c1170, c283, c306, c273] c1663 (by decide) p (sat_cons (step771 p h) (sat_cons (step1175 p h) (sat_cons (step1177 p h) (sat_cons (step1172 p h) (sat_cons (step1173 p h) (sat_cons (step1169 p h) (sat_cons (step1170 p h) (sat_cons (step283 p h) (sat_cons (step306 p h) (sat_cons (step273 p h) (sat_nil p)))))))))))
def c1664 : List Lit := [(1604, true)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c1663, c1198] c1664 (by decide) p (sat_cons (step1663 p h) (sat_cons (step1198 p h) (sat_nil p)))
def c1665 : List Lit := [(1613, true)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c1663, c1664, c777, c1214, c1199, c1215, c1189, c1191, c1146, c1150, c1186, c1187, c1184, c1138, c1124, c368, c1135, c1136, c1121, c243, c331, c357] c1665 (by decide) p (sat_cons (step1663 p h) (sat_cons (step1664 p h) (sat_cons (step777 p h) (sat_cons (step1214 p h) (sat_cons (step1199 p h) (sat_cons (step1215 p h) (sat_cons (step1189 p h) (sat_cons (step1191 p h) (sat_cons (step1146 p h) (sat_cons (step1150 p h) (sat_cons (step1186 p h) (sat_cons (step1187 p h) (sat_cons (step1184 p h) (sat_cons (step1138 p h) (sat_cons (step1124 p h) (sat_cons (step368 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step1121 p h) (sat_cons (step243 p h) (sat_cons (step331 p h) (sat_cons (step357 p h) (sat_nil p)))))))))))))))))))))))
def c1666 : List Lit := [(1695, true)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c1661, c1355] c1666 (by decide) p (sat_cons (step1661 p h) (sat_cons (step1355 p h) (sat_nil p)))
def c1667 : List Lit := [(19, false), (21, false), (57, false)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c760, c120, c105] c1667 (by decide) p (sat_cons (step760 p h) (sat_cons (step120 p h) (sat_cons (step105 p h) (sat_nil p))))
def c1668 : List Lit := [(1543, true), (20, true), (57, false)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c1056, c1059, c1654, c1077, c1060, c1072, c1058, c1650, c1667] c1668 (by decide) p (sat_cons (step1056 p h) (sat_cons (step1059 p h) (sat_cons (step1654 p h) (sat_cons (step1077 p h) (sat_cons (step1060 p h) (sat_cons (step1072 p h) (sat_cons (step1058 p h) (sat_cons (step1650 p h) (sat_cons (step1667 p h) (sat_nil p))))))))))
def c1669 : List Lit := [(1582, true), (1565, false), (36, false), (54, false)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c1129, c1160, c1156, c1130, c1140, c1122, c1133, c196] c1669 (by decide) p (sat_cons (step1129 p h) (sat_cons (step1160 p h) (sat_cons (step1156 p h) (sat_cons (step1130 p h) (sat_cons (step1140 p h) (sat_cons (step1122 p h) (sat_cons (step1133 p h) (sat_cons (step196 p h) (sat_nil p)))))))))
def c1670 : List Lit := [(1576, true), (36, false), (1605, true)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c1663, c770, c1199, c1191, c1183, c1189, c1186, c1203, c1180, c1138, c1140, c1135, c1136, c1132, c1133, c243, c252, c201, c267, c1171, c211] c1670 (by decide) p (sat_cons (step1663 p h) (sat_cons (step770 p h) (sat_cons (step1199 p h) (sat_cons (step1191 p h) (sat_cons (step1183 p h) (sat_cons (step1189 p h) (sat_cons (step1186 p h) (sat_cons (step1203 p h) (sat_cons (step1180 p h) (sat_cons (step1138 p h) (sat_cons (step1140 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step1132 p h) (sat_cons (step1133 p h) (sat_cons (step243 p h) (sat_cons (step252 p h) (sat_cons (step201 p h) (sat_cons (step267 p h) (sat_cons (step1171 p h) (sat_cons (step211 p h) (sat_nil p))))))))))))))))))))))
end B112E008
