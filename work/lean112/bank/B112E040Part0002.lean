import B112E040Part0001
namespace B112E040
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1653 : List Lit := [(1475, false), (1463, false), (9, false), (16, true), (1491, true), (41, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c1546, c674, c969, c977, c1026, c1013, c1008, c980, c1032, c970, c1586, c89, c931, c56] c1653 (by decide) p (sat_cons (step1546 p h) (sat_cons (step674 p h) (sat_cons (step969 p h) (sat_cons (step977 p h) (sat_cons (step1026 p h) (sat_cons (step1013 p h) (sat_cons (step1008 p h) (sat_cons (step980 p h) (sat_cons (step1032 p h) (sat_cons (step970 p h) (sat_cons (step1586 p h) (sat_cons (step89 p h) (sat_cons (step931 p h) (sat_cons (step56 p h) (sat_nil p)))))))))))))))
def c1654 : List Lit := [(1504, false), (1551, true), (1531, false), (1522, false), (47, true)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c686, c1115, c1094, c1103, c1132, c1159, c1089, c1090, c1154, c1067, c1135, c1133, c1064, c1106, c1118, c368, c1096, c1109, c370] c1654 (by decide) p (sat_cons (step686 p h) (sat_cons (step1115 p h) (sat_cons (step1094 p h) (sat_cons (step1103 p h) (sat_cons (step1132 p h) (sat_cons (step1159 p h) (sat_cons (step1089 p h) (sat_cons (step1090 p h) (sat_cons (step1154 p h) (sat_cons (step1067 p h) (sat_cons (step1135 p h) (sat_cons (step1133 p h) (sat_cons (step1064 p h) (sat_cons (step1106 p h) (sat_cons (step1118 p h) (sat_cons (step368 p h) (sat_cons (step1096 p h) (sat_cons (step1109 p h) (sat_cons (step370 p h) (sat_nil p))))))))))))))))))))
def c1655 : List Lit := [(37, false), (71, false), (1594, true), (1491, true), (30, true), (22, false)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c696, c1589, c1631, c461, c982, c439, c151, c132, c142, c987, c930, c972, c992, c1586, c974, c1003, c1032, c1039, c1008, c1620, c977, c968] c1655 (by decide) p (sat_cons (step696 p h) (sat_cons (step1589 p h) (sat_cons (step1631 p h) (sat_cons (step461 p h) (sat_cons (step982 p h) (sat_cons (step439 p h) (sat_cons (step151 p h) (sat_cons (step132 p h) (sat_cons (step142 p h) (sat_cons (step987 p h) (sat_cons (step930 p h) (sat_cons (step972 p h) (sat_cons (step992 p h) (sat_cons (step1586 p h) (sat_cons (step974 p h) (sat_cons (step1003 p h) (sat_cons (step1032 p h) (sat_cons (step1039 p h) (sat_cons (step1008 p h) (sat_cons (step1620 p h) (sat_cons (step977 p h) (sat_cons (step968 p h) (sat_nil p)))))))))))))))))))))))
def c1656 : List Lit := [(351, true), (1542, true), (1531, false), (58, true), (50, true), (47, true)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c689, c691, c687, c786, c788, c783, c784, c775, c781, c778, c774, c780, c777, c773, c431, c394, c380, c395, c1099, c382, c1108, c372, c1118, c1096, c1137, c1107] c1656 (by decide) p (sat_cons (step689 p h) (sat_cons (step691 p h) (sat_cons (step687 p h) (sat_cons (step786 p h) (sat_cons (step788 p h) (sat_cons (step783 p h) (sat_cons (step784 p h) (sat_cons (step775 p h) (sat_cons (step781 p h) (sat_cons (step778 p h) (sat_cons (step774 p h) (sat_cons (step780 p h) (sat_cons (step777 p h) (sat_cons (step773 p h) (sat_cons (step431 p h) (sat_cons (step394 p h) (sat_cons (step380 p h) (sat_cons (step395 p h) (sat_cons (step1099 p h) (sat_cons (step382 p h) (sat_cons (step1108 p h) (sat_cons (step372 p h) (sat_cons (step1118 p h) (sat_cons (step1096 p h) (sat_cons (step1137 p h) (sat_cons (step1107 p h) (sat_nil p)))))))))))))))))))))))))))
def c1657 : List Lit := [(1528, true), (56, false)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c691, c1108, c1109, c396, c390] c1657 (by decide) p (sat_cons (step691 p h) (sat_cons (step1108 p h) (sat_cons (step1109 p h) (sat_cons (step396 p h) (sat_cons (step390 p h) (sat_nil p))))))
def c1658 : List Lit := [(349, true), (1540, true), (1531, false), (58, true), (50, true)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c689, c691, c783, c784, c781, c778, c780, c777, c431, c394, c380, c395, c1099, c1108, c1101, c1118, c1133] c1658 (by decide) p (sat_cons (step689 p h) (sat_cons (step691 p h) (sat_cons (step783 p h) (sat_cons (step784 p h) (sat_cons (step781 p h) (sat_cons (step778 p h) (sat_cons (step780 p h) (sat_cons (step777 p h) (sat_cons (step431 p h) (sat_cons (step394 p h) (sat_cons (step380 p h) (sat_cons (step395 p h) (sat_cons (step1099 p h) (sat_cons (step1108 p h) (sat_cons (step1101 p h) (sat_cons (step1118 p h) (sat_cons (step1133 p h) (sat_nil p))))))))))))))))))
def c1659 : List Lit := [(48, true), (169, true), (1526, true), (50, true)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c687, c1099, c382, c1104, c372, c1095] c1659 (by decide) p (sat_cons (step687 p h) (sat_cons (step1099 p h) (sat_cons (step382 p h) (sat_cons (step1104 p h) (sat_cons (step372 p h) (sat_cons (step1095 p h) (sat_nil p)))))))
def c1660 : List Lit := [(1550, true), (1531, false), (58, true), (50, true), (1503, false), (1514, false)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c1537, c689, c687, c1542, c691, c1115, c1097, c1100, c1147, c1129, c1135, c1121, c1658, c789, c775, c774, c773, c1659, c380, c381, c431, c383, c780, c373, c781, c785, c778, c777, c394, c395, c1108, c1110, c1118, c370, c1128, c1064, c1153, c1067, c1085] c1660 (by decide) p (sat_cons (step1537 p h) (sat_cons (step689 p h) (sat_cons (step687 p h) (sat_cons (step1542 p h) (sat_cons (step691 p h) (sat_cons (step1115 p h) (sat_cons (step1097 p h) (sat_cons (step1100 p h) (sat_cons (step1147 p h) (sat_cons (step1129 p h) (sat_cons (step1135 p h) (sat_cons (step1121 p h) (sat_cons (step1658 p h) (sat_cons (step789 p h) (sat_cons (step775 p h) (sat_cons (step774 p h) (sat_cons (step773 p h) (sat_cons (step1659 p h) (sat_cons (step380 p h) (sat_cons (step381 p h) (sat_cons (step431 p h) (sat_cons (step383 p h) (sat_cons (step780 p h) (sat_cons (step373 p h) (sat_cons (step781 p h) (sat_cons (step785 p h) (sat_cons (step778 p h) (sat_cons (step777 p h) (sat_cons (step394 p h) (sat_cons (step395 p h) (sat_cons (step1108 p h) (sat_cons (step1110 p h) (sat_cons (step1118 p h) (sat_cons (step370 p h) (sat_cons (step1128 p h) (sat_cons (step1064 p h) (sat_cons (step1153 p h) (sat_cons (step1067 p h) (sat_cons (step1085 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c1661 : List Lit := [(3, false), (14, true)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c666, c6] c1661 (by decide) p (sat_cons (step666 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1662 : List Lit := [(3, false), (2, true)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c666, c7] c1662 (by decide) p (sat_cons (step666 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1663 : List Lit := [(2, true), (4, false), (10, true)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c667, c9] c1663 (by decide) p (sat_cons (step667 p h) (sat_cons (step9 p h) (sat_nil p)))
def c1664 : List Lit := [(1, true), (4, false), (10, true)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c667, c10] c1664 (by decide) p (sat_cons (step667 p h) (sat_cons (step10 p h) (sat_nil p)))
def c1665 : List Lit := [(2, true), (1, true), (4, false)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c667, c11] c1665 (by decide) p (sat_cons (step667 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1666 : List Lit := [(17, true), (8, true), (25, true), (6, false)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c668, c35] c1666 (by decide) p (sat_cons (step668 p h) (sat_cons (step35 p h) (sat_nil p)))
def c1667 : List Lit := [(17, true), (25, true), (5, true), (6, false)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c668, c36] c1667 (by decide) p (sat_cons (step668 p h) (sat_cons (step36 p h) (sat_nil p)))
def c1668 : List Lit := [(8, true), (25, true), (5, true), (6, false)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c668, c37] c1668 (by decide) p (sat_cons (step668 p h) (sat_cons (step37 p h) (sat_nil p)))
def c1669 : List Lit := [(17, true), (8, true), (5, true), (6, false)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c668, c38] c1669 (by decide) p (sat_cons (step668 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1670 : List Lit := [(7, false), (10, true), (5, true), (8, true)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c669, c42] c1670 (by decide) p (sat_cons (step669 p h) (sat_cons (step42 p h) (sat_nil p)))
def c1671 : List Lit := [(1, true), (7, false), (8, true), (10, true)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c669, c43] c1671 (by decide) p (sat_cons (step669 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1672 : List Lit := [(1, true), (7, false), (5, true), (10, true)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c669, c44] c1672 (by decide) p (sat_cons (step669 p h) (sat_cons (step44 p h) (sat_nil p)))
def c1673 : List Lit := [(1, true), (7, false), (8, true), (5, true)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c669, c45] c1673 (by decide) p (sat_cons (step669 p h) (sat_cons (step45 p h) (sat_nil p)))
def c1674 : List Lit := [(81, true), (5, true), (27, true), (10, true), (9, false)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c670, c53] c1674 (by decide) p (sat_cons (step670 p h) (sat_cons (step53 p h) (sat_nil p)))
def c1675 : List Lit := [(14, true), (12, false), (11, true), (17, true)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c671, c63] c1675 (by decide) p (sat_cons (step671 p h) (sat_cons (step63 p h) (sat_nil p)))
def c1676 : List Lit := [(12, false), (13, true), (11, true), (17, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c671, c64] c1676 (by decide) p (sat_cons (step671 p h) (sat_cons (step64 p h) (sat_nil p)))
def c1677 : List Lit := [(14, true), (13, true), (11, true), (12, false)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c671, c65] c1677 (by decide) p (sat_cons (step671 p h) (sat_cons (step65 p h) (sat_nil p)))
def c1678 : List Lit := [(19, true), (13, true), (15, false), (35, true)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c672, c73] c1678 (by decide) p (sat_cons (step672 p h) (sat_cons (step73 p h) (sat_nil p)))
def c1679 : List Lit := [(14, true), (13, true), (35, true), (15, false)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c672, c74] c1679 (by decide) p (sat_cons (step672 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1680 : List Lit := [(17, true), (11, true), (55, true), (36, true), (16, false)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c673, c77] c1680 (by decide) p (sat_cons (step673 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1681 : List Lit := [(17, true), (5, true), (16, false), (55, true), (36, true)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c673, c78] c1681 (by decide) p (sat_cons (step673 p h) (sat_cons (step78 p h) (sat_nil p)))
def c1682 : List Lit := [(11, true), (5, true), (36, true), (16, false), (55, true)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c673, c79] c1682 (by decide) p (sat_cons (step673 p h) (sat_cons (step79 p h) (sat_nil p)))
def c1683 : List Lit := [(5, true), (17, true), (55, true), (11, true), (16, false)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c673, c80] c1683 (by decide) p (sat_cons (step673 p h) (sat_cons (step80 p h) (sat_nil p)))
def c1684 : List Lit := [(17, true), (5, true), (36, true), (16, false), (11, true)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c673, c81] c1684 (by decide) p (sat_cons (step673 p h) (sat_cons (step81 p h) (sat_nil p)))
def c1685 : List Lit := [(19, true), (18, false), (41, true)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c674, c88] c1685 (by decide) p (sat_cons (step674 p h) (sat_cons (step88 p h) (sat_nil p)))
def c1686 : List Lit := [(10, true), (18, false), (41, true)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c674, c89] c1686 (by decide) p (sat_cons (step674 p h) (sat_cons (step89 p h) (sat_nil p)))
def c1687 : List Lit := [(19, true), (10, true), (18, false)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c674, c90] c1687 (by decide) p (sat_cons (step674 p h) (sat_cons (step90 p h) (sat_nil p)))
def c1688 : List Lit := [(21, false), (23, true), (25, true)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c675, c99] c1688 (by decide) p (sat_cons (step675 p h) (sat_cons (step99 p h) (sat_nil p)))
def c1689 : List Lit := [(21, false), (20, true), (25, true)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c675, c100] c1689 (by decide) p (sat_cons (step675 p h) (sat_cons (step100 p h) (sat_nil p)))
def c1690 : List Lit := [(20, true), (21, false), (23, true)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c675, c101] c1690 (by decide) p (sat_cons (step675 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1691 : List Lit := [(23, true), (20, true), (22, false), (31, true)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c676, c102] c1691 (by decide) p (sat_cons (step676 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1692 : List Lit := [(1, true), (23, true), (22, false), (31, true)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c676, c103] c1692 (by decide) p (sat_cons (step676 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1693 : List Lit := [(1, true), (20, true), (22, false), (31, true)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c676, c104] c1693 (by decide) p (sat_cons (step676 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1694 : List Lit := [(96, true), (29, true), (24, false), (35, true)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c677, c116] c1694 (by decide) p (sat_cons (step677 p h) (sat_cons (step116 p h) (sat_nil p)))
def c1695 : List Lit := [(96, true), (35, true), (24, false), (23, true)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c677, c117] c1695 (by decide) p (sat_cons (step677 p h) (sat_cons (step117 p h) (sat_nil p)))
def c1696 : List Lit := [(96, true), (29, true), (24, false), (23, true)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c677, c118] c1696 (by decide) p (sat_cons (step677 p h) (sat_cons (step118 p h) (sat_nil p)))
def c1697 : List Lit := [(35, true), (29, true), (23, true), (24, false)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c677, c119] c1697 (by decide) p (sat_cons (step677 p h) (sat_cons (step119 p h) (sat_nil p)))
def c1698 : List Lit := [(25, true), (65, true), (23, true), (29, true), (26, false), (100, true)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c678, c169] c1698 (by decide) p (sat_cons (step678 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1699 : List Lit := [(100, true), (8, true), (25, true), (29, true), (23, true), (26, false)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c678, c170] c1699 (by decide) p (sat_cons (step678 p h) (sat_cons (step170 p h) (sat_nil p)))
def c1700 : List Lit := [(40, true), (29, true), (28, false), (27, true)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c679, c180] c1700 (by decide) p (sat_cons (step679 p h) (sat_cons (step180 p h) (sat_nil p)))
def c1701 : List Lit := [(25, true), (29, true), (28, false), (40, true)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c679, c181] c1701 (by decide) p (sat_cons (step679 p h) (sat_cons (step181 p h) (sat_nil p)))
def c1702 : List Lit := [(25, true), (40, true), (27, true), (28, false)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c679, c182] c1702 (by decide) p (sat_cons (step679 p h) (sat_cons (step182 p h) (sat_nil p)))
def c1703 : List Lit := [(25, true), (29, true), (28, false), (27, true)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c679, c183] c1703 (by decide) p (sat_cons (step679 p h) (sat_cons (step183 p h) (sat_nil p)))
def c1704 : List Lit := [(13, true), (103, true), (68, true), (31, true), (32, false), (35, true)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c680, c223] c1704 (by decide) p (sat_cons (step680 p h) (sat_cons (step223 p h) (sat_nil p)))
def c1705 : List Lit := [(103, true), (13, true), (23, true), (31, true), (35, true), (32, false)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c680, c224] c1705 (by decide) p (sat_cons (step680 p h) (sat_cons (step224 p h) (sat_nil p)))
def c1706 : List Lit := [(35, true), (23, true), (31, true), (13, true), (68, true), (32, false)]
theorem step1706 (p : Nat → Bool) (h : Constraints p) : clause p c1706 = true :=
  Snake9.LocalRup.prove_clause [c680, c225] c1706 (by decide) p (sat_cons (step680 p h) (sat_cons (step225 p h) (sat_nil p)))
def c1707 : List Lit := [(33, true), (35, true), (34, false), (41, true)]
theorem step1707 (p : Nat → Bool) (h : Constraints p) : clause p c1707 = true :=
  Snake9.LocalRup.prove_clause [c681, c227] c1707 (by decide) p (sat_cons (step681 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1708 : List Lit := [(35, true), (31, true), (34, false), (41, true)]
theorem step1708 (p : Nat → Bool) (h : Constraints p) : clause p c1708 = true :=
  Snake9.LocalRup.prove_clause [c681, c228] c1708 (by decide) p (sat_cons (step681 p h) (sat_cons (step228 p h) (sat_nil p)))
def c1709 : List Lit := [(33, true), (31, true), (41, true), (34, false)]
theorem step1709 (p : Nat → Bool) (h : Constraints p) : clause p c1709 = true :=
  Snake9.LocalRup.prove_clause [c681, c229] c1709 (by decide) p (sat_cons (step681 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1710 : List Lit := [(33, true), (31, true), (34, false), (35, true)]
theorem step1710 (p : Nat → Bool) (h : Constraints p) : clause p c1710 = true :=
  Snake9.LocalRup.prove_clause [c681, c230] c1710 (by decide) p (sat_cons (step681 p h) (sat_cons (step230 p h) (sat_nil p)))
def c1711 : List Lit := [(17, true), (25, true), (40, true), (36, true), (37, false), (107, true)]
theorem step1711 (p : Nat → Bool) (h : Constraints p) : clause p c1711 = true :=
  Snake9.LocalRup.prove_clause [c682, c296] c1711 (by decide) p (sat_cons (step682 p h) (sat_cons (step296 p h) (sat_nil p)))
def c1712 : List Lit := [(108, true), (38, false), (41, true), (36, true)]
theorem step1712 (p : Nat → Bool) (h : Constraints p) : clause p c1712 = true :=
  Snake9.LocalRup.prove_clause [c683, c297] c1712 (by decide) p (sat_cons (step683 p h) (sat_cons (step297 p h) (sat_nil p)))
def c1713 : List Lit := [(31, true), (108, true), (41, true), (38, false)]
theorem step1713 (p : Nat → Bool) (h : Constraints p) : clause p c1713 = true :=
  Snake9.LocalRup.prove_clause [c683, c298] c1713 (by decide) p (sat_cons (step683 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1714 : List Lit := [(31, true), (38, false), (36, true), (108, true)]
theorem step1714 (p : Nat → Bool) (h : Constraints p) : clause p c1714 = true :=
  Snake9.LocalRup.prove_clause [c683, c299] c1714 (by decide) p (sat_cons (step683 p h) (sat_cons (step299 p h) (sat_nil p)))
def c1715 : List Lit := [(31, true), (38, false), (41, true), (36, true)]
theorem step1715 (p : Nat → Bool) (h : Constraints p) : clause p c1715 = true :=
  Snake9.LocalRup.prove_clause [c683, c300] c1715 (by decide) p (sat_cons (step683 p h) (sat_cons (step300 p h) (sat_nil p)))
def c1716 : List Lit := [(40, true), (33, true), (36, true), (39, false), (41, true)]
theorem step1716 (p : Nat → Bool) (h : Constraints p) : clause p c1716 = true :=
  Snake9.LocalRup.prove_clause [c684, c304] c1716 (by decide) p (sat_cons (step684 p h) (sat_cons (step304 p h) (sat_nil p)))
end B112E040
