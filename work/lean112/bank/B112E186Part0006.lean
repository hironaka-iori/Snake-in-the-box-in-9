import B112E186Part0005
namespace B112E186
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1784 : List Lit := [(1695, true), (83, true), (1680, false)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1133, c1101, c1149, c1437, c1154, c1782, c1138, c1067, c1081, c1085, c1103, c1110, c1073, c1059, c1070, c1071, c1056, c246, c1629, c264, c269, c1625, c1100, c280] c1784 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1133 p h) (sat_cons (step1101 p h) (sat_cons (step1149 p h) (sat_cons (step1437 p h) (sat_cons (step1154 p h) (sat_cons (step1782 p h) (sat_cons (step1138 p h) (sat_cons (step1067 p h) (sat_cons (step1081 p h) (sat_cons (step1085 p h) (sat_cons (step1103 p h) (sat_cons (step1110 p h) (sat_cons (step1073 p h) (sat_cons (step1059 p h) (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step1056 p h) (sat_cons (step246 p h) (sat_cons (step1629 p h) (sat_cons (step264 p h) (sat_cons (step269 p h) (sat_cons (step1625 p h) (sat_cons (step1100 p h) (sat_cons (step280 p h) (sat_nil p))))))))))))))))))))))))))
def c1785 : List Lit := [(117, false), (116, true), (114, false), (109, false)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c563, c1686] c1785 (by decide) p (sat_cons (step563 p h) (sat_cons (step1686 p h) (sat_nil p)))
def c1786 : List Lit := [(1681, false), (111, true), (1696, true), (83, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1134, c1495, c1155, c1081, c1085, c1073, c1075, c1059, c1070, c1067, c1056, c246] c1786 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1134 p h) (sat_cons (step1495 p h) (sat_cons (step1155 p h) (sat_cons (step1081 p h) (sat_cons (step1085 p h) (sat_cons (step1073 p h) (sat_cons (step1075 p h) (sat_cons (step1059 p h) (sat_cons (step1070 p h) (sat_cons (step1067 p h) (sat_cons (step1056 p h) (sat_cons (step246 p h) (sat_nil p))))))))))))))
def c1787 : List Lit := [(1659, true), (111, true), (77, true)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c1081, c1085, c1075, c1059, c1068, c1056, c1057, c1619, c217] c1787 (by decide) p (sat_cons (step1081 p h) (sat_cons (step1085 p h) (sat_cons (step1075 p h) (sat_cons (step1059 p h) (sat_cons (step1068 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1619 p h) (sat_cons (step217 p h) (sat_nil p))))))))))
def c1788 : List Lit := [(66, true), (77, true), (111, true), (105, false), (1660, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1060, c1056, c1058, c1059, c1086, c1075, c1068, c1619, c219] c1788 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1060 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step1086 p h) (sat_cons (step1075 p h) (sat_cons (step1068 p h) (sat_cons (step1619 p h) (sat_cons (step219 p h) (sat_nil p)))))))))))
def c1789 : List Lit := [(69, false), (66, false), (77, true), (111, true), (105, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c1619, c220] c1789 (by decide) p (sat_cons (step1619 p h) (sat_cons (step220 p h) (sat_nil p)))
def c1790 : List Lit := [(77, true), (111, true), (105, false), (83, true), (1696, true), (1680, false)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1133, c1161, c1082, c1078, c1101, c1787, c1155, c1138, c1110, c1788, c1789, c1068, c1069, c1076, c1070, c246, c1629, c269, c1099, c1100, c1108, c1634, c1635, c1103, c1374] c1790 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1133 p h) (sat_cons (step1161 p h) (sat_cons (step1082 p h) (sat_cons (step1078 p h) (sat_cons (step1101 p h) (sat_cons (step1787 p h) (sat_cons (step1155 p h) (sat_cons (step1138 p h) (sat_cons (step1110 p h) (sat_cons (step1788 p h) (sat_cons (step1789 p h) (sat_cons (step1068 p h) (sat_cons (step1069 p h) (sat_cons (step1076 p h) (sat_cons (step1070 p h) (sat_cons (step246 p h) (sat_cons (step1629 p h) (sat_cons (step269 p h) (sat_cons (step1099 p h) (sat_cons (step1100 p h) (sat_cons (step1108 p h) (sat_cons (step1634 p h) (sat_cons (step1635 p h) (sat_cons (step1103 p h) (sat_cons (step1374 p h) (sat_nil p)))))))))))))))))))))))))))
def c1791 : List Lit := [(1525, true), (24, false), (98, false)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c862, c863, c71] c1791 (by decide) p (sat_cons (step862 p h) (sat_cons (step863 p h) (sat_cons (step71 p h) (sat_nil p))))
def c1792 : List Lit := [(1573, true)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c934, c1707, c1769, c1433] c1792 (by decide) p (sat_cons (step934 p h) (sat_cons (step1707 p h) (sat_cons (step1769 p h) (sat_cons (step1433 p h) (sat_nil p)))))
def c1793 : List Lit := [(1598, true), (1580, false), (88, true), (1660, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c1509, c1519, c1480, c1594, c1061, c963, c1086, c188, c1075, c1067] c1793 (by decide) p (sat_cons (step1509 p h) (sat_cons (step1519 p h) (sat_cons (step1480 p h) (sat_cons (step1594 p h) (sat_cons (step1061 p h) (sat_cons (step963 p h) (sat_cons (step1086 p h) (sat_cons (step188 p h) (sat_cons (step1075 p h) (sat_cons (step1067 p h) (sat_nil p)))))))))))
def c1794 : List Lit := [(1606, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c1792, c1713] c1794 (by decide) p (sat_cons (step1792 p h) (sat_cons (step1713 p h) (sat_nil p)))
def c1795 : List Lit := [(1659, true), (1672, true), (60, false)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c1109, c1081, c1085, c1073, c1075, c1059, c1070, c1071, c1067, c1068, c1056, c246, c1629, c269, c1099, c1100, c1107, c276, c1102, c1635, c280] c1795 (by decide) p (sat_cons (step1109 p h) (sat_cons (step1081 p h) (sat_cons (step1085 p h) (sat_cons (step1073 p h) (sat_cons (step1075 p h) (sat_cons (step1059 p h) (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_cons (step1056 p h) (sat_cons (step246 p h) (sat_cons (step1629 p h) (sat_cons (step269 p h) (sat_cons (step1099 p h) (sat_cons (step1100 p h) (sat_cons (step1107 p h) (sat_cons (step276 p h) (sat_cons (step1102 p h) (sat_cons (step1635 p h) (sat_cons (step280 p h) (sat_nil p))))))))))))))))))))))
def c1796 : List Lit := [(76, true), (71, false), (69, false), (1672, true), (60, false)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c1109, c1099, c1100, c1107, c276, c1102, c1635, c280] c1796 (by decide) p (sat_cons (step1109 p h) (sat_cons (step1099 p h) (sat_cons (step1100 p h) (sat_cons (step1107 p h) (sat_cons (step276 p h) (sat_cons (step1102 p h) (sat_cons (step1635 p h) (sat_cons (step280 p h) (sat_nil p)))))))))
def c1797 : List Lit := [(97, false), (83, false), (96, true)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c1652, c1651, c1377] c1797 (by decide) p (sat_cons (step1652 p h) (sat_cons (step1651 p h) (sat_cons (step1377 p h) (sat_nil p))))
def c1798 : List Lit := [(1681, false), (1695, true), (60, false)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c1149, c1726, c1134, c1154, c1795] c1798 (by decide) p (sat_cons (step1149 p h) (sat_cons (step1726 p h) (sat_cons (step1134 p h) (sat_cons (step1154 p h) (sat_cons (step1795 p h) (sat_nil p))))))
def c1799 : List Lit := [(81, false), (1583, false), (67, true), (1600, true), (62, false), (70, false), (71, false)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c264, c1499, c1622, c965, c186, c190, c948, c963, c958, c971, c987] c1799 (by decide) p (sat_cons (step264 p h) (sat_cons (step1499 p h) (sat_cons (step1622 p h) (sat_cons (step965 p h) (sat_cons (step186 p h) (sat_cons (step190 p h) (sat_cons (step948 p h) (sat_cons (step963 p h) (sat_cons (step958 p h) (sat_cons (step971 p h) (sat_cons (step987 p h) (sat_nil p))))))))))))
def c1800 : List Lit := [(1653, true), (66, false), (67, true), (69, false), (1672, true), (60, false)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c1070, c1071, c1629, c1796, c269] c1800 (by decide) p (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step1629 p h) (sat_cons (step1796 p h) (sat_cons (step269 p h) (sat_nil p))))))
def c1801 : List Lit := [(111, false), (69, false), (112, false), (1734, true)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c595, c594, c1233] c1801 (by decide) p (sat_cons (step595 p h) (sat_cons (step594 p h) (sat_cons (step1233 p h) (sat_nil p))))
def c1802 : List Lit := [(81, false), (71, false), (51, true), (62, false), (65, false), (67, true), (70, false), (1600, true)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c264, c1799, c1627, c953, c251] c1802 (by decide) p (sat_cons (step264 p h) (sat_cons (step1799 p h) (sat_cons (step1627 p h) (sat_cons (step953 p h) (sat_cons (step251 p h) (sat_nil p))))))
def c1803 : List Lit := [(1588, true), (1677, true)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c1116, c1115, c962, c963, c412, c1600, c194] c1803 (by decide) p (sat_cons (step1116 p h) (sat_cons (step1115 p h) (sat_cons (step962 p h) (sat_cons (step963 p h) (sat_cons (step412 p h) (sat_cons (step1600 p h) (sat_cons (step194 p h) (sat_nil p))))))))
def c1804 : List Lit := [(1735, true), (1677, true)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c1116, c1115, c1234, c1236, c1231, c1232, c1228, c1229, c419, c621, c600, c1681] c1804 (by decide) p (sat_cons (step1116 p h) (sat_cons (step1115 p h) (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step1228 p h) (sat_cons (step1229 p h) (sat_cons (step419 p h) (sat_cons (step621 p h) (sat_cons (step600 p h) (sat_cons (step1681 p h) (sat_nil p)))))))))))))
def c1805 : List Lit := [(70, false), (62, false), (65, false), (66, false), (71, false), (75, false), (81, false), (1600, true), (60, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c246, c1512, c1802] c1805 (by decide) p (sat_cons (step246 p h) (sat_cons (step1512 p h) (sat_cons (step1802 p h) (sat_nil p))))
def c1806 : List Lit := [(1651, false), (1680, false), (1600, true), (1695, true), (60, false)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c1725, c1160, c1082, c1075, c1081, c1437, c1154, c1086, c1102, c1133, c1076, c1059, c1061, c1109, c1070, c1071, c1056, c1057, c1053, c1805, c1463] c1806 (by decide) p (sat_cons (step1725 p h) (sat_cons (step1160 p h) (sat_cons (step1082 p h) (sat_cons (step1075 p h) (sat_cons (step1081 p h) (sat_cons (step1437 p h) (sat_cons (step1154 p h) (sat_cons (step1086 p h) (sat_cons (step1102 p h) (sat_cons (step1133 p h) (sat_cons (step1076 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1109 p h) (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1053 p h) (sat_cons (step1805 p h) (sat_cons (step1463 p h) (sat_nil p))))))))))))))))))))))
def c1807 : List Lit := [(66, false), (67, false), (70, false), (1660, true)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c246, c240, c1070, c1057, c1073, c1059, c1086] c1807 (by decide) p (sat_cons (step246 p h) (sat_cons (step240 p h) (sat_cons (step1070 p h) (sat_cons (step1057 p h) (sat_cons (step1073 p h) (sat_cons (step1059 p h) (sat_cons (step1086 p h) (sat_nil p))))))))
def c1808 : List Lit := [(97, false), (83, false), (84, false), (101, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c1797, c456] c1808 (by decide) p (sat_cons (step1797 p h) (sat_cons (step456 p h) (sat_nil p)))
def c1809 : List Lit := [(1651, false), (1660, true), (1672, true), (1600, true), (60, false)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c1082, c1078, c1075, c1076, c1086, c1070, c1071, c1059, c1061, c1056, c1057, c1053, c241, c1800, c1629, c1069, c269, c1805, c1099, c1102, c1107] c1809 (by decide) p (sat_cons (step1082 p h) (sat_cons (step1078 p h) (sat_cons (step1075 p h) (sat_cons (step1076 p h) (sat_cons (step1086 p h) (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1053 p h) (sat_cons (step241 p h) (sat_cons (step1800 p h) (sat_cons (step1629 p h) (sat_cons (step1069 p h) (sat_cons (step269 p h) (sat_cons (step1805 p h) (sat_cons (step1099 p h) (sat_cons (step1102 p h) (sat_cons (step1107 p h) (sat_nil p))))))))))))))))))))))
def c1810 : List Lit := [(1659, true), (1673, true), (1534, false), (1630, true), (1592, false), (60, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c1792, c1702, c1025, c996, c1081, c1085, c1073, c1075, c1059, c1061, c1070, c1071, c1067, c1068, c1056, c1057, c1053, c1805, c246, c217, c1512, c1102, c1629, c1615, c1110, c269, c250, c251, c1100, c953, c276, c1635, c260, c1622, c186, c948, c958, c986, c1000, c995, c1708, c1031, c913, c894, c1518] c1810 (by decide) p (sat_cons (step1792 p h) (sat_cons (step1702 p h) (sat_cons (step1025 p h) (sat_cons (step996 p h) (sat_cons (step1081 p h) (sat_cons (step1085 p h) (sat_cons (step1073 p h) (sat_cons (step1075 p h) (sat_cons (step1059 p h) (sat_cons (step1061 p h) (sat_cons (step1070 p h) (sat_cons (step1071 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_cons (step1056 p h) (sat_cons (step1057 p h) (sat_cons (step1053 p h) (sat_cons (step1805 p h) (sat_cons (step246 p h) (sat_cons (step217 p h) (sat_cons (step1512 p h) (sat_cons (step1102 p h) (sat_cons (step1629 p h) (sat_cons (step1615 p h) (sat_cons (step1110 p h) (sat_cons (step269 p h) (sat_cons (step250 p h) (sat_cons (step251 p h) (sat_cons (step1100 p h) (sat_cons (step953 p h) (sat_cons (step276 p h) (sat_cons (step1635 p h) (sat_cons (step260 p h) (sat_cons (step1622 p h) (sat_cons (step186 p h) (sat_cons (step948 p h) (sat_cons (step958 p h) (sat_cons (step986 p h) (sat_cons (step1000 p h) (sat_cons (step995 p h) (sat_cons (step1708 p h) (sat_cons (step1031 p h) (sat_cons (step913 p h) (sat_cons (step894 p h) (sat_cons (step1518 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c1811 : List Lit := [(1519, true), (1677, true)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c1116, c1115, c851, c852, c59, c408, c1559] c1811 (by decide) p (sat_cons (step1116 p h) (sat_cons (step1115 p h) (sat_cons (step851 p h) (sat_cons (step852 p h) (sat_cons (step59 p h) (sat_cons (step408 p h) (sat_cons (step1559 p h) (sat_nil p))))))))
def c1812 : List Lit := [(19, false), (17, false), (90, true), (92, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c59, c1559] c1812 (by decide) p (sat_cons (step59 p h) (sat_cons (step1559 p h) (sat_nil p)))
def c1813 : List Lit := [(18, true), (13, false), (84, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c1547, c1549, c1353] c1813 (by decide) p (sat_cons (step1547 p h) (sat_cons (step1549 p h) (sat_cons (step1353 p h) (sat_nil p))))
def c1814 : List Lit := [(1694, true), (1685, false), (1534, false), (1630, true), (1592, false), (60, false), (1679, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c1148, c1153, c1137, c1810] c1814 (by decide) p (sat_cons (step1148 p h) (sat_cons (step1153 p h) (sat_cons (step1137 p h) (sat_cons (step1810 p h) (sat_nil p)))))
def c1815 : List Lit := [(66, false), (67, true), (47, true), (106, true), (105, false), (1660, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c1618, c218, c220, c1057, c1068, c1059, c1075, c1086] c1815 (by decide) p (sat_cons (step1618 p h) (sat_cons (step218 p h) (sat_cons (step220 p h) (sat_cons (step1057 p h) (sat_cons (step1068 p h) (sat_cons (step1059 p h) (sat_cons (step1075 p h) (sat_cons (step1086 p h) (sat_nil p)))))))))
def c1816 : List Lit := [(66, true), (67, false), (1660, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c1089, c1060, c1056, c1058, c1059, c1086, c1073, c1075, c1070, c1067, c243] c1816 (by decide) p (sat_cons (step1089 p h) (sat_cons (step1060 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step1086 p h) (sat_cons (step1073 p h) (sat_cons (step1075 p h) (sat_cons (step1070 p h) (sat_cons (step1067 p h) (sat_cons (step243 p h) (sat_nil p))))))))))))
def c1817 : List Lit := [(67, false), (70, false), (1660, true)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1807] c1817 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1807 p h) (sat_nil p)))
def c1818 : List Lit := [(107, false), (106, false), (1736, true), (84, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c546, c545, c1232, c1229, c1237] c1818 (by decide) p (sat_cons (step546 p h) (sat_cons (step545 p h) (sat_cons (step1232 p h) (sat_cons (step1229 p h) (sat_cons (step1237 p h) (sat_nil p))))))
def c1819 : List Lit := [(106, false), (77, true), (66, true), (69, false), (1660, true), (1736, true), (1718, true), (84, false)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1235, c1818, c1201, c1788, c543, c1801, c1230] c1819 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1235 p h) (sat_cons (step1818 p h) (sat_cons (step1201 p h) (sat_cons (step1788 p h) (sat_cons (step543 p h) (sat_cons (step1801 p h) (sat_cons (step1230 p h) (sat_nil p)))))))))
def c1820 : List Lit := [(105, false), (77, true), (66, true), (69, false), (1660, true), (1734, true)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1788, c593, c592, c1233] c1820 (by decide) p (sat_cons (step1788 p h) (sat_cons (step593 p h) (sat_cons (step592 p h) (sat_cons (step1233 p h) (sat_nil p)))))
def c1821 : List Lit := [(66, true), (1660, true), (1736, true), (1718, true), (84, false), (1672, true), (1600, true), (60, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c1809, c1067, c1817, c1068, c1089, c1060, c1235, c1478, c1056, c1058, c1059, c1062, c1086, c1053, c1073, c1512, c1071, c1802, c1102, c1107, c1098, c276, c1819, c1820, c1201, c344, c1668] c1821 (by decide) p (sat_cons (step1809 p h) (sat_cons (step1067 p h) (sat_cons (step1817 p h) (sat_cons (step1068 p h) (sat_cons (step1089 p h) (sat_cons (step1060 p h) (sat_cons (step1235 p h) (sat_cons (step1478 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step1062 p h) (sat_cons (step1086 p h) (sat_cons (step1053 p h) (sat_cons (step1073 p h) (sat_cons (step1512 p h) (sat_cons (step1071 p h) (sat_cons (step1802 p h) (sat_cons (step1102 p h) (sat_cons (step1107 p h) (sat_cons (step1098 p h) (sat_cons (step276 p h) (sat_cons (step1819 p h) (sat_cons (step1820 p h) (sat_cons (step1201 p h) (sat_cons (step344 p h) (sat_cons (step1668 p h) (sat_nil p))))))))))))))))))))))))))))
def c1822 : List Lit := [(67, false), (66, false), (1660, true)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c1082, c1807, c1067, c1075, c1076, c1086, c1070, c1059, c241, c1057] c1822 (by decide) p (sat_cons (step1082 p h) (sat_cons (step1807 p h) (sat_cons (step1067 p h) (sat_cons (step1075 p h) (sat_cons (step1076 p h) (sat_cons (step1086 p h) (sat_cons (step1070 p h) (sat_cons (step1059 p h) (sat_cons (step241 p h) (sat_cons (step1057 p h) (sat_nil p)))))))))))
def c1823 : List Lit := [(1680, false), (1694, true), (60, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1148, c1725, c1133, c1153, c1795] c1823 (by decide) p (sat_cons (step1148 p h) (sat_cons (step1725 p h) (sat_cons (step1133 p h) (sat_cons (step1153 p h) (sat_cons (step1795 p h) (sat_nil p))))))
def c1824 : List Lit := [(1735, true), (84, false), (101, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1234, c1236, c1231, c1232, c1228, c1229, c624, c600, c402, c547, c1679] c1824 (by decide) p (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step1228 p h) (sat_cons (step1229 p h) (sat_cons (step624 p h) (sat_cons (step600 p h) (sat_cons (step402 p h) (sat_cons (step547 p h) (sat_cons (step1679 p h) (sat_nil p))))))))))))
def c1825 : List Lit := [(1762, true), (1727, false), (1713, false), (1744, false), (101, false), (1715, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1257, c1293, c1289, c1223, c1262, c1206, c1234, c1236, c1231, c1232, c1228, c1229, c624, c600, c1468, c1680, c1201, c560] c1825 (by decide) p (sat_cons (step1257 p h) (sat_cons (step1293 p h) (sat_cons (step1289 p h) (sat_cons (step1223 p h) (sat_cons (step1262 p h) (sat_cons (step1206 p h) (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step1228 p h) (sat_cons (step1229 p h) (sat_cons (step624 p h) (sat_cons (step600 p h) (sat_cons (step1468 p h) (sat_cons (step1680 p h) (sat_cons (step1201 p h) (sat_cons (step560 p h) (sat_nil p)))))))))))))))))))
def c1826 : List Lit := [(112, false), (105, false), (111, false), (1734, true)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c597, c598, c1233] c1826 (by decide) p (sat_cons (step597 p h) (sat_cons (step598 p h) (sat_cons (step1233 p h) (sat_nil p))))
def c1827 : List Lit := [(105, false), (111, false), (1736, true)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1235, c1826, c1228, c1237, c1231, c1232, c599] c1827 (by decide) p (sat_cons (step1235 p h) (sat_cons (step1826 p h) (sat_cons (step1228 p h) (sat_cons (step1237 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step599 p h) (sat_nil p))))))))
def c1828 : List Lit := [(112, true), (113, false), (67, true), (107, false), (111, false), (1736, true), (1740, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1228, c1230, c1237, c551, c1231, c1666, c1397, c580, c1671, c1244, c563] c1828 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1228 p h) (sat_cons (step1230 p h) (sat_cons (step1237 p h) (sat_cons (step551 p h) (sat_cons (step1231 p h) (sat_cons (step1666 p h) (sat_cons (step1397 p h) (sat_cons (step580 p h) (sat_cons (step1671 p h) (sat_cons (step1244 p h) (sat_cons (step563 p h) (sat_nil p)))))))))))))
def c1829 : List Lit := [(1735, true), (1744, true), (101, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1234, c1236, c1231, c1232, c1228, c1229, c1444, c600, c624, c641, c1680, c1692, c563, c1479, c1243, c1251] c1829 (by decide) p (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step1228 p h) (sat_cons (step1229 p h) (sat_cons (step1444 p h) (sat_cons (step600 p h) (sat_cons (step624 p h) (sat_cons (step641 p h) (sat_cons (step1680 p h) (sat_cons (step1692 p h) (sat_cons (step563 p h) (sat_cons (step1479 p h) (sat_cons (step1243 p h) (sat_cons (step1251 p h) (sat_nil p)))))))))))))))))
def c1830 : List Lit := [(89, false), (98, false), (101, false), (99, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c501, c503, c1654] c1830 (by decide) p (sat_cons (step501 p h) (sat_cons (step503 p h) (sat_cons (step1654 p h) (sat_nil p))))
def c1831 : List Lit := [(121, false), (98, false), (101, false), (99, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c505, c507, c1654] c1831 (by decide) p (sat_cons (step505 p h) (sat_cons (step507 p h) (sat_cons (step1654 p h) (sat_nil p))))
def c1832 : List Lit := [(117, true), (121, true), (1744, true)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1253, c1243, c1244, c1251, c1245, c1246, c654, c1690] c1832 (by decide) p (sat_cons (step1253 p h) (sat_cons (step1243 p h) (sat_cons (step1244 p h) (sat_cons (step1251 p h) (sat_cons (step1245 p h) (sat_cons (step1246 p h) (sat_cons (step654 p h) (sat_cons (step1690 p h) (sat_nil p)))))))))
def c1833 : List Lit := [(1741, true), (121, true)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1246, c1690, c1692, c1399] c1833 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1246 p h) (sat_cons (step1690 p h) (sat_cons (step1692 p h) (sat_cons (step1399 p h) (sat_nil p))))))
def c1834 : List Lit := [(1713, true), (96, false), (94, true), (100, true), (101, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1183, c1185, c1192, c1194, c1187, c1184, c461] c1834 (by decide) p (sat_cons (step1183 p h) (sat_cons (step1185 p h) (sat_cons (step1192 p h) (sat_cons (step1194 p h) (sat_cons (step1187 p h) (sat_cons (step1184 p h) (sat_cons (step461 p h) (sat_nil p))))))))
def c1835 : List Lit := [(83, false), (1677, true), (87, false), (97, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1526, c1116, c345, c361, c1645] c1835 (by decide) p (sat_cons (step1526 p h) (sat_cons (step1116 p h) (sat_cons (step345 p h) (sat_cons (step361 p h) (sat_cons (step1645 p h) (sat_nil p))))))
def c1836 : List Lit := [(1763, false), (1685, false), (1693, false), (1534, false), (1592, false), (1679, false), (1783, true), (60, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c1310, c1304, c1814, c1750] c1836 (by decide) p (sat_cons (step1310 p h) (sat_cons (step1304 p h) (sat_cons (step1814 p h) (sat_cons (step1750 p h) (sat_nil p)))))
def c1837 : List Lit := [(1685, false), (1534, false), (1592, false), (1763, false), (1679, false), (1783, true), (60, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1147, c1836] c1837 (by decide) p (sat_cons (step1147 p h) (sat_cons (step1836 p h) (sat_nil p)))
def c1838 : List Lit := [(1733, true), (112, false), (1677, true)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c1116, c1115, c1231, c1232, c600, c419, c623, c1681] c1838 (by decide) p (sat_cons (step1116 p h) (sat_cons (step1115 p h) (sat_cons (step1231 p h) (sat_cons (step1232 p h) (sat_cons (step600 p h) (sat_cons (step419 p h) (sat_cons (step623 p h) (sat_cons (step1681 p h) (sat_nil p)))))))))
def c1839 : List Lit := [(113, false), (1721, true), (109, false), (1749, true), (1677, true), (1675, true), (60, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c1804, c1262, c1736, c1116, c1115, c1113, c1112, c401, c547, c621, c1679, c1670, c1827, c577, c579, c1201, c1242, c1206, c1251, c1196, c1780, c1245, c418, c518, c1664] c1839 (by decide) p (sat_cons (step1804 p h) (sat_cons (step1262 p h) (sat_cons (step1736 p h) (sat_cons (step1116 p h) (sat_cons (step1115 p h) (sat_cons (step1113 p h) (sat_cons (step1112 p h) (sat_cons (step401 p h) (sat_cons (step547 p h) (sat_cons (step621 p h) (sat_cons (step1679 p h) (sat_cons (step1670 p h) (sat_cons (step1827 p h) (sat_cons (step577 p h) (sat_cons (step579 p h) (sat_cons (step1201 p h) (sat_cons (step1242 p h) (sat_cons (step1206 p h) (sat_cons (step1251 p h) (sat_cons (step1196 p h) (sat_cons (step1780 p h) (sat_cons (step1245 p h) (sat_cons (step418 p h) (sat_cons (step518 p h) (sat_cons (step1664 p h) (sat_nil p))))))))))))))))))))))))))
def c1840 : List Lit := [(113, true), (109, false), (1749, true), (1677, true), (87, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1804, c1262, c1253, c1736, c1235, c1116, c1115, c1443, c1233, c419, c622, c1682, c563, c1243, c1244, c1251, c579, c1245, c1688, c654] c1840 (by decide) p (sat_cons (step1804 p h) (sat_cons (step1262 p h) (sat_cons (step1253 p h) (sat_cons (step1736 p h) (sat_cons (step1235 p h) (sat_cons (step1116 p h) (sat_cons (step1115 p h) (sat_cons (step1443 p h) (sat_cons (step1233 p h) (sat_cons (step419 p h) (sat_cons (step622 p h) (sat_cons (step1682 p h) (sat_cons (step563 p h) (sat_cons (step1243 p h) (sat_cons (step1244 p h) (sat_cons (step1251 p h) (sat_cons (step579 p h) (sat_cons (step1245 p h) (sat_cons (step1688 p h) (sat_cons (step654 p h) (sat_nil p)))))))))))))))))))))
def c1841 : List Lit := [(1749, true), (119, true), (109, false), (1731, false), (84, false)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1736, c1262, c1237, c1253, c1535, c1244] c1841 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1736 p h) (sat_cons (step1262 p h) (sat_cons (step1237 p h) (sat_cons (step1253 p h) (sat_cons (step1535 p h) (sat_cons (step1244 p h) (sat_nil p))))))))
def c1842 : List Lit := [(1667, true), (123, false), (69, false), (1660, true), (60, false)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1082, c1074, c1098, c1099, c276, c1632, c1635, c281, c1071, c1072, c1073, c269, c1086, c1056, c1059] c1842 (by decide) p (sat_cons (step1082 p h) (sat_cons (step1074 p h) (sat_cons (step1098 p h) (sat_cons (step1099 p h) (sat_cons (step276 p h) (sat_cons (step1632 p h) (sat_cons (step1635 p h) (sat_cons (step281 p h) (sat_cons (step1071 p h) (sat_cons (step1072 p h) (sat_cons (step1073 p h) (sat_cons (step269 p h) (sat_cons (step1086 p h) (sat_cons (step1056 p h) (sat_cons (step1059 p h) (sat_nil p))))))))))))))))
def c1843 : List Lit := [(66, true), (81, false), (70, false), (1600, true), (1660, true), (60, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1089, c1060, c1056, c1058, c1059, c1062, c1086, c1053, c1073, c1512, c1071, c1802] c1843 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1089 p h) (sat_cons (step1060 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step1062 p h) (sat_cons (step1086 p h) (sat_cons (step1053 p h) (sat_cons (step1073 p h) (sat_cons (step1512 p h) (sat_cons (step1071 p h) (sat_cons (step1802 p h) (sat_nil p))))))))))))))
def c1844 : List Lit := [(42, true), (1570, true), (164, true), (43, true)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c925, c144, c930, c1583, c920] c1844 (by decide) p (sat_cons (step925 p h) (sat_cons (step144 p h) (sat_cons (step930 p h) (sat_cons (step1583 p h) (sat_cons (step920 p h) (sat_nil p))))))
def c1845 : List Lit := [(1, true), (4, false), (1559, true), (1652, true), (1512, true), (10, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c845, c828, c1518, c1420, c1069, c7] c1845 (by decide) p (sat_cons (step845 p h) (sat_cons (step828 p h) (sat_cons (step1518 p h) (sat_cons (step1420 p h) (sat_cons (step1069 p h) (sat_cons (step7 p h) (sat_nil p)))))))
def c1846 : List Lit := [(4, false), (34, false), (1559, true), (1652, true), (1512, true), (10, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c1845, c1401, c829, c835, c842, c826, c1420, c1543, c7, c3, c1069] c1846 (by decide) p (sat_cons (step1845 p h) (sat_cons (step1401 p h) (sat_cons (step829 p h) (sat_cons (step835 p h) (sat_cons (step842 p h) (sat_cons (step826 p h) (sat_cons (step1420 p h) (sat_cons (step1543 p h) (sat_cons (step7 p h) (sat_cons (step3 p h) (sat_cons (step1069 p h) (sat_nil p))))))))))))
def c1847 : List Lit := [(1498, false), (1512, true)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c845, c826, c828, c842, c1401, c835, c829] c1847 (by decide) p (sat_cons (step845 p h) (sat_cons (step826 p h) (sat_cons (step828 p h) (sat_cons (step842 p h) (sat_cons (step1401 p h) (sat_cons (step835 p h) (sat_cons (step829 p h) (sat_nil p))))))))
end B112E186
