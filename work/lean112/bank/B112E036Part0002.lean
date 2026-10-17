import B112E036Part0001
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1773 : List Lit := [(54, true), (1638, true), (1694, true), (1560, false), (1629, false), (1635, false)]
theorem step1773 (p : Nat → Bool) (h : Constraints p) : clause p c1773 = true :=
  Snake9.LocalRup.prove_clause [c406, c1645, c1684, c1155, c1157, c1161, c69, c71, c72, c1196, c997, c1043, c1047, c1222, c1004, c1051, c1261, c1030, c1087, c1677, c1067, c1054, c1673, c1045, c1717] c1773 (by decide) p (sat_cons (step406 p h) (sat_cons (step1645 p h) (sat_cons (step1684 p h) (sat_cons (step1155 p h) (sat_cons (step1157 p h) (sat_cons (step1161 p h) (sat_cons (step69 p h) (sat_cons (step71 p h) (sat_cons (step72 p h) (sat_cons (step1196 p h) (sat_cons (step997 p h) (sat_cons (step1043 p h) (sat_cons (step1047 p h) (sat_cons (step1222 p h) (sat_cons (step1004 p h) (sat_cons (step1051 p h) (sat_cons (step1261 p h) (sat_cons (step1030 p h) (sat_cons (step1087 p h) (sat_cons (step1677 p h) (sat_cons (step1067 p h) (sat_cons (step1054 p h) (sat_cons (step1673 p h) (sat_cons (step1045 p h) (sat_cons (step1717 p h) (sat_nil p))))))))))))))))))))))))))
def c1774 : List Lit := [(100, true), (108, true), (227, true), (101, true), (98, true), (93, true), (1778, true), (95, true), (117, false), (109, false)]
theorem step1774 (p : Nat → Bool) (h : Constraints p) : clause p c1774 = true :=
  Snake9.LocalRup.prove_clause [c812, c1391, c575, c1399, c1388, c562, c539] c1774 (by decide) p (sat_cons (step812 p h) (sat_cons (step1391 p h) (sat_cons (step575 p h) (sat_cons (step1399 p h) (sat_cons (step1388 p h) (sat_cons (step562 p h) (sat_cons (step539 p h) (sat_nil p))))))))
def c1775 : List Lit := [(108, true), (227, true), (101, true), (98, true), (93, true), (102, true), (105, false), (1778, true), (95, true), (117, false), (109, false)]
theorem step1775 (p : Nat → Bool) (h : Constraints p) : clause p c1775 = true :=
  Snake9.LocalRup.prove_clause [c817, c1774, c563, c678, c672] c1775 (by decide) p (sat_cons (step817 p h) (sat_cons (step1774 p h) (sat_cons (step563 p h) (sat_cons (step678 p h) (sat_cons (step672 p h) (sat_nil p))))))
def c1776 : List Lit := [(101, true), (98, true), (93, true), (120, false), (102, true), (105, false), (1778, true), (112, true), (95, true), (117, false), (1781, true)]
theorem step1776 (p : Nat → Bool) (h : Constraints p) : clause p c1776 = true :=
  Snake9.LocalRup.prove_clause [c1650, c817, c1404, c1403, c737, c961, c964, c966, c979, c985, c957, c942, c937, c936, c1775, c1641, c661, c1388, c1399, c1391, c563, c678, c673] c1776 (by decide) p (sat_cons (step1650 p h) (sat_cons (step817 p h) (sat_cons (step1404 p h) (sat_cons (step1403 p h) (sat_cons (step737 p h) (sat_cons (step961 p h) (sat_cons (step964 p h) (sat_cons (step966 p h) (sat_cons (step979 p h) (sat_cons (step985 p h) (sat_cons (step957 p h) (sat_cons (step942 p h) (sat_cons (step937 p h) (sat_cons (step936 p h) (sat_cons (step1775 p h) (sat_cons (step1641 p h) (sat_cons (step661 p h) (sat_cons (step1388 p h) (sat_cons (step1399 p h) (sat_cons (step1391 p h) (sat_cons (step563 p h) (sat_cons (step678 p h) (sat_cons (step673 p h) (sat_nil p))))))))))))))))))))))))
def c1777 : List Lit := [(39, true), (1624, true), (31, true), (101, false)]
theorem step1777 (p : Nat → Bool) (h : Constraints p) : clause p c1777 = true :=
  Snake9.LocalRup.prove_clause [c1129, c1119, c1712, c1120, c1127, c190, c1122] c1777 (by decide) p (sat_cons (step1129 p h) (sat_cons (step1119 p h) (sat_cons (step1712 p h) (sat_cons (step1120 p h) (sat_cons (step1127 p h) (sat_cons (step190 p h) (sat_cons (step1122 p h) (sat_nil p))))))))
def c1778 : List Lit := [(1552, false), (1601, true), (6, false), (37, false), (4, true)]
theorem step1778 (p : Nat → Bool) (h : Constraints p) : clause p c1778 = true :=
  Snake9.LocalRup.prove_clause [c1714, c1086, c1037, c1033, c1034, c1083, c1018, c1716, c1011, c998, c23, c1008, c999] c1778 (by decide) p (sat_cons (step1714 p h) (sat_cons (step1086 p h) (sat_cons (step1037 p h) (sat_cons (step1033 p h) (sat_cons (step1034 p h) (sat_cons (step1083 p h) (sat_cons (step1018 p h) (sat_cons (step1716 p h) (sat_cons (step1011 p h) (sat_cons (step998 p h) (sat_cons (step23 p h) (sat_cons (step1008 p h) (sat_cons (step999 p h) (sat_nil p))))))))))))))
def c1779 : List Lit := [(1549, true), (6, false), (37, false)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c999, c1000, c18] c1779 (by decide) p (sat_cons (step999 p h) (sat_cons (step1000 p h) (sat_cons (step18 p h) (sat_nil p))))
def c1780 : List Lit := [(1566, true), (1548, false), (6, false), (37, false)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c1779, c1008, c1041, c1038, c1009, c1018, c1011, c23, c20, c1001] c1780 (by decide) p (sat_cons (step1779 p h) (sat_cons (step1008 p h) (sat_cons (step1041 p h) (sat_cons (step1038 p h) (sat_cons (step1009 p h) (sat_cons (step1018 p h) (sat_cons (step1011 p h) (sat_cons (step23 p h) (sat_cons (step20 p h) (sat_cons (step1001 p h) (sat_nil p)))))))))))
def c1781 : List Lit := [(1735, true), (101, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c806, c1328, c1330, c1702, c1326, c1323, c1760, c1620, c388] c1781 (by decide) p (sat_cons (step806 p h) (sat_cons (step1328 p h) (sat_cons (step1330 p h) (sat_cons (step1702 p h) (sat_cons (step1326 p h) (sat_cons (step1323 p h) (sat_cons (step1760 p h) (sat_cons (step1620 p h) (sat_cons (step388 p h) (sat_nil p))))))))))
def c1782 : List Lit := [(1791, true), (1779, false), (34, true), (1772, false), (106, true), (38, false), (39, false)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c785, c1404, c1409, c1397, c1426, c1430, c1410, c1398, c1405, c1390, c551, c175, c168] c1782 (by decide) p (sat_cons (step785 p h) (sat_cons (step1404 p h) (sat_cons (step1409 p h) (sat_cons (step1397 p h) (sat_cons (step1426 p h) (sat_cons (step1430 p h) (sat_cons (step1410 p h) (sat_cons (step1398 p h) (sat_cons (step1405 p h) (sat_cons (step1390 p h) (sat_cons (step551 p h) (sat_cons (step175 p h) (sat_cons (step168 p h) (sat_nil p))))))))))))))
def c1783 : List Lit := [(1799, true), (95, true)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c820, c1444, c1446, c1441, c1442, c1439, c710, c702] c1783 (by decide) p (sat_cons (step820 p h) (sat_cons (step1444 p h) (sat_cons (step1446 p h) (sat_cons (step1441 p h) (sat_cons (step1442 p h) (sat_cons (step1439 p h) (sat_cons (step710 p h) (sat_cons (step702 p h) (sat_nil p)))))))))
def c1784 : List Lit := [(1811, true), (118, true), (101, false)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c1453, c1470, c1467, c1454, c1458, c1460, c1725, c1456, c738] c1784 (by decide) p (sat_cons (step1453 p h) (sat_cons (step1470 p h) (sat_cons (step1467 p h) (sat_cons (step1454 p h) (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step1725 p h) (sat_cons (step1456 p h) (sat_cons (step738 p h) (sat_nil p))))))))))
def c1785 : List Lit := [(100, false), (114, false), (117, false), (92, false)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c819, c496, c727, c698] c1785 (by decide) p (sat_cons (step819 p h) (sat_cons (step496 p h) (sat_cons (step727 p h) (sat_cons (step698 p h) (sat_nil p)))))
def c1786 : List Lit := [(34, false), (2, false), (5, false)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c1645, c3] c1786 (by decide) p (sat_cons (step1645 p h) (sat_cons (step3 p h) (sat_nil p)))
def c1787 : List Lit := [(2, false), (5, true), (1, true), (34, true)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c768, c4] c1787 (by decide) p (sat_cons (step768 p h) (sat_cons (step4 p h) (sat_nil p)))
def c1788 : List Lit := [(4, false), (5, true), (3, true), (35, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c769, c11] c1788 (by decide) p (sat_cons (step769 p h) (sat_cons (step11 p h) (sat_nil p)))
def c1789 : List Lit := [(22, true), (14, true), (7, false), (74, true)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c770, c28] c1789 (by decide) p (sat_cons (step770 p h) (sat_cons (step28 p h) (sat_nil p)))
def c1790 : List Lit := [(22, true), (74, true), (7, false), (6, true)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c770, c29] c1790 (by decide) p (sat_cons (step770 p h) (sat_cons (step29 p h) (sat_nil p)))
def c1791 : List Lit := [(74, true), (6, true), (14, true), (7, false)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c770, c30] c1791 (by decide) p (sat_cons (step770 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1792 : List Lit := [(22, true), (6, true), (14, true), (7, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c770, c31] c1792 (by decide) p (sat_cons (step770 p h) (sat_cons (step31 p h) (sat_nil p)))
def c1793 : List Lit := [(1, true), (6, true), (8, false), (15, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c771, c34] c1793 (by decide) p (sat_cons (step771 p h) (sat_cons (step34 p h) (sat_nil p)))
def c1794 : List Lit := [(10, true), (6, true), (9, false)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c772, c35] c1794 (by decide) p (sat_cons (step772 p h) (sat_cons (step35 p h) (sat_nil p)))
def c1795 : List Lit := [(3, true), (10, true), (9, false)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c772, c36] c1795 (by decide) p (sat_cons (step772 p h) (sat_cons (step36 p h) (sat_nil p)))
def c1796 : List Lit := [(3, true), (9, false), (6, true)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c772, c37] c1796 (by decide) p (sat_cons (step772 p h) (sat_cons (step37 p h) (sat_nil p)))
def c1797 : List Lit := [(81, true), (12, true), (11, false)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c773, c40] c1797 (by decide) p (sat_cons (step773 p h) (sat_cons (step40 p h) (sat_nil p)))
def c1798 : List Lit := [(12, true), (3, true), (11, false)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c773, c41] c1798 (by decide) p (sat_cons (step773 p h) (sat_cons (step41 p h) (sat_nil p)))
def c1799 : List Lit := [(12, true), (18, true), (13, false)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c774, c45] c1799 (by decide) p (sat_cons (step774 p h) (sat_cons (step45 p h) (sat_nil p)))
def c1800 : List Lit := [(5, true), (18, true), (13, false)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c774, c46] c1800 (by decide) p (sat_cons (step774 p h) (sat_cons (step46 p h) (sat_nil p)))
def c1801 : List Lit := [(12, true), (5, true), (13, false)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c774, c47] c1801 (by decide) p (sat_cons (step774 p h) (sat_cons (step47 p h) (sat_nil p)))
def c1802 : List Lit := [(15, true), (18, true), (16, false)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c775, c59] c1802 (by decide) p (sat_cons (step775 p h) (sat_cons (step59 p h) (sat_nil p)))
def c1803 : List Lit := [(14, true), (18, true), (16, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c775, c60] c1803 (by decide) p (sat_cons (step775 p h) (sat_cons (step60 p h) (sat_nil p)))
def c1804 : List Lit := [(15, true), (14, true), (16, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c775, c61] c1804 (by decide) p (sat_cons (step775 p h) (sat_cons (step61 p h) (sat_nil p)))
def c1805 : List Lit := [(19, false), (22, true)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c776, c66] c1805 (by decide) p (sat_cons (step776 p h) (sat_cons (step66 p h) (sat_nil p)))
def c1806 : List Lit := [(2, false), (19, false)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c1645, c406, c67] c1806 (by decide) p (sat_cons (step1645 p h) (sat_cons (step406 p h) (sat_cons (step67 p h) (sat_nil p))))
def c1807 : List Lit := [(2, false), (21, false)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c1645, c406, c68] c1807 (by decide) p (sat_cons (step1645 p h) (sat_cons (step406 p h) (sat_cons (step68 p h) (sat_nil p))))
def c1808 : List Lit := [(2, false), (52, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c1645, c406, c69] c1808 (by decide) p (sat_cons (step1645 p h) (sat_cons (step406 p h) (sat_cons (step69 p h) (sat_nil p))))
def c1809 : List Lit := [(19, false), (21, false)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c1645, c406, c70] c1809 (by decide) p (sat_cons (step1645 p h) (sat_cons (step406 p h) (sat_cons (step70 p h) (sat_nil p))))
def c1810 : List Lit := [(19, false), (52, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c1645, c406, c71] c1810 (by decide) p (sat_cons (step1645 p h) (sat_cons (step406 p h) (sat_cons (step71 p h) (sat_nil p))))
def c1811 : List Lit := [(21, false), (52, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c1645, c406, c72] c1811 (by decide) p (sat_cons (step1645 p h) (sat_cons (step406 p h) (sat_cons (step72 p h) (sat_nil p))))
def c1812 : List Lit := [(24, false), (21, false), (5, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c1645, c73] c1812 (by decide) p (sat_cons (step1645 p h) (sat_cons (step73 p h) (sat_nil p)))
def c1813 : List Lit := [(24, true), (5, true), (21, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c777, c74] c1813 (by decide) p (sat_cons (step777 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1814 : List Lit := [(29, true), (22, true), (23, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c778, c82] c1814 (by decide) p (sat_cons (step778 p h) (sat_cons (step82 p h) (sat_nil p)))
def c1815 : List Lit := [(22, true), (23, false), (24, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c778, c83] c1815 (by decide) p (sat_cons (step778 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1816 : List Lit := [(66, true), (27, false), (15, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c781, c89] c1816 (by decide) p (sat_cons (step781 p h) (sat_cons (step89 p h) (sat_nil p)))
def c1817 : List Lit := [(28, false), (30, true)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c782, c90] c1817 (by decide) p (sat_cons (step782 p h) (sat_cons (step90 p h) (sat_nil p)))
def c1818 : List Lit := [(28, false), (29, true)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c782, c91] c1818 (by decide) p (sat_cons (step782 p h) (sat_cons (step91 p h) (sat_nil p)))
def c1819 : List Lit := [(28, true), (30, false), (27, true), (158, true)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1647, c95] c1819 (by decide) p (sat_cons (step1647 p h) (sat_cons (step95 p h) (sat_nil p)))
def c1820 : List Lit := [(30, false), (28, true), (158, true), (17, true)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1647, c96] c1820 (by decide) p (sat_cons (step1647 p h) (sat_cons (step96 p h) (sat_nil p)))
def c1821 : List Lit := [(30, false), (27, true), (158, true), (17, true)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c1647, c97] c1821 (by decide) p (sat_cons (step1647 p h) (sat_cons (step97 p h) (sat_nil p)))
def c1822 : List Lit := [(34, true), (42, true), (32, false), (35, true), (89, true)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c783, c113] c1822 (by decide) p (sat_cons (step783 p h) (sat_cons (step113 p h) (sat_nil p)))
def c1823 : List Lit := [(42, true), (32, false), (31, true), (35, true), (89, true)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c783, c114] c1823 (by decide) p (sat_cons (step783 p h) (sat_cons (step114 p h) (sat_nil p)))
def c1824 : List Lit := [(34, true), (42, true), (31, true), (32, false), (89, true)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c783, c115] c1824 (by decide) p (sat_cons (step783 p h) (sat_cons (step115 p h) (sat_nil p)))
def c1825 : List Lit := [(34, true), (35, true), (32, false), (89, true), (31, true)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c783, c116] c1825 (by decide) p (sat_cons (step783 p h) (sat_cons (step116 p h) (sat_nil p)))
def c1826 : List Lit := [(42, true), (34, true), (32, false), (31, true), (35, true)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c783, c117] c1826 (by decide) p (sat_cons (step783 p h) (sat_cons (step117 p h) (sat_nil p)))
def c1827 : List Lit := [(46, true), (37, false), (31, true), (95, true)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c784, c159] c1827 (by decide) p (sat_cons (step784 p h) (sat_cons (step159 p h) (sat_nil p)))
def c1828 : List Lit := [(46, true), (6, true), (37, false), (95, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c784, c160] c1828 (by decide) p (sat_cons (step784 p h) (sat_cons (step160 p h) (sat_nil p)))
def c1829 : List Lit := [(6, true), (37, false), (95, true), (31, true)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c784, c161] c1829 (by decide) p (sat_cons (step784 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1830 : List Lit := [(46, true), (37, false), (31, true), (6, true)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c784, c162] c1830 (by decide) p (sat_cons (step784 p h) (sat_cons (step162 p h) (sat_nil p)))
def c1831 : List Lit := [(58, true), (40, true), (97, true), (38, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c785, c166] c1831 (by decide) p (sat_cons (step785 p h) (sat_cons (step166 p h) (sat_nil p)))
def c1832 : List Lit := [(58, true), (34, true), (97, true), (38, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c785, c167] c1832 (by decide) p (sat_cons (step785 p h) (sat_cons (step167 p h) (sat_nil p)))
def c1833 : List Lit := [(40, true), (34, true), (97, true), (38, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c785, c168] c1833 (by decide) p (sat_cons (step785 p h) (sat_cons (step168 p h) (sat_nil p)))
def c1834 : List Lit := [(40, true), (58, true), (38, false), (34, true)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c785, c169] c1834 (by decide) p (sat_cons (step785 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1835 : List Lit := [(40, true), (48, true), (39, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c786, c171] c1835 (by decide) p (sat_cons (step786 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1836 : List Lit := [(39, false), (35, true), (48, true)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c786, c172] c1836 (by decide) p (sat_cons (step786 p h) (sat_cons (step172 p h) (sat_nil p)))
end B112E036
