import B112E040Part0003
namespace B112E040
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1781 : List Lit := [(102, true), (107, true), (108, true), (36, true), (106, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c715, c586] c1781 (by decide) p (sat_cons (step715 p h) (sat_cons (step586 p h) (sat_nil p)))
def c1782 : List Lit := [(108, true), (106, false), (107, true), (97, true), (36, true)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c715, c587] c1782 (by decide) p (sat_cons (step715 p h) (sat_cons (step587 p h) (sat_nil p)))
def c1783 : List Lit := [(102, true), (108, true), (106, false), (36, true), (97, true)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c715, c588] c1783 (by decide) p (sat_cons (step715 p h) (sat_cons (step588 p h) (sat_nil p)))
def c1784 : List Lit := [(102, true), (107, true), (36, true), (106, false), (97, true)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c715, c589] c1784 (by decide) p (sat_cons (step715 p h) (sat_cons (step589 p h) (sat_nil p)))
def c1785 : List Lit := [(103, true), (119, true), (100, true), (109, false), (108, true), (107, true)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c716, c628] c1785 (by decide) p (sat_cons (step716 p h) (sat_cons (step628 p h) (sat_nil p)))
def c1786 : List Lit := [(89, true), (108, true), (107, true), (109, false), (103, true), (119, true)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c716, c629] c1786 (by decide) p (sat_cons (step716 p h) (sat_cons (step629 p h) (sat_nil p)))
def c1787 : List Lit := [(89, true), (108, true), (119, true), (109, false), (100, true), (107, true)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c716, c630] c1787 (by decide) p (sat_cons (step716 p h) (sat_cons (step630 p h) (sat_nil p)))
def c1788 : List Lit := [(91, true), (104, true), (110, false), (107, true)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c717, c634] c1788 (by decide) p (sat_cons (step717 p h) (sat_cons (step634 p h) (sat_nil p)))
def c1789 : List Lit := [(104, true), (107, true), (40, true), (110, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c717, c635] c1789 (by decide) p (sat_cons (step717 p h) (sat_cons (step635 p h) (sat_nil p)))
def c1790 : List Lit := [(91, true), (107, true), (40, true), (110, false)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c717, c636] c1790 (by decide) p (sat_cons (step717 p h) (sat_cons (step636 p h) (sat_nil p)))
def c1791 : List Lit := [(101, true), (108, true), (111, false)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c718, c638] c1791 (by decide) p (sat_cons (step718 p h) (sat_cons (step638 p h) (sat_nil p)))
def c1792 : List Lit := [(108, true), (111, false), (41, true)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c718, c639] c1792 (by decide) p (sat_cons (step718 p h) (sat_cons (step639 p h) (sat_nil p)))
def c1793 : List Lit := [(101, true), (111, false), (41, true)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c718, c640] c1793 (by decide) p (sat_cons (step718 p h) (sat_cons (step640 p h) (sat_nil p)))
def c1794 : List Lit := [(113, false), (114, true)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c719, c649] c1794 (by decide) p (sat_cons (step719 p h) (sat_cons (step649 p h) (sat_nil p)))
def c1795 : List Lit := [(113, false), (112, true)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c719, c650] c1795 (by decide) p (sat_cons (step719 p h) (sat_cons (step650 p h) (sat_nil p)))
def c1796 : List Lit := [(115, false), (112, true)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c720, c654] c1796 (by decide) p (sat_cons (step720 p h) (sat_cons (step654 p h) (sat_nil p)))
def c1797 : List Lit := [(115, false), (55, true)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c720, c655] c1797 (by decide) p (sat_cons (step720 p h) (sat_cons (step655 p h) (sat_nil p)))
def c1798 : List Lit := [(114, true), (89, true), (116, false), (119, true)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c721, c660] c1798 (by decide) p (sat_cons (step721 p h) (sat_cons (step660 p h) (sat_nil p)))
def c1799 : List Lit := [(74, true), (119, true), (120, false)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c722, c665] c1799 (by decide) p (sat_cons (step722 p h) (sat_cons (step665 p h) (sat_nil p)))
def c1800 : List Lit := [(257, false), (259, false)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c1545, c734] c1800 (by decide) p (sat_cons (step1545 p h) (sat_cons (step734 p h) (sat_nil p)))
def c1801 : List Lit := [(255, false), (261, false)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c1543, c738] c1801 (by decide) p (sat_cons (step1543 p h) (sat_cons (step738 p h) (sat_nil p)))
def c1802 : List Lit := [(277, false), (291, false)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c1538, c757] c1802 (by decide) p (sat_cons (step1538 p h) (sat_cons (step757 p h) (sat_nil p)))
def c1803 : List Lit := [(265, false), (293, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c1532, c761] c1803 (by decide) p (sat_cons (step1532 p h) (sat_cons (step761 p h) (sat_nil p)))
def c1804 : List Lit := [(341, false), (347, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c1542, c785] c1804 (by decide) p (sat_cons (step1542 p h) (sat_cons (step785 p h) (sat_nil p)))
def c1805 : List Lit := [(323, false), (351, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c1531, c793] c1805 (by decide) p (sat_cons (step1531 p h) (sat_cons (step793 p h) (sat_nil p)))
def c1806 : List Lit := [(295, false), (353, false)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c1528, c797] c1806 (by decide) p (sat_cons (step1528 p h) (sat_cons (step797 p h) (sat_nil p)))
def c1807 : List Lit := [(367, false), (381, false)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c1536, c815] c1807 (by decide) p (sat_cons (step1536 p h) (sat_cons (step815 p h) (sat_nil p)))
def c1808 : List Lit := [(395, false), (409, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c1535, c828] c1808 (by decide) p (sat_cons (step1535 p h) (sat_cons (step828 p h) (sat_nil p)))
def c1809 : List Lit := [(383, false), (411, false)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c1530, c832] c1809 (by decide) p (sat_cons (step1530 p h) (sat_cons (step832 p h) (sat_nil p)))
def c1810 : List Lit := [(431, false), (437, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c1541, c849] c1810 (by decide) p (sat_cons (step1541 p h) (sat_cons (step849 p h) (sat_nil p)))
def c1811 : List Lit := [(455, false), (457, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c1544, c860] c1811 (by decide) p (sat_cons (step1544 p h) (sat_cons (step860 p h) (sat_nil p)))
def c1812 : List Lit := [(459, false), (465, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c1540, c865] c1812 (by decide) p (sat_cons (step1540 p h) (sat_cons (step865 p h) (sat_nil p)))
def c1813 : List Lit := [(441, false), (469, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c1529, c873] c1813 (by decide) p (sat_cons (step1529 p h) (sat_cons (step873 p h) (sat_nil p)))
def c1814 : List Lit := [(413, false), (471, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c1527, c878] c1814 (by decide) p (sat_cons (step1527 p h) (sat_cons (step878 p h) (sat_nil p)))
def c1815 : List Lit := [(355, false), (473, false)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c883, c881] c1815 (by decide) p (sat_cons (step883 p h) (sat_cons (step881 p h) (sat_nil p)))
def c1816 : List Lit := [(933, false), (1065, false)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c929, c928] c1816 (by decide) p (sat_cons (step929 p h) (sat_cons (step928 p h) (sat_nil p)))
def c1817 : List Lit := [(1477, false), (1486, true)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1021] c1817 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1021 p h) (sat_nil p)))
def c1818 : List Lit := [(1478, false), (1487, true)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1022] c1818 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1022 p h) (sat_nil p)))
def c1819 : List Lit := [(1479, false), (1488, true)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1023] c1819 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1023 p h) (sat_nil p)))
def c1820 : List Lit := [(1480, false), (1489, true)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1024] c1820 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1024 p h) (sat_nil p)))
def c1821 : List Lit := [(1481, false), (1490, true)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1025] c1821 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1025 p h) (sat_nil p)))
def c1822 : List Lit := [(1482, false), (1491, true)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1026] c1822 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1026 p h) (sat_nil p)))
def c1823 : List Lit := [(1483, false), (1492, true)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1027] c1823 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1027 p h) (sat_nil p)))
def c1824 : List Lit := [(1525, false), (1538, true)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1131] c1824 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1131 p h) (sat_nil p)))
def c1825 : List Lit := [(1526, false), (1539, true)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1134] c1825 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c1826 : List Lit := [(1538, false), (1547, true)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1140] c1826 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1140 p h) (sat_nil p)))
def c1827 : List Lit := [(1539, false), (1548, true)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1141] c1827 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1141 p h) (sat_nil p)))
def c1828 : List Lit := [(1540, false), (1549, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1142] c1828 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1142 p h) (sat_nil p)))
def c1829 : List Lit := [(1542, false), (1551, true)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1560, c1143] c1829 (by decide) p (sat_cons (step1560 p h) (sat_cons (step1143 p h) (sat_nil p)))
def c1830 : List Lit := [(1547, true), (1514, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1578, c1144] c1830 (by decide) p (sat_cons (step1578 p h) (sat_cons (step1144 p h) (sat_nil p)))
def c1831 : List Lit := [(1515, false), (1547, true)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1559, c1150] c1831 (by decide) p (sat_cons (step1559 p h) (sat_cons (step1150 p h) (sat_nil p)))
def c1832 : List Lit := [(1548, true), (1515, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1578, c1151] c1832 (by decide) p (sat_cons (step1578 p h) (sat_cons (step1151 p h) (sat_nil p)))
def c1833 : List Lit := [(1516, false), (1548, true)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1559, c1156] c1833 (by decide) p (sat_cons (step1559 p h) (sat_cons (step1156 p h) (sat_nil p)))
def c1834 : List Lit := [(1549, true), (1516, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1578, c1157] c1834 (by decide) p (sat_cons (step1578 p h) (sat_cons (step1157 p h) (sat_nil p)))
def c1835 : List Lit := [(1517, false), (1550, true)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1578, c1163] c1835 (by decide) p (sat_cons (step1578 p h) (sat_cons (step1163 p h) (sat_nil p)))
def c1836 : List Lit := [(1518, false), (1551, true)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c1578, c1168] c1836 (by decide) p (sat_cons (step1578 p h) (sat_cons (step1168 p h) (sat_nil p)))
def c1837 : List Lit := [(1519, false), (1552, true)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1578, c1172] c1837 (by decide) p (sat_cons (step1578 p h) (sat_cons (step1172 p h) (sat_nil p)))
def c1838 : List Lit := [(1567, true), (1490, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1197] c1838 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1197 p h) (sat_nil p)))
def c1839 : List Lit := [(1554, false), (1490, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c1619, c1205] c1839 (by decide) p (sat_cons (step1619 p h) (sat_cons (step1205 p h) (sat_nil p)))
def c1840 : List Lit := [(1568, true), (1491, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1206] c1840 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1206 p h) (sat_nil p)))
def c1841 : List Lit := [(1553, false), (1491, false)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c1619, c1213] c1841 (by decide) p (sat_cons (step1619 p h) (sat_cons (step1213 p h) (sat_nil p)))
def c1842 : List Lit := [(1569, true), (1492, false)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1214] c1842 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1214 p h) (sat_nil p)))
def c1843 : List Lit := [(1552, false), (1492, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c1619, c1220] c1843 (by decide) p (sat_cons (step1619 p h) (sat_cons (step1220 p h) (sat_nil p)))
def c1844 : List Lit := [(1570, true), (1493, false)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1221] c1844 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1221 p h) (sat_nil p)))
end B112E040
