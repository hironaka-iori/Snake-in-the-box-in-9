import B112E034Inputs
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1779 : List Lit := [(1, true)]
theorem step1779 (p : Nat → Bool) (h : Constraints p) : clause p c1779 = true :=
  Snake9.LocalRup.prove_clause [c29, c28] c1779 (by decide) p (sat_cons (step29 p h) (sat_cons (step28 p h) (sat_nil p)))
def c1780 : List Lit := [(15, false), (14, false), (20, false)]
theorem step1780 (p : Nat → Bool) (h : Constraints p) : clause p c1780 = true :=
  Snake9.LocalRup.prove_clause [c1779, c37] c1780 (by decide) p (sat_cons (step1779 p h) (sat_cons (step37 p h) (sat_nil p)))
def c1781 : List Lit := [(15, false), (14, false), (87, false)]
theorem step1781 (p : Nat → Bool) (h : Constraints p) : clause p c1781 = true :=
  Snake9.LocalRup.prove_clause [c1779, c38] c1781 (by decide) p (sat_cons (step1779 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1782 : List Lit := [(15, false), (20, false), (87, false)]
theorem step1782 (p : Nat → Bool) (h : Constraints p) : clause p c1782 = true :=
  Snake9.LocalRup.prove_clause [c1779, c39] c1782 (by decide) p (sat_cons (step1779 p h) (sat_cons (step39 p h) (sat_nil p)))
def c1783 : List Lit := [(51, false), (54, false), (87, false)]
theorem step1783 (p : Nat → Bool) (h : Constraints p) : clause p c1783 = true :=
  Snake9.LocalRup.prove_clause [c1779, c212] c1783 (by decide) p (sat_cons (step1779 p h) (sat_cons (step212 p h) (sat_nil p)))
def c1784 : List Lit := [(7, false)]
theorem step1784 (p : Nat → Bool) (h : Constraints p) : clause p c1784 = true :=
  Snake9.LocalRup.prove_clause [c845, c17] c1784 (by decide) p (sat_cons (step845 p h) (sat_cons (step17 p h) (sat_nil p)))
def c1785 : List Lit := [(8, false)]
theorem step1785 (p : Nat → Bool) (h : Constraints p) : clause p c1785 = true :=
  Snake9.LocalRup.prove_clause [c846, c18] c1785 (by decide) p (sat_cons (step846 p h) (sat_cons (step18 p h) (sat_nil p)))
def c1786 : List Lit := [(506, false)]
theorem step1786 (p : Nat → Bool) (h : Constraints p) : clause p c1786 = true :=
  Snake9.LocalRup.prove_clause [c1090, c1087] c1786 (by decide) p (sat_cons (step1090 p h) (sat_cons (step1087 p h) (sat_nil p)))
def c1787 : List Lit := [(380, false)]
theorem step1787 (p : Nat → Bool) (h : Constraints p) : clause p c1787 = true :=
  Snake9.LocalRup.prove_clause [c1090, c1089] c1787 (by decide) p (sat_cons (step1090 p h) (sat_cons (step1089 p h) (sat_nil p)))
def c1788 : List Lit := [(504, false)]
theorem step1788 (p : Nat → Bool) (h : Constraints p) : clause p c1788 = true :=
  Snake9.LocalRup.prove_clause [c1786, c1083] c1788 (by decide) p (sat_cons (step1786 p h) (sat_cons (step1083 p h) (sat_nil p)))
def c1789 : List Lit := [(442, false)]
theorem step1789 (p : Nat → Bool) (h : Constraints p) : clause p c1789 = true :=
  Snake9.LocalRup.prove_clause [c1786, c1086] c1789 (by decide) p (sat_cons (step1786 p h) (sat_cons (step1086 p h) (sat_nil p)))
def c1790 : List Lit := [(378, false)]
theorem step1790 (p : Nat → Bool) (h : Constraints p) : clause p c1790 = true :=
  Snake9.LocalRup.prove_clause [c1787, c986] c1790 (by decide) p (sat_cons (step1787 p h) (sat_cons (step986 p h) (sat_nil p)))
def c1791 : List Lit := [(316, false)]
theorem step1791 (p : Nat → Bool) (h : Constraints p) : clause p c1791 = true :=
  Snake9.LocalRup.prove_clause [c1787, c989] c1791 (by decide) p (sat_cons (step1787 p h) (sat_cons (step989 p h) (sat_nil p)))
def c1792 : List Lit := [(502, false)]
theorem step1792 (p : Nat → Bool) (h : Constraints p) : clause p c1792 = true :=
  Snake9.LocalRup.prove_clause [c1788, c1078] c1792 (by decide) p (sat_cons (step1788 p h) (sat_cons (step1078 p h) (sat_nil p)))
def c1793 : List Lit := [(472, false)]
theorem step1793 (p : Nat → Bool) (h : Constraints p) : clause p c1793 = true :=
  Snake9.LocalRup.prove_clause [c1788, c1081] c1793 (by decide) p (sat_cons (step1788 p h) (sat_cons (step1081 p h) (sat_nil p)))
def c1794 : List Lit := [(440, false)]
theorem step1794 (p : Nat → Bool) (h : Constraints p) : clause p c1794 = true :=
  Snake9.LocalRup.prove_clause [c1789, c1028] c1794 (by decide) p (sat_cons (step1789 p h) (sat_cons (step1028 p h) (sat_nil p)))
def c1795 : List Lit := [(410, false)]
theorem step1795 (p : Nat → Bool) (h : Constraints p) : clause p c1795 = true :=
  Snake9.LocalRup.prove_clause [c1789, c1031] c1795 (by decide) p (sat_cons (step1789 p h) (sat_cons (step1031 p h) (sat_nil p)))
def c1796 : List Lit := [(346, false)]
theorem step1796 (p : Nat → Bool) (h : Constraints p) : clause p c1796 = true :=
  Snake9.LocalRup.prove_clause [c1790, c984] c1796 (by decide) p (sat_cons (step1790 p h) (sat_cons (step984 p h) (sat_nil p)))
def c1797 : List Lit := [(314, false)]
theorem step1797 (p : Nat → Bool) (h : Constraints p) : clause p c1797 = true :=
  Snake9.LocalRup.prove_clause [c1791, c944] c1797 (by decide) p (sat_cons (step1791 p h) (sat_cons (step944 p h) (sat_nil p)))
def c1798 : List Lit := [(284, false)]
theorem step1798 (p : Nat → Bool) (h : Constraints p) : clause p c1798 = true :=
  Snake9.LocalRup.prove_clause [c1791, c947] c1798 (by decide) p (sat_cons (step1791 p h) (sat_cons (step947 p h) (sat_nil p)))
def c1799 : List Lit := [(500, false)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c1792, c1074] c1799 (by decide) p (sat_cons (step1792 p h) (sat_cons (step1074 p h) (sat_nil p)))
def c1800 : List Lit := [(486, false)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c1792, c1076] c1800 (by decide) p (sat_cons (step1792 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c1801 : List Lit := [(470, false)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c1793, c1051] c1801 (by decide) p (sat_cons (step1793 p h) (sat_cons (step1051 p h) (sat_nil p)))
def c1802 : List Lit := [(456, false)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c1793, c1054] c1802 (by decide) p (sat_cons (step1793 p h) (sat_cons (step1054 p h) (sat_nil p)))
def c1803 : List Lit := [(394, false)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c1795, c1009] c1803 (by decide) p (sat_cons (step1795 p h) (sat_cons (step1009 p h) (sat_nil p)))
def c1804 : List Lit := [(344, false)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c1796, c965] c1804 (by decide) p (sat_cons (step1796 p h) (sat_cons (step965 p h) (sat_nil p)))
def c1805 : List Lit := [(312, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c1797, c939] c1805 (by decide) p (sat_cons (step1797 p h) (sat_cons (step939 p h) (sat_nil p)))
def c1806 : List Lit := [(298, false)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c1797, c942] c1806 (by decide) p (sat_cons (step1797 p h) (sat_cons (step942 p h) (sat_nil p)))
def c1807 : List Lit := [(282, false)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c1798, c913] c1807 (by decide) p (sat_cons (step1798 p h) (sat_cons (step913 p h) (sat_nil p)))
def c1808 : List Lit := [(498, false)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c1799, c1071] c1808 (by decide) p (sat_cons (step1799 p h) (sat_cons (step1071 p h) (sat_nil p)))
def c1809 : List Lit := [(478, false)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c1800, c1061] c1809 (by decide) p (sat_cons (step1800 p h) (sat_cons (step1061 p h) (sat_nil p)))
def c1810 : List Lit := [(336, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c1804, c963] c1810 (by decide) p (sat_cons (step1804 p h) (sat_cons (step963 p h) (sat_nil p)))
def c1811 : List Lit := [(310, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c1805, c935] c1811 (by decide) p (sat_cons (step1805 p h) (sat_cons (step935 p h) (sat_nil p)))
def c1812 : List Lit := [(496, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c1808, c1069] c1812 (by decide) p (sat_cons (step1808 p h) (sat_cons (step1069 p h) (sat_nil p)))
def c1813 : List Lit := [(308, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c1811, c931] c1813 (by decide) p (sat_cons (step1811 p h) (sat_cons (step931 p h) (sat_nil p)))
def c1814 : List Lit := [(1542, true)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c1784, c1094] c1814 (by decide) p (sat_cons (step1784 p h) (sat_cons (step1094 p h) (sat_nil p)))
def c1815 : List Lit := [(6, true), (1543, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c1784, c1095] c1815 (by decide) p (sat_cons (step1784 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c1816 : List Lit := [(1544, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1096] c1816 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1096 p h) (sat_nil p)))
def c1817 : List Lit := [(1540, false), (1545, true)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1097] c1817 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1097 p h) (sat_nil p)))
def c1818 : List Lit := [(1541, false), (1546, true)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1099] c1818 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1099 p h) (sat_nil p)))
def c1819 : List Lit := [(1548, true)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1785, c1101] c1819 (by decide) p (sat_cons (step1785 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c1820 : List Lit := [(9, true), (1549, true)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1785, c1102] c1820 (by decide) p (sat_cons (step1785 p h) (sat_cons (step1102 p h) (sat_nil p)))
def c1821 : List Lit := [(1552, true)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c1819, c1104] c1821 (by decide) p (sat_cons (step1819 p h) (sat_cons (step1104 p h) (sat_nil p)))
def c1822 : List Lit := [(1550, false), (1553, true)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c1819, c1105] c1822 (by decide) p (sat_cons (step1819 p h) (sat_cons (step1105 p h) (sat_nil p)))
def c1823 : List Lit := [(1554, false), (1559, true)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1108] c1823 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1108 p h) (sat_nil p)))
def c1824 : List Lit := [(1545, false), (1558, true)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1821, c1109] c1824 (by decide) p (sat_cons (step1821 p h) (sat_cons (step1109 p h) (sat_nil p)))
def c1825 : List Lit := [(1546, false), (1559, true)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1821, c1112] c1825 (by decide) p (sat_cons (step1821 p h) (sat_cons (step1112 p h) (sat_nil p)))
def c1826 : List Lit := [(1547, false), (1560, true)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1821, c1115] c1826 (by decide) p (sat_cons (step1821 p h) (sat_cons (step1115 p h) (sat_nil p)))
def c1827 : List Lit := [(1705, true)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c874, c1377, c1379, c1374, c1371, c1372, c267, c269] c1827 (by decide) p (sat_cons (step874 p h) (sat_cons (step1377 p h) (sat_cons (step1379 p h) (sat_cons (step1374 p h) (sat_cons (step1371 p h) (sat_cons (step1372 p h) (sat_cons (step267 p h) (sat_cons (step269 p h) (sat_nil p)))))))))
def c1828 : List Lit := [(1717, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1401] c1828 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1401 p h) (sat_nil p)))
def c1829 : List Lit := [(53, true), (1713, true), (1644, true)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c879, c1391, c1388, c1389, c1393, c1386, c334, c1270, c1252, c1254, c1267, c293, c1258, c1260, c327, c1255, c1256, c246] c1829 (by decide) p (sat_cons (step879 p h) (sat_cons (step1391 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1393 p h) (sat_cons (step1386 p h) (sat_cons (step334 p h) (sat_cons (step1270 p h) (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step1267 p h) (sat_cons (step293 p h) (sat_cons (step1258 p h) (sat_cons (step1260 p h) (sat_cons (step327 p h) (sat_cons (step1255 p h) (sat_cons (step1256 p h) (sat_cons (step246 p h) (sat_nil p)))))))))))))))))))
def c1830 : List Lit := [(1640, true), (53, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c872, c1258, c1260, c1255, c1256, c246, c259, c261] c1830 (by decide) p (sat_cons (step872 p h) (sat_cons (step1258 p h) (sat_cons (step1260 p h) (sat_cons (step1255 p h) (sat_cons (step1256 p h) (sat_cons (step246 p h) (sat_cons (step259 p h) (sat_cons (step261 p h) (sat_nil p)))))))))
def c1831 : List Lit := [(51, false), (1541, true)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1779, c29, c3, c5, c1093] c1831 (by decide) p (sat_cons (step1779 p h) (sat_cons (step29 p h) (sat_cons (step3 p h) (sat_cons (step5 p h) (sat_cons (step1093 p h) (sat_nil p))))))
def c1832 : List Lit := [(1643, true)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1263, c1266, c1830, c1252] c1832 (by decide) p (sat_cons (step1263 p h) (sat_cons (step1266 p h) (sat_cons (step1830 p h) (sat_cons (step1252 p h) (sat_nil p)))))
def c1833 : List Lit := [(1648, true)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1832, c1274] c1833 (by decide) p (sat_cons (step1832 p h) (sat_cons (step1274 p h) (sat_nil p)))
def c1834 : List Lit := [(1616, true), (39, false), (35, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1211, c1213, c1209, c1206, c157] c1834 (by decide) p (sat_cons (step1211 p h) (sat_cons (step1213 p h) (sat_cons (step1209 p h) (sat_cons (step1206 p h) (sat_cons (step157 p h) (sat_nil p))))))
def c1835 : List Lit := [(1633, true), (42, false), (1604, true), (51, true), (1630, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c866, c1192, c1191, c1245, c1247, c1243, c1238, c1239, c96, c197, c167, c196] c1835 (by decide) p (sat_cons (step866 p h) (sat_cons (step1192 p h) (sat_cons (step1191 p h) (sat_cons (step1245 p h) (sat_cons (step1247 p h) (sat_cons (step1243 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step96 p h) (sat_cons (step197 p h) (sat_cons (step167 p h) (sat_cons (step196 p h) (sat_nil p)))))))))))))
def c1836 : List Lit := [(1583, true), (1565, false), (21, true)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c854, c1129, c1133, c1140, c1158, c1154, c1130, c1143, c1141, c1122, c1134, c1135, c78, c45] c1836 (by decide) p (sat_cons (step854 p h) (sat_cons (step1129 p h) (sat_cons (step1133 p h) (sat_cons (step1140 p h) (sat_cons (step1158 p h) (sat_cons (step1154 p h) (sat_cons (step1130 p h) (sat_cons (step1143 p h) (sat_cons (step1141 p h) (sat_cons (step1122 p h) (sat_cons (step1134 p h) (sat_cons (step1135 p h) (sat_cons (step78 p h) (sat_cons (step45 p h) (sat_nil p)))))))))))))))
def c1837 : List Lit := [(1553, true), (27, true), (1704, true), (56, false), (6, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c848, c847, c1822, c1106, c1103, c1820, c24, c20, c26, c272, c1376] c1837 (by decide) p (sat_cons (step848 p h) (sat_cons (step847 p h) (sat_cons (step1822 p h) (sat_cons (step1106 p h) (sat_cons (step1103 p h) (sat_cons (step1820 p h) (sat_cons (step24 p h) (sat_cons (step20 p h) (sat_cons (step26 p h) (sat_cons (step272 p h) (sat_cons (step1376 p h) (sat_nil p))))))))))))
def c1838 : List Lit := [(283, true), (68, true), (11, true), (6, false), (3, true)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c844, c912, c914, c909, c903, c908, c902, c907, c901, c27, c12, c14] c1838 (by decide) p (sat_cons (step844 p h) (sat_cons (step912 p h) (sat_cons (step914 p h) (sat_cons (step909 p h) (sat_cons (step903 p h) (sat_cons (step908 p h) (sat_cons (step902 p h) (sat_cons (step907 p h) (sat_cons (step901 p h) (sat_cons (step27 p h) (sat_cons (step12 p h) (sat_cons (step14 p h) (sat_nil p)))))))))))))
def c1839 : List Lit := [(64, true), (65, false), (68, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c875, c278, c279, c1742] c1839 (by decide) p (sat_cons (step875 p h) (sat_cons (step278 p h) (sat_cons (step279 p h) (sat_cons (step1742 p h) (sat_nil p)))))
def c1840 : List Lit := [(1790, true), (103, true), (101, false), (29, false), (1782, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1528, c1535, c1539, c1531, c1510, c1520, c1508, c500] c1840 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1528 p h) (sat_cons (step1535 p h) (sat_cons (step1539 p h) (sat_cons (step1531 p h) (sat_cons (step1510 p h) (sat_cons (step1520 p h) (sat_cons (step1508 p h) (sat_cons (step500 p h) (sat_nil p))))))))))
def c1841 : List Lit := [(1820, true), (1806, false), (1803, false), (45, true), (113, true), (117, true)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c898, c1575, c1584, c1558, c1554, c1563, c1603, c1608, c1585, c1566, c1564, c1578, c1556, c1559, c799, c625] c1841 (by decide) p (sat_cons (step898 p h) (sat_cons (step1575 p h) (sat_cons (step1584 p h) (sat_cons (step1558 p h) (sat_cons (step1554 p h) (sat_cons (step1563 p h) (sat_cons (step1603 p h) (sat_cons (step1608 p h) (sat_cons (step1585 p h) (sat_cons (step1566 p h) (sat_cons (step1564 p h) (sat_cons (step1578 p h) (sat_cons (step1556 p h) (sat_cons (step1559 p h) (sat_cons (step799 p h) (sat_cons (step625 p h) (sat_nil p)))))))))))))))))
def c1842 : List Lit := [(1746, true), (81, false), (1725, false)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c883, c1425, c1463, c1458, c1426, c1444, c1420, c1431, c368, c365] c1842 (by decide) p (sat_cons (step883 p h) (sat_cons (step1425 p h) (sat_cons (step1463 p h) (sat_cons (step1458 p h) (sat_cons (step1426 p h) (sat_cons (step1444 p h) (sat_cons (step1420 p h) (sat_cons (step1431 p h) (sat_cons (step368 p h) (sat_cons (step365 p h) (sat_nil p)))))))))))
end B112E034
