import B112E050Inputs
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1816 : List Lit := [(14, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c2, c1] c1816 (by decide) p (sat_cons (step2 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1817 : List Lit := [(7, false), (6, false), (44, false)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1816, c13] c1817 (by decide) p (sat_cons (step1816 p h) (sat_cons (step13 p h) (sat_nil p)))
def c1818 : List Lit := [(7, false), (6, false), (80, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1816, c14] c1818 (by decide) p (sat_cons (step1816 p h) (sat_cons (step14 p h) (sat_nil p)))
def c1819 : List Lit := [(7, false), (44, false), (80, false)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1816, c15] c1819 (by decide) p (sat_cons (step1816 p h) (sat_cons (step15 p h) (sat_nil p)))
def c1820 : List Lit := [(142, true), (7, true), (12, true), (13, true)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1816, c27] c1820 (by decide) p (sat_cons (step1816 p h) (sat_cons (step27 p h) (sat_nil p)))
def c1821 : List Lit := [(11, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c850, c24] c1821 (by decide) p (sat_cons (step850 p h) (sat_cons (step24 p h) (sat_nil p)))
def c1822 : List Lit := [(12, false)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c851, c25] c1822 (by decide) p (sat_cons (step851 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1823 : List Lit := [(13, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c852, c26] c1823 (by decide) p (sat_cons (step852 p h) (sat_cons (step26 p h) (sat_nil p)))
def c1824 : List Lit := [(506, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1097, c1094] c1824 (by decide) p (sat_cons (step1097 p h) (sat_cons (step1094 p h) (sat_nil p)))
def c1825 : List Lit := [(380, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1097, c1096] c1825 (by decide) p (sat_cons (step1097 p h) (sat_cons (step1096 p h) (sat_nil p)))
def c1826 : List Lit := [(504, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1824, c1090] c1826 (by decide) p (sat_cons (step1824 p h) (sat_cons (step1090 p h) (sat_nil p)))
def c1827 : List Lit := [(442, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1824, c1093] c1827 (by decide) p (sat_cons (step1824 p h) (sat_cons (step1093 p h) (sat_nil p)))
def c1828 : List Lit := [(378, false)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1825, c1006] c1828 (by decide) p (sat_cons (step1825 p h) (sat_cons (step1006 p h) (sat_nil p)))
def c1829 : List Lit := [(316, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1825, c1009] c1829 (by decide) p (sat_cons (step1825 p h) (sat_cons (step1009 p h) (sat_nil p)))
def c1830 : List Lit := [(502, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1826, c1085] c1830 (by decide) p (sat_cons (step1826 p h) (sat_cons (step1085 p h) (sat_nil p)))
def c1831 : List Lit := [(472, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1826, c1088] c1831 (by decide) p (sat_cons (step1826 p h) (sat_cons (step1088 p h) (sat_nil p)))
def c1832 : List Lit := [(440, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1046] c1832 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1046 p h) (sat_nil p)))
def c1833 : List Lit := [(410, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1048] c1833 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1048 p h) (sat_nil p)))
def c1834 : List Lit := [(376, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1001] c1834 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1001 p h) (sat_nil p)))
def c1835 : List Lit := [(346, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1004] c1835 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1004 p h) (sat_nil p)))
def c1836 : List Lit := [(314, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c1829, c955] c1836 (by decide) p (sat_cons (step1829 p h) (sat_cons (step955 p h) (sat_nil p)))
def c1837 : List Lit := [(284, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1829, c958] c1837 (by decide) p (sat_cons (step1829 p h) (sat_cons (step958 p h) (sat_nil p)))
def c1838 : List Lit := [(456, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c1831, c1068] c1838 (by decide) p (sat_cons (step1831 p h) (sat_cons (step1068 p h) (sat_nil p)))
def c1839 : List Lit := [(438, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c1832, c1043] c1839 (by decide) p (sat_cons (step1832 p h) (sat_cons (step1043 p h) (sat_nil p)))
def c1840 : List Lit := [(408, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1029] c1840 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1029 p h) (sat_nil p)))
def c1841 : List Lit := [(374, false)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c1834, c996] c1841 (by decide) p (sat_cons (step1834 p h) (sat_cons (step996 p h) (sat_nil p)))
def c1842 : List Lit := [(360, false)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1834, c999] c1842 (by decide) p (sat_cons (step1834 p h) (sat_cons (step999 p h) (sat_nil p)))
def c1843 : List Lit := [(344, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c1835, c975] c1843 (by decide) p (sat_cons (step1835 p h) (sat_cons (step975 p h) (sat_nil p)))
def c1844 : List Lit := [(312, false)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c1836, c950] c1844 (by decide) p (sat_cons (step1836 p h) (sat_cons (step950 p h) (sat_nil p)))
def c1845 : List Lit := [(298, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c1836, c953] c1845 (by decide) p (sat_cons (step1836 p h) (sat_cons (step953 p h) (sat_nil p)))
def c1846 : List Lit := [(282, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c1837, c920] c1846 (by decide) p (sat_cons (step1837 p h) (sat_cons (step920 p h) (sat_nil p)))
def c1847 : List Lit := [(448, false)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c1838, c1058] c1847 (by decide) p (sat_cons (step1838 p h) (sat_cons (step1058 p h) (sat_nil p)))
def c1848 : List Lit := [(400, false)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c1840, c1027] c1848 (by decide) p (sat_cons (step1840 p h) (sat_cons (step1027 p h) (sat_nil p)))
def c1849 : List Lit := [(366, false)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c1841, c994] c1849 (by decide) p (sat_cons (step1841 p h) (sat_cons (step994 p h) (sat_nil p)))
def c1850 : List Lit := [(310, false)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1844, c947] c1850 (by decide) p (sat_cons (step1844 p h) (sat_cons (step947 p h) (sat_nil p)))
def c1851 : List Lit := [(290, false)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c1845, c936] c1851 (by decide) p (sat_cons (step1845 p h) (sat_cons (step936 p h) (sat_nil p)))
def c1852 : List Lit := [(308, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c1850, c944] c1852 (by decide) p (sat_cons (step1850 p h) (sat_cons (step944 p h) (sat_nil p)))
def c1853 : List Lit := [(1565, true)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c1821, c1822, c1110] c1853 (by decide) p (sat_cons (step1821 p h) (sat_cons (step1822 p h) (sat_cons (step1110 p h) (sat_nil p))))
def c1854 : List Lit := [(1567, true)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1111] c1854 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1111 p h) (sat_nil p)))
def c1855 : List Lit := [(1562, false), (1568, true)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1112] c1855 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1112 p h) (sat_nil p)))
def c1856 : List Lit := [(1563, false), (1569, true)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c1853, c1113] c1856 (by decide) p (sat_cons (step1853 p h) (sat_cons (step1113 p h) (sat_nil p)))
def c1857 : List Lit := [(1571, true)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c1854, c1114] c1857 (by decide) p (sat_cons (step1854 p h) (sat_cons (step1114 p h) (sat_nil p)))
def c1858 : List Lit := [(1558, false), (1572, true)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c1854, c1117] c1858 (by decide) p (sat_cons (step1854 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c1859 : List Lit := [(1559, false), (1573, true)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c1854, c1119] c1859 (by decide) p (sat_cons (step1854 p h) (sat_cons (step1119 p h) (sat_nil p)))
def c1860 : List Lit := [(1560, false), (1574, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c1854, c1122] c1860 (by decide) p (sat_cons (step1854 p h) (sat_cons (step1122 p h) (sat_nil p)))
def c1861 : List Lit := [(1578, true)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c1823, c1123] c1861 (by decide) p (sat_cons (step1823 p h) (sat_cons (step1123 p h) (sat_nil p)))
def c1862 : List Lit := [(16, true), (1579, true)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c1823, c1124] c1862 (by decide) p (sat_cons (step1823 p h) (sat_cons (step1124 p h) (sat_nil p)))
def c1863 : List Lit := [(1582, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c1861, c1129] c1863 (by decide) p (sat_cons (step1861 p h) (sat_cons (step1129 p h) (sat_nil p)))
def c1864 : List Lit := [(1580, false), (1583, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c1861, c1130] c1864 (by decide) p (sat_cons (step1861 p h) (sat_cons (step1130 p h) (sat_nil p)))
def c1865 : List Lit := [(1581, false), (1584, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c1861, c1131] c1865 (by decide) p (sat_cons (step1861 p h) (sat_cons (step1131 p h) (sat_nil p)))
def c1866 : List Lit := [(1594, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1149] c1866 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1149 p h) (sat_nil p)))
def c1867 : List Lit := [(1590, false), (1595, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1150] c1867 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1150 p h) (sat_nil p)))
def c1868 : List Lit := [(1591, false), (1596, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1151] c1868 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1151 p h) (sat_nil p)))
def c1869 : List Lit := [(1592, false), (1597, true)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1152] c1869 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1152 p h) (sat_nil p)))
def c1870 : List Lit := [(1593, false), (1598, true)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1153] c1870 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1153 p h) (sat_nil p)))
def c1871 : List Lit := [(1604, true)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c1857, c1866, c1165] c1871 (by decide) p (sat_cons (step1857 p h) (sat_cons (step1866 p h) (sat_cons (step1165 p h) (sat_nil p))))
def c1872 : List Lit := [(1596, false), (1606, true)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c1857, c1166] c1872 (by decide) p (sat_cons (step1857 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c1873 : List Lit := [(1597, false), (1607, true)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c1857, c1167] c1873 (by decide) p (sat_cons (step1857 p h) (sat_cons (step1167 p h) (sat_nil p)))
def c1874 : List Lit := [(1572, false), (1605, true)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c1866, c1168] c1874 (by decide) p (sat_cons (step1866 p h) (sat_cons (step1168 p h) (sat_nil p)))
def c1875 : List Lit := [(1573, false), (1606, true)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c1866, c1174] c1875 (by decide) p (sat_cons (step1866 p h) (sat_cons (step1174 p h) (sat_nil p)))
def c1876 : List Lit := [(1574, false), (1607, true)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c1866, c1179] c1876 (by decide) p (sat_cons (step1866 p h) (sat_cons (step1179 p h) (sat_nil p)))
def c1877 : List Lit := [(1670, false), (1689, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c1871, c1316] c1877 (by decide) p (sat_cons (step1871 p h) (sat_cons (step1316 p h) (sat_nil p)))
def c1878 : List Lit := [(1723, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c880, c1397, c1401, c1389, c1391, c1375, c1386, c1387, c1384, c1372, c331, c298, c303] c1878 (by decide) p (sat_cons (step880 p h) (sat_cons (step1397 p h) (sat_cons (step1401 p h) (sat_cons (step1389 p h) (sat_cons (step1391 p h) (sat_cons (step1375 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step1384 p h) (sat_cons (step1372 p h) (sat_cons (step331 p h) (sat_cons (step298 p h) (sat_cons (step303 p h) (sat_nil p))))))))))))))
def c1879 : List Lit := [(1735, true), (1653, true)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c881, c883, c1425, c1427, c1423, c1419, c1420, c364, c358, c366, c367, c350, c1774, c1251] c1879 (by decide) p (sat_cons (step881 p h) (sat_cons (step883 p h) (sat_cons (step1425 p h) (sat_cons (step1427 p h) (sat_cons (step1423 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step364 p h) (sat_cons (step358 p h) (sat_cons (step366 p h) (sat_cons (step367 p h) (sat_cons (step350 p h) (sat_cons (step1774 p h) (sat_cons (step1251 p h) (sat_nil p)))))))))))))))
end B112E050
