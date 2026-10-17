import B112E019Inputs
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1806 : List Lit := [(61, true)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c280, c279] c1806 (by decide) p (sat_cons (step280 p h) (sat_cons (step279 p h) (sat_nil p)))
def c1807 : List Lit := [(182, false), (59, false)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c280, c281] c1807 (by decide) p (sat_cons (step280 p h) (sat_cons (step281 p h) (sat_nil p)))
def c1808 : List Lit := [(182, true), (59, true)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c1806, c282] c1808 (by decide) p (sat_cons (step1806 p h) (sat_cons (step282 p h) (sat_nil p)))
def c1809 : List Lit := [(1, false)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c850, c1] c1809 (by decide) p (sat_cons (step850 p h) (sat_cons (step1 p h) (sat_nil p)))
def c1810 : List Lit := [(478, false)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c1175, c1172] c1810 (by decide) p (sat_cons (step1175 p h) (sat_cons (step1172 p h) (sat_nil p)))
def c1811 : List Lit := [(360, false)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c1175, c1174] c1811 (by decide) p (sat_cons (step1175 p h) (sat_cons (step1174 p h) (sat_nil p)))
def c1812 : List Lit := [(476, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c1810, c1168] c1812 (by decide) p (sat_cons (step1810 p h) (sat_cons (step1168 p h) (sat_nil p)))
def c1813 : List Lit := [(418, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c1810, c1171] c1813 (by decide) p (sat_cons (step1810 p h) (sat_cons (step1171 p h) (sat_nil p)))
def c1814 : List Lit := [(358, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1031] c1814 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1031 p h) (sat_nil p)))
def c1815 : List Lit := [(300, false)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c1811, c1034] c1815 (by decide) p (sat_cons (step1811 p h) (sat_cons (step1034 p h) (sat_nil p)))
def c1816 : List Lit := [(474, false)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c1812, c1163] c1816 (by decide) p (sat_cons (step1812 p h) (sat_cons (step1163 p h) (sat_nil p)))
def c1817 : List Lit := [(446, false)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c1812, c1166] c1817 (by decide) p (sat_cons (step1812 p h) (sat_cons (step1166 p h) (sat_nil p)))
def c1818 : List Lit := [(416, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1104] c1818 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1104 p h) (sat_nil p)))
def c1819 : List Lit := [(388, false)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1107] c1819 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1107 p h) (sat_nil p)))
def c1820 : List Lit := [(356, false)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1026] c1820 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1026 p h) (sat_nil p)))
def c1821 : List Lit := [(328, false)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1029] c1821 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1029 p h) (sat_nil p)))
def c1822 : List Lit := [(298, false)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c1815, c959] c1822 (by decide) p (sat_cons (step1815 p h) (sat_cons (step959 p h) (sat_nil p)))
def c1823 : List Lit := [(270, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1815, c962] c1823 (by decide) p (sat_cons (step1815 p h) (sat_cons (step962 p h) (sat_nil p)))
def c1824 : List Lit := [(472, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1158] c1824 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1158 p h) (sat_nil p)))
def c1825 : List Lit := [(458, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1161] c1825 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1161 p h) (sat_nil p)))
def c1826 : List Lit := [(444, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1130] c1826 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1130 p h) (sat_nil p)))
def c1827 : List Lit := [(430, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1133] c1827 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1133 p h) (sat_nil p)))
def c1828 : List Lit := [(414, false)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1818, c1099] c1828 (by decide) p (sat_cons (step1818 p h) (sat_cons (step1099 p h) (sat_nil p)))
def c1829 : List Lit := [(400, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1818, c1102] c1829 (by decide) p (sat_cons (step1818 p h) (sat_cons (step1102 p h) (sat_nil p)))
def c1830 : List Lit := [(386, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1819, c1069] c1830 (by decide) p (sat_cons (step1819 p h) (sat_cons (step1069 p h) (sat_nil p)))
def c1831 : List Lit := [(372, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1819, c1072] c1831 (by decide) p (sat_cons (step1819 p h) (sat_cons (step1072 p h) (sat_nil p)))
def c1832 : List Lit := [(354, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1820, c1021] c1832 (by decide) p (sat_cons (step1820 p h) (sat_cons (step1021 p h) (sat_nil p)))
def c1833 : List Lit := [(340, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c1820, c1024] c1833 (by decide) p (sat_cons (step1820 p h) (sat_cons (step1024 p h) (sat_nil p)))
def c1834 : List Lit := [(326, false)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c1821, c987] c1834 (by decide) p (sat_cons (step1821 p h) (sat_cons (step987 p h) (sat_nil p)))
def c1835 : List Lit := [(312, false)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1821, c990] c1835 (by decide) p (sat_cons (step1821 p h) (sat_cons (step990 p h) (sat_nil p)))
def c1836 : List Lit := [(296, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c1822, c955] c1836 (by decide) p (sat_cons (step1822 p h) (sat_cons (step955 p h) (sat_nil p)))
def c1837 : List Lit := [(282, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c1822, c957] c1837 (by decide) p (sat_cons (step1822 p h) (sat_cons (step957 p h) (sat_nil p)))
def c1838 : List Lit := [(254, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c1823, c932] c1838 (by decide) p (sat_cons (step1823 p h) (sat_cons (step932 p h) (sat_nil p)))
def c1839 : List Lit := [(464, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c1824, c1156] c1839 (by decide) p (sat_cons (step1824 p h) (sat_cons (step1156 p h) (sat_nil p)))
def c1840 : List Lit := [(456, false)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c1825, c1142] c1840 (by decide) p (sat_cons (step1825 p h) (sat_cons (step1142 p h) (sat_nil p)))
def c1841 : List Lit := [(436, false)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c1826, c1128] c1841 (by decide) p (sat_cons (step1826 p h) (sat_cons (step1128 p h) (sat_nil p)))
def c1842 : List Lit := [(428, false)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1115] c1842 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1115 p h) (sat_nil p)))
def c1843 : List Lit := [(412, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1094] c1843 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1094 p h) (sat_nil p)))
def c1844 : List Lit := [(406, false)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1097] c1844 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1097 p h) (sat_nil p)))
def c1845 : List Lit := [(398, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c1829, c1082] c1845 (by decide) p (sat_cons (step1829 p h) (sat_cons (step1082 p h) (sat_nil p)))
def c1846 : List Lit := [(384, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c1830, c1064] c1846 (by decide) p (sat_cons (step1830 p h) (sat_cons (step1064 p h) (sat_nil p)))
def c1847 : List Lit := [(378, false)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c1830, c1067] c1847 (by decide) p (sat_cons (step1830 p h) (sat_cons (step1067 p h) (sat_nil p)))
def c1848 : List Lit := [(370, false)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c1831, c1046] c1848 (by decide) p (sat_cons (step1831 p h) (sat_cons (step1046 p h) (sat_nil p)))
def c1849 : List Lit := [(364, false)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c1831, c1049] c1849 (by decide) p (sat_cons (step1831 p h) (sat_cons (step1049 p h) (sat_nil p)))
def c1850 : List Lit := [(352, false)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c1832, c1016] c1850 (by decide) p (sat_cons (step1832 p h) (sat_cons (step1016 p h) (sat_nil p)))
def c1851 : List Lit := [(346, false)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c1832, c1019] c1851 (by decide) p (sat_cons (step1832 p h) (sat_cons (step1019 p h) (sat_nil p)))
def c1852 : List Lit := [(338, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1001] c1852 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1001 p h) (sat_nil p)))
def c1853 : List Lit := [(332, false)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1004] c1853 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1004 p h) (sat_nil p)))
def c1854 : List Lit := [(318, false)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1834, c985] c1854 (by decide) p (sat_cons (step1834 p h) (sat_cons (step985 p h) (sat_nil p)))
def c1855 : List Lit := [(280, false)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c1837, c942] c1855 (by decide) p (sat_cons (step1837 p h) (sat_cons (step942 p h) (sat_nil p)))
def c1856 : List Lit := [(252, false)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c1838, c919] c1856 (by decide) p (sat_cons (step1838 p h) (sat_cons (step919 p h) (sat_nil p)))
def c1857 : List Lit := [(394, false)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c1845, c1080] c1857 (by decide) p (sat_cons (step1845 p h) (sat_cons (step1080 p h) (sat_nil p)))
def c1858 : List Lit := [(382, false)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c1846, c1062] c1858 (by decide) p (sat_cons (step1846 p h) (sat_cons (step1062 p h) (sat_nil p)))
def c1859 : List Lit := [(376, false)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c1847, c1055] c1859 (by decide) p (sat_cons (step1847 p h) (sat_cons (step1055 p h) (sat_nil p)))
def c1860 : List Lit := [(362, false)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c1849, c1039] c1860 (by decide) p (sat_cons (step1849 p h) (sat_cons (step1039 p h) (sat_nil p)))
def c1861 : List Lit := [(336, false)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c1852, c999] c1861 (by decide) p (sat_cons (step1852 p h) (sat_cons (step999 p h) (sat_nil p)))
def c1862 : List Lit := [(123, true), (126, true), (128, true), (130, true), (132, true), (135, true), (137, true), (139, true), (140, true), (142, true), (145, true), (147, true), (149, true), (152, true), (154, true), (156, true), (157, true), (159, true), (162, true), (164, true), (165, true), (167, true), (169, true), (172, true), (173, true), (175, true), (176, true), (179, true), (182, true), (184, true), (185, true), (187, true), (188, true), (190, true), (192, true), (193, true), (196, true), (197, true), (201, true), (202, true), (203, true), (206, true), (208, true), (210, true), (212, true), (213, true), (216, true), (219, true), (220, true), (223, true), (224, true), (228, true), (231, true), (233, true), (234, true), (236, true), (237, true), (239, true), (241, true)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.TreeRup.prove_clause [c850, c851, c852, c853, c854, c855, c856, c857, c858, c859, c860, c861, c862, c863, c864, c865, c866, c867, c868, c869, c870, c871, c872, c873, c874, c875, c876, c877, c878, c879, c880, c881, c882, c883, c884, c885, c886, c887, c888, c889, c890, c891, c892, c893, c894, c895, c896, c897, c898, c899, c900, c901, c902, c903, c904, c905, c906, c907, c908, c909, c910, c1176] c1862 (by decide) p (sat_cons (step850 p h) (sat_cons (step851 p h) (sat_cons (step852 p h) (sat_cons (step853 p h) (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step856 p h) (sat_cons (step857 p h) (sat_cons (step858 p h) (sat_cons (step859 p h) (sat_cons (step860 p h) (sat_cons (step861 p h) (sat_cons (step862 p h) (sat_cons (step863 p h) (sat_cons (step864 p h) (sat_cons (step865 p h) (sat_cons (step866 p h) (sat_cons (step867 p h) (sat_cons (step868 p h) (sat_cons (step869 p h) (sat_cons (step870 p h) (sat_cons (step871 p h) (sat_cons (step872 p h) (sat_cons (step873 p h) (sat_cons (step874 p h) (sat_cons (step875 p h) (sat_cons (step876 p h) (sat_cons (step877 p h) (sat_cons (step878 p h) (sat_cons (step879 p h) (sat_cons (step880 p h) (sat_cons (step881 p h) (sat_cons (step882 p h) (sat_cons (step883 p h) (sat_cons (step884 p h) (sat_cons (step885 p h) (sat_cons (step886 p h) (sat_cons (step887 p h) (sat_cons (step888 p h) (sat_cons (step889 p h) (sat_cons (step890 p h) (sat_cons (step891 p h) (sat_cons (step892 p h) (sat_cons (step893 p h) (sat_cons (step894 p h) (sat_cons (step895 p h) (sat_cons (step896 p h) (sat_cons (step897 p h) (sat_cons (step898 p h) (sat_cons (step899 p h) (sat_cons (step900 p h) (sat_cons (step901 p h) (sat_cons (step902 p h) (sat_cons (step903 p h) (sat_cons (step904 p h) (sat_cons (step905 p h) (sat_cons (step906 p h) (sat_cons (step907 p h) (sat_cons (step908 p h) (sat_cons (step909 p h) (sat_cons (step910 p h) (sat_cons (step1176 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1863 : List Lit := [(1620, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c1860, c1444, c1448, c1436, c1438, c1425, c1427, c1433, c1430, c1422, c1423, c283, c298, c316, c293, c297, c1037] c1863 (by decide) p (sat_cons (step1860 p h) (sat_cons (step1444 p h) (sat_cons (step1448 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1425 p h) (sat_cons (step1427 p h) (sat_cons (step1433 p h) (sat_cons (step1430 p h) (sat_cons (step1422 p h) (sat_cons (step1423 p h) (sat_cons (step283 p h) (sat_cons (step298 p h) (sat_cons (step316 p h) (sat_cons (step293 p h) (sat_cons (step297 p h) (sat_cons (step1037 p h) (sat_nil p))))))))))))))))))
def c1864 : List Lit := [(1651, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1516] c1864 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1516 p h) (sat_nil p)))
def c1865 : List Lit := [(1607, true), (1616, true), (1627, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c1830, c1462, c1463, c1438, c1431, c377, c1430, c1436, c1433, c1422, c1423, c353, c298, c316, c363, c330, c1059, c1050, c1061, c1056, c1066] c1865 (by decide) p (sat_cons (step1830 p h) (sat_cons (step1462 p h) (sat_cons (step1463 p h) (sat_cons (step1438 p h) (sat_cons (step1431 p h) (sat_cons (step377 p h) (sat_cons (step1430 p h) (sat_cons (step1436 p h) (sat_cons (step1433 p h) (sat_cons (step1422 p h) (sat_cons (step1423 p h) (sat_cons (step353 p h) (sat_cons (step298 p h) (sat_cons (step316 p h) (sat_cons (step363 p h) (sat_cons (step330 p h) (sat_cons (step1059 p h) (sat_cons (step1050 p h) (sat_cons (step1061 p h) (sat_cons (step1056 p h) (sat_cons (step1066 p h) (sat_nil p))))))))))))))))))))))
def c1866 : List Lit := [(1497, true), (1627, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c1855, c1463, c1462, c1217, c1219, c1214, c1215, c85, c350, c82, c91, c936, c937, c940] c1866 (by decide) p (sat_cons (step1855 p h) (sat_cons (step1463 p h) (sat_cons (step1462 p h) (sat_cons (step1217 p h) (sat_cons (step1219 p h) (sat_cons (step1214 p h) (sat_cons (step1215 p h) (sat_cons (step85 p h) (sat_cons (step350 p h) (sat_cons (step82 p h) (sat_cons (step91 p h) (sat_cons (step936 p h) (sat_cons (step937 p h) (sat_cons (step940 p h) (sat_nil p)))))))))))))))
def c1867 : List Lit := [(1497, true), (1489, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c861, c1855, c1815, c1200, c1217, c1219, c1214, c1215, c85, c89, c91, c93, c937, c938, c940, c941, c936, c956, c84, c961, c68, c929, c1188, c928, c1191, c1194, c924, c1204, c1186, c921, c1182, c26, c32, c33, c1755] c1867 (by decide) p (sat_cons (step861 p h) (sat_cons (step1855 p h) (sat_cons (step1815 p h) (sat_cons (step1200 p h) (sat_cons (step1217 p h) (sat_cons (step1219 p h) (sat_cons (step1214 p h) (sat_cons (step1215 p h) (sat_cons (step85 p h) (sat_cons (step89 p h) (sat_cons (step91 p h) (sat_cons (step93 p h) (sat_cons (step937 p h) (sat_cons (step938 p h) (sat_cons (step940 p h) (sat_cons (step941 p h) (sat_cons (step936 p h) (sat_cons (step956 p h) (sat_cons (step84 p h) (sat_cons (step961 p h) (sat_cons (step68 p h) (sat_cons (step929 p h) (sat_cons (step1188 p h) (sat_cons (step928 p h) (sat_cons (step1191 p h) (sat_cons (step1194 p h) (sat_cons (step924 p h) (sat_cons (step1204 p h) (sat_cons (step1186 p h) (sat_cons (step921 p h) (sat_cons (step1182 p h) (sat_cons (step26 p h) (sat_cons (step32 p h) (sat_cons (step33 p h) (sat_cons (step1755 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c1868 : List Lit := [(1516, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c1823, c1251, c1260, c1867, c1239, c1240, c1255, c1228, c1199, c1203, c1226, c1191, c1193, c1180, c1189, c1185, c1177, c1178, c6, c44, c17, c42, c913, c922, c916, c923, c918, c928, c931] c1868 (by decide) p (sat_cons (step1823 p h) (sat_cons (step1251 p h) (sat_cons (step1260 p h) (sat_cons (step1867 p h) (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step1255 p h) (sat_cons (step1228 p h) (sat_cons (step1199 p h) (sat_cons (step1203 p h) (sat_cons (step1226 p h) (sat_cons (step1191 p h) (sat_cons (step1193 p h) (sat_cons (step1180 p h) (sat_cons (step1189 p h) (sat_cons (step1185 p h) (sat_cons (step1177 p h) (sat_cons (step1178 p h) (sat_cons (step6 p h) (sat_cons (step44 p h) (sat_cons (step17 p h) (sat_cons (step42 p h) (sat_cons (step913 p h) (sat_cons (step922 p h) (sat_cons (step916 p h) (sat_cons (step923 p h) (sat_cons (step918 p h) (sat_cons (step928 p h) (sat_cons (step931 p h) (sat_nil p))))))))))))))))))))))))))))))
def c1869 : List Lit := [(1480, true), (7, false), (17, true), (14, false), (128, true)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c1185, c1186, c44, c34, c22] c1869 (by decide) p (sat_cons (step1185 p h) (sat_cons (step1186 p h) (sat_cons (step44 p h) (sat_cons (step34 p h) (sat_cons (step22 p h) (sat_nil p))))))
end B112E019
