import B112E008Part0002
namespace B112E008
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1799 : List Lit := [(1521, true), (34, false), (1, false), (1513, false), (4, true), (5, true)]
theorem step1799 (p : Nat → Bool) (h : Constraints p) : clause p c1799 = true :=
  Snake9.LocalRup.prove_clause [c750, c1032, c1018, c1020, c1044, c1047, c1035, c1021, c1023, c1025, c1019, c1551, c20, c13] c1799 (by decide) p (sat_cons (step750 p h) (sat_cons (step1032 p h) (sat_cons (step1018 p h) (sat_cons (step1020 p h) (sat_cons (step1044 p h) (sat_cons (step1047 p h) (sat_cons (step1035 p h) (sat_cons (step1021 p h) (sat_cons (step1023 p h) (sat_cons (step1025 p h) (sat_cons (step1019 p h) (sat_cons (step1551 p h) (sat_cons (step20 p h) (sat_cons (step13 p h) (sat_nil p)))))))))))))))
def c1800 : List Lit := [(1576, true), (96, true)]
theorem step1800 (p : Nat → Bool) (h : Constraints p) : clause p c1800 = true :=
  Snake9.LocalRup.prove_clause [c770, c1138, c1140, c1135, c1136, c1132, c1133, c1691, c252, c264] c1800 (by decide) p (sat_cons (step770 p h) (sat_cons (step1138 p h) (sat_cons (step1140 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step1132 p h) (sat_cons (step1133 p h) (sat_cons (step1691 p h) (sat_cons (step252 p h) (sat_cons (step264 p h) (sat_nil p)))))))))))
def c1801 : List Lit := [(1572, true), (34, false), (1594, true), (51, true), (43, true), (47, false), (103, false)]
theorem step1801 (p : Nat → Bool) (h : Constraints p) : clause p c1801 = true :=
  Snake9.LocalRup.prove_clause [c772, c1132, c1133, c293, c1174, c1179, c1169, c279, c209] c1801 (by decide) p (sat_cons (step772 p h) (sat_cons (step1132 p h) (sat_cons (step1133 p h) (sat_cons (step293 p h) (sat_cons (step1174 p h) (sat_cons (step1179 p h) (sat_cons (step1169 p h) (sat_cons (step279 p h) (sat_cons (step209 p h) (sat_nil p))))))))))
def c1802 : List Lit := [(1544, true), (1526, false)]
theorem step1802 (p : Nat → Bool) (h : Constraints p) : clause p c1802 = true :=
  Snake9.LocalRup.prove_clause [c1064, c1655, c1080, c1065, c1652, c1056, c1069, c1610] c1802 (by decide) p (sat_cons (step1064 p h) (sat_cons (step1655 p h) (sat_cons (step1080 p h) (sat_cons (step1065 p h) (sat_cons (step1652 p h) (sat_cons (step1056 p h) (sat_cons (step1069 p h) (sat_cons (step1610 p h) (sat_nil p)))))))))
def c1803 : List Lit := [(2, true), (11, true), (3, false), (4, true)]
theorem step1803 (p : Nat → Bool) (h : Constraints p) : clause p c1803 = true :=
  Snake9.LocalRup.prove_clause [c750, c20] c1803 (by decide) p (sat_cons (step750 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1804 : List Lit := [(11, true), (1, true), (3, false), (4, true)]
theorem step1804 (p : Nat → Bool) (h : Constraints p) : clause p c1804 = true :=
  Snake9.LocalRup.prove_clause [c750, c21] c1804 (by decide) p (sat_cons (step750 p h) (sat_cons (step21 p h) (sat_nil p)))
def c1805 : List Lit := [(2, true), (1, true), (11, true), (3, false)]
theorem step1805 (p : Nat → Bool) (h : Constraints p) : clause p c1805 = true :=
  Snake9.LocalRup.prove_clause [c750, c22] c1805 (by decide) p (sat_cons (step750 p h) (sat_cons (step22 p h) (sat_nil p)))
def c1806 : List Lit := [(2, true), (1, true), (3, false), (4, true)]
theorem step1806 (p : Nat → Bool) (h : Constraints p) : clause p c1806 = true :=
  Snake9.LocalRup.prove_clause [c750, c23] c1806 (by decide) p (sat_cons (step750 p h) (sat_cons (step23 p h) (sat_nil p)))
def c1807 : List Lit := [(22, true), (7, true), (75, true), (5, false)]
theorem step1807 (p : Nat → Bool) (h : Constraints p) : clause p c1807 = true :=
  Snake9.LocalRup.prove_clause [c751, c35] c1807 (by decide) p (sat_cons (step751 p h) (sat_cons (step35 p h) (sat_nil p)))
def c1808 : List Lit := [(22, true), (1, true), (5, false), (75, true)]
theorem step1808 (p : Nat → Bool) (h : Constraints p) : clause p c1808 = true :=
  Snake9.LocalRup.prove_clause [c751, c36] c1808 (by decide) p (sat_cons (step751 p h) (sat_cons (step36 p h) (sat_nil p)))
def c1809 : List Lit := [(7, true), (1, true), (5, false), (75, true)]
theorem step1809 (p : Nat → Bool) (h : Constraints p) : clause p c1809 = true :=
  Snake9.LocalRup.prove_clause [c751, c37] c1809 (by decide) p (sat_cons (step751 p h) (sat_cons (step37 p h) (sat_nil p)))
def c1810 : List Lit := [(22, true), (7, true), (5, false), (1, true)]
theorem step1810 (p : Nat → Bool) (h : Constraints p) : clause p c1810 = true :=
  Snake9.LocalRup.prove_clause [c751, c38] c1810 (by decide) p (sat_cons (step751 p h) (sat_cons (step38 p h) (sat_nil p)))
def c1811 : List Lit := [(23, true), (2, true), (6, false), (39, true)]
theorem step1811 (p : Nat → Bool) (h : Constraints p) : clause p c1811 = true :=
  Snake9.LocalRup.prove_clause [c752, c42] c1811 (by decide) p (sat_cons (step752 p h) (sat_cons (step42 p h) (sat_nil p)))
def c1812 : List Lit := [(2, true), (39, true), (15, true), (6, false)]
theorem step1812 (p : Nat → Bool) (h : Constraints p) : clause p c1812 = true :=
  Snake9.LocalRup.prove_clause [c752, c43] c1812 (by decide) p (sat_cons (step752 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1813 : List Lit := [(2, true), (23, true), (15, true), (6, false)]
theorem step1813 (p : Nat → Bool) (h : Constraints p) : clause p c1813 = true :=
  Snake9.LocalRup.prove_clause [c752, c44] c1813 (by decide) p (sat_cons (step752 p h) (sat_cons (step44 p h) (sat_nil p)))
def c1814 : List Lit := [(7, true), (18, true), (8, false)]
theorem step1814 (p : Nat → Bool) (h : Constraints p) : clause p c1814 = true :=
  Snake9.LocalRup.prove_clause [c753, c48] c1814 (by decide) p (sat_cons (step753 p h) (sat_cons (step48 p h) (sat_nil p)))
def c1815 : List Lit := [(18, true), (8, false), (4, true)]
theorem step1815 (p : Nat → Bool) (h : Constraints p) : clause p c1815 = true :=
  Snake9.LocalRup.prove_clause [c753, c49] c1815 (by decide) p (sat_cons (step753 p h) (sat_cons (step49 p h) (sat_nil p)))
def c1816 : List Lit := [(7, true), (8, false), (4, true)]
theorem step1816 (p : Nat → Bool) (h : Constraints p) : clause p c1816 = true :=
  Snake9.LocalRup.prove_clause [c753, c50] c1816 (by decide) p (sat_cons (step753 p h) (sat_cons (step50 p h) (sat_nil p)))
def c1817 : List Lit := [(11, true), (10, false), (9, true)]
theorem step1817 (p : Nat → Bool) (h : Constraints p) : clause p c1817 = true :=
  Snake9.LocalRup.prove_clause [c754, c54] c1817 (by decide) p (sat_cons (step754 p h) (sat_cons (step54 p h) (sat_nil p)))
def c1818 : List Lit := [(11, true), (1, true), (10, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c754, c55] c1818 (by decide) p (sat_cons (step754 p h) (sat_cons (step55 p h) (sat_nil p)))
def c1819 : List Lit := [(1, true), (10, false), (9, true)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c754, c56] c1819 (by decide) p (sat_cons (step754 p h) (sat_cons (step56 p h) (sat_nil p)))
def c1820 : List Lit := [(16, true), (12, false), (79, true)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c755, c61] c1820 (by decide) p (sat_cons (step755 p h) (sat_cons (step61 p h) (sat_nil p)))
def c1821 : List Lit := [(9, true), (12, false), (79, true)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c755, c62] c1821 (by decide) p (sat_cons (step755 p h) (sat_cons (step62 p h) (sat_nil p)))
def c1822 : List Lit := [(9, true), (16, true), (12, false)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c755, c63] c1822 (by decide) p (sat_cons (step755 p h) (sat_cons (step63 p h) (sat_nil p)))
def c1823 : List Lit := [(11, false), (13, false), (4, false)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c1607, c64] c1823 (by decide) p (sat_cons (step1607 p h) (sat_cons (step64 p h) (sat_nil p)))
def c1824 : List Lit := [(18, false), (13, false), (4, false)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c1607, c65] c1824 (by decide) p (sat_cons (step1607 p h) (sat_cons (step65 p h) (sat_nil p)))
def c1825 : List Lit := [(46, false), (13, false), (4, false)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c1607, c66] c1825 (by decide) p (sat_cons (step1607 p h) (sat_cons (step66 p h) (sat_nil p)))
def c1826 : List Lit := [(81, false), (4, false), (13, false)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c1607, c67] c1826 (by decide) p (sat_cons (step1607 p h) (sat_cons (step67 p h) (sat_nil p)))
def c1827 : List Lit := [(11, false), (18, false), (13, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c1607, c68] c1827 (by decide) p (sat_cons (step1607 p h) (sat_cons (step68 p h) (sat_nil p)))
def c1828 : List Lit := [(11, false), (46, false), (13, false)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c1607, c69] c1828 (by decide) p (sat_cons (step1607 p h) (sat_cons (step69 p h) (sat_nil p)))
def c1829 : List Lit := [(11, false), (81, false), (13, false)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c1607, c70] c1829 (by decide) p (sat_cons (step1607 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1830 : List Lit := [(46, false), (18, false), (13, false)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c1607, c71] c1830 (by decide) p (sat_cons (step1607 p h) (sat_cons (step71 p h) (sat_nil p)))
def c1831 : List Lit := [(81, false), (18, false), (13, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c1607, c72] c1831 (by decide) p (sat_cons (step1607 p h) (sat_cons (step72 p h) (sat_nil p)))
def c1832 : List Lit := [(81, false), (46, false), (13, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c1607, c73] c1832 (by decide) p (sat_cons (step1607 p h) (sat_cons (step73 p h) (sat_nil p)))
def c1833 : List Lit := [(16, true), (14, false), (47, true), (15, true)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c756, c77] c1833 (by decide) p (sat_cons (step756 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1834 : List Lit := [(16, true), (17, false), (18, true)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c757, c91] c1834 (by decide) p (sat_cons (step757 p h) (sat_cons (step91 p h) (sat_nil p)))
def c1835 : List Lit := [(17, false), (15, true), (18, true)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c757, c92] c1835 (by decide) p (sat_cons (step757 p h) (sat_cons (step92 p h) (sat_nil p)))
def c1836 : List Lit := [(16, true), (15, true), (17, false)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c757, c93] c1836 (by decide) p (sat_cons (step757 p h) (sat_cons (step93 p h) (sat_nil p)))
def c1837 : List Lit := [(23, true), (52, true), (19, false)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c758, c101] c1837 (by decide) p (sat_cons (step758 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1838 : List Lit := [(2, true), (52, true), (19, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c758, c102] c1838 (by decide) p (sat_cons (step758 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1839 : List Lit := [(23, true), (2, true), (19, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c758, c103] c1839 (by decide) p (sat_cons (step758 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1840 : List Lit := [(20, false), (4, true), (55, true)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c759, c104] c1840 (by decide) p (sat_cons (step759 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1841 : List Lit := [(21, false), (23, true)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c760, c105] c1841 (by decide) p (sat_cons (step760 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1842 : List Lit := [(21, false), (22, true)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c760, c106] c1842 (by decide) p (sat_cons (step760 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1843 : List Lit := [(57, true), (21, true), (19, true), (29, true), (147, true), (23, false)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c1612, c123] c1843 (by decide) p (sat_cons (step1612 p h) (sat_cons (step123 p h) (sat_nil p)))
def c1844 : List Lit := [(19, true), (57, true), (6, true), (23, false), (147, true), (29, true)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c1612, c124] c1844 (by decide) p (sat_cons (step1612 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1845 : List Lit := [(19, true), (57, true), (147, true), (6, true), (21, true), (23, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c1612, c125] c1845 (by decide) p (sat_cons (step1612 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1846 : List Lit := [(25, false), (31, true)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c762, c127] c1846 (by decide) p (sat_cons (step762 p h) (sat_cons (step127 p h) (sat_nil p)))
def c1847 : List Lit := [(30, true), (31, true), (28, false)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c763, c135] c1847 (by decide) p (sat_cons (step763 p h) (sat_cons (step135 p h) (sat_nil p)))
def c1848 : List Lit := [(31, true), (22, true), (28, false)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c763, c136] c1848 (by decide) p (sat_cons (step763 p h) (sat_cons (step136 p h) (sat_nil p)))
def c1849 : List Lit := [(30, true), (22, true), (28, false)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c763, c137] c1849 (by decide) p (sat_cons (step763 p h) (sat_cons (step137 p h) (sat_nil p)))
def c1850 : List Lit := [(30, true), (29, false), (15, true)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c764, c140] c1850 (by decide) p (sat_cons (step764 p h) (sat_cons (step140 p h) (sat_nil p)))
def c1851 : List Lit := [(23, true), (29, false), (15, true)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c764, c141] c1851 (by decide) p (sat_cons (step764 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1852 : List Lit := [(36, true), (33, false), (32, true), (87, true)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c765, c161] c1852 (by decide) p (sat_cons (step765 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1853 : List Lit := [(36, true), (1, true), (87, true), (33, false)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c765, c162] c1853 (by decide) p (sat_cons (step765 p h) (sat_cons (step162 p h) (sat_nil p)))
def c1854 : List Lit := [(1, true), (33, false), (32, true), (87, true)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c765, c163] c1854 (by decide) p (sat_cons (step765 p h) (sat_cons (step163 p h) (sat_nil p)))
def c1855 : List Lit := [(36, true), (33, false), (1, true), (32, true)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c765, c164] c1855 (by decide) p (sat_cons (step765 p h) (sat_cons (step164 p h) (sat_nil p)))
def c1856 : List Lit := [(37, true), (52, true), (32, true), (39, true), (43, true), (34, false), (88, true)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c766, c187] c1856 (by decide) p (sat_cons (step766 p h) (sat_cons (step187 p h) (sat_nil p)))
def c1857 : List Lit := [(37, true), (2, true), (34, false), (32, true), (39, true), (43, true), (88, true)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c766, c188] c1857 (by decide) p (sat_cons (step766 p h) (sat_cons (step188 p h) (sat_nil p)))
def c1858 : List Lit := [(41, true), (37, true), (35, false), (36, true)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c767, c191] c1858 (by decide) p (sat_cons (step767 p h) (sat_cons (step191 p h) (sat_nil p)))
def c1859 : List Lit := [(41, true), (37, true), (35, false), (32, true)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c767, c192] c1859 (by decide) p (sat_cons (step767 p h) (sat_cons (step192 p h) (sat_nil p)))
def c1860 : List Lit := [(36, true), (41, true), (35, false), (32, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c767, c193] c1860 (by decide) p (sat_cons (step767 p h) (sat_cons (step193 p h) (sat_nil p)))
def c1861 : List Lit := [(37, true), (36, true), (32, true), (35, false)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c767, c194] c1861 (by decide) p (sat_cons (step767 p h) (sat_cons (step194 p h) (sat_nil p)))
def c1862 : List Lit := [(41, true), (47, true), (39, true), (38, false), (92, true)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c768, c219] c1862 (by decide) p (sat_cons (step768 p h) (sat_cons (step219 p h) (sat_nil p)))
end B112E008
