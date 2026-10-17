import B112E036Part0002
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1837 : List Lit := [(40, true), (39, false), (35, true)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c786, c173] c1837 (by decide) p (sat_cons (step786 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1838 : List Lit := [(43, true), (46, true), (42, true), (41, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c787, c183] c1838 (by decide) p (sat_cons (step787 p h) (sat_cons (step183 p h) (sat_nil p)))
def c1839 : List Lit := [(43, true), (46, true), (31, true), (41, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c787, c184] c1839 (by decide) p (sat_cons (step787 p h) (sat_cons (step184 p h) (sat_nil p)))
def c1840 : List Lit := [(46, true), (42, true), (41, false), (31, true)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c787, c185] c1840 (by decide) p (sat_cons (step787 p h) (sat_cons (step185 p h) (sat_nil p)))
def c1841 : List Lit := [(43, true), (41, false), (31, true), (42, true)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c787, c186] c1841 (by decide) p (sat_cons (step787 p h) (sat_cons (step186 p h) (sat_nil p)))
def c1842 : List Lit := [(43, true), (44, false), (102, true), (42, true)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c788, c201] c1842 (by decide) p (sat_cons (step788 p h) (sat_cons (step201 p h) (sat_nil p)))
def c1843 : List Lit := [(43, true), (44, false), (34, true), (102, true)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c788, c202] c1843 (by decide) p (sat_cons (step788 p h) (sat_cons (step202 p h) (sat_nil p)))
def c1844 : List Lit := [(44, false), (34, true), (102, true), (42, true)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c788, c203] c1844 (by decide) p (sat_cons (step788 p h) (sat_cons (step203 p h) (sat_nil p)))
def c1845 : List Lit := [(43, true), (42, true), (34, true), (44, false)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c788, c204] c1845 (by decide) p (sat_cons (step788 p h) (sat_cons (step204 p h) (sat_nil p)))
def c1846 : List Lit := [(43, true), (49, true), (45, false)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c789, c205] c1846 (by decide) p (sat_cons (step789 p h) (sat_cons (step205 p h) (sat_nil p)))
def c1847 : List Lit := [(49, true), (36, true), (45, false)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c789, c206] c1847 (by decide) p (sat_cons (step789 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1848 : List Lit := [(43, true), (36, true), (45, false)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c789, c207] c1848 (by decide) p (sat_cons (step789 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1849 : List Lit := [(49, true), (47, false), (48, true)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c790, c219] c1849 (by decide) p (sat_cons (step790 p h) (sat_cons (step219 p h) (sat_nil p)))
def c1850 : List Lit := [(49, true), (46, true), (47, false)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c790, c220] c1850 (by decide) p (sat_cons (step790 p h) (sat_cons (step220 p h) (sat_nil p)))
def c1851 : List Lit := [(46, true), (47, false), (48, true)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c790, c221] c1851 (by decide) p (sat_cons (step790 p h) (sat_cons (step221 p h) (sat_nil p)))
def c1852 : List Lit := [(51, false), (34, false), (52, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c1645, c250] c1852 (by decide) p (sat_cons (step1645 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1853 : List Lit := [(58, false), (34, false), (52, false)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c1645, c251] c1853 (by decide) p (sat_cons (step1645 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1854 : List Lit := [(51, false), (58, false), (52, false)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c1645, c252] c1854 (by decide) p (sat_cons (step1645 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1855 : List Lit := [(52, false), (58, true), (51, true), (34, true)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c791, c253] c1855 (by decide) p (sat_cons (step791 p h) (sat_cons (step253 p h) (sat_nil p)))
def c1856 : List Lit := [(62, true), (35, true), (54, false)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c792, c258] c1856 (by decide) p (sat_cons (step792 p h) (sat_cons (step258 p h) (sat_nil p)))
def c1857 : List Lit := [(53, true), (35, true), (54, false)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c792, c259] c1857 (by decide) p (sat_cons (step792 p h) (sat_cons (step259 p h) (sat_nil p)))
def c1858 : List Lit := [(36, true), (55, false), (51, true), (53, true), (113, true)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c793, c261] c1858 (by decide) p (sat_cons (step793 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1859 : List Lit := [(36, true), (60, true), (51, true), (53, true), (55, false)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c793, c262] c1859 (by decide) p (sat_cons (step793 p h) (sat_cons (step262 p h) (sat_nil p)))
def c1860 : List Lit := [(116, true), (65, true), (56, false), (58, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c794, c263] c1860 (by decide) p (sat_cons (step794 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1861 : List Lit := [(22, true), (116, true), (56, false), (65, true)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c794, c264] c1861 (by decide) p (sat_cons (step794 p h) (sat_cons (step264 p h) (sat_nil p)))
def c1862 : List Lit := [(22, true), (116, true), (56, false), (58, true)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c794, c265] c1862 (by decide) p (sat_cons (step794 p h) (sat_cons (step265 p h) (sat_nil p)))
def c1863 : List Lit := [(22, true), (65, true), (56, false), (58, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c794, c266] c1863 (by decide) p (sat_cons (step794 p h) (sat_cons (step266 p h) (sat_nil p)))
def c1864 : List Lit := [(60, true), (66, true), (57, false), (58, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c795, c270] c1864 (by decide) p (sat_cons (step795 p h) (sat_cons (step270 p h) (sat_nil p)))
def c1865 : List Lit := [(58, true), (66, true), (51, true), (57, false)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c795, c271] c1865 (by decide) p (sat_cons (step795 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1866 : List Lit := [(60, true), (58, true), (51, true), (57, false)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c795, c272] c1866 (by decide) p (sat_cons (step795 p h) (sat_cons (step272 p h) (sat_nil p)))
def c1867 : List Lit := [(59, false), (60, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c796, c293] c1867 (by decide) p (sat_cons (step796 p h) (sat_cons (step293 p h) (sat_nil p)))
def c1868 : List Lit := [(59, false), (53, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c796, c294] c1868 (by decide) p (sat_cons (step796 p h) (sat_cons (step294 p h) (sat_nil p)))
def c1869 : List Lit := [(123, true), (62, true), (61, false)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c797, c299] c1869 (by decide) p (sat_cons (step797 p h) (sat_cons (step299 p h) (sat_nil p)))
def c1870 : List Lit := [(53, true), (123, true), (61, false)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c797, c300] c1870 (by decide) p (sat_cons (step797 p h) (sat_cons (step300 p h) (sat_nil p)))
def c1871 : List Lit := [(62, true), (53, true), (61, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c797, c301] c1871 (by decide) p (sat_cons (step797 p h) (sat_cons (step301 p h) (sat_nil p)))
def c1872 : List Lit := [(63, false), (68, true)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c798, c306] c1872 (by decide) p (sat_cons (step798 p h) (sat_cons (step306 p h) (sat_nil p)))
def c1873 : List Lit := [(63, false), (62, true)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c798, c307] c1873 (by decide) p (sat_cons (step798 p h) (sat_cons (step307 p h) (sat_nil p)))
def c1874 : List Lit := [(65, true), (66, true), (64, false)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c799, c309] c1874 (by decide) p (sat_cons (step799 p h) (sat_cons (step309 p h) (sat_nil p)))
def c1875 : List Lit := [(66, true), (46, true), (64, false)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c799, c310] c1875 (by decide) p (sat_cons (step799 p h) (sat_cons (step310 p h) (sat_nil p)))
def c1876 : List Lit := [(65, true), (46, true), (64, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c799, c311] c1876 (by decide) p (sat_cons (step799 p h) (sat_cons (step311 p h) (sat_nil p)))
def c1877 : List Lit := [(66, true), (68, true), (67, false), (65, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c800, c331] c1877 (by decide) p (sat_cons (step800 p h) (sat_cons (step331 p h) (sat_nil p)))
def c1878 : List Lit := [(66, true), (68, true), (67, false), (58, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c800, c332] c1878 (by decide) p (sat_cons (step800 p h) (sat_cons (step332 p h) (sat_nil p)))
def c1879 : List Lit := [(68, true), (65, true), (67, false), (58, true)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c800, c333] c1879 (by decide) p (sat_cons (step800 p h) (sat_cons (step333 p h) (sat_nil p)))
def c1880 : List Lit := [(66, true), (65, true), (67, false), (58, true)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c800, c334] c1880 (by decide) p (sat_cons (step800 p h) (sat_cons (step334 p h) (sat_nil p)))
def c1881 : List Lit := [(74, true), (70, false), (89, true), (78, true)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c801, c347] c1881 (by decide) p (sat_cons (step801 p h) (sat_cons (step347 p h) (sat_nil p)))
def c1882 : List Lit := [(78, true), (70, false), (69, true), (89, true)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c801, c348] c1882 (by decide) p (sat_cons (step801 p h) (sat_cons (step348 p h) (sat_nil p)))
def c1883 : List Lit := [(74, true), (70, false), (89, true), (69, true)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c801, c349] c1883 (by decide) p (sat_cons (step801 p h) (sat_cons (step349 p h) (sat_nil p)))
def c1884 : List Lit := [(74, true), (70, false), (69, true), (78, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c801, c350] c1884 (by decide) p (sat_cons (step801 p h) (sat_cons (step350 p h) (sat_nil p)))
def c1885 : List Lit := [(71, true), (77, true), (72, false), (94, true)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c802, c352] c1885 (by decide) p (sat_cons (step802 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1886 : List Lit := [(77, true), (72, false), (5, true), (94, true)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c802, c353] c1886 (by decide) p (sat_cons (step802 p h) (sat_cons (step353 p h) (sat_nil p)))
def c1887 : List Lit := [(71, true), (5, true), (72, false), (94, true)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c802, c354] c1887 (by decide) p (sat_cons (step802 p h) (sat_cons (step354 p h) (sat_nil p)))
def c1888 : List Lit := [(77, true), (5, true), (72, false), (71, true)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c802, c355] c1888 (by decide) p (sat_cons (step802 p h) (sat_cons (step355 p h) (sat_nil p)))
def c1889 : List Lit := [(73, false), (74, true), (95, true), (69, true)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c803, c357] c1889 (by decide) p (sat_cons (step803 p h) (sat_cons (step357 p h) (sat_nil p)))
def c1890 : List Lit := [(73, false), (74, true), (95, true), (6, true)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c803, c358] c1890 (by decide) p (sat_cons (step803 p h) (sat_cons (step358 p h) (sat_nil p)))
def c1891 : List Lit := [(73, false), (6, true), (95, true), (69, true)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c803, c359] c1891 (by decide) p (sat_cons (step803 p h) (sat_cons (step359 p h) (sat_nil p)))
def c1892 : List Lit := [(73, false), (74, true), (69, true), (6, true)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c803, c360] c1892 (by decide) p (sat_cons (step803 p h) (sat_cons (step360 p h) (sat_nil p)))
def c1893 : List Lit := [(77, true), (75, false), (97, true)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c804, c371] c1893 (by decide) p (sat_cons (step804 p h) (sat_cons (step371 p h) (sat_nil p)))
def c1894 : List Lit := [(75, false), (74, true), (97, true)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c804, c372] c1894 (by decide) p (sat_cons (step804 p h) (sat_cons (step372 p h) (sat_nil p)))
def c1895 : List Lit := [(77, true), (75, false), (74, true)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c804, c373] c1895 (by decide) p (sat_cons (step804 p h) (sat_cons (step373 p h) (sat_nil p)))
def c1896 : List Lit := [(77, true), (76, false), (74, true)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c805, c375] c1896 (by decide) p (sat_cons (step805 p h) (sat_cons (step375 p h) (sat_nil p)))
def c1897 : List Lit := [(79, true), (80, false), (102, true)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c806, c386] c1897 (by decide) p (sat_cons (step806 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1898 : List Lit := [(78, true), (80, false), (102, true)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c806, c387] c1898 (by decide) p (sat_cons (step806 p h) (sat_cons (step387 p h) (sat_nil p)))
def c1899 : List Lit := [(79, true), (80, false), (78, true)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c806, c388] c1899 (by decide) p (sat_cons (step806 p h) (sat_cons (step388 p h) (sat_nil p)))
def c1900 : List Lit := [(81, true), (79, true), (82, false), (86, true)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c807, c394] c1900 (by decide) p (sat_cons (step807 p h) (sat_cons (step394 p h) (sat_nil p)))
end B112E036
