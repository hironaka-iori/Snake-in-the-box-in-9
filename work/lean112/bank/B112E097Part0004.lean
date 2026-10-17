import B112E097Part0003
namespace B112E097
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1851 : List Lit := [(24, true), (23, true), (25, false)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c699, c75] c1851 (by decide) p (sat_cons (step699 p h) (sat_cons (step75 p h) (sat_nil p)))
def c1852 : List Lit := [(24, true), (16, true), (25, false)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c699, c76] c1852 (by decide) p (sat_cons (step699 p h) (sat_cons (step76 p h) (sat_nil p)))
def c1853 : List Lit := [(16, true), (23, true), (25, false)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c699, c77] c1853 (by decide) p (sat_cons (step699 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1854 : List Lit := [(27, true), (26, true), (28, false)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c700, c81] c1854 (by decide) p (sat_cons (step700 p h) (sat_cons (step81 p h) (sat_nil p)))
def c1855 : List Lit := [(27, true), (19, true), (28, false)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c700, c82] c1855 (by decide) p (sat_cons (step700 p h) (sat_cons (step82 p h) (sat_nil p)))
def c1856 : List Lit := [(19, true), (26, true), (28, false)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c700, c83] c1856 (by decide) p (sat_cons (step700 p h) (sat_cons (step83 p h) (sat_nil p)))
def c1857 : List Lit := [(35, true), (31, true), (29, false), (102, true)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c701, c87] c1857 (by decide) p (sat_cons (step701 p h) (sat_cons (step87 p h) (sat_nil p)))
def c1858 : List Lit := [(30, true), (35, true), (29, false), (102, true)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c701, c88] c1858 (by decide) p (sat_cons (step701 p h) (sat_cons (step88 p h) (sat_nil p)))
def c1859 : List Lit := [(30, true), (31, true), (29, false), (102, true)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c701, c89] c1859 (by decide) p (sat_cons (step701 p h) (sat_cons (step89 p h) (sat_nil p)))
def c1860 : List Lit := [(30, true), (31, true), (29, false), (35, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c701, c90] c1860 (by decide) p (sat_cons (step701 p h) (sat_cons (step90 p h) (sat_nil p)))
def c1861 : List Lit := [(42, true), (35, true), (107, true), (34, false)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c702, c102] c1861 (by decide) p (sat_cons (step702 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1862 : List Lit := [(42, true), (17, true), (34, false), (107, true)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c702, c103] c1862 (by decide) p (sat_cons (step702 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1863 : List Lit := [(35, true), (17, true), (34, false), (107, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c702, c104] c1863 (by decide) p (sat_cons (step702 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1864 : List Lit := [(42, true), (35, true), (34, false), (17, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c702, c105] c1864 (by decide) p (sat_cons (step702 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1865 : List Lit := [(36, false), (112, true), (37, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c703, c112] c1865 (by decide) p (sat_cons (step703 p h) (sat_cons (step112 p h) (sat_nil p)))
def c1866 : List Lit := [(32, true), (36, false), (112, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c703, c113] c1866 (by decide) p (sat_cons (step703 p h) (sat_cons (step113 p h) (sat_nil p)))
def c1867 : List Lit := [(32, true), (36, false), (37, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c703, c114] c1867 (by decide) p (sat_cons (step703 p h) (sat_cons (step114 p h) (sat_nil p)))
def c1868 : List Lit := [(42, true), (38, false), (41, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c704, c123] c1868 (by decide) p (sat_cons (step704 p h) (sat_cons (step123 p h) (sat_nil p)))
def c1869 : List Lit := [(39, true), (38, false), (42, true)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c704, c124] c1869 (by decide) p (sat_cons (step704 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1870 : List Lit := [(39, true), (38, false), (41, true)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c704, c125] c1870 (by decide) p (sat_cons (step704 p h) (sat_cons (step125 p h) (sat_nil p)))
def c1871 : List Lit := [(40, false), (39, true)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c705, c129] c1871 (by decide) p (sat_cons (step705 p h) (sat_cons (step129 p h) (sat_nil p)))
def c1872 : List Lit := [(40, false), (30, true)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c705, c130] c1872 (by decide) p (sat_cons (step705 p h) (sat_cons (step130 p h) (sat_nil p)))
def c1873 : List Lit := [(27, true), (42, true), (120, true), (43, false)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c706, c141] c1873 (by decide) p (sat_cons (step706 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1874 : List Lit := [(42, true), (44, false), (45, true)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c707, c142] c1874 (by decide) p (sat_cons (step707 p h) (sat_cons (step142 p h) (sat_nil p)))
def c1875 : List Lit := [(41, true), (44, false), (45, true)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c707, c143] c1875 (by decide) p (sat_cons (step707 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1876 : List Lit := [(42, true), (41, true), (44, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c707, c144] c1876 (by decide) p (sat_cons (step707 p h) (sat_cons (step144 p h) (sat_nil p)))
def c1877 : List Lit := [(45, true), (46, false), (123, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c708, c152] c1877 (by decide) p (sat_cons (step708 p h) (sat_cons (step152 p h) (sat_nil p)))
def c1878 : List Lit := [(46, false), (37, true), (123, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c708, c153] c1878 (by decide) p (sat_cons (step708 p h) (sat_cons (step153 p h) (sat_nil p)))
def c1879 : List Lit := [(45, true), (46, false), (37, true)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c708, c154] c1879 (by decide) p (sat_cons (step708 p h) (sat_cons (step154 p h) (sat_nil p)))
def c1880 : List Lit := [(49, true), (52, true), (47, false)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c709, c155] c1880 (by decide) p (sat_cons (step709 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1881 : List Lit := [(48, true), (52, true), (47, false)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c709, c156] c1881 (by decide) p (sat_cons (step709 p h) (sat_cons (step156 p h) (sat_nil p)))
def c1882 : List Lit := [(48, true), (49, true), (47, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c709, c157] c1882 (by decide) p (sat_cons (step709 p h) (sat_cons (step157 p h) (sat_nil p)))
def c1883 : List Lit := [(62, true), (71, true), (53, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c710, c207] c1883 (by decide) p (sat_cons (step710 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1884 : List Lit := [(71, true), (52, true), (53, false)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c710, c208] c1884 (by decide) p (sat_cons (step710 p h) (sat_cons (step208 p h) (sat_nil p)))
def c1885 : List Lit := [(62, true), (52, true), (53, false)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c710, c209] c1885 (by decide) p (sat_cons (step710 p h) (sat_cons (step209 p h) (sat_nil p)))
def c1886 : List Lit := [(63, true), (56, true), (52, true), (54, false)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c711, c213] c1886 (by decide) p (sat_cons (step711 p h) (sat_cons (step213 p h) (sat_nil p)))
def c1887 : List Lit := [(63, true), (54, false), (52, true), (48, true)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c711, c214] c1887 (by decide) p (sat_cons (step711 p h) (sat_cons (step214 p h) (sat_nil p)))
def c1888 : List Lit := [(56, true), (54, false), (52, true), (48, true)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c711, c215] c1888 (by decide) p (sat_cons (step711 p h) (sat_cons (step215 p h) (sat_nil p)))
def c1889 : List Lit := [(56, true), (88, true), (52, true), (55, false)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c712, c216] c1889 (by decide) p (sat_cons (step712 p h) (sat_cons (step216 p h) (sat_nil p)))
def c1890 : List Lit := [(56, true), (49, true), (88, true), (55, false)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c712, c217] c1890 (by decide) p (sat_cons (step712 p h) (sat_cons (step217 p h) (sat_nil p)))
def c1891 : List Lit := [(49, true), (88, true), (52, true), (55, false)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c712, c218] c1891 (by decide) p (sat_cons (step712 p h) (sat_cons (step218 p h) (sat_nil p)))
def c1892 : List Lit := [(56, true), (49, true), (52, true), (55, false)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c712, c219] c1892 (by decide) p (sat_cons (step712 p h) (sat_cons (step219 p h) (sat_nil p)))
def c1893 : List Lit := [(62, true), (60, true), (57, false), (92, true)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c713, c231] c1893 (by decide) p (sat_cons (step713 p h) (sat_cons (step231 p h) (sat_nil p)))
def c1894 : List Lit := [(62, true), (58, true), (92, true), (57, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c713, c232] c1894 (by decide) p (sat_cons (step713 p h) (sat_cons (step232 p h) (sat_nil p)))
def c1895 : List Lit := [(60, true), (58, true), (92, true), (57, false)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c713, c233] c1895 (by decide) p (sat_cons (step713 p h) (sat_cons (step233 p h) (sat_nil p)))
def c1896 : List Lit := [(60, true), (62, true), (57, false), (58, true)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c713, c234] c1896 (by decide) p (sat_cons (step713 p h) (sat_cons (step234 p h) (sat_nil p)))
def c1897 : List Lit := [(11, true), (49, true), (59, false), (77, true)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c714, c255] c1897 (by decide) p (sat_cons (step714 p h) (sat_cons (step255 p h) (sat_nil p)))
def c1898 : List Lit := [(60, true), (58, true), (61, false)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c715, c259] c1898 (by decide) p (sat_cons (step715 p h) (sat_cons (step259 p h) (sat_nil p)))
def c1899 : List Lit := [(60, true), (61, false), (51, true)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c715, c260] c1899 (by decide) p (sat_cons (step715 p h) (sat_cons (step260 p h) (sat_nil p)))
def c1900 : List Lit := [(58, true), (61, false), (51, true)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c715, c261] c1900 (by decide) p (sat_cons (step715 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1901 : List Lit := [(63, true), (62, true), (64, false)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c716, c269] c1901 (by decide) p (sat_cons (step716 p h) (sat_cons (step269 p h) (sat_nil p)))
def c1902 : List Lit := [(63, true), (64, false), (58, true)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c716, c270] c1902 (by decide) p (sat_cons (step716 p h) (sat_cons (step270 p h) (sat_nil p)))
def c1903 : List Lit := [(62, true), (58, true), (64, false)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c716, c271] c1903 (by decide) p (sat_cons (step716 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1904 : List Lit := [(67, true), (65, false), (71, true), (102, true)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c717, c274] c1904 (by decide) p (sat_cons (step717 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1905 : List Lit := [(67, true), (66, true), (65, false), (102, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c717, c275] c1905 (by decide) p (sat_cons (step717 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1906 : List Lit := [(78, true), (71, true), (70, false), (107, true)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c719, c290] c1906 (by decide) p (sat_cons (step719 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1907 : List Lit := [(78, true), (52, true), (107, true), (70, false)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c719, c291] c1907 (by decide) p (sat_cons (step719 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1908 : List Lit := [(71, true), (52, true), (107, true), (70, false)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c719, c292] c1908 (by decide) p (sat_cons (step719 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1909 : List Lit := [(78, true), (71, true), (70, false), (52, true)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c719, c293] c1909 (by decide) p (sat_cons (step719 p h) (sat_cons (step293 p h) (sat_nil p)))
def c1910 : List Lit := [(68, true), (72, false), (112, true), (73, true)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c720, c298] c1910 (by decide) p (sat_cons (step720 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1911 : List Lit := [(56, true), (72, false), (73, true), (112, true)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c720, c299] c1911 (by decide) p (sat_cons (step720 p h) (sat_cons (step299 p h) (sat_nil p)))
def c1912 : List Lit := [(68, true), (56, true), (72, false), (112, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c720, c300] c1912 (by decide) p (sat_cons (step720 p h) (sat_cons (step300 p h) (sat_nil p)))
def c1913 : List Lit := [(56, true), (68, true), (72, false), (73, true)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c720, c301] c1913 (by decide) p (sat_cons (step720 p h) (sat_cons (step301 p h) (sat_nil p)))
def c1914 : List Lit := [(78, true), (77, true), (74, false)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c721, c308] c1914 (by decide) p (sat_cons (step721 p h) (sat_cons (step308 p h) (sat_nil p)))
end B112E097
