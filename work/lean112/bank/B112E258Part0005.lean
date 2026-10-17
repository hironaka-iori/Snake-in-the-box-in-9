import B112E258Part0004
namespace B112E258
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1818 : List Lit := [(27, true), (32, true), (33, false)]
theorem step1818 (p : Nat → Bool) (h : Constraints p) : clause p c1818 = true :=
  Snake9.LocalRup.prove_clause [c653, c202] c1818 (by decide) p (sat_cons (step653 p h) (sat_cons (step202 p h) (sat_nil p)))
def c1819 : List Lit := [(35, false), (34, true), (95, true)]
theorem step1819 (p : Nat → Bool) (h : Constraints p) : clause p c1819 = true :=
  Snake9.LocalRup.prove_clause [c654, c206] c1819 (by decide) p (sat_cons (step654 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1820 : List Lit := [(16, true), (35, false), (95, true)]
theorem step1820 (p : Nat → Bool) (h : Constraints p) : clause p c1820 = true :=
  Snake9.LocalRup.prove_clause [c654, c207] c1820 (by decide) p (sat_cons (step654 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1821 : List Lit := [(16, true), (35, false), (34, true)]
theorem step1821 (p : Nat → Bool) (h : Constraints p) : clause p c1821 = true :=
  Snake9.LocalRup.prove_clause [c654, c208] c1821 (by decide) p (sat_cons (step654 p h) (sat_cons (step208 p h) (sat_nil p)))
def c1822 : List Lit := [(37, false), (36, true), (97, true)]
theorem step1822 (p : Nat → Bool) (h : Constraints p) : clause p c1822 = true :=
  Snake9.LocalRup.prove_clause [c655, c212] c1822 (by decide) p (sat_cons (step655 p h) (sat_cons (step212 p h) (sat_nil p)))
def c1823 : List Lit := [(27, true), (37, false), (97, true)]
theorem step1823 (p : Nat → Bool) (h : Constraints p) : clause p c1823 = true :=
  Snake9.LocalRup.prove_clause [c655, c213] c1823 (by decide) p (sat_cons (step655 p h) (sat_cons (step213 p h) (sat_nil p)))
def c1824 : List Lit := [(27, true), (37, false), (36, true)]
theorem step1824 (p : Nat → Bool) (h : Constraints p) : clause p c1824 = true :=
  Snake9.LocalRup.prove_clause [c655, c214] c1824 (by decide) p (sat_cons (step655 p h) (sat_cons (step214 p h) (sat_nil p)))
def c1825 : List Lit := [(39, false), (38, true)]
theorem step1825 (p : Nat → Bool) (h : Constraints p) : clause p c1825 = true :=
  Snake9.LocalRup.prove_clause [c656, c218] c1825 (by decide) p (sat_cons (step656 p h) (sat_cons (step218 p h) (sat_nil p)))
def c1826 : List Lit := [(39, false), (20, true)]
theorem step1826 (p : Nat → Bool) (h : Constraints p) : clause p c1826 = true :=
  Snake9.LocalRup.prove_clause [c656, c219] c1826 (by decide) p (sat_cons (step656 p h) (sat_cons (step219 p h) (sat_nil p)))
def c1827 : List Lit := [(40, true), (101, true), (41, false)]
theorem step1827 (p : Nat → Bool) (h : Constraints p) : clause p c1827 = true :=
  Snake9.LocalRup.prove_clause [c657, c223] c1827 (by decide) p (sat_cons (step657 p h) (sat_cons (step223 p h) (sat_nil p)))
def c1828 : List Lit := [(101, true), (41, false), (23, true)]
theorem step1828 (p : Nat → Bool) (h : Constraints p) : clause p c1828 = true :=
  Snake9.LocalRup.prove_clause [c657, c224] c1828 (by decide) p (sat_cons (step657 p h) (sat_cons (step224 p h) (sat_nil p)))
def c1829 : List Lit := [(40, true), (41, false), (23, true)]
theorem step1829 (p : Nat → Bool) (h : Constraints p) : clause p c1829 = true :=
  Snake9.LocalRup.prove_clause [c657, c225] c1829 (by decide) p (sat_cons (step657 p h) (sat_cons (step225 p h) (sat_nil p)))
def c1830 : List Lit := [(53, true), (42, true), (1, true), (43, false), (46, true)]
theorem step1830 (p : Nat → Bool) (h : Constraints p) : clause p c1830 = true :=
  Snake9.LocalRup.prove_clause [c658, c233] c1830 (by decide) p (sat_cons (step658 p h) (sat_cons (step233 p h) (sat_nil p)))
def c1831 : List Lit := [(42, true), (1, true), (46, true), (6, true), (43, false)]
theorem step1831 (p : Nat → Bool) (h : Constraints p) : clause p c1831 = true :=
  Snake9.LocalRup.prove_clause [c658, c234] c1831 (by decide) p (sat_cons (step658 p h) (sat_cons (step234 p h) (sat_nil p)))
def c1832 : List Lit := [(46, false), (43, false), (15, false)]
theorem step1832 (p : Nat → Bool) (h : Constraints p) : clause p c1832 = true :=
  Snake9.LocalRup.prove_clause [c242, c238] c1832 (by decide) p (sat_cons (step242 p h) (sat_cons (step238 p h) (sat_nil p)))
def c1833 : List Lit := [(168, false), (43, false)]
theorem step1833 (p : Nat → Bool) (h : Constraints p) : clause p c1833 = true :=
  Snake9.LocalRup.prove_clause [c242, c239] c1833 (by decide) p (sat_cons (step242 p h) (sat_cons (step239 p h) (sat_nil p)))
def c1834 : List Lit := [(46, true), (106, true)]
theorem step1834 (p : Nat → Bool) (h : Constraints p) : clause p c1834 = true :=
  Snake9.LocalRup.prove_clause [c242, c241] c1834 (by decide) p (sat_cons (step242 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1835 : List Lit := [(44, true), (48, false), (170, true)]
theorem step1835 (p : Nat → Bool) (h : Constraints p) : clause p c1835 = true :=
  Snake9.LocalRup.prove_clause [c1499, c244] c1835 (by decide) p (sat_cons (step1499 p h) (sat_cons (step244 p h) (sat_nil p)))
def c1836 : List Lit := [(50, false), (62, true)]
theorem step1836 (p : Nat → Bool) (h : Constraints p) : clause p c1836 = true :=
  Snake9.LocalRup.prove_clause [c660, c248] c1836 (by decide) p (sat_cons (step660 p h) (sat_cons (step248 p h) (sat_nil p)))
def c1837 : List Lit := [(50, false), (48, true)]
theorem step1837 (p : Nat → Bool) (h : Constraints p) : clause p c1837 = true :=
  Snake9.LocalRup.prove_clause [c660, c249] c1837 (by decide) p (sat_cons (step660 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1838 : List Lit := [(109, true), (23, true), (51, false)]
theorem step1838 (p : Nat → Bool) (h : Constraints p) : clause p c1838 = true :=
  Snake9.LocalRup.prove_clause [c661, c251] c1838 (by decide) p (sat_cons (step661 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1839 : List Lit := [(49, true), (23, true), (51, false)]
theorem step1839 (p : Nat → Bool) (h : Constraints p) : clause p c1839 = true :=
  Snake9.LocalRup.prove_clause [c661, c252] c1839 (by decide) p (sat_cons (step661 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1840 : List Lit := [(55, false), (54, true)]
theorem step1840 (p : Nat → Bool) (h : Constraints p) : clause p c1840 = true :=
  Snake9.LocalRup.prove_clause [c663, c263] c1840 (by decide) p (sat_cons (step663 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1841 : List Lit := [(55, false), (53, true)]
theorem step1841 (p : Nat → Bool) (h : Constraints p) : clause p c1841 = true :=
  Snake9.LocalRup.prove_clause [c663, c264] c1841 (by decide) p (sat_cons (step663 p h) (sat_cons (step264 p h) (sat_nil p)))
def c1842 : List Lit := [(54, true), (57, true), (58, false), (114, true)]
theorem step1842 (p : Nat → Bool) (h : Constraints p) : clause p c1842 = true :=
  Snake9.LocalRup.prove_clause [c664, c270] c1842 (by decide) p (sat_cons (step664 p h) (sat_cons (step270 p h) (sat_nil p)))
def c1843 : List Lit := [(45, true), (54, true), (58, false), (57, true)]
theorem step1843 (p : Nat → Bool) (h : Constraints p) : clause p c1843 = true :=
  Snake9.LocalRup.prove_clause [c664, c271] c1843 (by decide) p (sat_cons (step664 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1844 : List Lit := [(61, false), (60, true)]
theorem step1844 (p : Nat → Bool) (h : Constraints p) : clause p c1844 = true :=
  Snake9.LocalRup.prove_clause [c665, c276] c1844 (by decide) p (sat_cons (step665 p h) (sat_cons (step276 p h) (sat_nil p)))
def c1845 : List Lit := [(61, false), (49, true)]
theorem step1845 (p : Nat → Bool) (h : Constraints p) : clause p c1845 = true :=
  Snake9.LocalRup.prove_clause [c665, c277] c1845 (by decide) p (sat_cons (step665 p h) (sat_cons (step277 p h) (sat_nil p)))
def c1846 : List Lit := [(63, false), (122, true)]
theorem step1846 (p : Nat → Bool) (h : Constraints p) : clause p c1846 = true :=
  Snake9.LocalRup.prove_clause [c666, c281] c1846 (by decide) p (sat_cons (step666 p h) (sat_cons (step281 p h) (sat_nil p)))
def c1847 : List Lit := [(63, false), (62, true)]
theorem step1847 (p : Nat → Bool) (h : Constraints p) : clause p c1847 = true :=
  Snake9.LocalRup.prove_clause [c666, c282] c1847 (by decide) p (sat_cons (step666 p h) (sat_cons (step282 p h) (sat_nil p)))
def c1848 : List Lit := [(68, true), (74, true), (65, false), (64, true)]
theorem step1848 (p : Nat → Bool) (h : Constraints p) : clause p c1848 = true :=
  Snake9.LocalRup.prove_clause [c667, c305] c1848 (by decide) p (sat_cons (step667 p h) (sat_cons (step305 p h) (sat_nil p)))
def c1849 : List Lit := [(6, true), (74, true), (65, false), (68, true)]
theorem step1849 (p : Nat → Bool) (h : Constraints p) : clause p c1849 = true :=
  Snake9.LocalRup.prove_clause [c667, c306] c1849 (by decide) p (sat_cons (step667 p h) (sat_cons (step306 p h) (sat_nil p)))
def c1850 : List Lit := [(6, true), (74, true), (65, false), (64, true)]
theorem step1850 (p : Nat → Bool) (h : Constraints p) : clause p c1850 = true :=
  Snake9.LocalRup.prove_clause [c667, c307] c1850 (by decide) p (sat_cons (step667 p h) (sat_cons (step307 p h) (sat_nil p)))
def c1851 : List Lit := [(6, true), (68, true), (65, false), (64, true)]
theorem step1851 (p : Nat → Bool) (h : Constraints p) : clause p c1851 = true :=
  Snake9.LocalRup.prove_clause [c667, c308] c1851 (by decide) p (sat_cons (step667 p h) (sat_cons (step308 p h) (sat_nil p)))
def c1852 : List Lit := [(70, true), (66, false), (64, true), (83, true)]
theorem step1852 (p : Nat → Bool) (h : Constraints p) : clause p c1852 = true :=
  Snake9.LocalRup.prove_clause [c668, c311] c1852 (by decide) p (sat_cons (step668 p h) (sat_cons (step311 p h) (sat_nil p)))
def c1853 : List Lit := [(7, true), (70, true), (66, false), (83, true)]
theorem step1853 (p : Nat → Bool) (h : Constraints p) : clause p c1853 = true :=
  Snake9.LocalRup.prove_clause [c668, c312] c1853 (by decide) p (sat_cons (step668 p h) (sat_cons (step312 p h) (sat_nil p)))
def c1854 : List Lit := [(7, true), (66, false), (83, true), (64, true)]
theorem step1854 (p : Nat → Bool) (h : Constraints p) : clause p c1854 = true :=
  Snake9.LocalRup.prove_clause [c668, c313] c1854 (by decide) p (sat_cons (step668 p h) (sat_cons (step313 p h) (sat_nil p)))
def c1855 : List Lit := [(7, true), (70, true), (66, false), (64, true)]
theorem step1855 (p : Nat → Bool) (h : Constraints p) : clause p c1855 = true :=
  Snake9.LocalRup.prove_clause [c668, c314] c1855 (by decide) p (sat_cons (step668 p h) (sat_cons (step314 p h) (sat_nil p)))
def c1856 : List Lit := [(71, true), (103, true), (75, true), (64, true), (67, false)]
theorem step1856 (p : Nat → Bool) (h : Constraints p) : clause p c1856 = true :=
  Snake9.LocalRup.prove_clause [c669, c322] c1856 (by decide) p (sat_cons (step669 p h) (sat_cons (step322 p h) (sat_nil p)))
def c1857 : List Lit := [(75, true), (68, true), (103, true), (64, true), (67, false)]
theorem step1857 (p : Nat → Bool) (h : Constraints p) : clause p c1857 = true :=
  Snake9.LocalRup.prove_clause [c669, c323] c1857 (by decide) p (sat_cons (step669 p h) (sat_cons (step323 p h) (sat_nil p)))
def c1858 : List Lit := [(71, true), (68, true), (103, true), (64, true), (67, false)]
theorem step1858 (p : Nat → Bool) (h : Constraints p) : clause p c1858 = true :=
  Snake9.LocalRup.prove_clause [c669, c324] c1858 (by decide) p (sat_cons (step669 p h) (sat_cons (step324 p h) (sat_nil p)))
def c1859 : List Lit := [(71, true), (75, true), (64, true), (67, false), (68, true)]
theorem step1859 (p : Nat → Bool) (h : Constraints p) : clause p c1859 = true :=
  Snake9.LocalRup.prove_clause [c669, c325] c1859 (by decide) p (sat_cons (step669 p h) (sat_cons (step325 p h) (sat_nil p)))
def c1860 : List Lit := [(72, true), (76, true), (69, false), (68, true)]
theorem step1860 (p : Nat → Bool) (h : Constraints p) : clause p c1860 = true :=
  Snake9.LocalRup.prove_clause [c670, c339] c1860 (by decide) p (sat_cons (step670 p h) (sat_cons (step339 p h) (sat_nil p)))
def c1861 : List Lit := [(9, true), (76, true), (69, false), (72, true)]
theorem step1861 (p : Nat → Bool) (h : Constraints p) : clause p c1861 = true :=
  Snake9.LocalRup.prove_clause [c670, c340] c1861 (by decide) p (sat_cons (step670 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1862 : List Lit := [(9, true), (76, true), (69, false), (68, true)]
theorem step1862 (p : Nat → Bool) (h : Constraints p) : clause p c1862 = true :=
  Snake9.LocalRup.prove_clause [c670, c341] c1862 (by decide) p (sat_cons (step670 p h) (sat_cons (step341 p h) (sat_nil p)))
def c1863 : List Lit := [(9, true), (72, true), (69, false), (68, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c670, c342] c1863 (by decide) p (sat_cons (step670 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1864 : List Lit := [(74, true), (73, false), (75, true), (64, true)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c671, c361] c1864 (by decide) p (sat_cons (step671 p h) (sat_cons (step361 p h) (sat_nil p)))
def c1865 : List Lit := [(74, true), (73, false), (14, true), (75, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c671, c362] c1865 (by decide) p (sat_cons (step671 p h) (sat_cons (step362 p h) (sat_nil p)))
def c1866 : List Lit := [(14, true), (73, false), (75, true), (64, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c671, c363] c1866 (by decide) p (sat_cons (step671 p h) (sat_cons (step363 p h) (sat_nil p)))
def c1867 : List Lit := [(74, true), (14, true), (73, false), (64, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c671, c364] c1867 (by decide) p (sat_cons (step671 p h) (sat_cons (step364 p h) (sat_nil p)))
def c1868 : List Lit := [(77, false), (74, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c672, c390] c1868 (by decide) p (sat_cons (step672 p h) (sat_cons (step390 p h) (sat_nil p)))
def c1869 : List Lit := [(77, false), (19, true)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c672, c391] c1869 (by decide) p (sat_cons (step672 p h) (sat_cons (step391 p h) (sat_nil p)))
def c1870 : List Lit := [(70, true), (80, true), (78, false)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c673, c393] c1870 (by decide) p (sat_cons (step673 p h) (sat_cons (step393 p h) (sat_nil p)))
def c1871 : List Lit := [(20, true), (80, true), (78, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c673, c394] c1871 (by decide) p (sat_cons (step673 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1872 : List Lit := [(70, true), (20, true), (78, false)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c673, c395] c1872 (by decide) p (sat_cons (step673 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1873 : List Lit := [(100, true), (80, true), (75, true), (79, false)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c674, c399] c1873 (by decide) p (sat_cons (step674 p h) (sat_cons (step399 p h) (sat_nil p)))
def c1874 : List Lit := [(100, true), (80, true), (79, false), (71, true)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c674, c400] c1874 (by decide) p (sat_cons (step674 p h) (sat_cons (step400 p h) (sat_nil p)))
def c1875 : List Lit := [(100, true), (79, false), (71, true), (75, true)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c674, c401] c1875 (by decide) p (sat_cons (step674 p h) (sat_cons (step401 p h) (sat_nil p)))
def c1876 : List Lit := [(80, true), (79, false), (75, true), (71, true)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c674, c402] c1876 (by decide) p (sat_cons (step674 p h) (sat_cons (step402 p h) (sat_nil p)))
def c1877 : List Lit := [(87, true), (110, true), (82, false), (64, true), (83, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c676, c430] c1877 (by decide) p (sat_cons (step676 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1878 : List Lit := [(24, true), (110, true), (87, true), (82, false), (83, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c676, c431] c1878 (by decide) p (sat_cons (step676 p h) (sat_cons (step431 p h) (sat_nil p)))
def c1879 : List Lit := [(24, true), (110, true), (87, true), (82, false), (64, true)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c676, c432] c1879 (by decide) p (sat_cons (step676 p h) (sat_cons (step432 p h) (sat_nil p)))
def c1880 : List Lit := [(24, true), (110, true), (64, true), (83, true), (82, false)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c676, c433] c1880 (by decide) p (sat_cons (step676 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1881 : List Lit := [(24, true), (82, false), (64, true), (87, true), (83, true)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c676, c434] c1881 (by decide) p (sat_cons (step676 p h) (sat_cons (step434 p h) (sat_nil p)))
end B112E258
