import B112E008Part0003
namespace B112E008
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1863 : List Lit := [(41, true), (38, false), (92, true), (47, true), (32, true)]
theorem step1863 (p : Nat → Bool) (h : Constraints p) : clause p c1863 = true :=
  Snake9.LocalRup.prove_clause [c768, c220] c1863 (by decide) p (sat_cons (step768 p h) (sat_cons (step220 p h) (sat_nil p)))
def c1864 : List Lit := [(32, true), (47, true), (39, true), (92, true), (38, false)]
theorem step1864 (p : Nat → Bool) (h : Constraints p) : clause p c1864 = true :=
  Snake9.LocalRup.prove_clause [c768, c221] c1864 (by decide) p (sat_cons (step768 p h) (sat_cons (step221 p h) (sat_nil p)))
def c1865 : List Lit := [(41, true), (39, true), (38, false), (32, true), (92, true)]
theorem step1865 (p : Nat → Bool) (h : Constraints p) : clause p c1865 = true :=
  Snake9.LocalRup.prove_clause [c768, c222] c1865 (by decide) p (sat_cons (step768 p h) (sat_cons (step222 p h) (sat_nil p)))
def c1866 : List Lit := [(41, true), (32, true), (39, true), (38, false), (47, true)]
theorem step1866 (p : Nat → Bool) (h : Constraints p) : clause p c1866 = true :=
  Snake9.LocalRup.prove_clause [c768, c223] c1866 (by decide) p (sat_cons (step768 p h) (sat_cons (step223 p h) (sat_nil p)))
def c1867 : List Lit := [(58, true), (40, false), (93, true), (49, true)]
theorem step1867 (p : Nat → Bool) (h : Constraints p) : clause p c1867 = true :=
  Snake9.LocalRup.prove_clause [c769, c247] c1867 (by decide) p (sat_cons (step769 p h) (sat_cons (step247 p h) (sat_nil p)))
def c1868 : List Lit := [(58, true), (40, false), (93, true), (39, true)]
theorem step1868 (p : Nat → Bool) (h : Constraints p) : clause p c1868 = true :=
  Snake9.LocalRup.prove_clause [c769, c248] c1868 (by decide) p (sat_cons (step769 p h) (sat_cons (step248 p h) (sat_nil p)))
def c1869 : List Lit := [(49, true), (39, true), (40, false), (93, true)]
theorem step1869 (p : Nat → Bool) (h : Constraints p) : clause p c1869 = true :=
  Snake9.LocalRup.prove_clause [c769, c249] c1869 (by decide) p (sat_cons (step769 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1870 : List Lit := [(58, true), (49, true), (39, true), (40, false)]
theorem step1870 (p : Nat → Bool) (h : Constraints p) : clause p c1870 = true :=
  Snake9.LocalRup.prove_clause [c769, c250] c1870 (by decide) p (sat_cons (step769 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1871 : List Lit := [(41, true), (39, true), (96, true), (42, false)]
theorem step1871 (p : Nat → Bool) (h : Constraints p) : clause p c1871 = true :=
  Snake9.LocalRup.prove_clause [c770, c264] c1871 (by decide) p (sat_cons (step770 p h) (sat_cons (step264 p h) (sat_nil p)))
def c1872 : List Lit := [(37, true), (41, true), (96, true), (42, false)]
theorem step1872 (p : Nat → Bool) (h : Constraints p) : clause p c1872 = true :=
  Snake9.LocalRup.prove_clause [c770, c265] c1872 (by decide) p (sat_cons (step770 p h) (sat_cons (step265 p h) (sat_nil p)))
def c1873 : List Lit := [(37, true), (39, true), (42, false), (96, true)]
theorem step1873 (p : Nat → Bool) (h : Constraints p) : clause p c1873 = true :=
  Snake9.LocalRup.prove_clause [c770, c266] c1873 (by decide) p (sat_cons (step770 p h) (sat_cons (step266 p h) (sat_nil p)))
def c1874 : List Lit := [(41, true), (37, true), (39, true), (42, false)]
theorem step1874 (p : Nat → Bool) (h : Constraints p) : clause p c1874 = true :=
  Snake9.LocalRup.prove_clause [c770, c267] c1874 (by decide) p (sat_cons (step770 p h) (sat_cons (step267 p h) (sat_nil p)))
def c1875 : List Lit := [(50, true), (44, false), (46, true)]
theorem step1875 (p : Nat → Bool) (h : Constraints p) : clause p c1875 = true :=
  Snake9.LocalRup.prove_clause [c771, c273] c1875 (by decide) p (sat_cons (step771 p h) (sat_cons (step273 p h) (sat_nil p)))
def c1876 : List Lit := [(50, true), (36, true), (44, false)]
theorem step1876 (p : Nat → Bool) (h : Constraints p) : clause p c1876 = true :=
  Snake9.LocalRup.prove_clause [c771, c274] c1876 (by decide) p (sat_cons (step771 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1877 : List Lit := [(36, true), (44, false), (46, true)]
theorem step1877 (p : Nat → Bool) (h : Constraints p) : clause p c1877 = true :=
  Snake9.LocalRup.prove_clause [c771, c275] c1877 (by decide) p (sat_cons (step771 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1878 : List Lit := [(45, false), (46, true), (43, true)]
theorem step1878 (p : Nat → Bool) (h : Constraints p) : clause p c1878 = true :=
  Snake9.LocalRup.prove_clause [c772, c277] c1878 (by decide) p (sat_cons (step772 p h) (sat_cons (step277 p h) (sat_nil p)))
def c1879 : List Lit := [(45, false), (37, true), (46, true)]
theorem step1879 (p : Nat → Bool) (h : Constraints p) : clause p c1879 = true :=
  Snake9.LocalRup.prove_clause [c772, c278] c1879 (by decide) p (sat_cons (step772 p h) (sat_cons (step278 p h) (sat_nil p)))
def c1880 : List Lit := [(37, true), (45, false), (43, true)]
theorem step1880 (p : Nat → Bool) (h : Constraints p) : clause p c1880 = true :=
  Snake9.LocalRup.prove_clause [c772, c279] c1880 (by decide) p (sat_cons (step772 p h) (sat_cons (step279 p h) (sat_nil p)))
def c1881 : List Lit := [(49, true), (50, true), (48, false)]
theorem step1881 (p : Nat → Bool) (h : Constraints p) : clause p c1881 = true :=
  Snake9.LocalRup.prove_clause [c773, c297] c1881 (by decide) p (sat_cons (step773 p h) (sat_cons (step297 p h) (sat_nil p)))
def c1882 : List Lit := [(50, true), (47, true), (48, false)]
theorem step1882 (p : Nat → Bool) (h : Constraints p) : clause p c1882 = true :=
  Snake9.LocalRup.prove_clause [c773, c298] c1882 (by decide) p (sat_cons (step773 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1883 : List Lit := [(49, true), (47, true), (48, false)]
theorem step1883 (p : Nat → Bool) (h : Constraints p) : clause p c1883 = true :=
  Snake9.LocalRup.prove_clause [c773, c299] c1883 (by decide) p (sat_cons (step773 p h) (sat_cons (step299 p h) (sat_nil p)))
def c1884 : List Lit := [(64, true), (55, true), (53, false), (58, true)]
theorem step1884 (p : Nat → Bool) (h : Constraints p) : clause p c1884 = true :=
  Snake9.LocalRup.prove_clause [c774, c337] c1884 (by decide) p (sat_cons (step774 p h) (sat_cons (step337 p h) (sat_nil p)))
def c1885 : List Lit := [(52, true), (58, true), (55, true), (53, false)]
theorem step1885 (p : Nat → Bool) (h : Constraints p) : clause p c1885 = true :=
  Snake9.LocalRup.prove_clause [c774, c338] c1885 (by decide) p (sat_cons (step774 p h) (sat_cons (step338 p h) (sat_nil p)))
def c1886 : List Lit := [(59, true), (54, false), (55, true)]
theorem step1886 (p : Nat → Bool) (h : Constraints p) : clause p c1886 = true :=
  Snake9.LocalRup.prove_clause [c775, c340] c1886 (by decide) p (sat_cons (step775 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1887 : List Lit := [(59, true), (54, false), (36, true)]
theorem step1887 (p : Nat → Bool) (h : Constraints p) : clause p c1887 = true :=
  Snake9.LocalRup.prove_clause [c775, c341] c1887 (by decide) p (sat_cons (step775 p h) (sat_cons (step341 p h) (sat_nil p)))
def c1888 : List Lit := [(54, false), (36, true), (55, true)]
theorem step1888 (p : Nat → Bool) (h : Constraints p) : clause p c1888 = true :=
  Snake9.LocalRup.prove_clause [c775, c342] c1888 (by decide) p (sat_cons (step775 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1889 : List Lit := [(59, true), (56, false), (58, true), (114, true)]
theorem step1889 (p : Nat → Bool) (h : Constraints p) : clause p c1889 = true :=
  Snake9.LocalRup.prove_clause [c776, c351] c1889 (by decide) p (sat_cons (step776 p h) (sat_cons (step351 p h) (sat_nil p)))
def c1890 : List Lit := [(22, true), (56, false), (58, true), (114, true)]
theorem step1890 (p : Nat → Bool) (h : Constraints p) : clause p c1890 = true :=
  Snake9.LocalRup.prove_clause [c776, c352] c1890 (by decide) p (sat_cons (step776 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1891 : List Lit := [(59, true), (22, true), (56, false), (58, true)]
theorem step1891 (p : Nat → Bool) (h : Constraints p) : clause p c1891 = true :=
  Snake9.LocalRup.prove_clause [c776, c353] c1891 (by decide) p (sat_cons (step776 p h) (sat_cons (step353 p h) (sat_nil p)))
def c1892 : List Lit := [(52, true), (57, false), (39, true), (58, true)]
theorem step1892 (p : Nat → Bool) (h : Constraints p) : clause p c1892 = true :=
  Snake9.LocalRup.prove_clause [c777, c357] c1892 (by decide) p (sat_cons (step777 p h) (sat_cons (step357 p h) (sat_nil p)))
def c1893 : List Lit := [(23, true), (57, false), (58, true), (52, true)]
theorem step1893 (p : Nat → Bool) (h : Constraints p) : clause p c1893 = true :=
  Snake9.LocalRup.prove_clause [c777, c358] c1893 (by decide) p (sat_cons (step777 p h) (sat_cons (step358 p h) (sat_nil p)))
def c1894 : List Lit := [(23, true), (58, true), (39, true), (57, false)]
theorem step1894 (p : Nat → Bool) (h : Constraints p) : clause p c1894 = true :=
  Snake9.LocalRup.prove_clause [c777, c359] c1894 (by decide) p (sat_cons (step777 p h) (sat_cons (step359 p h) (sat_nil p)))
def c1895 : List Lit := [(23, true), (57, false), (39, true), (52, true)]
theorem step1895 (p : Nat → Bool) (h : Constraints p) : clause p c1895 = true :=
  Snake9.LocalRup.prove_clause [c777, c360] c1895 (by decide) p (sat_cons (step777 p h) (sat_cons (step360 p h) (sat_nil p)))
def c1896 : List Lit := [(69, true), (59, true), (60, false), (58, true)]
theorem step1896 (p : Nat → Bool) (h : Constraints p) : clause p c1896 = true :=
  Snake9.LocalRup.prove_clause [c778, c385] c1896 (by decide) p (sat_cons (step778 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1897 : List Lit := [(69, true), (59, true), (60, false), (55, true)]
theorem step1897 (p : Nat → Bool) (h : Constraints p) : clause p c1897 = true :=
  Snake9.LocalRup.prove_clause [c778, c386] c1897 (by decide) p (sat_cons (step778 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1898 : List Lit := [(69, true), (58, true), (60, false), (55, true)]
theorem step1898 (p : Nat → Bool) (h : Constraints p) : clause p c1898 = true :=
  Snake9.LocalRup.prove_clause [c778, c387] c1898 (by decide) p (sat_cons (step778 p h) (sat_cons (step387 p h) (sat_nil p)))
def c1899 : List Lit := [(59, true), (58, true), (60, false), (55, true)]
theorem step1899 (p : Nat → Bool) (h : Constraints p) : clause p c1899 = true :=
  Snake9.LocalRup.prove_clause [c778, c388] c1899 (by decide) p (sat_cons (step778 p h) (sat_cons (step388 p h) (sat_nil p)))
def c1900 : List Lit := [(62, false), (64, true)]
theorem step1900 (p : Nat → Bool) (h : Constraints p) : clause p c1900 = true :=
  Snake9.LocalRup.prove_clause [c779, c391] c1900 (by decide) p (sat_cons (step779 p h) (sat_cons (step391 p h) (sat_nil p)))
def c1901 : List Lit := [(62, false), (61, true)]
theorem step1901 (p : Nat → Bool) (h : Constraints p) : clause p c1901 = true :=
  Snake9.LocalRup.prove_clause [c779, c392] c1901 (by decide) p (sat_cons (step779 p h) (sat_cons (step392 p h) (sat_nil p)))
def c1902 : List Lit := [(67, true), (118, true), (65, false)]
theorem step1902 (p : Nat → Bool) (h : Constraints p) : clause p c1902 = true :=
  Snake9.LocalRup.prove_clause [c780, c397] c1902 (by decide) p (sat_cons (step780 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1903 : List Lit := [(118, true), (61, true), (65, false)]
theorem step1903 (p : Nat → Bool) (h : Constraints p) : clause p c1903 = true :=
  Snake9.LocalRup.prove_clause [c780, c398] c1903 (by decide) p (sat_cons (step780 p h) (sat_cons (step398 p h) (sat_nil p)))
def c1904 : List Lit := [(68, false), (69, true)]
theorem step1904 (p : Nat → Bool) (h : Constraints p) : clause p c1904 = true :=
  Snake9.LocalRup.prove_clause [c782, c404] c1904 (by decide) p (sat_cons (step782 p h) (sat_cons (step404 p h) (sat_nil p)))
def c1905 : List Lit := [(68, false), (67, true)]
theorem step1905 (p : Nat → Bool) (h : Constraints p) : clause p c1905 = true :=
  Snake9.LocalRup.prove_clause [c782, c405] c1905 (by decide) p (sat_cons (step782 p h) (sat_cons (step405 p h) (sat_nil p)))
def c1906 : List Lit := [(70, true), (87, true), (71, false), (75, true)]
theorem step1906 (p : Nat → Bool) (h : Constraints p) : clause p c1906 = true :=
  Snake9.LocalRup.prove_clause [c783, c414] c1906 (by decide) p (sat_cons (step783 p h) (sat_cons (step414 p h) (sat_nil p)))
def c1907 : List Lit := [(75, true), (1, true), (87, true), (71, false)]
theorem step1907 (p : Nat → Bool) (h : Constraints p) : clause p c1907 = true :=
  Snake9.LocalRup.prove_clause [c783, c415] c1907 (by decide) p (sat_cons (step783 p h) (sat_cons (step415 p h) (sat_nil p)))
def c1908 : List Lit := [(1, true), (70, true), (71, false), (87, true)]
theorem step1908 (p : Nat → Bool) (h : Constraints p) : clause p c1908 = true :=
  Snake9.LocalRup.prove_clause [c783, c416] c1908 (by decide) p (sat_cons (step783 p h) (sat_cons (step416 p h) (sat_nil p)))
def c1909 : List Lit := [(1, true), (70, true), (75, true), (71, false)]
theorem step1909 (p : Nat → Bool) (h : Constraints p) : clause p c1909 = true :=
  Snake9.LocalRup.prove_clause [c783, c417] c1909 (by decide) p (sat_cons (step783 p h) (sat_cons (step417 p h) (sat_nil p)))
def c1910 : List Lit := [(91, true), (4, true), (73, false), (81, true)]
theorem step1910 (p : Nat → Bool) (h : Constraints p) : clause p c1910 = true :=
  Snake9.LocalRup.prove_clause [c784, c422] c1910 (by decide) p (sat_cons (step784 p h) (sat_cons (step422 p h) (sat_nil p)))
def c1911 : List Lit := [(76, true), (75, true), (74, false), (92, true)]
theorem step1911 (p : Nat → Bool) (h : Constraints p) : clause p c1911 = true :=
  Snake9.LocalRup.prove_clause [c785, c426] c1911 (by decide) p (sat_cons (step785 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1912 : List Lit := [(76, true), (70, true), (74, false), (92, true)]
theorem step1912 (p : Nat → Bool) (h : Constraints p) : clause p c1912 = true :=
  Snake9.LocalRup.prove_clause [c785, c427] c1912 (by decide) p (sat_cons (step785 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1913 : List Lit := [(70, true), (75, true), (92, true), (74, false)]
theorem step1913 (p : Nat → Bool) (h : Constraints p) : clause p c1913 = true :=
  Snake9.LocalRup.prove_clause [c785, c428] c1913 (by decide) p (sat_cons (step785 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1914 : List Lit := [(76, true), (96, true), (77, false)]
theorem step1914 (p : Nat → Bool) (h : Constraints p) : clause p c1914 = true :=
  Snake9.LocalRup.prove_clause [c786, c437] c1914 (by decide) p (sat_cons (step786 p h) (sat_cons (step437 p h) (sat_nil p)))
def c1915 : List Lit := [(72, true), (96, true), (77, false)]
theorem step1915 (p : Nat → Bool) (h : Constraints p) : clause p c1915 = true :=
  Snake9.LocalRup.prove_clause [c786, c438] c1915 (by decide) p (sat_cons (step786 p h) (sat_cons (step438 p h) (sat_nil p)))
def c1916 : List Lit := [(85, true), (81, true), (80, false)]
theorem step1916 (p : Nat → Bool) (h : Constraints p) : clause p c1916 = true :=
  Snake9.LocalRup.prove_clause [c787, c443] c1916 (by decide) p (sat_cons (step787 p h) (sat_cons (step443 p h) (sat_nil p)))
def c1917 : List Lit := [(85, true), (79, true), (80, false)]
theorem step1917 (p : Nat → Bool) (h : Constraints p) : clause p c1917 = true :=
  Snake9.LocalRup.prove_clause [c787, c444] c1917 (by decide) p (sat_cons (step787 p h) (sat_cons (step444 p h) (sat_nil p)))
def c1918 : List Lit := [(79, true), (81, true), (80, false)]
theorem step1918 (p : Nat → Bool) (h : Constraints p) : clause p c1918 = true :=
  Snake9.LocalRup.prove_clause [c787, c445] c1918 (by decide) p (sat_cons (step787 p h) (sat_cons (step445 p h) (sat_nil p)))
def c1919 : List Lit := [(84, true), (85, true), (82, false)]
theorem step1919 (p : Nat → Bool) (h : Constraints p) : clause p c1919 = true :=
  Snake9.LocalRup.prove_clause [c788, c449] c1919 (by decide) p (sat_cons (step788 p h) (sat_cons (step449 p h) (sat_nil p)))
def c1920 : List Lit := [(85, true), (75, true), (82, false)]
theorem step1920 (p : Nat → Bool) (h : Constraints p) : clause p c1920 = true :=
  Snake9.LocalRup.prove_clause [c788, c450] c1920 (by decide) p (sat_cons (step788 p h) (sat_cons (step450 p h) (sat_nil p)))
def c1921 : List Lit := [(84, true), (75, true), (82, false)]
theorem step1921 (p : Nat → Bool) (h : Constraints p) : clause p c1921 = true :=
  Snake9.LocalRup.prove_clause [c788, c451] c1921 (by decide) p (sat_cons (step788 p h) (sat_cons (step451 p h) (sat_nil p)))
def c1922 : List Lit := [(84, true), (78, true), (83, false), (104, true)]
theorem step1922 (p : Nat → Bool) (h : Constraints p) : clause p c1922 = true :=
  Snake9.LocalRup.prove_clause [c789, c453] c1922 (by decide) p (sat_cons (step789 p h) (sat_cons (step453 p h) (sat_nil p)))
def c1923 : List Lit := [(84, true), (15, true), (104, true), (83, false)]
theorem step1923 (p : Nat → Bool) (h : Constraints p) : clause p c1923 = true :=
  Snake9.LocalRup.prove_clause [c789, c454] c1923 (by decide) p (sat_cons (step789 p h) (sat_cons (step454 p h) (sat_nil p)))
def c1924 : List Lit := [(78, true), (15, true), (83, false), (104, true)]
theorem step1924 (p : Nat → Bool) (h : Constraints p) : clause p c1924 = true :=
  Snake9.LocalRup.prove_clause [c789, c455] c1924 (by decide) p (sat_cons (step789 p h) (sat_cons (step455 p h) (sat_nil p)))
def c1925 : List Lit := [(84, true), (78, true), (15, true), (83, false)]
theorem step1925 (p : Nat → Bool) (h : Constraints p) : clause p c1925 = true :=
  Snake9.LocalRup.prove_clause [c789, c456] c1925 (by decide) p (sat_cons (step789 p h) (sat_cons (step456 p h) (sat_nil p)))
def c1926 : List Lit := [(70, true), (32, true), (86, false), (88, true), (87, true), (92, true), (98, true)]
theorem step1926 (p : Nat → Bool) (h : Constraints p) : clause p c1926 = true :=
  Snake9.LocalRup.prove_clause [c790, c472] c1926 (by decide) p (sat_cons (step790 p h) (sat_cons (step472 p h) (sat_nil p)))
end B112E008
