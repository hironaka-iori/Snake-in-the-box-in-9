import B112E260Part0002
namespace B112E260
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2295 : List Lit := [(1534, false), (4, true), (39, true), (1672, true), (121, false)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c2235, c1755, c2283, c2187, c2292, c2291, c2293, c2294, c1796, c2203, c35, c2207, c2183, c1952, c2180, c1801, c2287, c2157, c2178] c2295 (by decide) p (sat_cons (step2235 p h) (sat_cons (step1755 p h) (sat_cons (step2283 p h) (sat_cons (step2187 p h) (sat_cons (step2292 p h) (sat_cons (step2291 p h) (sat_cons (step2293 p h) (sat_cons (step2294 p h) (sat_cons (step1796 p h) (sat_cons (step2203 p h) (sat_cons (step35 p h) (sat_cons (step2207 p h) (sat_cons (step2183 p h) (sat_cons (step1952 p h) (sat_cons (step2180 p h) (sat_cons (step1801 p h) (sat_cons (step2287 p h) (sat_cons (step2157 p h) (sat_cons (step2178 p h) (sat_nil p))))))))))))))))))))
def c2296 : List Lit := [(1571, true), (8, false), (9, false), (3, false), (4, true), (1621, false), (39, true), (1652, true), (121, false)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c2294, c2193, c2273, c2203, c35, c1853, c1918, c2259, c1856, c1945, c1881] c2296 (by decide) p (sat_cons (step2294 p h) (sat_cons (step2193 p h) (sat_cons (step2273 p h) (sat_cons (step2203 p h) (sat_cons (step35 p h) (sat_cons (step1853 p h) (sat_cons (step1918 p h) (sat_cons (step2259 p h) (sat_cons (step1856 p h) (sat_cons (step1945 p h) (sat_cons (step1881 p h) (sat_nil p))))))))))))
def c2297 : List Lit := [(1611, false), (1571, false), (1533, false), (1638, false), (1672, true), (1632, false)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c1782, c1832, c1951, c1939, c1938, c1919, c1952, c2172, c1836, c1783] c2297 (by decide) p (sat_cons (step1782 p h) (sat_cons (step1832 p h) (sat_cons (step1951 p h) (sat_cons (step1939 p h) (sat_cons (step1938 p h) (sat_cons (step1919 p h) (sat_cons (step1952 p h) (sat_cons (step2172 p h) (sat_cons (step1836 p h) (sat_cons (step1783 p h) (sat_nil p)))))))))))
def c2298 : List Lit := [(4, true), (39, true), (1672, true), (121, false)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c2170, c823, c821, c2187, c2283, c1894, c1917, c2235, c1950, c1753, c1755, c1761, c2295, c1762, c1756, c1757, c2293, c1876, c1933, c1953, c2296, c1840, c1784, c1774, c2297, c1877, c2259, c34, c1771, c1772, c1773, c1776, c146, c1783, c1767, c1768, c1836, c134, c1952, c1934, c1919, c1896, c1895, c1890, c1891, c72, c374, c126] c2298 (by decide) p (sat_cons (step2170 p h) (sat_cons (step823 p h) (sat_cons (step821 p h) (sat_cons (step2187 p h) (sat_cons (step2283 p h) (sat_cons (step1894 p h) (sat_cons (step1917 p h) (sat_cons (step2235 p h) (sat_cons (step1950 p h) (sat_cons (step1753 p h) (sat_cons (step1755 p h) (sat_cons (step1761 p h) (sat_cons (step2295 p h) (sat_cons (step1762 p h) (sat_cons (step1756 p h) (sat_cons (step1757 p h) (sat_cons (step2293 p h) (sat_cons (step1876 p h) (sat_cons (step1933 p h) (sat_cons (step1953 p h) (sat_cons (step2296 p h) (sat_cons (step1840 p h) (sat_cons (step1784 p h) (sat_cons (step1774 p h) (sat_cons (step2297 p h) (sat_cons (step1877 p h) (sat_cons (step2259 p h) (sat_cons (step34 p h) (sat_cons (step1771 p h) (sat_cons (step1772 p h) (sat_cons (step1773 p h) (sat_cons (step1776 p h) (sat_cons (step146 p h) (sat_cons (step1783 p h) (sat_cons (step1767 p h) (sat_cons (step1768 p h) (sat_cons (step1836 p h) (sat_cons (step134 p h) (sat_cons (step1952 p h) (sat_cons (step1934 p h) (sat_cons (step1919 p h) (sat_cons (step1896 p h) (sat_cons (step1895 p h) (sat_cons (step1890 p h) (sat_cons (step1891 p h) (sat_cons (step72 p h) (sat_cons (step374 p h) (sat_cons (step126 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c2299 : List Lit := [(14, true), (54, false), (1618, true), (1542, true)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c823, c821, c1774, c1771, c1772, c1776, c146, c1767, c1768, c134, c1890, c72, c374, c126] c2299 (by decide) p (sat_cons (step823 p h) (sat_cons (step821 p h) (sat_cons (step1774 p h) (sat_cons (step1771 p h) (sat_cons (step1772 p h) (sat_cons (step1776 p h) (sat_cons (step146 p h) (sat_cons (step1767 p h) (sat_cons (step1768 p h) (sat_cons (step134 p h) (sat_cons (step1890 p h) (sat_cons (step72 p h) (sat_cons (step374 p h) (sat_cons (step126 p h) (sat_nil p)))))))))))))))
def c2300 : List Lit := [(11, false), (14, false), (37, false), (38, false), (1572, true), (58, false), (5, true), (3, false), (4, false)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c822, c816, c131, c271, c2, c120, c25, c1808, c151, c1810, c1796, c1825, c2159, c1802, c2243, c1823, c2157, c155, c1811, c1809] c2300 (by decide) p (sat_cons (step822 p h) (sat_cons (step816 p h) (sat_cons (step131 p h) (sat_cons (step271 p h) (sat_cons (step2 p h) (sat_cons (step120 p h) (sat_cons (step25 p h) (sat_cons (step1808 p h) (sat_cons (step151 p h) (sat_cons (step1810 p h) (sat_cons (step1796 p h) (sat_cons (step1825 p h) (sat_cons (step2159 p h) (sat_cons (step1802 p h) (sat_cons (step2243 p h) (sat_cons (step1823 p h) (sat_cons (step2157 p h) (sat_cons (step155 p h) (sat_cons (step1811 p h) (sat_cons (step1809 p h) (sat_nil p)))))))))))))))))))))
def c2301 : List Lit := [(19, false), (21, false), (1566, true), (4, false)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c155, c154, c1807, c1804, c1813] c2301 (by decide) p (sat_cons (step155 p h) (sat_cons (step154 p h) (sat_cons (step1807 p h) (sat_cons (step1804 p h) (sat_cons (step1813 p h) (sat_nil p))))))
def c2302 : List Lit := [(21, false), (1555, false), (1572, true), (4, false)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c2159, c1823, c2301, c2157, c1802, c2255, c1825, c1804, c1812] c2302 (by decide) p (sat_cons (step2159 p h) (sat_cons (step1823 p h) (sat_cons (step2301 p h) (sat_cons (step2157 p h) (sat_cons (step1802 p h) (sat_cons (step2255 p h) (sat_cons (step1825 p h) (sat_cons (step1804 p h) (sat_cons (step1812 p h) (sat_nil p))))))))))
def c2303 : List Lit := [(22, true), (38, false), (1572, true), (58, false), (8, false), (5, true), (3, false), (4, false)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c829, c1828, c1796, c2302, c2178, c2243, c2157, c1825, c1803, c1812, c1797, c1804, c197, c205] c2303 (by decide) p (sat_cons (step829 p h) (sat_cons (step1828 p h) (sat_cons (step1796 p h) (sat_cons (step2302 p h) (sat_cons (step2178 p h) (sat_cons (step2243 p h) (sat_cons (step2157 p h) (sat_cons (step1825 p h) (sat_cons (step1803 p h) (sat_cons (step1812 p h) (sat_cons (step1797 p h) (sat_cons (step1804 p h) (sat_cons (step197 p h) (sat_cons (step205 p h) (sat_nil p)))))))))))))))
def c2304 : List Lit := [(1639, true), (9, false), (3, false), (1571, false), (39, true), (1672, true), (121, false)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c826, c2187, c2283, c1894, c1917, c2298, c29, c2259, c1877, c2297, c1759, c1757, c1938, c1952, c1919, c1918, c2172, c2185, c1779, c1832, c1833, c1951, c2164, c1944, c1881, c1856, c1853, c2303, c151, c171, c156, c157, c1804, c1807, c2244, c1816, c1806] c2304 (by decide) p (sat_cons (step826 p h) (sat_cons (step2187 p h) (sat_cons (step2283 p h) (sat_cons (step1894 p h) (sat_cons (step1917 p h) (sat_cons (step2298 p h) (sat_cons (step29 p h) (sat_cons (step2259 p h) (sat_cons (step1877 p h) (sat_cons (step2297 p h) (sat_cons (step1759 p h) (sat_cons (step1757 p h) (sat_cons (step1938 p h) (sat_cons (step1952 p h) (sat_cons (step1919 p h) (sat_cons (step1918 p h) (sat_cons (step2172 p h) (sat_cons (step2185 p h) (sat_cons (step1779 p h) (sat_cons (step1832 p h) (sat_cons (step1833 p h) (sat_cons (step1951 p h) (sat_cons (step2164 p h) (sat_cons (step1944 p h) (sat_cons (step1881 p h) (sat_cons (step1856 p h) (sat_cons (step1853 p h) (sat_cons (step2303 p h) (sat_cons (step151 p h) (sat_cons (step171 p h) (sat_cons (step156 p h) (sat_cons (step157 p h) (sat_cons (step1804 p h) (sat_cons (step1807 p h) (sat_cons (step2244 p h) (sat_cons (step1816 p h) (sat_cons (step1806 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c2305 : List Lit := [(9, false), (3, false), (1571, false), (39, true), (1672, true), (121, false)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c2170, c2298, c1950, c29, c2259, c1877, c1940, c2304, c1945, c1939, c1881, c1951, c1856, c1830, c1832, c1853, c1854, c1779, c1773, c1775, c2172, c1771, c1768, c1920, c2300, c2185] c2305 (by decide) p (sat_cons (step2170 p h) (sat_cons (step2298 p h) (sat_cons (step1950 p h) (sat_cons (step29 p h) (sat_cons (step2259 p h) (sat_cons (step1877 p h) (sat_cons (step1940 p h) (sat_cons (step2304 p h) (sat_cons (step1945 p h) (sat_cons (step1939 p h) (sat_cons (step1881 p h) (sat_cons (step1951 p h) (sat_cons (step1856 p h) (sat_cons (step1830 p h) (sat_cons (step1832 p h) (sat_cons (step1853 p h) (sat_cons (step1854 p h) (sat_cons (step1779 p h) (sat_cons (step1773 p h) (sat_cons (step1775 p h) (sat_cons (step2172 p h) (sat_cons (step1771 p h) (sat_cons (step1768 p h) (sat_cons (step1920 p h) (sat_cons (step2300 p h) (sat_cons (step2185 p h) (sat_nil p)))))))))))))))))))))))))))
def c2306 : List Lit := [(1633, true), (5, true), (1572, true), (38, false), (8, false), (3, false), (4, false), (121, false)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c826, c2164, c2185, c2303, c151, c171, c156, c157, c1804, c1807, c2244, c1816, c1806] c2306 (by decide) p (sat_cons (step826 p h) (sat_cons (step2164 p h) (sat_cons (step2185 p h) (sat_cons (step2303 p h) (sat_cons (step151 p h) (sat_cons (step171 p h) (sat_cons (step156 p h) (sat_cons (step157 p h) (sat_cons (step1804 p h) (sat_cons (step1807 p h) (sat_cons (step2244 p h) (sat_cons (step1816 p h) (sat_cons (step1806 p h) (sat_nil p))))))))))))))
def c2307 : List Lit := [(1633, false), (1533, false), (1606, false), (1571, false), (1672, true)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c1876, c1782, c1832, c1951, c1935, c2183, c1920, c1952, c2172, c1836, c1783] c2307 (by decide) p (sat_cons (step1876 p h) (sat_cons (step1782 p h) (sat_cons (step1832 p h) (sat_cons (step1951 p h) (sat_cons (step1935 p h) (sat_cons (step2183 p h) (sat_cons (step1920 p h) (sat_cons (step1952 p h) (sat_cons (step2172 p h) (sat_cons (step1836 p h) (sat_cons (step1783 p h) (sat_nil p))))))))))))
def c2308 : List Lit := [(14, true), (1533, false), (1610, false), (1571, false), (1617, false), (1672, true), (1632, false)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c1894, c1917, c1933, c1953, c1840, c1784, c1771, c1773, c1783, c1836, c1952, c1934, c1919, c1896, c1895, c2299, c1891] c2308 (by decide) p (sat_cons (step1894 p h) (sat_cons (step1917 p h) (sat_cons (step1933 p h) (sat_cons (step1953 p h) (sat_cons (step1840 p h) (sat_cons (step1784 p h) (sat_cons (step1771 p h) (sat_cons (step1773 p h) (sat_cons (step1783 p h) (sat_cons (step1836 p h) (sat_cons (step1952 p h) (sat_cons (step1934 p h) (sat_cons (step1919 p h) (sat_cons (step1896 p h) (sat_cons (step1895 p h) (sat_cons (step2299 p h) (sat_cons (step1891 p h) (sat_nil p))))))))))))))))))
def c2309 : List Lit := [(3, false), (1571, false), (39, true), (1672, true), (121, false)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c2298, c2187, c2283, c1894, c1917, c2272, c2292, c1876, c1760, c1933, c1953, c2305, c1756, c1758, c1759, c1782, c2297, c1880, c1856, c1853, c2307, c2308, c30, c2306, c1833, c1837, c1952, c1783, c1934, c2172, c1919] c2309 (by decide) p (sat_cons (step2298 p h) (sat_cons (step2187 p h) (sat_cons (step2283 p h) (sat_cons (step1894 p h) (sat_cons (step1917 p h) (sat_cons (step2272 p h) (sat_cons (step2292 p h) (sat_cons (step1876 p h) (sat_cons (step1760 p h) (sat_cons (step1933 p h) (sat_cons (step1953 p h) (sat_cons (step2305 p h) (sat_cons (step1756 p h) (sat_cons (step1758 p h) (sat_cons (step1759 p h) (sat_cons (step1782 p h) (sat_cons (step2297 p h) (sat_cons (step1880 p h) (sat_cons (step1856 p h) (sat_cons (step1853 p h) (sat_cons (step2307 p h) (sat_cons (step2308 p h) (sat_cons (step30 p h) (sat_cons (step2306 p h) (sat_cons (step1833 p h) (sat_cons (step1837 p h) (sat_cons (step1952 p h) (sat_cons (step1783 p h) (sat_cons (step1934 p h) (sat_cons (step2172 p h) (sat_cons (step1919 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2310 : List Lit := [(5, true), (1571, false), (39, true), (1672, true), (121, false)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c837, c2187, c2283, c1894, c1917, c2309, c1754, c1761, c2297, c1877, c1862, c1869, c2259, c1756, c1762, c2189, c2186, c1876, c1879, c2185, c1872, c1870, c1856, c1863, c1864, c1865, c1854, c278, c291, c335] c2310 (by decide) p (sat_cons (step837 p h) (sat_cons (step2187 p h) (sat_cons (step2283 p h) (sat_cons (step1894 p h) (sat_cons (step1917 p h) (sat_cons (step2309 p h) (sat_cons (step1754 p h) (sat_cons (step1761 p h) (sat_cons (step2297 p h) (sat_cons (step1877 p h) (sat_cons (step1862 p h) (sat_cons (step1869 p h) (sat_cons (step2259 p h) (sat_cons (step1756 p h) (sat_cons (step1762 p h) (sat_cons (step2189 p h) (sat_cons (step2186 p h) (sat_cons (step1876 p h) (sat_cons (step1879 p h) (sat_cons (step2185 p h) (sat_cons (step1872 p h) (sat_cons (step1870 p h) (sat_cons (step1856 p h) (sat_cons (step1863 p h) (sat_cons (step1864 p h) (sat_cons (step1865 p h) (sat_cons (step1854 p h) (sat_cons (step278 p h) (sat_cons (step291 p h) (sat_cons (step335 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2311 : List Lit := [(1534, false), (5, false), (1571, false), (4, false), (1617, false), (39, true), (1672, true), (1632, false)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1869, c2231, c1954, c1846, c1894, c1917, c1875, c2189, c1787, c1876, c1872, c1863, c44, c1771, c1773, c1786, c1840, c1953, c1929, c1919, c1896, c1895, c2299, c1891] c2311 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1869 p h) (sat_cons (step2231 p h) (sat_cons (step1954 p h) (sat_cons (step1846 p h) (sat_cons (step1894 p h) (sat_cons (step1917 p h) (sat_cons (step1875 p h) (sat_cons (step2189 p h) (sat_cons (step1787 p h) (sat_cons (step1876 p h) (sat_cons (step1872 p h) (sat_cons (step1863 p h) (sat_cons (step44 p h) (sat_cons (step1771 p h) (sat_cons (step1773 p h) (sat_cons (step1786 p h) (sat_cons (step1840 p h) (sat_cons (step1953 p h) (sat_cons (step1929 p h) (sat_cons (step1919 p h) (sat_cons (step1896 p h) (sat_cons (step1895 p h) (sat_cons (step2299 p h) (sat_cons (step1891 p h) (sat_nil p))))))))))))))))))))))))))
def c2312 : List Lit := [(1571, false), (39, true), (1672, true), (121, false)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c2298, c2283, c2187, c2309, c1754, c1761, c2310, c2311, c1762, c1756, c40, c42, c2308, c1863, c1876, c1872] c2312 (by decide) p (sat_cons (step2298 p h) (sat_cons (step2283 p h) (sat_cons (step2187 p h) (sat_cons (step2309 p h) (sat_cons (step1754 p h) (sat_cons (step1761 p h) (sat_cons (step2310 p h) (sat_cons (step2311 p h) (sat_cons (step1762 p h) (sat_cons (step1756 p h) (sat_cons (step40 p h) (sat_cons (step42 p h) (sat_cons (step2308 p h) (sat_cons (step1863 p h) (sat_cons (step1876 p h) (sat_cons (step1872 p h) (sat_nil p)))))))))))))))))
def c2313 : List Lit := [(1531, true), (5, false), (1571, true), (4, false)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c1756, c1757, c41, c2193] c2313 (by decide) p (sat_cons (step1756 p h) (sat_cons (step1757 p h) (sat_cons (step41 p h) (sat_cons (step2193 p h) (sat_nil p)))))
def c2314 : List Lit := [(9, false), (1531, false), (5, false), (1633, false), (4, false), (39, true), (1672, true)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c29, c40, c41, c42, c1754, c1771, c1796, c1863, c1762, c1773, c2159, c1872, c1786, c1821, c2183, c1839, c1952] c2314 (by decide) p (sat_cons (step29 p h) (sat_cons (step40 p h) (sat_cons (step41 p h) (sat_cons (step42 p h) (sat_cons (step1754 p h) (sat_cons (step1771 p h) (sat_cons (step1796 p h) (sat_cons (step1863 p h) (sat_cons (step1762 p h) (sat_cons (step1773 p h) (sat_cons (step2159 p h) (sat_cons (step1872 p h) (sat_cons (step1786 p h) (sat_cons (step1821 p h) (sat_cons (step2183 p h) (sat_cons (step1839 p h) (sat_cons (step1952 p h) (sat_nil p))))))))))))))))))
def c2315 : List Lit := [(22, true), (9, true), (1639, false), (1571, true), (4, false), (39, true), (1672, true)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c1824, c2163, c1862, c1869, c1796, c2193, c2159, c1802, c1758, c1821, c2157, c1760, c2301, c1785, c2178, c1835, c1853, c1951, c1856, c1939, c1879, c1880, c1934, c2272, c1952, c1754, c1839, c1763, c1788] c2315 (by decide) p (sat_cons (step1824 p h) (sat_cons (step2163 p h) (sat_cons (step1862 p h) (sat_cons (step1869 p h) (sat_cons (step1796 p h) (sat_cons (step2193 p h) (sat_cons (step2159 p h) (sat_cons (step1802 p h) (sat_cons (step1758 p h) (sat_cons (step1821 p h) (sat_cons (step2157 p h) (sat_cons (step1760 p h) (sat_cons (step2301 p h) (sat_cons (step1785 p h) (sat_cons (step2178 p h) (sat_cons (step1835 p h) (sat_cons (step1853 p h) (sat_cons (step1951 p h) (sat_cons (step1856 p h) (sat_cons (step1939 p h) (sat_cons (step1879 p h) (sat_cons (step1880 p h) (sat_cons (step1934 p h) (sat_cons (step2272 p h) (sat_cons (step1952 p h) (sat_cons (step1754 p h) (sat_cons (step1839 p h) (sat_cons (step1763 p h) (sat_cons (step1788 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2316 : List Lit := [(5, false), (1639, false), (1633, false), (1571, true), (4, false), (39, true), (1672, true)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c2313, c2314, c2315, c31, c45, c43, c1754, c1863, c1771, c1762, c1872, c1773, c2183, c1786, c1952, c2166, c1839, c1951, c2281, c1939, c1853, c1880, c1856] c2316 (by decide) p (sat_cons (step2313 p h) (sat_cons (step2314 p h) (sat_cons (step2315 p h) (sat_cons (step31 p h) (sat_cons (step45 p h) (sat_cons (step43 p h) (sat_cons (step1754 p h) (sat_cons (step1863 p h) (sat_cons (step1771 p h) (sat_cons (step1762 p h) (sat_cons (step1872 p h) (sat_cons (step1773 p h) (sat_cons (step2183 p h) (sat_cons (step1786 p h) (sat_cons (step1952 p h) (sat_cons (step2166 p h) (sat_cons (step1839 p h) (sat_cons (step1951 p h) (sat_cons (step2281 p h) (sat_cons (step1939 p h) (sat_cons (step1853 p h) (sat_cons (step1880 p h) (sat_cons (step1856 p h) (sat_nil p))))))))))))))))))))))))
def c2317 : List Lit := [(1534, false), (1606, false), (21, true), (5, true), (1639, false), (1633, false), (1672, true)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c2170, c2183, c1952, c1950, c2180, c1801, c2157, c2178, c1853, c1856, c1880, c1940, c1939, c1920, c1951, c2172, c2166, c1786] c2317 (by decide) p (sat_cons (step2170 p h) (sat_cons (step2183 p h) (sat_cons (step1952 p h) (sat_cons (step1950 p h) (sat_cons (step2180 p h) (sat_cons (step1801 p h) (sat_cons (step2157 p h) (sat_cons (step2178 p h) (sat_cons (step1853 p h) (sat_cons (step1856 p h) (sat_cons (step1880 p h) (sat_cons (step1940 p h) (sat_cons (step1939 p h) (sat_cons (step1920 p h) (sat_cons (step1951 p h) (sat_cons (step2172 p h) (sat_cons (step2166 p h) (sat_cons (step1786 p h) (sat_nil p)))))))))))))))))))
def c2318 : List Lit := [(1606, false), (21, true), (9, true), (1533, false), (5, true), (1639, false), (1633, false), (1571, true), (1672, true)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c2170, c829, c1950, c2317, c1760, c1758, c2273, c1853, c1856, c1880, c1940, c1939, c1920, c1951, c2172, c1783, c1835, c2162, c1821, c1812, c2159, c1804, c1795, c205, c197] c2318 (by decide) p (sat_cons (step2170 p h) (sat_cons (step829 p h) (sat_cons (step1950 p h) (sat_cons (step2317 p h) (sat_cons (step1760 p h) (sat_cons (step1758 p h) (sat_cons (step2273 p h) (sat_cons (step1853 p h) (sat_cons (step1856 p h) (sat_cons (step1880 p h) (sat_cons (step1940 p h) (sat_cons (step1939 p h) (sat_cons (step1920 p h) (sat_cons (step1951 p h) (sat_cons (step2172 p h) (sat_cons (step1783 p h) (sat_cons (step1835 p h) (sat_cons (step2162 p h) (sat_cons (step1821 p h) (sat_cons (step1812 p h) (sat_cons (step2159 p h) (sat_cons (step1804 p h) (sat_cons (step1795 p h) (sat_cons (step205 p h) (sat_cons (step197 p h) (sat_nil p))))))))))))))))))))))))))
def c2319 : List Lit := [(9, true), (1531, false), (1639, false), (1633, false), (1571, true), (4, false), (39, true), (1672, true)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c2170, c837, c1759, c2316, c1862, c1869, c1950, c2315, c2207, c2318, c1872, c1870, c2272, c1863, c1864, c1865, c1754, c335, c1762, c291, c277, c1854, c1856, c1879, c1934, c1952, c2180, c1801, c2157, c2178, c1855, c1857, c1884, c1940, c1939, c1920, c1951, c2172, c2166, c1786] c2319 (by decide) p (sat_cons (step2170 p h) (sat_cons (step837 p h) (sat_cons (step1759 p h) (sat_cons (step2316 p h) (sat_cons (step1862 p h) (sat_cons (step1869 p h) (sat_cons (step1950 p h) (sat_cons (step2315 p h) (sat_cons (step2207 p h) (sat_cons (step2318 p h) (sat_cons (step1872 p h) (sat_cons (step1870 p h) (sat_cons (step2272 p h) (sat_cons (step1863 p h) (sat_cons (step1864 p h) (sat_cons (step1865 p h) (sat_cons (step1754 p h) (sat_cons (step335 p h) (sat_cons (step1762 p h) (sat_cons (step291 p h) (sat_cons (step277 p h) (sat_cons (step1854 p h) (sat_cons (step1856 p h) (sat_cons (step1879 p h) (sat_cons (step1934 p h) (sat_cons (step1952 p h) (sat_cons (step2180 p h) (sat_cons (step1801 p h) (sat_cons (step2157 p h) (sat_cons (step2178 p h) (sat_cons (step1855 p h) (sat_cons (step1857 p h) (sat_cons (step1884 p h) (sat_cons (step1940 p h) (sat_cons (step1939 p h) (sat_cons (step1920 p h) (sat_cons (step1951 p h) (sat_cons (step2172 p h) (sat_cons (step2166 p h) (sat_cons (step1786 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c2320 : List Lit := [(1531, false), (1639, false), (1633, false), (1571, true), (4, false), (39, true), (1672, true)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c2170, c2316, c1950, c1945, c1759, c2319, c2259, c1877, c1881, c1940, c1939, c1856, c1920, c1951, c1853, c2172, c2281, c1783, c1835] c2320 (by decide) p (sat_cons (step2170 p h) (sat_cons (step2316 p h) (sat_cons (step1950 p h) (sat_cons (step1945 p h) (sat_cons (step1759 p h) (sat_cons (step2319 p h) (sat_cons (step2259 p h) (sat_cons (step1877 p h) (sat_cons (step1881 p h) (sat_cons (step1940 p h) (sat_cons (step1939 p h) (sat_cons (step1856 p h) (sat_cons (step1920 p h) (sat_cons (step1951 p h) (sat_cons (step1853 p h) (sat_cons (step2172 p h) (sat_cons (step2281 p h) (sat_cons (step1783 p h) (sat_cons (step1835 p h) (sat_nil p))))))))))))))))))))
def c2321 : List Lit := [(39, true), (1672, true), (121, false)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c2170, c1950, c2283, c1894, c2298, c2312, c2265, c1918, c1945, c2316, c2320, c1756, c1757, c2259, c2273, c1881, c1853, c1856] c2321 (by decide) p (sat_cons (step2170 p h) (sat_cons (step1950 p h) (sat_cons (step2283 p h) (sat_cons (step1894 p h) (sat_cons (step2298 p h) (sat_cons (step2312 p h) (sat_cons (step2265 p h) (sat_cons (step1918 p h) (sat_cons (step1945 p h) (sat_cons (step2316 p h) (sat_cons (step2320 p h) (sat_cons (step1756 p h) (sat_cons (step1757 p h) (sat_cons (step2259 p h) (sat_cons (step2273 p h) (sat_cons (step1881 p h) (sat_cons (step1853 p h) (sat_cons (step1856 p h) (sat_nil p)))))))))))))))))))
def c2322 : List Lit := [(14, false), (11, false), (29, false), (5, true)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c822, c131, c120] c2322 (by decide) p (sat_cons (step822 p h) (sat_cons (step131 p h) (sat_cons (step120 p h) (sat_nil p))))
def c2323 : List Lit := [(81, true), (20, true), (3, false), (40, true), (5, true)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c816, c24] c2323 (by decide) p (sat_cons (step816 p h) (sat_cons (step24 p h) (sat_nil p)))
def c2324 : List Lit := [(6, false), (23, false), (8, false)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c592, c52] c2324 (by decide) p (sat_cons (step592 p h) (sat_cons (step52 p h) (sat_nil p)))
def c2325 : List Lit := [(133, false), (8, false)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c592, c53] c2325 (by decide) p (sat_cons (step592 p h) (sat_cons (step53 p h) (sat_nil p)))
def c2326 : List Lit := [(26, true), (44, true), (8, false)]
theorem step2326 (p : Nat → Bool) (h : Constraints p) : clause p c2326 = true :=
  Snake9.LocalRup.prove_clause [c818, c63] c2326 (by decide) p (sat_cons (step818 p h) (sat_cons (step63 p h) (sat_nil p)))
def c2327 : List Lit := [(44, true), (6, true), (8, false)]
theorem step2327 (p : Nat → Bool) (h : Constraints p) : clause p c2327 = true :=
  Snake9.LocalRup.prove_clause [c818, c64] c2327 (by decide) p (sat_cons (step818 p h) (sat_cons (step64 p h) (sat_nil p)))
def c2328 : List Lit := [(26, true), (6, true), (8, false)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c818, c65] c2328 (by decide) p (sat_cons (step818 p h) (sat_cons (step65 p h) (sat_nil p)))
def c2329 : List Lit := [(46, true), (9, false), (5, true)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c819, c68] c2329 (by decide) p (sat_cons (step819 p h) (sat_cons (step68 p h) (sat_nil p)))
def c2330 : List Lit := [(7, true), (9, false), (5, true)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c819, c69] c2330 (by decide) p (sat_cons (step819 p h) (sat_cons (step69 p h) (sat_nil p)))
def c2331 : List Lit := [(15, true), (89, true), (10, true), (11, false), (12, true), (48, true), (28, true)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c820, c112] c2331 (by decide) p (sat_cons (step820 p h) (sat_cons (step112 p h) (sat_nil p)))
def c2332 : List Lit := [(1, true), (15, true), (11, false), (12, true), (28, true), (48, true), (89, true)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c820, c113] c2332 (by decide) p (sat_cons (step820 p h) (sat_cons (step113 p h) (sat_nil p)))
def c2333 : List Lit := [(15, true), (1, true), (28, true), (10, true), (11, false), (48, true), (89, true)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c820, c114] c2333 (by decide) p (sat_cons (step820 p h) (sat_cons (step114 p h) (sat_nil p)))
def c2334 : List Lit := [(48, true), (10, true), (28, true), (1, true), (11, false), (12, true), (89, true)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c820, c115] c2334 (by decide) p (sat_cons (step820 p h) (sat_cons (step115 p h) (sat_nil p)))
def c2335 : List Lit := [(15, true), (89, true), (1, true), (10, true), (11, false), (12, true), (48, true)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c820, c116] c2335 (by decide) p (sat_cons (step820 p h) (sat_cons (step116 p h) (sat_nil p)))
def c2336 : List Lit := [(15, true), (89, true), (1, true), (10, true), (11, false), (12, true), (28, true)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c820, c117] c2336 (by decide) p (sat_cons (step820 p h) (sat_cons (step117 p h) (sat_nil p)))
def c2337 : List Lit := [(30, true), (50, true), (13, false)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c821, c125] c2337 (by decide) p (sat_cons (step821 p h) (sat_cons (step125 p h) (sat_nil p)))
def c2338 : List Lit := [(10, true), (50, true), (13, false)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c821, c126] c2338 (by decide) p (sat_cons (step821 p h) (sat_cons (step126 p h) (sat_nil p)))
def c2339 : List Lit := [(30, true), (10, true), (13, false)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c821, c127] c2339 (by decide) p (sat_cons (step821 p h) (sat_cons (step127 p h) (sat_nil p)))
def c2340 : List Lit := [(51, true), (12, true), (14, false)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c822, c129] c2340 (by decide) p (sat_cons (step822 p h) (sat_cons (step129 p h) (sat_nil p)))
def c2341 : List Lit := [(51, true), (14, false), (5, true)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c822, c130] c2341 (by decide) p (sat_cons (step822 p h) (sat_cons (step130 p h) (sat_nil p)))
def c2342 : List Lit := [(12, true), (14, false), (5, true)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c822, c131] c2342 (by decide) p (sat_cons (step822 p h) (sat_cons (step131 p h) (sat_nil p)))
def c2343 : List Lit := [(33, true), (16, false), (53, true)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c2106, c141] c2343 (by decide) p (sat_cons (step2106 p h) (sat_cons (step141 p h) (sat_nil p)))
def c2344 : List Lit := [(53, true), (143, true), (16, false)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c2106, c143] c2344 (by decide) p (sat_cons (step2106 p h) (sat_cons (step143 p h) (sat_nil p)))
def c2345 : List Lit := [(33, true), (16, false), (143, true)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c2106, c144] c2345 (by decide) p (sat_cons (step2106 p h) (sat_cons (step144 p h) (sat_nil p)))
def c2346 : List Lit := [(17, false), (34, true)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c823, c145] c2346 (by decide) p (sat_cons (step823 p h) (sat_cons (step145 p h) (sat_nil p)))
def c2347 : List Lit := [(17, false), (15, true)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c823, c146] c2347 (by decide) p (sat_cons (step823 p h) (sat_cons (step146 p h) (sat_nil p)))
def c2348 : List Lit := [(56, true), (19, false), (21, true)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c825, c149] c2348 (by decide) p (sat_cons (step825 p h) (sat_cons (step149 p h) (sat_nil p)))
def c2349 : List Lit := [(32, true), (26, true), (6, true), (23, false), (60, true)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c827, c182] c2349 (by decide) p (sat_cons (step827 p h) (sat_cons (step182 p h) (sat_nil p)))
def c2350 : List Lit := [(24, true), (26, true), (23, false), (6, true), (60, true)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c827, c183] c2350 (by decide) p (sat_cons (step827 p h) (sat_cons (step183 p h) (sat_nil p)))
def c2351 : List Lit := [(24, true), (62, true), (25, false)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c828, c193] c2351 (by decide) p (sat_cons (step828 p h) (sat_cons (step193 p h) (sat_nil p)))
def c2352 : List Lit := [(7, true), (62, true), (25, false)]
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c828, c194] c2352 (by decide) p (sat_cons (step828 p h) (sat_cons (step194 p h) (sat_nil p)))
def c2353 : List Lit := [(24, true), (7, true), (25, false)]
theorem step2353 (p : Nat → Bool) (h : Constraints p) : clause p c2353 = true :=
  Snake9.LocalRup.prove_clause [c828, c195] c2353 (by decide) p (sat_cons (step828 p h) (sat_cons (step195 p h) (sat_nil p)))
def c2354 : List Lit := [(65, true), (27, false), (21, true)]
theorem step2354 (p : Nat → Bool) (h : Constraints p) : clause p c2354 = true :=
  Snake9.LocalRup.prove_clause [c829, c204] c2354 (by decide) p (sat_cons (step829 p h) (sat_cons (step204 p h) (sat_nil p)))
def c2355 : List Lit := [(26, true), (27, false), (21, true)]
theorem step2355 (p : Nat → Bool) (h : Constraints p) : clause p c2355 = true :=
  Snake9.LocalRup.prove_clause [c829, c205] c2355 (by decide) p (sat_cons (step829 p h) (sat_cons (step205 p h) (sat_nil p)))
def c2356 : List Lit := [(67, true), (28, true), (29, false)]
theorem step2356 (p : Nat → Bool) (h : Constraints p) : clause p c2356 = true :=
  Snake9.LocalRup.prove_clause [c830, c212] c2356 (by decide) p (sat_cons (step830 p h) (sat_cons (step212 p h) (sat_nil p)))
def c2357 : List Lit := [(67, true), (12, true), (29, false)]
theorem step2357 (p : Nat → Bool) (h : Constraints p) : clause p c2357 = true :=
  Snake9.LocalRup.prove_clause [c830, c213] c2357 (by decide) p (sat_cons (step830 p h) (sat_cons (step213 p h) (sat_nil p)))
def c2358 : List Lit := [(28, true), (12, true), (29, false)]
theorem step2358 (p : Nat → Bool) (h : Constraints p) : clause p c2358 = true :=
  Snake9.LocalRup.prove_clause [c830, c214] c2358 (by decide) p (sat_cons (step830 p h) (sat_cons (step214 p h) (sat_nil p)))
end B112E260
