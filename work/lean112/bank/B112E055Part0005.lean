import B112E055Part0004
namespace B112E055
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2262 : List Lit := [(359, false), (373, false)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c1956, c1136] c2262 (by decide) p (sat_cons (step1956 p h) (sat_cons (step1136 p h) (sat_nil p)))
def c2263 : List Lit := [(345, false), (375, false)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c1950, c1141] c2263 (by decide) p (sat_cons (step1950 p h) (sat_cons (step1141 p h) (sat_nil p)))
def c2264 : List Lit := [(315, false), (377, false)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c1947, c1146] c2264 (by decide) p (sat_cons (step1947 p h) (sat_cons (step1146 p h) (sat_nil p)))
def c2265 : List Lit := [(387, false), (389, false)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c1985, c1156] c2265 (by decide) p (sat_cons (step1985 p h) (sat_cons (step1156 p h) (sat_nil p)))
def c2266 : List Lit := [(385, false), (391, false)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c1967, c1160] c2266 (by decide) p (sat_cons (step1967 p h) (sat_cons (step1160 p h) (sat_nil p)))
def c2267 : List Lit := [(395, false), (397, false)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c1984, c1165] c2267 (by decide) p (sat_cons (step1984 p h) (sat_cons (step1165 p h) (sat_nil p)))
def c2268 : List Lit := [(399, false), (405, false)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c1966, c1172] c2268 (by decide) p (sat_cons (step1966 p h) (sat_cons (step1172 p h) (sat_nil p)))
def c2269 : List Lit := [(393, false), (407, false)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c1955, c1177] c2269 (by decide) p (sat_cons (step1955 p h) (sat_cons (step1177 p h) (sat_nil p)))
def c2270 : List Lit := [(411, false), (413, false)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c1983, c1183] c2270 (by decide) p (sat_cons (step1983 p h) (sat_cons (step1183 p h) (sat_nil p)))
def c2271 : List Lit := [(415, false), (421, false)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c1965, c1190] c2271 (by decide) p (sat_cons (step1965 p h) (sat_cons (step1190 p h) (sat_nil p)))
def c2272 : List Lit := [(431, false), (433, false)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c1982, c1198] c2272 (by decide) p (sat_cons (step1982 p h) (sat_cons (step1198 p h) (sat_nil p)))
def c2273 : List Lit := [(423, false), (437, false)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c1954, c1205] c2273 (by decide) p (sat_cons (step1954 p h) (sat_cons (step1205 p h) (sat_nil p)))
def c2274 : List Lit := [(409, false), (439, false)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c1949, c1210] c2274 (by decide) p (sat_cons (step1949 p h) (sat_cons (step1210 p h) (sat_nil p)))
def c2275 : List Lit := [(226, false), (227, false)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c1994, c1214] c2275 (by decide) p (sat_cons (step1994 p h) (sat_cons (step1214 p h) (sat_nil p)))
def c2276 : List Lit := [(449, false), (451, false)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c1980, c1221] c2276 (by decide) p (sat_cons (step1980 p h) (sat_cons (step1221 p h) (sat_nil p)))
def c2277 : List Lit := [(447, false), (453, false)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c1963, c1225] c2277 (by decide) p (sat_cons (step1963 p h) (sat_cons (step1225 p h) (sat_nil p)))
def c2278 : List Lit := [(457, false), (459, false)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c1979, c1231] c2278 (by decide) p (sat_cons (step1979 p h) (sat_cons (step1231 p h) (sat_nil p)))
def c2279 : List Lit := [(238, false), (239, false)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c1993, c1235] c2279 (by decide) p (sat_cons (step1993 p h) (sat_cons (step1235 p h) (sat_nil p)))
def c2280 : List Lit := [(463, false), (465, false)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c1978, c1239] c2280 (by decide) p (sat_cons (step1978 p h) (sat_cons (step1239 p h) (sat_nil p)))
def c2281 : List Lit := [(461, false), (467, false)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c1962, c1243] c2281 (by decide) p (sat_cons (step1962 p h) (sat_cons (step1243 p h) (sat_nil p)))
def c2282 : List Lit := [(455, false), (469, false)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c1953, c1248] c2282 (by decide) p (sat_cons (step1953 p h) (sat_cons (step1248 p h) (sat_nil p)))
def c2283 : List Lit := [(477, false), (483, false)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c1961, c1258] c2283 (by decide) p (sat_cons (step1961 p h) (sat_cons (step1258 p h) (sat_nil p)))
def c2284 : List Lit := [(248, false), (249, false)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c1992, c1261] c2284 (by decide) p (sat_cons (step1992 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c2285 : List Lit := [(487, false), (489, false)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1977, c1265] c2285 (by decide) p (sat_cons (step1977 p h) (sat_cons (step1265 p h) (sat_nil p)))
def c2286 : List Lit := [(491, false), (497, false)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1275] c2286 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1275 p h) (sat_nil p)))
def c2287 : List Lit := [(485, false), (499, false)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1280] c2287 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1280 p h) (sat_nil p)))
def c2288 : List Lit := [(471, false), (501, false)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c1948, c1285] c2288 (by decide) p (sat_cons (step1948 p h) (sat_cons (step1285 p h) (sat_nil p)))
def c2289 : List Lit := [(441, false), (503, false)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c1946, c1290] c2289 (by decide) p (sat_cons (step1946 p h) (sat_cons (step1290 p h) (sat_nil p)))
def c2290 : List Lit := [(379, false), (505, false)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c1295, c1293] c2290 (by decide) p (sat_cons (step1295 p h) (sat_cons (step1293 p h) (sat_nil p)))
def c2291 : List Lit := [(1608, false), (1617, true)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c2006, c1381] c2291 (by decide) p (sat_cons (step2006 p h) (sat_cons (step1381 p h) (sat_nil p)))
def c2292 : List Lit := [(1609, false), (1618, true)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c2006, c1382] c2292 (by decide) p (sat_cons (step2006 p h) (sat_cons (step1382 p h) (sat_nil p)))
def c2293 : List Lit := [(1610, false), (1619, true)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c2006, c1383] c2293 (by decide) p (sat_cons (step2006 p h) (sat_cons (step1383 p h) (sat_nil p)))
def c2294 : List Lit := [(1611, false), (1620, true)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c2006, c1384] c2294 (by decide) p (sat_cons (step2006 p h) (sat_cons (step1384 p h) (sat_nil p)))
def c2295 : List Lit := [(1617, true), (1585, false)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c2005, c1385] c2295 (by decide) p (sat_cons (step2005 p h) (sat_cons (step1385 p h) (sat_nil p)))
def c2296 : List Lit := [(1618, true), (1586, false)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c2005, c1390] c2296 (by decide) p (sat_cons (step2005 p h) (sat_cons (step1390 p h) (sat_nil p)))
def c2297 : List Lit := [(1587, false), (1619, true)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c2005, c1395] c2297 (by decide) p (sat_cons (step2005 p h) (sat_cons (step1395 p h) (sat_nil p)))
def c2298 : List Lit := [(1588, false), (1620, true)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c2005, c1399] c2298 (by decide) p (sat_cons (step2005 p h) (sat_cons (step1399 p h) (sat_nil p)))
def c2299 : List Lit := [(1682, false), (1700, true)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c2007, c1515] c2299 (by decide) p (sat_cons (step2007 p h) (sat_cons (step1515 p h) (sat_nil p)))
def c2300 : List Lit := [(1685, false), (1703, true)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c2007, c1516] c2300 (by decide) p (sat_cons (step2007 p h) (sat_cons (step1516 p h) (sat_nil p)))
def c2301 : List Lit := [(1759, false), (1768, true)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c1998, c1648] c2301 (by decide) p (sat_cons (step1998 p h) (sat_cons (step1648 p h) (sat_nil p)))
def c2302 : List Lit := [(1760, false), (1769, true)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c1998, c1649] c2302 (by decide) p (sat_cons (step1998 p h) (sat_cons (step1649 p h) (sat_nil p)))
def c2303 : List Lit := [(1761, false), (1770, true)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c1998, c1650] c2303 (by decide) p (sat_cons (step1998 p h) (sat_cons (step1650 p h) (sat_nil p)))
def c2304 : List Lit := [(1762, false), (1771, true)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c1998, c1651] c2304 (by decide) p (sat_cons (step1998 p h) (sat_cons (step1651 p h) (sat_nil p)))
def c2305 : List Lit := [(1763, false), (1772, true)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c1998, c1652] c2305 (by decide) p (sat_cons (step1998 p h) (sat_cons (step1652 p h) (sat_nil p)))
def c2306 : List Lit := [(1764, false), (1773, true)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c1998, c1653] c2306 (by decide) p (sat_cons (step1998 p h) (sat_cons (step1653 p h) (sat_nil p)))
def c2307 : List Lit := [(1798, false), (1831, true)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c2022, c1802] c2307 (by decide) p (sat_cons (step2022 p h) (sat_cons (step1802 p h) (sat_nil p)))
def c2308 : List Lit := [(1799, false), (1832, true)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c2022, c1808] c2308 (by decide) p (sat_cons (step2022 p h) (sat_cons (step1808 p h) (sat_nil p)))
def c2309 : List Lit := [(1800, false), (1833, true)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c2022, c1814] c2309 (by decide) p (sat_cons (step2022 p h) (sat_cons (step1814 p h) (sat_nil p)))
def c2310 : List Lit := [(1801, false), (1834, true)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c2022, c1820] c2310 (by decide) p (sat_cons (step2022 p h) (sat_cons (step1820 p h) (sat_nil p)))
def c2311 : List Lit := [(1834, false), (1853, true)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c2047, c1826] c2311 (by decide) p (sat_cons (step2047 p h) (sat_cons (step1826 p h) (sat_nil p)))
def c2312 : List Lit := [(1854, true), (1772, false)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c2105, c1852] c2312 (by decide) p (sat_cons (step2105 p h) (sat_cons (step1852 p h) (sat_nil p)))
def c2313 : List Lit := [(1773, false), (1855, true)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c2105, c1859] c2313 (by decide) p (sat_cons (step2105 p h) (sat_cons (step1859 p h) (sat_nil p)))
def c2314 : List Lit := [(1774, false), (1856, true)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c2105, c1865] c2314 (by decide) p (sat_cons (step2105 p h) (sat_cons (step1865 p h) (sat_nil p)))
def c2315 : List Lit := [(1775, false), (1857, true)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c2105, c1870] c2315 (by decide) p (sat_cons (step2105 p h) (sat_cons (step1870 p h) (sat_nil p)))
def c2316 : List Lit := [(1776, false), (1858, true)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c2105, c1874] c2316 (by decide) p (sat_cons (step2105 p h) (sat_cons (step1874 p h) (sat_nil p)))
def c2317 : List Lit := [(1700, false), (1860, false)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1876] c2317 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1876 p h) (sat_nil p)))
def c2318 : List Lit := [(1701, false), (1859, false)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1877] c2318 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1877 p h) (sat_nil p)))
def c2319 : List Lit := [(1702, false), (1858, false)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1878] c2319 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1878 p h) (sat_nil p)))
def c2320 : List Lit := [(1703, false), (1857, false)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1879] c2320 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1879 p h) (sat_nil p)))
def c2321 : List Lit := [(1704, false), (1856, false)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1880] c2321 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1880 p h) (sat_nil p)))
def c2322 : List Lit := [(1705, false), (1855, false)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1881] c2322 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1881 p h) (sat_nil p)))
def c2323 : List Lit := [(1706, false), (1854, false)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1882] c2323 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1882 p h) (sat_nil p)))
def c2324 : List Lit := [(1707, false), (1853, false)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1883] c2324 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1883 p h) (sat_nil p)))
def c2325 : List Lit := [(72, false), (1747, true), (81, true), (84, false), (14, false)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c551, c552, c1596, c1598, c1606] c2325 (by decide) p (sat_cons (step551 p h) (sat_cons (step552 p h) (sat_cons (step1596 p h) (sat_cons (step1598 p h) (sat_cons (step1606 p h) (sat_nil p))))))
end B112E055
