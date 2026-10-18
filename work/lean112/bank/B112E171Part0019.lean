import B112E171Part0018
namespace B112E171
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2272 : List Lit := [(66, false), (69, false)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c2233, c2223, c2204, c2251, c1864, c2241, c2173, c2163, c2244, c1750, c2271, c855, c1943, c852, c183, c178, c946, c1232, c951, c814, c1377, c1367, c1573, c1399, c1388] c2272 (by decide) p (sat_cons (step2233 p h) (sat_cons (step2223 p h) (sat_cons (step2204 p h) (sat_cons (step2251 p h) (sat_cons (step1864 p h) (sat_cons (step2241 p h) (sat_cons (step2173 p h) (sat_cons (step2163 p h) (sat_cons (step2244 p h) (sat_cons (step1750 p h) (sat_cons (step2271 p h) (sat_cons (step855 p h) (sat_cons (step1943 p h) (sat_cons (step852 p h) (sat_cons (step183 p h) (sat_cons (step178 p h) (sat_cons (step946 p h) (sat_cons (step1232 p h) (sat_cons (step951 p h) (sat_cons (step814 p h) (sat_cons (step1377 p h) (sat_cons (step1367 p h) (sat_cons (step1573 p h) (sat_cons (step1399 p h) (sat_cons (step1388 p h) (sat_nil p))))))))))))))))))))))))))
def c2273 : List Lit := [(69, false)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c2266, c2268, c2272] c2273 (by decide) p (sat_cons (step2266 p h) (sat_cons (step2268 p h) (sat_cons (step2272 p h) (sat_nil p))))
def c2274 : List Lit := [(1497, true)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c2273, c864] c2274 (by decide) p (sat_cons (step2273 p h) (sat_cons (step864 p h) (sat_nil p)))
def c2275 : List Lit := [(1499, true)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c2274, c866] c2275 (by decide) p (sat_cons (step2274 p h) (sat_cons (step866 p h) (sat_nil p)))
def c2276 : List Lit := [(1455, true), (1544, false), (66, true)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c2274, c1866, c2254, c2251, c1865, c2252, c2163, c2173, c2232, c1864, c2235, c2242, c2258, c861, c869, c2268, c797, c793, c767, c777, c762, c768, c769, c202, c178, c199, c1534, c171, c884, c951, c1659] c2276 (by decide) p (sat_cons (step2274 p h) (sat_cons (step1866 p h) (sat_cons (step2254 p h) (sat_cons (step2251 p h) (sat_cons (step1865 p h) (sat_cons (step2252 p h) (sat_cons (step2163 p h) (sat_cons (step2173 p h) (sat_cons (step2232 p h) (sat_cons (step1864 p h) (sat_cons (step2235 p h) (sat_cons (step2242 p h) (sat_cons (step2258 p h) (sat_cons (step861 p h) (sat_cons (step869 p h) (sat_cons (step2268 p h) (sat_cons (step797 p h) (sat_cons (step793 p h) (sat_cons (step767 p h) (sat_cons (step777 p h) (sat_cons (step762 p h) (sat_cons (step768 p h) (sat_cons (step769 p h) (sat_cons (step202 p h) (sat_cons (step178 p h) (sat_cons (step199 p h) (sat_cons (step1534 p h) (sat_cons (step171 p h) (sat_cons (step884 p h) (sat_cons (step951 p h) (sat_cons (step1659 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2277 : List Lit := [(1544, false), (66, true)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c2274, c2241, c2204, c2250, c2249, c2236, c2165, c2207, c2196, c2273, c2268, c1170, c861, c869, c879, c948, c1376, c1383, c2276, c812, c1365, c1397, c2259, c1673, c1572, c1754, c899, c1901, c1129, c1937, c819, c1019, c1366, c1398] c2277 (by decide) p (sat_cons (step2274 p h) (sat_cons (step2241 p h) (sat_cons (step2204 p h) (sat_cons (step2250 p h) (sat_cons (step2249 p h) (sat_cons (step2236 p h) (sat_cons (step2165 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step2273 p h) (sat_cons (step2268 p h) (sat_cons (step1170 p h) (sat_cons (step861 p h) (sat_cons (step869 p h) (sat_cons (step879 p h) (sat_cons (step948 p h) (sat_cons (step1376 p h) (sat_cons (step1383 p h) (sat_cons (step2276 p h) (sat_cons (step812 p h) (sat_cons (step1365 p h) (sat_cons (step1397 p h) (sat_cons (step2259 p h) (sat_cons (step1673 p h) (sat_cons (step1572 p h) (sat_cons (step1754 p h) (sat_cons (step899 p h) (sat_cons (step1901 p h) (sat_cons (step1129 p h) (sat_cons (step1937 p h) (sat_cons (step819 p h) (sat_cons (step1019 p h) (sat_cons (step1366 p h) (sat_cons (step1398 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c2278 : List Lit := [(66, true)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c2274, c2241, c2163, c2173, c2273, c1864, c2242, c2235, c1865, c2258, c2254, c2207, c2196, c861, c2268, c869, c1170, c879, c2277, c946, c1256, c183, c180, c1129, c1937, c1534, c769, c2057, c884, c777, c1398, c1641, c793, c1366, c1754, c819, c1901] c2278 (by decide) p (sat_cons (step2274 p h) (sat_cons (step2241 p h) (sat_cons (step2163 p h) (sat_cons (step2173 p h) (sat_cons (step2273 p h) (sat_cons (step1864 p h) (sat_cons (step2242 p h) (sat_cons (step2235 p h) (sat_cons (step1865 p h) (sat_cons (step2258 p h) (sat_cons (step2254 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step861 p h) (sat_cons (step2268 p h) (sat_cons (step869 p h) (sat_cons (step1170 p h) (sat_cons (step879 p h) (sat_cons (step2277 p h) (sat_cons (step946 p h) (sat_cons (step1256 p h) (sat_cons (step183 p h) (sat_cons (step180 p h) (sat_cons (step1129 p h) (sat_cons (step1937 p h) (sat_cons (step1534 p h) (sat_cons (step769 p h) (sat_cons (step2057 p h) (sat_cons (step884 p h) (sat_cons (step777 p h) (sat_cons (step1398 p h) (sat_cons (step1641 p h) (sat_cons (step793 p h) (sat_cons (step1366 p h) (sat_cons (step1754 p h) (sat_cons (step819 p h) (sat_cons (step1901 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c2279 : List Lit := [(1544, false), (57, false)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c2241, c2209, c2278, c2243, c1866, c2254, c2251, c1865, c2252, c2173, c2163, c2232, c1864, c2273, c2235, c2242, c2258, c2023, c1452, c1170, c2265, c797, c793, c767, c777, c762, c768, c769, c202, c178, c179, c199, c1534, c865, c171, c867, c951, c884, c1659] c2279 (by decide) p (sat_cons (step2241 p h) (sat_cons (step2209 p h) (sat_cons (step2278 p h) (sat_cons (step2243 p h) (sat_cons (step1866 p h) (sat_cons (step2254 p h) (sat_cons (step2251 p h) (sat_cons (step1865 p h) (sat_cons (step2252 p h) (sat_cons (step2173 p h) (sat_cons (step2163 p h) (sat_cons (step2232 p h) (sat_cons (step1864 p h) (sat_cons (step2273 p h) (sat_cons (step2235 p h) (sat_cons (step2242 p h) (sat_cons (step2258 p h) (sat_cons (step2023 p h) (sat_cons (step1452 p h) (sat_cons (step1170 p h) (sat_cons (step2265 p h) (sat_cons (step797 p h) (sat_cons (step793 p h) (sat_cons (step767 p h) (sat_cons (step777 p h) (sat_cons (step762 p h) (sat_cons (step768 p h) (sat_cons (step769 p h) (sat_cons (step202 p h) (sat_cons (step178 p h) (sat_cons (step179 p h) (sat_cons (step199 p h) (sat_cons (step1534 p h) (sat_cons (step865 p h) (sat_cons (step171 p h) (sat_cons (step867 p h) (sat_cons (step951 p h) (sat_cons (step884 p h) (sat_cons (step1659 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c2280 : List Lit := [(57, false)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c2241, c2243, c2278, c2163, c2173, c2273, c2209, c2258, c1865, c2254, c2207, c2196, c1170, c2023, c2279, c946, c1256, c180, c2024, c769, c1393, c1024, c777, c1398, c1382, c793, c1366, c1754, c819, c1901] c2280 (by decide) p (sat_cons (step2241 p h) (sat_cons (step2243 p h) (sat_cons (step2278 p h) (sat_cons (step2163 p h) (sat_cons (step2173 p h) (sat_cons (step2273 p h) (sat_cons (step2209 p h) (sat_cons (step2258 p h) (sat_cons (step1865 p h) (sat_cons (step2254 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step1170 p h) (sat_cons (step2023 p h) (sat_cons (step2279 p h) (sat_cons (step946 p h) (sat_cons (step1256 p h) (sat_cons (step180 p h) (sat_cons (step2024 p h) (sat_cons (step769 p h) (sat_cons (step1393 p h) (sat_cons (step1024 p h) (sat_cons (step777 p h) (sat_cons (step1398 p h) (sat_cons (step1382 p h) (sat_cons (step793 p h) (sat_cons (step1366 p h) (sat_cons (step1754 p h) (sat_cons (step819 p h) (sat_cons (step1901 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2281 : List Lit := [(1447, true)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c2280, c1864, c773] c2281 (by decide) p (sat_cons (step2280 p h) (sat_cons (step1864 p h) (sat_cons (step773 p h) (sat_nil p))))
def c2282 : List Lit := [(1455, true)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c2281, c2232, c2251, c1993] c2282 (by decide) p (sat_cons (step2281 p h) (sat_cons (step2232 p h) (sat_cons (step2251 p h) (sat_cons (step1993 p h) (sat_nil p)))))
def c2283 : List Lit := [(1464, true)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c2282, c2204, c812] c2283 (by decide) p (sat_cons (step2282 p h) (sat_cons (step2204 p h) (sat_cons (step812 p h) (sat_nil p))))
def c2284 : List Lit := [(1480, true)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c2283, c1365] c2284 (by decide) p (sat_cons (step2283 p h) (sat_cons (step1365 p h) (sat_nil p)))
def c2285 : List Lit := [(1611, false)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c2284, c1397] c2285 (by decide) p (sat_cons (step2284 p h) (sat_cons (step1397 p h) (sat_nil p)))
def c2286 : List Lit := [(1500, false), (1492, false)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c2282, c2165, c2173, c2236, c2250, c2244, c2245, c1864, c2163, c2196, c2207, c2281, c2285, c879, c2269, c1673, c778, c1754, c768, c769, c1901, c1162, c819, c1398, c1366] c2286 (by decide) p (sat_cons (step2282 p h) (sat_cons (step2165 p h) (sat_cons (step2173 p h) (sat_cons (step2236 p h) (sat_cons (step2250 p h) (sat_cons (step2244 p h) (sat_cons (step2245 p h) (sat_cons (step1864 p h) (sat_cons (step2163 p h) (sat_cons (step2196 p h) (sat_cons (step2207 p h) (sat_cons (step2281 p h) (sat_cons (step2285 p h) (sat_cons (step879 p h) (sat_cons (step2269 p h) (sat_cons (step1673 p h) (sat_cons (step778 p h) (sat_cons (step1754 p h) (sat_cons (step768 p h) (sat_cons (step769 p h) (sat_cons (step1901 p h) (sat_cons (step1162 p h) (sat_cons (step819 p h) (sat_cons (step1398 p h) (sat_cons (step1366 p h) (sat_nil p))))))))))))))))))))))))))
def c2287 : List Lit := [(1492, false)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c2194, c2275, c2258, c2173, c2163, c2273, c2207, c2196, c2281, c2254, c2286, c867, c1922, c865, c1427, c1881, c179, c1930, c1754, c769, c1399, c1901, c778, c1367, c820, c794] c2287 (by decide) p (sat_cons (step2194 p h) (sat_cons (step2275 p h) (sat_cons (step2258 p h) (sat_cons (step2173 p h) (sat_cons (step2163 p h) (sat_cons (step2273 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step2281 p h) (sat_cons (step2254 p h) (sat_cons (step2286 p h) (sat_cons (step867 p h) (sat_cons (step1922 p h) (sat_cons (step865 p h) (sat_cons (step1427 p h) (sat_cons (step1881 p h) (sat_cons (step179 p h) (sat_cons (step1930 p h) (sat_cons (step1754 p h) (sat_cons (step769 p h) (sat_cons (step1399 p h) (sat_cons (step1901 p h) (sat_cons (step778 p h) (sat_cons (step1367 p h) (sat_cons (step820 p h) (sat_cons (step794 p h) (sat_nil p)))))))))))))))))))))))))))
def c2288 : List Lit := [(1490, false)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c2287, c855] c2288 (by decide) p (sat_cons (step2287 p h) (sat_cons (step855 p h) (sat_nil p)))
def c2289 : List Lit := [(1456, true)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c2287, c1864, c2251, c2281, c1584] c2289 (by decide) p (sat_cons (step2287 p h) (sat_cons (step1864 p h) (sat_cons (step2251 p h) (sat_cons (step2281 p h) (sat_cons (step1584 p h) (sat_nil p))))))
def c2290 : List Lit := [(63, true)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c2288, c852] c2290 (by decide) p (sat_cons (step2288 p h) (sat_cons (step852 p h) (sat_nil p)))
def c2291 : List Lit := [(1465, true)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c2289, c2204, c813] c2291 (by decide) p (sat_cons (step2289 p h) (sat_cons (step2204 p h) (sat_cons (step813 p h) (sat_nil p))))
def c2292 : List Lit := [(88, false)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c2290, c2173, c2163, c183] c2292 (by decide) p (sat_cons (step2290 p h) (sat_cons (step2173 p h) (sat_cons (step2163 p h) (sat_cons (step183 p h) (sat_nil p)))))
def c2293 : List Lit := [(52, false)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c2290, c2173, c2163, c178] c2293 (by decide) p (sat_cons (step2290 p h) (sat_cons (step2173 p h) (sat_cons (step2163 p h) (sat_cons (step178 p h) (sat_nil p)))))
def c2294 : List Lit := [(71, false)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c2290, c2163, c2173, c182] c2294 (by decide) p (sat_cons (step2290 p h) (sat_cons (step2163 p h) (sat_cons (step2173 p h) (sat_cons (step182 p h) (sat_nil p)))))
def c2295 : List Lit := [(1481, true)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c2291, c1366] c2295 (by decide) p (sat_cons (step2291 p h) (sat_cons (step1366 p h) (sat_nil p)))
def c2296 : List Lit := [(1544, true)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c2292, c946] c2296 (by decide) p (sat_cons (step2292 p h) (sat_cons (step946 p h) (sat_nil p)))
def c2297 : List Lit := [(1457, true)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c2293, c2251, c1864, c2241, c2287, c1232] c2297 (by decide) p (sat_cons (step2293 p h) (sat_cons (step2251 p h) (sat_cons (step1864 p h) (sat_cons (step2241 p h) (sat_cons (step2287 p h) (sat_cons (step1232 p h) (sat_nil p)))))))
def c2298 : List Lit := [(1498, true)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c2294, c2273, c865] c2298 (by decide) p (sat_cons (step2294 p h) (sat_cons (step2273 p h) (sat_cons (step865 p h) (sat_nil p))))
def c2299 : List Lit := [(1610, false)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c2295, c1398] c2299 (by decide) p (sat_cons (step2295 p h) (sat_cons (step1398 p h) (sat_nil p)))
def c2300 : List Lit := [(1546, true)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c2296, c948] c2300 (by decide) p (sat_cons (step2296 p h) (sat_cons (step948 p h) (sat_nil p)))
def c2301 : List Lit := [(1500, true)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c2298, c867] c2301 (by decide) p (sat_cons (step2298 p h) (sat_cons (step867 p h) (sat_nil p)))
def c2302 : List Lit := [(1558, true)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c2300, c1376] c2302 (by decide) p (sat_cons (step2300 p h) (sat_cons (step1376 p h) (sat_nil p)))
def c2303 : List Lit := [(1504, true)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c2301, c875] c2303 (by decide) p (sat_cons (step2301 p h) (sat_cons (step875 p h) (sat_nil p)))
def c2304 : List Lit := [(1590, true)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c2302, c1383] c2304 (by decide) p (sat_cons (step2302 p h) (sat_cons (step1383 p h) (sat_nil p)))
def c2305 : List Lit := [(1532, true)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c2303, c1372] c2305 (by decide) p (sat_cons (step2303 p h) (sat_cons (step1372 p h) (sat_nil p)))
def c2306 : List Lit := [(1582, false)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c2303, c2299, c1636] c2306 (by decide) p (sat_cons (step2303 p h) (sat_cons (step2299 p h) (sat_cons (step1636 p h) (sat_nil p))))
def c2307 : List Lit := [(1608, true)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c2304, c2305, c1009] c2307 (by decide) p (sat_cons (step2304 p h) (sat_cons (step2305 p h) (sat_cons (step1009 p h) (sat_nil p))))
def c2308 : List Lit := [(103, true)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c2306, c2207, c1754] c2308 (by decide) p (sat_cons (step2306 p h) (sat_cons (step2207 p h) (sat_cons (step1754 p h) (sat_nil p))))
def c2309 : List Lit := [(1483, false)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c2307, c1400] c2309 (by decide) p (sat_cons (step2307 p h) (sat_cons (step1400 p h) (sat_nil p)))
def c2310 : List Lit := [(1434, true)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c2308, c2196, c1901] c2310 (by decide) p (sat_cons (step2308 p h) (sat_cons (step2196 p h) (sat_cons (step1901 p h) (sat_nil p))))
def c2311 : List Lit := [(1467, false)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c2309, c1368] c2311 (by decide) p (sat_cons (step2309 p h) (sat_cons (step1368 p h) (sat_nil p)))
def c2312 : List Lit := []
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c2310, c2311, c2297, c821] c2312 (by decide) p (sat_cons (step2310 p h) (sat_cons (step2311 p h) (sat_cons (step2297 p h) (sat_cons (step821 p h) (sat_nil p)))))
end B112E171
