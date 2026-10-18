import B112E171Part0017
namespace B112E171
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2208 : List Lit := [(417, false)]
theorem step2208 (p : Nat → Bool) (h : Constraints p) : clause p c2208 = true :=
  Snake9.LocalRup.prove_clause [c2199, c655] c2208 (by decide) p (sat_cons (step2199 p h) (sat_cons (step655 p h) (sat_nil p)))
def c2209 : List Lit := [(389, false)]
theorem step2209 (p : Nat → Bool) (h : Constraints p) : clause p c2209 = true :=
  Snake9.LocalRup.prove_clause [c2200, c601] c2209 (by decide) p (sat_cons (step2200 p h) (sat_cons (step601 p h) (sat_nil p)))
def c2210 : List Lit := [(363, false)]
theorem step2210 (p : Nat → Bool) (h : Constraints p) : clause p c2210 = true :=
  Snake9.LocalRup.prove_clause [c2200, c603] c2210 (by decide) p (sat_cons (step2200 p h) (sat_cons (step603 p h) (sat_nil p)))
def c2211 : List Lit := [(329, false)]
theorem step2211 (p : Nat → Bool) (h : Constraints p) : clause p c2211 = true :=
  Snake9.LocalRup.prove_clause [c2201, c532] c2211 (by decide) p (sat_cons (step2201 p h) (sat_cons (step532 p h) (sat_nil p)))
def c2212 : List Lit := [(123, false)]
theorem step2212 (p : Nat → Bool) (h : Constraints p) : clause p c2212 = true :=
  Snake9.LocalRup.prove_clause [c2202, c459] c2212 (by decide) p (sat_cons (step2202 p h) (sat_cons (step459 p h) (sat_nil p)))
def c2213 : List Lit := [(7, true)]
theorem step2213 (p : Nat → Bool) (h : Constraints p) : clause p c2213 = true :=
  Snake9.LocalRup.prove_clause [c2203, c1285] c2213 (by decide) p (sat_cons (step2203 p h) (sat_cons (step1285 p h) (sat_nil p)))
def c2214 : List Lit := [(119, false)]
theorem step2214 (p : Nat → Bool) (h : Constraints p) : clause p c2214 = true :=
  Snake9.LocalRup.prove_clause [c2205, c449] c2214 (by decide) p (sat_cons (step2205 p h) (sat_cons (step449 p h) (sat_nil p)))
def c2215 : List Lit := [(116, false)]
theorem step2215 (p : Nat → Bool) (h : Constraints p) : clause p c2215 = true :=
  Snake9.LocalRup.prove_clause [c2206, c447] c2215 (by decide) p (sat_cons (step2206 p h) (sat_cons (step447 p h) (sat_nil p)))
def c2216 : List Lit := [(415, false)]
theorem step2216 (p : Nat → Bool) (h : Constraints p) : clause p c2216 = true :=
  Snake9.LocalRup.prove_clause [c2208, c625] c2216 (by decide) p (sat_cons (step2208 p h) (sat_cons (step625 p h) (sat_nil p)))
def c2217 : List Lit := [(403, false)]
theorem step2217 (p : Nat → Bool) (h : Constraints p) : clause p c2217 = true :=
  Snake9.LocalRup.prove_clause [c2208, c627] c2217 (by decide) p (sat_cons (step2208 p h) (sat_cons (step627 p h) (sat_nil p)))
def c2218 : List Lit := [(387, false)]
theorem step2218 (p : Nat → Bool) (h : Constraints p) : clause p c2218 = true :=
  Snake9.LocalRup.prove_clause [c2209, c596] c2218 (by decide) p (sat_cons (step2209 p h) (sat_cons (step596 p h) (sat_nil p)))
def c2219 : List Lit := [(375, false)]
theorem step2219 (p : Nat → Bool) (h : Constraints p) : clause p c2219 = true :=
  Snake9.LocalRup.prove_clause [c2209, c598] c2219 (by decide) p (sat_cons (step2209 p h) (sat_cons (step598 p h) (sat_nil p)))
def c2220 : List Lit := [(361, false)]
theorem step2220 (p : Nat → Bool) (h : Constraints p) : clause p c2220 = true :=
  Snake9.LocalRup.prove_clause [c2210, c571] c2220 (by decide) p (sat_cons (step2210 p h) (sat_cons (step571 p h) (sat_nil p)))
def c2221 : List Lit := [(349, false)]
theorem step2221 (p : Nat → Bool) (h : Constraints p) : clause p c2221 = true :=
  Snake9.LocalRup.prove_clause [c2210, c573] c2221 (by decide) p (sat_cons (step2210 p h) (sat_cons (step573 p h) (sat_nil p)))
def c2222 : List Lit := [(325, false)]
theorem step2222 (p : Nat → Bool) (h : Constraints p) : clause p c2222 = true :=
  Snake9.LocalRup.prove_clause [c2211, c531] c2222 (by decide) p (sat_cons (step2211 p h) (sat_cons (step531 p h) (sat_nil p)))
def c2223 : List Lit := [(9, true)]
theorem step2223 (p : Nat → Bool) (h : Constraints p) : clause p c2223 = true :=
  Snake9.LocalRup.prove_clause [c2213, c1284] c2223 (by decide) p (sat_cons (step2213 p h) (sat_cons (step1284 p h) (sat_nil p)))
def c2224 : List Lit := [(3, true)]
theorem step2224 (p : Nat → Bool) (h : Constraints p) : clause p c2224 = true :=
  Snake9.LocalRup.prove_clause [c2214, c2172, c16] c2224 (by decide) p (sat_cons (step2214 p h) (sat_cons (step2172 p h) (sat_cons (step16 p h) (sat_nil p))))
def c2225 : List Lit := [(413, false)]
theorem step2225 (p : Nat → Bool) (h : Constraints p) : clause p c2225 = true :=
  Snake9.LocalRup.prove_clause [c2216, c622] c2225 (by decide) p (sat_cons (step2216 p h) (sat_cons (step622 p h) (sat_nil p)))
def c2226 : List Lit := [(407, false)]
theorem step2226 (p : Nat → Bool) (h : Constraints p) : clause p c2226 = true :=
  Snake9.LocalRup.prove_clause [c2216, c623] c2226 (by decide) p (sat_cons (step2216 p h) (sat_cons (step623 p h) (sat_nil p)))
def c2227 : List Lit := [(395, false)]
theorem step2227 (p : Nat → Bool) (h : Constraints p) : clause p c2227 = true :=
  Snake9.LocalRup.prove_clause [c2217, c613] c2227 (by decide) p (sat_cons (step2217 p h) (sat_cons (step613 p h) (sat_nil p)))
def c2228 : List Lit := [(379, false)]
theorem step2228 (p : Nat → Bool) (h : Constraints p) : clause p c2228 = true :=
  Snake9.LocalRup.prove_clause [c2218, c594] c2228 (by decide) p (sat_cons (step2218 p h) (sat_cons (step594 p h) (sat_nil p)))
def c2229 : List Lit := [(373, false)]
theorem step2229 (p : Nat → Bool) (h : Constraints p) : clause p c2229 = true :=
  Snake9.LocalRup.prove_clause [c2219, c584] c2229 (by decide) p (sat_cons (step2219 p h) (sat_cons (step584 p h) (sat_nil p)))
def c2230 : List Lit := [(359, false)]
theorem step2230 (p : Nat → Bool) (h : Constraints p) : clause p c2230 = true :=
  Snake9.LocalRup.prove_clause [c2220, c567] c2230 (by decide) p (sat_cons (step2220 p h) (sat_cons (step567 p h) (sat_nil p)))
def c2231 : List Lit := [(341, false)]
theorem step2231 (p : Nat → Bool) (h : Constraints p) : clause p c2231 = true :=
  Snake9.LocalRup.prove_clause [c2221, c554] c2231 (by decide) p (sat_cons (step2221 p h) (sat_cons (step554 p h) (sat_nil p)))
def c2232 : List Lit := [(168, false)]
theorem step2232 (p : Nat → Bool) (h : Constraints p) : clause p c2232 = true :=
  Snake9.LocalRup.prove_clause [c2222, c527] c2232 (by decide) p (sat_cons (step2222 p h) (sat_cons (step527 p h) (sat_nil p)))
def c2233 : List Lit := [(41, true)]
theorem step2233 (p : Nat → Bool) (h : Constraints p) : clause p c2233 = true :=
  Snake9.LocalRup.prove_clause [c2223, c2212, c22] c2233 (by decide) p (sat_cons (step2223 p h) (sat_cons (step2212 p h) (sat_cons (step22 p h) (sat_nil p))))
def c2234 : List Lit := [(409, false)]
theorem step2234 (p : Nat → Bool) (h : Constraints p) : clause p c2234 = true :=
  Snake9.LocalRup.prove_clause [c2225, c621] c2234 (by decide) p (sat_cons (step2225 p h) (sat_cons (step621 p h) (sat_nil p)))
def c2235 : List Lit := [(207, false)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c2226, c619] c2235 (by decide) p (sat_cons (step2226 p h) (sat_cons (step619 p h) (sat_nil p)))
def c2236 : List Lit := [(200, false)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c2227, c608] c2236 (by decide) p (sat_cons (step2227 p h) (sat_cons (step608 p h) (sat_nil p)))
def c2237 : List Lit := [(193, false)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c2228, c588] c2237 (by decide) p (sat_cons (step2228 p h) (sat_cons (step588 p h) (sat_nil p)))
def c2238 : List Lit := [(369, false)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c2229, c583] c2238 (by decide) p (sat_cons (step2229 p h) (sat_cons (step583 p h) (sat_nil p)))
def c2239 : List Lit := [(355, false)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c2230, c564] c2239 (by decide) p (sat_cons (step2230 p h) (sat_cons (step564 p h) (sat_nil p)))
def c2240 : List Lit := [(339, false)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c2231, c548] c2240 (by decide) p (sat_cons (step2231 p h) (sat_cons (step548 p h) (sat_nil p)))
def c2241 : List Lit := [(172, false)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c2231, c549] c2241 (by decide) p (sat_cons (step2231 p h) (sat_cons (step549 p h) (sat_nil p)))
def c2242 : List Lit := [(210, false)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c2234, c620] c2242 (by decide) p (sat_cons (step2234 p h) (sat_cons (step620 p h) (sat_nil p)))
def c2243 : List Lit := [(190, false)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c2238, c577] c2243 (by decide) p (sat_cons (step2238 p h) (sat_cons (step577 p h) (sat_nil p)))
def c2244 : List Lit := [(183, false)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c2239, c559] c2244 (by decide) p (sat_cons (step2239 p h) (sat_cons (step559 p h) (sat_nil p)))
def c2245 : List Lit := [(174, false)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c2240, c547] c2245 (by decide) p (sat_cons (step2240 p h) (sat_cons (step547 p h) (sat_nil p)))
def c2246 : List Lit := [(1500, false), (74, true), (69, false), (44, false)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c2204, c2188, c875, c2185, c2186, c879] c2246 (by decide) p (sat_cons (step2204 p h) (sat_cons (step2188 p h) (sat_cons (step875 p h) (sat_cons (step2185 p h) (sat_cons (step2186 p h) (sat_cons (step879 p h) (sat_nil p)))))))
def c2247 : List Lit := [(66, true), (69, false), (44, false)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c2164, c2204, c1864, c2244, c2209, c2194, c2173, c2163, c2207, c2232, c2196, c2181, c773, c2095, c2093, c811, c1364, c1396, c761, c763, c861, c1314, c1532, c868, c2246, c1531, c1478, c1310, c1881, c1416, c179, c1754, c1392, c2174, c1901, c1399, c781, c1367, c790, c820] c2247 (by decide) p (sat_cons (step2164 p h) (sat_cons (step2204 p h) (sat_cons (step1864 p h) (sat_cons (step2244 p h) (sat_cons (step2209 p h) (sat_cons (step2194 p h) (sat_cons (step2173 p h) (sat_cons (step2163 p h) (sat_cons (step2207 p h) (sat_cons (step2232 p h) (sat_cons (step2196 p h) (sat_cons (step2181 p h) (sat_cons (step773 p h) (sat_cons (step2095 p h) (sat_cons (step2093 p h) (sat_cons (step811 p h) (sat_cons (step1364 p h) (sat_cons (step1396 p h) (sat_cons (step761 p h) (sat_cons (step763 p h) (sat_cons (step861 p h) (sat_cons (step1314 p h) (sat_cons (step1532 p h) (sat_cons (step868 p h) (sat_cons (step2246 p h) (sat_cons (step1531 p h) (sat_cons (step1478 p h) (sat_cons (step1310 p h) (sat_cons (step1881 p h) (sat_cons (step1416 p h) (sat_cons (step179 p h) (sat_cons (step1754 p h) (sat_cons (step1392 p h) (sat_cons (step2174 p h) (sat_cons (step1901 p h) (sat_cons (step1399 p h) (sat_cons (step781 p h) (sat_cons (step1367 p h) (sat_cons (step790 p h) (sat_cons (step820 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c2248 : List Lit := [(69, false), (44, false)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c2164, c1864, c2204, c2244, c2169, c2215, c2209, c2241, c2095, c2181, c773, c1996, c812, c1365, c1397, c2247, c1750, c246, c110, c169, c270, c5, c950, c274, c273, c100, c1376, c2180, c863, c223, c1383, c866, c857, c1023, c878, c933] c2248 (by decide) p (sat_cons (step2164 p h) (sat_cons (step1864 p h) (sat_cons (step2204 p h) (sat_cons (step2244 p h) (sat_cons (step2169 p h) (sat_cons (step2215 p h) (sat_cons (step2209 p h) (sat_cons (step2241 p h) (sat_cons (step2095 p h) (sat_cons (step2181 p h) (sat_cons (step773 p h) (sat_cons (step1996 p h) (sat_cons (step812 p h) (sat_cons (step1365 p h) (sat_cons (step1397 p h) (sat_cons (step2247 p h) (sat_cons (step1750 p h) (sat_cons (step246 p h) (sat_cons (step110 p h) (sat_cons (step169 p h) (sat_cons (step270 p h) (sat_cons (step5 p h) (sat_cons (step950 p h) (sat_cons (step274 p h) (sat_cons (step273 p h) (sat_cons (step100 p h) (sat_cons (step1376 p h) (sat_cons (step2180 p h) (sat_cons (step863 p h) (sat_cons (step223 p h) (sat_cons (step1383 p h) (sat_cons (step866 p h) (sat_cons (step857 p h) (sat_cons (step1023 p h) (sat_cons (step878 p h) (sat_cons (step933 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c2249 : List Lit := [(11, true)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c2171, c2160, c2165, c678, c1560, c679, c680, c47, c473, c685, c476, c722, c477, c1328, c715, c1350, c1329, c472, c713, c699, c485, c470, c697, c480, c36, c51, c48, c46, c30, c31, c704, c705, c58, c712, c57, c1287, c707, c67] c2249 (by decide) p (sat_cons (step2171 p h) (sat_cons (step2160 p h) (sat_cons (step2165 p h) (sat_cons (step678 p h) (sat_cons (step1560 p h) (sat_cons (step679 p h) (sat_cons (step680 p h) (sat_cons (step47 p h) (sat_cons (step473 p h) (sat_cons (step685 p h) (sat_cons (step476 p h) (sat_cons (step722 p h) (sat_cons (step477 p h) (sat_cons (step1328 p h) (sat_cons (step715 p h) (sat_cons (step1350 p h) (sat_cons (step1329 p h) (sat_cons (step472 p h) (sat_cons (step713 p h) (sat_cons (step699 p h) (sat_cons (step485 p h) (sat_cons (step470 p h) (sat_cons (step697 p h) (sat_cons (step480 p h) (sat_cons (step36 p h) (sat_cons (step51 p h) (sat_cons (step48 p h) (sat_cons (step46 p h) (sat_cons (step30 p h) (sat_cons (step31 p h) (sat_cons (step704 p h) (sat_cons (step705 p h) (sat_cons (step58 p h) (sat_cons (step712 p h) (sat_cons (step57 p h) (sat_cons (step1287 p h) (sat_cons (step707 p h) (sat_cons (step67 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c2250 : List Lit := [(16, false)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c2249, c2165, c2170, c1154] c2250 (by decide) p (sat_cons (step2249 p h) (sat_cons (step2165 p h) (sat_cons (step2170 p h) (sat_cons (step1154 p h) (sat_nil p)))))
def c2251 : List Lit := [(44, false)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c2164, c2249, c2215, c2169, c1864, c2243, c2235, c2204, c2242, c2188, c2209, c2095, c2248, c864, c1, c5, c110, c109, c111, c861, c1314, c773, c899, c1321, c869, c306, c1996, c371, c875, c812, c1574, c2186, c1365, c963, c2024, c1397, c1383, c1023] c2251 (by decide) p (sat_cons (step2164 p h) (sat_cons (step2249 p h) (sat_cons (step2215 p h) (sat_cons (step2169 p h) (sat_cons (step1864 p h) (sat_cons (step2243 p h) (sat_cons (step2235 p h) (sat_cons (step2204 p h) (sat_cons (step2242 p h) (sat_cons (step2188 p h) (sat_cons (step2209 p h) (sat_cons (step2095 p h) (sat_cons (step2248 p h) (sat_cons (step864 p h) (sat_cons (step1 p h) (sat_cons (step5 p h) (sat_cons (step110 p h) (sat_cons (step109 p h) (sat_cons (step111 p h) (sat_cons (step861 p h) (sat_cons (step1314 p h) (sat_cons (step773 p h) (sat_cons (step899 p h) (sat_cons (step1321 p h) (sat_cons (step869 p h) (sat_cons (step306 p h) (sat_cons (step1996 p h) (sat_cons (step371 p h) (sat_cons (step875 p h) (sat_cons (step812 p h) (sat_cons (step1574 p h) (sat_cons (step2186 p h) (sat_cons (step1365 p h) (sat_cons (step963 p h) (sat_cons (step2024 p h) (sat_cons (step1397 p h) (sat_cons (step1383 p h) (sat_cons (step1023 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c2252 : List Lit := [(48, false)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c2224, c2169, c2172, c6] c2252 (by decide) p (sat_cons (step2224 p h) (sat_cons (step2169 p h) (sat_cons (step2172 p h) (sat_cons (step6 p h) (sat_nil p)))))
def c2253 : List Lit := [(1439, true)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c2252, c761] c2253 (by decide) p (sat_cons (step2252 p h) (sat_cons (step761 p h) (sat_nil p)))
def c2254 : List Lit := [(1442, true)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c2253, c2251, c766] c2254 (by decide) p (sat_cons (step2253 p h) (sat_cons (step2251 p h) (sat_cons (step766 p h) (sat_nil p))))
def c2255 : List Lit := [(1454, true)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c2254, c1866, c792] c2255 (by decide) p (sat_cons (step2254 p h) (sat_cons (step1866 p h) (sat_cons (step792 p h) (sat_nil p))))
def c2256 : List Lit := [(1463, true)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c2255, c2204, c811] c2256 (by decide) p (sat_cons (step2255 p h) (sat_cons (step2204 p h) (sat_cons (step811 p h) (sat_nil p))))
def c2257 : List Lit := [(1479, true)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c2256, c1364] c2257 (by decide) p (sat_cons (step2256 p h) (sat_cons (step1364 p h) (sat_nil p)))
def c2258 : List Lit := [(1612, false)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c2257, c1396] c2258 (by decide) p (sat_cons (step2257 p h) (sat_cons (step1396 p h) (sat_nil p)))
def c2259 : List Lit := [(1547, false), (1611, true), (1500, false), (66, true), (57, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c2241, c2242, c2235, c2200, c1170, c2078, c1016, c1385, c1377, c968, c1384, c1574, c1020, c371, c1596, c365, c899] c2259 (by decide) p (sat_cons (step2241 p h) (sat_cons (step2242 p h) (sat_cons (step2235 p h) (sat_cons (step2200 p h) (sat_cons (step1170 p h) (sat_cons (step2078 p h) (sat_cons (step1016 p h) (sat_cons (step1385 p h) (sat_cons (step1377 p h) (sat_cons (step968 p h) (sat_cons (step1384 p h) (sat_cons (step1574 p h) (sat_cons (step1020 p h) (sat_cons (step371 p h) (sat_cons (step1596 p h) (sat_cons (step365 p h) (sat_cons (step899 p h) (sat_nil p))))))))))))))))))
def c2260 : List Lit := [(1611, true), (1500, false), (66, true), (57, false), (69, false)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c2251, c2244, c2241, c2207, c2196, c2254, c1865, c2163, c2173, c1864, c1170, c879, c1971, c1399, c1367, c1308, c272, c1673, c1754, c1901, c820, c794, c780, c1530, c950, c1376, c1383, c1023, c2259, c951, c946, c1256, c183, c1129, c1534, c941, c884] c2260 (by decide) p (sat_cons (step2251 p h) (sat_cons (step2244 p h) (sat_cons (step2241 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step2254 p h) (sat_cons (step1865 p h) (sat_cons (step2163 p h) (sat_cons (step2173 p h) (sat_cons (step1864 p h) (sat_cons (step1170 p h) (sat_cons (step879 p h) (sat_cons (step1971 p h) (sat_cons (step1399 p h) (sat_cons (step1367 p h) (sat_cons (step1308 p h) (sat_cons (step272 p h) (sat_cons (step1673 p h) (sat_cons (step1754 p h) (sat_cons (step1901 p h) (sat_cons (step820 p h) (sat_cons (step794 p h) (sat_cons (step780 p h) (sat_cons (step1530 p h) (sat_cons (step950 p h) (sat_cons (step1376 p h) (sat_cons (step1383 p h) (sat_cons (step1023 p h) (sat_cons (step2259 p h) (sat_cons (step951 p h) (sat_cons (step946 p h) (sat_cons (step1256 p h) (sat_cons (step183 p h) (sat_cons (step1129 p h) (sat_cons (step1534 p h) (sat_cons (step941 p h) (sat_cons (step884 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c2261 : List Lit := [(1455, true), (65, true), (69, false)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c2244, c1866, c2253, c2251, c1865, c2252, c272, c797, c1884, c767, c777, c762, c768, c769, c202, c2065] c2261 (by decide) p (sat_cons (step2244 p h) (sat_cons (step1866 p h) (sat_cons (step2253 p h) (sat_cons (step2251 p h) (sat_cons (step1865 p h) (sat_cons (step2252 p h) (sat_cons (step272 p h) (sat_cons (step797 p h) (sat_cons (step1884 p h) (sat_cons (step767 p h) (sat_cons (step777 p h) (sat_cons (step762 p h) (sat_cons (step768 p h) (sat_cons (step769 p h) (sat_cons (step202 p h) (sat_cons (step2065 p h) (sat_nil p)))))))))))))))))
def c2262 : List Lit := [(66, true), (57, false), (69, false)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c2241, c2251, c2244, c2214, c2209, c2204, c2173, c2163, c1864, c1170, c861, c1308, c1532, c868, c272, c878, c2261, c812, c1365, c1397, c2260, c1531, c1478, c1310, c1882, c182, c1376, c1534, c1383, c883, c1023, c938] c2262 (by decide) p (sat_cons (step2241 p h) (sat_cons (step2251 p h) (sat_cons (step2244 p h) (sat_cons (step2214 p h) (sat_cons (step2209 p h) (sat_cons (step2204 p h) (sat_cons (step2173 p h) (sat_cons (step2163 p h) (sat_cons (step1864 p h) (sat_cons (step1170 p h) (sat_cons (step861 p h) (sat_cons (step1308 p h) (sat_cons (step1532 p h) (sat_cons (step868 p h) (sat_cons (step272 p h) (sat_cons (step878 p h) (sat_cons (step2261 p h) (sat_cons (step812 p h) (sat_cons (step1365 p h) (sat_cons (step1397 p h) (sat_cons (step2260 p h) (sat_cons (step1531 p h) (sat_cons (step1478 p h) (sat_cons (step1310 p h) (sat_cons (step1882 p h) (sat_cons (step182 p h) (sat_cons (step1376 p h) (sat_cons (step1534 p h) (sat_cons (step1383 p h) (sat_cons (step883 p h) (sat_cons (step1023 p h) (sat_cons (step938 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c2263 : List Lit := [(1505, false), (57, false), (69, false)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c2209, c2252, c2251, c2204, c2207, c2196, c2254, c1865, c2244, c2242, c2235, c2262, c2037, c812, c1365, c1397, c1452, c1940, c1673, c937, c1399, c1754, c1020, c1367, c1901, c1384, c820, c819, c1377, c794, c1366, c780, c1398, c2014, c2057, c951, c946] c2263 (by decide) p (sat_cons (step2209 p h) (sat_cons (step2252 p h) (sat_cons (step2251 p h) (sat_cons (step2204 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step2254 p h) (sat_cons (step1865 p h) (sat_cons (step2244 p h) (sat_cons (step2242 p h) (sat_cons (step2235 p h) (sat_cons (step2262 p h) (sat_cons (step2037 p h) (sat_cons (step812 p h) (sat_cons (step1365 p h) (sat_cons (step1397 p h) (sat_cons (step1452 p h) (sat_cons (step1940 p h) (sat_cons (step1673 p h) (sat_cons (step937 p h) (sat_cons (step1399 p h) (sat_cons (step1754 p h) (sat_cons (step1020 p h) (sat_cons (step1367 p h) (sat_cons (step1901 p h) (sat_cons (step1384 p h) (sat_cons (step820 p h) (sat_cons (step819 p h) (sat_cons (step1377 p h) (sat_cons (step794 p h) (sat_cons (step1366 p h) (sat_cons (step780 p h) (sat_cons (step1398 p h) (sat_cons (step2014 p h) (sat_cons (step2057 p h) (sat_cons (step951 p h) (sat_cons (step946 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c2264 : List Lit := [(1525, true), (1544, false), (1455, false), (76, true), (1524, false), (1492, false)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c2204, c2209, c2237, c2250, c2249, c2236, c2165, c2207, c2196, c877, c927, c812, c1365, c1397, c1012, c1478, c1109, c1919, c899, c878, c1572, c931, c1377, c1384, c1002, c1015, c1754, c1398, c1901, c1366, c819] c2264 (by decide) p (sat_cons (step2204 p h) (sat_cons (step2209 p h) (sat_cons (step2237 p h) (sat_cons (step2250 p h) (sat_cons (step2249 p h) (sat_cons (step2236 p h) (sat_cons (step2165 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step877 p h) (sat_cons (step927 p h) (sat_cons (step812 p h) (sat_cons (step1365 p h) (sat_cons (step1397 p h) (sat_cons (step1012 p h) (sat_cons (step1478 p h) (sat_cons (step1109 p h) (sat_cons (step1919 p h) (sat_cons (step899 p h) (sat_cons (step878 p h) (sat_cons (step1572 p h) (sat_cons (step931 p h) (sat_cons (step1377 p h) (sat_cons (step1384 p h) (sat_cons (step1002 p h) (sat_cons (step1015 p h) (sat_cons (step1754 p h) (sat_cons (step1398 p h) (sat_cons (step1901 p h) (sat_cons (step1366 p h) (sat_cons (step819 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2265 : List Lit := [(1544, false), (1455, false), (76, true), (1524, false), (1492, false)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c2258, c2207, c2196, c948, c1376, c1383, c2264, c1416, c1021, c1019, c998, c1398, c1754, c1366, c1901, c819] c2265 (by decide) p (sat_cons (step2258 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step948 p h) (sat_cons (step1376 p h) (sat_cons (step1383 p h) (sat_cons (step2264 p h) (sat_cons (step1416 p h) (sat_cons (step1021 p h) (sat_cons (step1019 p h) (sat_cons (step998 p h) (sat_cons (step1398 p h) (sat_cons (step1754 p h) (sat_cons (step1366 p h) (sat_cons (step1901 p h) (sat_cons (step819 p h) (sat_nil p)))))))))))))))))
def c2266 : List Lit := [(57, false), (69, false)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c2241, c2209, c2243, c2251, c2252, c2173, c2163, c1864, c1170, c2262, c1452, c2023, c2037, c2263, c2265, c946, c183, c184, c1534, c863, c883, c866] c2266 (by decide) p (sat_cons (step2241 p h) (sat_cons (step2209 p h) (sat_cons (step2243 p h) (sat_cons (step2251 p h) (sat_cons (step2252 p h) (sat_cons (step2173 p h) (sat_cons (step2163 p h) (sat_cons (step1864 p h) (sat_cons (step1170 p h) (sat_cons (step2262 p h) (sat_cons (step1452 p h) (sat_cons (step2023 p h) (sat_cons (step2037 p h) (sat_cons (step2263 p h) (sat_cons (step2265 p h) (sat_cons (step946 p h) (sat_cons (step183 p h) (sat_cons (step184 p h) (sat_cons (step1534 p h) (sat_cons (step863 p h) (sat_cons (step883 p h) (sat_cons (step866 p h) (sat_nil p)))))))))))))))))))))))
def c2267 : List Lit := [(1492, false), (76, true), (1524, false), (66, true), (1447, false)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c2232, c2163, c2173, c2237, c2204, c2254, c2251, c2241, c861, c1993, c812, c1365, c1397, c1394, c1971, c2265, c1399, c946, c1256, c1367, c183, c184, c180, c1109, c814, c852, c863, c769, c942, c795, c869, c778, c884, c781, c799, c858, c770, c767, c1516] c2267 (by decide) p (sat_cons (step2232 p h) (sat_cons (step2163 p h) (sat_cons (step2173 p h) (sat_cons (step2237 p h) (sat_cons (step2204 p h) (sat_cons (step2254 p h) (sat_cons (step2251 p h) (sat_cons (step2241 p h) (sat_cons (step861 p h) (sat_cons (step1993 p h) (sat_cons (step812 p h) (sat_cons (step1365 p h) (sat_cons (step1397 p h) (sat_cons (step1394 p h) (sat_cons (step1971 p h) (sat_cons (step2265 p h) (sat_cons (step1399 p h) (sat_cons (step946 p h) (sat_cons (step1256 p h) (sat_cons (step1367 p h) (sat_cons (step183 p h) (sat_cons (step184 p h) (sat_cons (step180 p h) (sat_cons (step1109 p h) (sat_cons (step814 p h) (sat_cons (step852 p h) (sat_cons (step863 p h) (sat_cons (step769 p h) (sat_cons (step942 p h) (sat_cons (step795 p h) (sat_cons (step869 p h) (sat_cons (step778 p h) (sat_cons (step884 p h) (sat_cons (step781 p h) (sat_cons (step799 p h) (sat_cons (step858 p h) (sat_cons (step770 p h) (sat_cons (step767 p h) (sat_cons (step1516 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c2268 : List Lit := [(66, true), (57, true)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c1864, c2209, c2243, c2188, c2173, c2163, c773, c861, c1314, c1509, c306, c2267, c855, c2186, c852, c875, c182, c869, c863] c2268 (by decide) p (sat_cons (step1864 p h) (sat_cons (step2209 p h) (sat_cons (step2243 p h) (sat_cons (step2188 p h) (sat_cons (step2173 p h) (sat_cons (step2163 p h) (sat_cons (step773 p h) (sat_cons (step861 p h) (sat_cons (step1314 p h) (sat_cons (step1509 p h) (sat_cons (step306 p h) (sat_cons (step2267 p h) (sat_cons (step855 p h) (sat_cons (step2186 p h) (sat_cons (step852 p h) (sat_cons (step875 p h) (sat_cons (step182 p h) (sat_cons (step869 p h) (sat_cons (step863 p h) (sat_nil p))))))))))))))))))))
def c2269 : List Lit := [(1500, false), (1492, false), (1450, false)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c2254, c2204, c2214, c2251, c2207, c2196, c1535, c1398, c794, c875, c879, c1636, c1940, c1754, c1399, c1901, c1367, c820] c2269 (by decide) p (sat_cons (step2254 p h) (sat_cons (step2204 p h) (sat_cons (step2214 p h) (sat_cons (step2251 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step1535 p h) (sat_cons (step1398 p h) (sat_cons (step794 p h) (sat_cons (step875 p h) (sat_cons (step879 p h) (sat_cons (step1636 p h) (sat_cons (step1940 p h) (sat_cons (step1754 p h) (sat_cons (step1399 p h) (sat_cons (step1901 p h) (sat_cons (step1367 p h) (sat_cons (step820 p h) (sat_nil p)))))))))))))))))))
def c2270 : List Lit := [(1544, false), (1492, false), (69, false)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c1864, c2204, c2214, c2251, c2209, c2207, c2196, c2254, c2244, c2266, c773, c2268, c1528, c778, c1535, c1398, c794, c948, c1376, c1383, c1019, c1416, c1478, c1919, c878, c1372, c1636, c1009, c1754, c1400, c1901, c1368, c820, c821, c1367, c795, c1399, c781, c1010, c2014, c1384, c951, c1377] c2270 (by decide) p (sat_cons (step1864 p h) (sat_cons (step2204 p h) (sat_cons (step2214 p h) (sat_cons (step2251 p h) (sat_cons (step2209 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step2254 p h) (sat_cons (step2244 p h) (sat_cons (step2266 p h) (sat_cons (step773 p h) (sat_cons (step2268 p h) (sat_cons (step1528 p h) (sat_cons (step778 p h) (sat_cons (step1535 p h) (sat_cons (step1398 p h) (sat_cons (step794 p h) (sat_cons (step948 p h) (sat_cons (step1376 p h) (sat_cons (step1383 p h) (sat_cons (step1019 p h) (sat_cons (step1416 p h) (sat_cons (step1478 p h) (sat_cons (step1919 p h) (sat_cons (step878 p h) (sat_cons (step1372 p h) (sat_cons (step1636 p h) (sat_cons (step1009 p h) (sat_cons (step1754 p h) (sat_cons (step1400 p h) (sat_cons (step1901 p h) (sat_cons (step1368 p h) (sat_cons (step820 p h) (sat_cons (step821 p h) (sat_cons (step1367 p h) (sat_cons (step795 p h) (sat_cons (step1399 p h) (sat_cons (step781 p h) (sat_cons (step1010 p h) (sat_cons (step2014 p h) (sat_cons (step1384 p h) (sat_cons (step951 p h) (sat_cons (step1377 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c2271 : List Lit := [(1492, false), (69, false)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c2244, c1864, c2204, c2214, c2251, c2163, c2173, c2207, c2196, c2209, c2254, c2241, c2266, c773, c2268, c1528, c778, c1535, c1398, c1393, c794, c2270, c946, c1256, c183, c184, c180, c1129, c2040, c852, c863, c1391, c1015, c866, c1400, c1382, c878, c1368, c1754, c933, c1901, c1188, c820, c821, c274, c1367, c795, c1192, c1399, c781, c1940, c770, c883, c1516, c858] c2271 (by decide) p (sat_cons (step2244 p h) (sat_cons (step1864 p h) (sat_cons (step2204 p h) (sat_cons (step2214 p h) (sat_cons (step2251 p h) (sat_cons (step2163 p h) (sat_cons (step2173 p h) (sat_cons (step2207 p h) (sat_cons (step2196 p h) (sat_cons (step2209 p h) (sat_cons (step2254 p h) (sat_cons (step2241 p h) (sat_cons (step2266 p h) (sat_cons (step773 p h) (sat_cons (step2268 p h) (sat_cons (step1528 p h) (sat_cons (step778 p h) (sat_cons (step1535 p h) (sat_cons (step1398 p h) (sat_cons (step1393 p h) (sat_cons (step794 p h) (sat_cons (step2270 p h) (sat_cons (step946 p h) (sat_cons (step1256 p h) (sat_cons (step183 p h) (sat_cons (step184 p h) (sat_cons (step180 p h) (sat_cons (step1129 p h) (sat_cons (step2040 p h) (sat_cons (step852 p h) (sat_cons (step863 p h) (sat_cons (step1391 p h) (sat_cons (step1015 p h) (sat_cons (step866 p h) (sat_cons (step1400 p h) (sat_cons (step1382 p h) (sat_cons (step878 p h) (sat_cons (step1368 p h) (sat_cons (step1754 p h) (sat_cons (step933 p h) (sat_cons (step1901 p h) (sat_cons (step1188 p h) (sat_cons (step820 p h) (sat_cons (step821 p h) (sat_cons (step274 p h) (sat_cons (step1367 p h) (sat_cons (step795 p h) (sat_cons (step1192 p h) (sat_cons (step1399 p h) (sat_cons (step781 p h) (sat_cons (step1940 p h) (sat_cons (step770 p h) (sat_cons (step883 p h) (sat_cons (step1516 p h) (sat_cons (step858 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end B112E171
