import B112E089Part0004
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2332 : List Lit := [(174, false), (175, false)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c2061, c1131] c2332 (by decide) p (sat_cons (step2061 p h) (sat_cons (step1131 p h) (sat_nil p)))
def c2333 : List Lit := [(339, false), (345, false)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c2036, c1137] c2333 (by decide) p (sat_cons (step2036 p h) (sat_cons (step1137 p h) (sat_nil p)))
def c2334 : List Lit := [(349, false), (351, false)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c2051, c1143] c2334 (by decide) p (sat_cons (step2051 p h) (sat_cons (step1143 p h) (sat_nil p)))
def c2335 : List Lit := [(353, false), (359, false)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c2035, c1148] c2335 (by decide) p (sat_cons (step2035 p h) (sat_cons (step1148 p h) (sat_nil p)))
def c2336 : List Lit := [(347, false), (361, false)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c2024, c1153] c2336 (by decide) p (sat_cons (step2024 p h) (sat_cons (step1153 p h) (sat_nil p)))
def c2337 : List Lit := [(333, false), (363, false)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c2018, c1158] c2337 (by decide) p (sat_cons (step2018 p h) (sat_cons (step1158 p h) (sat_nil p)))
def c2338 : List Lit := [(305, false), (365, false)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c2015, c1163] c2338 (by decide) p (sat_cons (step2015 p h) (sat_cons (step1163 p h) (sat_nil p)))
def c2339 : List Lit := [(186, false), (369, false)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c2050, c1168] c2339 (by decide) p (sat_cons (step2050 p h) (sat_cons (step1168 p h) (sat_nil p)))
def c2340 : List Lit := [(371, false), (377, false)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c2034, c1175] c2340 (by decide) p (sat_cons (step2034 p h) (sat_cons (step1175 p h) (sat_nil p)))
def c2341 : List Lit := [(381, false), (383, false)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c2049, c1181] c2341 (by decide) p (sat_cons (step2049 p h) (sat_cons (step1181 p h) (sat_nil p)))
def c2342 : List Lit := [(199, false), (200, false)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c2060, c1185] c2342 (by decide) p (sat_cons (step2060 p h) (sat_cons (step1185 p h) (sat_nil p)))
def c2343 : List Lit := [(387, false), (389, false)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c2048, c1189] c2343 (by decide) p (sat_cons (step2048 p h) (sat_cons (step1189 p h) (sat_nil p)))
def c2344 : List Lit := [(385, false), (391, false)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c2033, c1193] c2344 (by decide) p (sat_cons (step2033 p h) (sat_cons (step1193 p h) (sat_nil p)))
def c2345 : List Lit := [(379, false), (393, false)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c2023, c1198] c2345 (by decide) p (sat_cons (step2023 p h) (sat_cons (step1198 p h) (sat_nil p)))
def c2346 : List Lit := [(395, false), (425, false)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c2017, c1223] c2346 (by decide) p (sat_cons (step2017 p h) (sat_cons (step1223 p h) (sat_nil p)))
def c2347 : List Lit := [(218, false), (429, false)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c2046, c1228] c2347 (by decide) p (sat_cons (step2046 p h) (sat_cons (step1228 p h) (sat_nil p)))
def c2348 : List Lit := [(433, false), (435, false)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c2045, c1233] c2348 (by decide) p (sat_cons (step2045 p h) (sat_cons (step1233 p h) (sat_nil p)))
def c2349 : List Lit := [(431, false), (437, false)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c2031, c1237] c2349 (by decide) p (sat_cons (step2031 p h) (sat_cons (step1237 p h) (sat_nil p)))
def c2350 : List Lit := [(441, false), (443, false)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c2044, c1244] c2350 (by decide) p (sat_cons (step2044 p h) (sat_cons (step1244 p h) (sat_nil p)))
def c2351 : List Lit := [(439, false), (453, false)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c2021, c1253] c2351 (by decide) p (sat_cons (step2021 p h) (sat_cons (step1253 p h) (sat_nil p)))
def c2352 : List Lit := [(463, false), (465, false)]
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c2043, c1261] c2352 (by decide) p (sat_cons (step2043 p h) (sat_cons (step1261 p h) (sat_nil p)))
def c2353 : List Lit := [(461, false), (467, false)]
theorem step2353 (p : Nat → Bool) (h : Constraints p) : clause p c2353 = true :=
  Snake9.LocalRup.prove_clause [c2029, c1265] c2353 (by decide) p (sat_cons (step2029 p h) (sat_cons (step1265 p h) (sat_nil p)))
def c2354 : List Lit := [(243, false), (244, false)]
theorem step2354 (p : Nat → Bool) (h : Constraints p) : clause p c2354 = true :=
  Snake9.LocalRup.prove_clause [c2059, c1269] c2354 (by decide) p (sat_cons (step2059 p h) (sat_cons (step1269 p h) (sat_nil p)))
def c2355 : List Lit := [(471, false), (473, false)]
theorem step2355 (p : Nat → Bool) (h : Constraints p) : clause p c2355 = true :=
  Snake9.LocalRup.prove_clause [c2042, c1273] c2355 (by decide) p (sat_cons (step2042 p h) (sat_cons (step1273 p h) (sat_nil p)))
def c2356 : List Lit := [(477, false), (479, false)]
theorem step2356 (p : Nat → Bool) (h : Constraints p) : clause p c2356 = true :=
  Snake9.LocalRup.prove_clause [c2041, c1278] c2356 (by decide) p (sat_cons (step2041 p h) (sat_cons (step1278 p h) (sat_nil p)))
def c2357 : List Lit := [(475, false), (481, false)]
theorem step2357 (p : Nat → Bool) (h : Constraints p) : clause p c2357 = true :=
  Snake9.LocalRup.prove_clause [c2028, c1282] c2357 (by decide) p (sat_cons (step2028 p h) (sat_cons (step1282 p h) (sat_nil p)))
def c2358 : List Lit := [(469, false), (483, false)]
theorem step2358 (p : Nat → Bool) (h : Constraints p) : clause p c2358 = true :=
  Snake9.LocalRup.prove_clause [c2020, c1287] c2358 (by decide) p (sat_cons (step2020 p h) (sat_cons (step1287 p h) (sat_nil p)))
def c2359 : List Lit := [(455, false), (485, false)]
theorem step2359 (p : Nat → Bool) (h : Constraints p) : clause p c2359 = true :=
  Snake9.LocalRup.prove_clause [c2016, c1292] c2359 (by decide) p (sat_cons (step2016 p h) (sat_cons (step1292 p h) (sat_nil p)))
def c2360 : List Lit := [(427, false), (487, false)]
theorem step2360 (p : Nat → Bool) (h : Constraints p) : clause p c2360 = true :=
  Snake9.LocalRup.prove_clause [c2014, c1297] c2360 (by decide) p (sat_cons (step2014 p h) (sat_cons (step1297 p h) (sat_nil p)))
def c2361 : List Lit := [(367, false), (489, false)]
theorem step2361 (p : Nat → Bool) (h : Constraints p) : clause p c2361 = true :=
  Snake9.LocalRup.prove_clause [c1302, c1300] c2361 (by decide) p (sat_cons (step1302 p h) (sat_cons (step1300 p h) (sat_nil p)))
def c2362 : List Lit := [(1542, false), (1551, true)]
theorem step2362 (p : Nat → Bool) (h : Constraints p) : clause p c2362 = true :=
  Snake9.LocalRup.prove_clause [c2078, c1387] c2362 (by decide) p (sat_cons (step2078 p h) (sat_cons (step1387 p h) (sat_nil p)))
def c2363 : List Lit := [(1543, false), (1552, true)]
theorem step2363 (p : Nat → Bool) (h : Constraints p) : clause p c2363 = true :=
  Snake9.LocalRup.prove_clause [c2078, c1388] c2363 (by decide) p (sat_cons (step2078 p h) (sat_cons (step1388 p h) (sat_nil p)))
def c2364 : List Lit := [(1544, false), (1553, true)]
theorem step2364 (p : Nat → Bool) (h : Constraints p) : clause p c2364 = true :=
  Snake9.LocalRup.prove_clause [c2078, c1389] c2364 (by decide) p (sat_cons (step2078 p h) (sat_cons (step1389 p h) (sat_nil p)))
def c2365 : List Lit := [(1545, false), (1554, true)]
theorem step2365 (p : Nat → Bool) (h : Constraints p) : clause p c2365 = true :=
  Snake9.LocalRup.prove_clause [c2078, c1390] c2365 (by decide) p (sat_cons (step2078 p h) (sat_cons (step1390 p h) (sat_nil p)))
def c2366 : List Lit := [(1546, false), (1555, true)]
theorem step2366 (p : Nat → Bool) (h : Constraints p) : clause p c2366 = true :=
  Snake9.LocalRup.prove_clause [c2078, c1391] c2366 (by decide) p (sat_cons (step2078 p h) (sat_cons (step1391 p h) (sat_nil p)))
def c2367 : List Lit := [(1633, true), (1552, false)]
theorem step2367 (p : Nat → Bool) (h : Constraints p) : clause p c2367 = true :=
  Snake9.LocalRup.prove_clause [c2081, c1565] c2367 (by decide) p (sat_cons (step2081 p h) (sat_cons (step1565 p h) (sat_nil p)))
def c2368 : List Lit := [(1634, true), (1553, false)]
theorem step2368 (p : Nat → Bool) (h : Constraints p) : clause p c2368 = true :=
  Snake9.LocalRup.prove_clause [c2081, c1574] c2368 (by decide) p (sat_cons (step2081 p h) (sat_cons (step1574 p h) (sat_nil p)))
def c2369 : List Lit := [(1635, true), (1554, false)]
theorem step2369 (p : Nat → Bool) (h : Constraints p) : clause p c2369 = true :=
  Snake9.LocalRup.prove_clause [c2081, c1583] c2369 (by decide) p (sat_cons (step2081 p h) (sat_cons (step1583 p h) (sat_nil p)))
def c2370 : List Lit := [(1636, true), (1555, false)]
theorem step2370 (p : Nat → Bool) (h : Constraints p) : clause p c2370 = true :=
  Snake9.LocalRup.prove_clause [c2081, c1591] c2370 (by decide) p (sat_cons (step2081 p h) (sat_cons (step1591 p h) (sat_nil p)))
def c2371 : List Lit := [(1637, true), (1556, false)]
theorem step2371 (p : Nat → Bool) (h : Constraints p) : clause p c2371 = true :=
  Snake9.LocalRup.prove_clause [c2081, c1598] c2371 (by decide) p (sat_cons (step2081 p h) (sat_cons (step1598 p h) (sat_nil p)))
def c2372 : List Lit := [(1695, true), (1663, false)]
theorem step2372 (p : Nat → Bool) (h : Constraints p) : clause p c2372 = true :=
  Snake9.LocalRup.prove_clause [c2166, c1700] c2372 (by decide) p (sat_cons (step2166 p h) (sat_cons (step1700 p h) (sat_nil p)))
def c2373 : List Lit := [(1696, true), (1664, false)]
theorem step2373 (p : Nat → Bool) (h : Constraints p) : clause p c2373 = true :=
  Snake9.LocalRup.prove_clause [c2166, c1707] c2373 (by decide) p (sat_cons (step2166 p h) (sat_cons (step1707 p h) (sat_nil p)))
def c2374 : List Lit := [(1697, true), (1665, false)]
theorem step2374 (p : Nat → Bool) (h : Constraints p) : clause p c2374 = true :=
  Snake9.LocalRup.prove_clause [c2166, c1714] c2374 (by decide) p (sat_cons (step2166 p h) (sat_cons (step1714 p h) (sat_nil p)))
def c2375 : List Lit := [(1698, true), (1666, false)]
theorem step2375 (p : Nat → Bool) (h : Constraints p) : clause p c2375 = true :=
  Snake9.LocalRup.prove_clause [c2166, c1721] c2375 (by decide) p (sat_cons (step2166 p h) (sat_cons (step1721 p h) (sat_nil p)))
def c2376 : List Lit := [(1699, true), (1667, false)]
theorem step2376 (p : Nat → Bool) (h : Constraints p) : clause p c2376 = true :=
  Snake9.LocalRup.prove_clause [c2166, c1729] c2376 (by decide) p (sat_cons (step2166 p h) (sat_cons (step1729 p h) (sat_nil p)))
def c2377 : List Lit := [(1700, true), (1668, false)]
theorem step2377 (p : Nat → Bool) (h : Constraints p) : clause p c2377 = true :=
  Snake9.LocalRup.prove_clause [c2166, c1737] c2377 (by decide) p (sat_cons (step2166 p h) (sat_cons (step1737 p h) (sat_nil p)))
def c2378 : List Lit := [(1669, false), (1701, true)]
theorem step2378 (p : Nat → Bool) (h : Constraints p) : clause p c2378 = true :=
  Snake9.LocalRup.prove_clause [c2166, c1744] c2378 (by decide) p (sat_cons (step2166 p h) (sat_cons (step1744 p h) (sat_nil p)))
def c2379 : List Lit := [(1633, false), (1788, false)]
theorem step2379 (p : Nat → Bool) (h : Constraints p) : clause p c2379 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1942] c2379 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1942 p h) (sat_nil p)))
def c2380 : List Lit := [(1634, false), (1787, false)]
theorem step2380 (p : Nat → Bool) (h : Constraints p) : clause p c2380 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1943] c2380 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1943 p h) (sat_nil p)))
def c2381 : List Lit := [(1635, false), (1786, false)]
theorem step2381 (p : Nat → Bool) (h : Constraints p) : clause p c2381 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1944] c2381 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1944 p h) (sat_nil p)))
def c2382 : List Lit := [(1636, false), (1785, false)]
theorem step2382 (p : Nat → Bool) (h : Constraints p) : clause p c2382 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1945] c2382 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1945 p h) (sat_nil p)))
def c2383 : List Lit := [(1637, false), (1784, false)]
theorem step2383 (p : Nat → Bool) (h : Constraints p) : clause p c2383 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1946] c2383 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1946 p h) (sat_nil p)))
def c2384 : List Lit := [(1638, false), (1783, false)]
theorem step2384 (p : Nat → Bool) (h : Constraints p) : clause p c2384 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1947] c2384 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1947 p h) (sat_nil p)))
def c2385 : List Lit := [(1639, false), (1782, false)]
theorem step2385 (p : Nat → Bool) (h : Constraints p) : clause p c2385 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1948] c2385 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1948 p h) (sat_nil p)))
def c2386 : List Lit := [(1640, false), (1781, false)]
theorem step2386 (p : Nat → Bool) (h : Constraints p) : clause p c2386 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1949] c2386 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1949 p h) (sat_nil p)))
def c2387 : List Lit := [(1641, false), (1780, false)]
theorem step2387 (p : Nat → Bool) (h : Constraints p) : clause p c2387 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1950] c2387 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1950 p h) (sat_nil p)))
def c2388 : List Lit := [(1642, false), (1779, false)]
theorem step2388 (p : Nat → Bool) (h : Constraints p) : clause p c2388 = true :=
  Snake9.LocalRup.prove_clause [c1952, c1951] c2388 (by decide) p (sat_cons (step1952 p h) (sat_cons (step1951 p h) (sat_nil p)))
def c2389 : List Lit := [(113, false), (120, true), (237, true), (63, true), (62, true)]
theorem step2389 (p : Nat → Bool) (h : Constraints p) : clause p c2389 = true :=
  Snake9.LocalRup.prove_clause [c906, c905, c2008, c2300] c2389 (by decide) p (sat_cons (step906 p h) (sat_cons (step905 p h) (sat_cons (step2008 p h) (sat_cons (step2300 p h) (sat_nil p)))))
def c2390 : List Lit := [(1726, true), (1589, true), (1719, false), (49, false), (73, false)]
theorem step2390 (p : Nat → Bool) (h : Constraints p) : clause p c2390 = true :=
  Snake9.LocalRup.prove_clause [c1770, c1779, c1783, c1773, c1756, c1758, c1764, c1765, c1753, c1750, c1751, c340, c848, c809, c1463, c817, c842, c1227, c839, c2349, c1230, c1231] c2390 (by decide) p (sat_cons (step1770 p h) (sat_cons (step1779 p h) (sat_cons (step1783 p h) (sat_cons (step1773 p h) (sat_cons (step1756 p h) (sat_cons (step1758 p h) (sat_cons (step1764 p h) (sat_cons (step1765 p h) (sat_cons (step1753 p h) (sat_cons (step1750 p h) (sat_cons (step1751 p h) (sat_cons (step340 p h) (sat_cons (step848 p h) (sat_cons (step809 p h) (sat_cons (step1463 p h) (sat_cons (step817 p h) (sat_cons (step842 p h) (sat_cons (step1227 p h) (sat_cons (step839 p h) (sat_cons (step2349 p h) (sat_cons (step1230 p h) (sat_cons (step1231 p h) (sat_nil p)))))))))))))))))))))))
def c2391 : List Lit := [(439, true), (99, false), (94, false), (96, false), (107, true), (103, true)]
theorem step2391 (p : Nat → Bool) (h : Constraints p) : clause p c2391 = true :=
  Snake9.LocalRup.prove_clause [c1234, c1236, c1231, c1227, c1230, c817, c809, c806, c2289, c2279, c840] c2391 (by decide) p (sat_cons (step1234 p h) (sat_cons (step1236 p h) (sat_cons (step1231 p h) (sat_cons (step1227 p h) (sat_cons (step1230 p h) (sat_cons (step817 p h) (sat_cons (step809 p h) (sat_cons (step806 p h) (sat_cons (step2289 p h) (sat_cons (step2279 p h) (sat_cons (step840 p h) (sat_nil p))))))))))))
def c2392 : List Lit := [(69, false), (1570, true), (56, false), (51, false), (487, false), (46, false), (39, true)]
theorem step2392 (p : Nat → Bool) (h : Constraints p) : clause p c2392 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1425, c1294, c2361, c1160, c1157, c1123, c1099, c1098, c1097, c2360, c1222, c1195, c1192, c1180, c1177, c643, c642, c641, c2002, c682, c1413, c2209, c1415, c1423, c1418, c201, c199, c1964] c2392 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1425 p h) (sat_cons (step1294 p h) (sat_cons (step2361 p h) (sat_cons (step1160 p h) (sat_cons (step1157 p h) (sat_cons (step1123 p h) (sat_cons (step1099 p h) (sat_cons (step1098 p h) (sat_cons (step1097 p h) (sat_cons (step2360 p h) (sat_cons (step1222 p h) (sat_cons (step1195 p h) (sat_cons (step1192 p h) (sat_cons (step1180 p h) (sat_cons (step1177 p h) (sat_cons (step643 p h) (sat_cons (step642 p h) (sat_cons (step641 p h) (sat_cons (step2002 p h) (sat_cons (step682 p h) (sat_cons (step1413 p h) (sat_cons (step2209 p h) (sat_cons (step1415 p h) (sat_cons (step1423 p h) (sat_cons (step1418 p h) (sat_cons (step201 p h) (sat_cons (step199 p h) (sat_cons (step1964 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2393 : List Lit := [(32, true), (75, true), (1570, true), (158, true), (39, true)]
theorem step2393 (p : Nat → Bool) (h : Constraints p) : clause p c2393 = true :=
  Snake9.LocalRup.prove_clause [c1416, c1425, c1413, c2209, c1415, c1423, c1418, c201, c199, c1964] c2393 (by decide) p (sat_cons (step1416 p h) (sat_cons (step1425 p h) (sat_cons (step1413 p h) (sat_cons (step2209 p h) (sat_cons (step1415 p h) (sat_cons (step1423 p h) (sat_cons (step1418 p h) (sat_cons (step201 p h) (sat_cons (step199 p h) (sat_cons (step1964 p h) (sat_nil p)))))))))))
def c2394 : List Lit := [(42, false), (96, false), (52, true), (54, false), (51, false), (178, true)]
theorem step2394 (p : Nat → Bool) (h : Constraints p) : clause p c2394 = true :=
  Snake9.LocalRup.prove_clause [c284, c364, c379] c2394 (by decide) p (sat_cons (step284 p h) (sat_cons (step364 p h) (sat_cons (step379 p h) (sat_nil p))))
def c2395 : List Lit := [(1544, true), (57, false), (61, false), (1534, false), (1525, false)]
theorem step2395 (p : Nat → Bool) (h : Constraints p) : clause p c2395 = true :=
  Snake9.LocalRup.prove_clause [c1364, c2129, c1378, c170, c1076, c1348, c1077, c1342, c1343, c1080, c437, c104, c100, c2323, c116, c1069, c1067, c1068] c2395 (by decide) p (sat_cons (step1364 p h) (sat_cons (step2129 p h) (sat_cons (step1378 p h) (sat_cons (step170 p h) (sat_cons (step1076 p h) (sat_cons (step1348 p h) (sat_cons (step1077 p h) (sat_cons (step1342 p h) (sat_cons (step1343 p h) (sat_cons (step1080 p h) (sat_cons (step437 p h) (sat_cons (step104 p h) (sat_cons (step100 p h) (sat_cons (step2323 p h) (sat_cons (step116 p h) (sat_cons (step1069 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_nil p)))))))))))))))))))
end B112E089
