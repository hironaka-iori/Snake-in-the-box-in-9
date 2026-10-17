import B112E057Part0005
namespace B112E057
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2409 : List Lit := [(916, true), (883, false)]
theorem step2409 (p : Nat → Bool) (h : Constraints p) : clause p c2409 = true :=
  Snake9.LocalRup.prove_clause [c2179, c1360] c2409 (by decide) p (sat_cons (step2179 p h) (sat_cons (step1360 p h) (sat_nil p)))
def c2410 : List Lit := [(917, true), (884, false)]
theorem step2410 (p : Nat → Bool) (h : Constraints p) : clause p c2410 = true :=
  Snake9.LocalRup.prove_clause [c2179, c1366] c2410 (by decide) p (sat_cons (step2179 p h) (sat_cons (step1366 p h) (sat_nil p)))
def c2411 : List Lit := [(885, false), (918, true)]
theorem step2411 (p : Nat → Bool) (h : Constraints p) : clause p c2411 = true :=
  Snake9.LocalRup.prove_clause [c2179, c1373] c2411 (by decide) p (sat_cons (step2179 p h) (sat_cons (step1373 p h) (sat_nil p)))
def c2412 : List Lit := [(886, false), (919, true)]
theorem step2412 (p : Nat → Bool) (h : Constraints p) : clause p c2412 = true :=
  Snake9.LocalRup.prove_clause [c2179, c1379] c2412 (by decide) p (sat_cons (step2179 p h) (sat_cons (step1379 p h) (sat_nil p)))
def c2413 : List Lit := [(887, false), (920, true)]
theorem step2413 (p : Nat → Bool) (h : Constraints p) : clause p c2413 = true :=
  Snake9.LocalRup.prove_clause [c2179, c1383] c2413 (by decide) p (sat_cons (step2179 p h) (sat_cons (step1383 p h) (sat_nil p)))
def c2414 : List Lit := [(888, false), (921, true)]
theorem step2414 (p : Nat → Bool) (h : Constraints p) : clause p c2414 = true :=
  Snake9.LocalRup.prove_clause [c2179, c1387] c2414 (by decide) p (sat_cons (step2179 p h) (sat_cons (step1387 p h) (sat_nil p)))
def c2415 : List Lit := [(981, true), (972, false)]
theorem step2415 (p : Nat → Bool) (h : Constraints p) : clause p c2415 = true :=
  Snake9.LocalRup.prove_clause [c2162, c1480] c2415 (by decide) p (sat_cons (step2162 p h) (sat_cons (step1480 p h) (sat_nil p)))
def c2416 : List Lit := [(982, true), (973, false)]
theorem step2416 (p : Nat → Bool) (h : Constraints p) : clause p c2416 = true :=
  Snake9.LocalRup.prove_clause [c2162, c1481] c2416 (by decide) p (sat_cons (step2162 p h) (sat_cons (step1481 p h) (sat_nil p)))
def c2417 : List Lit := [(974, false), (983, true)]
theorem step2417 (p : Nat → Bool) (h : Constraints p) : clause p c2417 = true :=
  Snake9.LocalRup.prove_clause [c2162, c1482] c2417 (by decide) p (sat_cons (step2162 p h) (sat_cons (step1482 p h) (sat_nil p)))
def c2418 : List Lit := [(975, false), (984, true)]
theorem step2418 (p : Nat → Bool) (h : Constraints p) : clause p c2418 = true :=
  Snake9.LocalRup.prove_clause [c2162, c1483] c2418 (by decide) p (sat_cons (step2162 p h) (sat_cons (step1483 p h) (sat_nil p)))
def c2419 : List Lit := [(976, false), (985, true)]
theorem step2419 (p : Nat → Bool) (h : Constraints p) : clause p c2419 = true :=
  Snake9.LocalRup.prove_clause [c2162, c1484] c2419 (by decide) p (sat_cons (step2162 p h) (sat_cons (step1484 p h) (sat_nil p)))
def c2420 : List Lit := [(1071, true), (1038, false)]
theorem step2420 (p : Nat → Bool) (h : Constraints p) : clause p c2420 = true :=
  Snake9.LocalRup.prove_clause [c2155, c1641] c2420 (by decide) p (sat_cons (step2155 p h) (sat_cons (step1641 p h) (sat_nil p)))
def c2421 : List Lit := [(1039, false), (1072, true)]
theorem step2421 (p : Nat → Bool) (h : Constraints p) : clause p c2421 = true :=
  Snake9.LocalRup.prove_clause [c2155, c1649] c2421 (by decide) p (sat_cons (step2155 p h) (sat_cons (step1649 p h) (sat_nil p)))
def c2422 : List Lit := [(1040, false), (1073, true)]
theorem step2422 (p : Nat → Bool) (h : Constraints p) : clause p c2422 = true :=
  Snake9.LocalRup.prove_clause [c2155, c1657] c2422 (by decide) p (sat_cons (step2155 p h) (sat_cons (step1657 p h) (sat_nil p)))
def c2423 : List Lit := [(1041, false), (1074, true)]
theorem step2423 (p : Nat → Bool) (h : Constraints p) : clause p c2423 = true :=
  Snake9.LocalRup.prove_clause [c2155, c1664] c2423 (by decide) p (sat_cons (step2155 p h) (sat_cons (step1664 p h) (sat_nil p)))
def c2424 : List Lit := [(1042, false), (1075, true)]
theorem step2424 (p : Nat → Bool) (h : Constraints p) : clause p c2424 = true :=
  Snake9.LocalRup.prove_clause [c2155, c1670] c2424 (by decide) p (sat_cons (step2155 p h) (sat_cons (step1670 p h) (sat_nil p)))
def c2425 : List Lit := [(1003, false), (1161, false)]
theorem step2425 (p : Nat → Bool) (h : Constraints p) : clause p c2425 = true :=
  Snake9.LocalRup.prove_clause [c1834, c1827] c2425 (by decide) p (sat_cons (step1834 p h) (sat_cons (step1827 p h) (sat_nil p)))
def c2426 : List Lit := [(1004, false), (1160, false)]
theorem step2426 (p : Nat → Bool) (h : Constraints p) : clause p c2426 = true :=
  Snake9.LocalRup.prove_clause [c1834, c1828] c2426 (by decide) p (sat_cons (step1834 p h) (sat_cons (step1828 p h) (sat_nil p)))
def c2427 : List Lit := [(1005, false), (1159, false)]
theorem step2427 (p : Nat → Bool) (h : Constraints p) : clause p c2427 = true :=
  Snake9.LocalRup.prove_clause [c1834, c1829] c2427 (by decide) p (sat_cons (step1834 p h) (sat_cons (step1829 p h) (sat_nil p)))
def c2428 : List Lit := [(1006, false), (1158, false)]
theorem step2428 (p : Nat → Bool) (h : Constraints p) : clause p c2428 = true :=
  Snake9.LocalRup.prove_clause [c1834, c1830] c2428 (by decide) p (sat_cons (step1834 p h) (sat_cons (step1830 p h) (sat_nil p)))
def c2429 : List Lit := [(1007, false), (1157, false)]
theorem step2429 (p : Nat → Bool) (h : Constraints p) : clause p c2429 = true :=
  Snake9.LocalRup.prove_clause [c1834, c1831] c2429 (by decide) p (sat_cons (step1834 p h) (sat_cons (step1831 p h) (sat_nil p)))
def c2430 : List Lit := [(1008, false), (1156, false)]
theorem step2430 (p : Nat → Bool) (h : Constraints p) : clause p c2430 = true :=
  Snake9.LocalRup.prove_clause [c1834, c1832] c2430 (by decide) p (sat_cons (step1834 p h) (sat_cons (step1832 p h) (sat_nil p)))
def c2431 : List Lit := [(1009, false), (1155, false)]
theorem step2431 (p : Nat → Bool) (h : Constraints p) : clause p c2431 = true :=
  Snake9.LocalRup.prove_clause [c1834, c1833] c2431 (by decide) p (sat_cons (step1834 p h) (sat_cons (step1833 p h) (sat_nil p)))
def c2432 : List Lit := [(1589, false), (1598, true)]
theorem step2432 (p : Nat → Bool) (h : Constraints p) : clause p c2432 = true :=
  Snake9.LocalRup.prove_clause [c2093, c1863] c2432 (by decide) p (sat_cons (step2093 p h) (sat_cons (step1863 p h) (sat_nil p)))
def c2433 : List Lit := [(1627, true), (1622, false)]
theorem step2433 (p : Nat → Bool) (h : Constraints p) : clause p c2433 = true :=
  Snake9.LocalRup.prove_clause [c2097, c1879] c2433 (by decide) p (sat_cons (step2097 p h) (sat_cons (step1879 p h) (sat_nil p)))
def c2434 : List Lit := [(1623, false), (1628, true)]
theorem step2434 (p : Nat → Bool) (h : Constraints p) : clause p c2434 = true :=
  Snake9.LocalRup.prove_clause [c2097, c1880] c2434 (by decide) p (sat_cons (step2097 p h) (sat_cons (step1880 p h) (sat_nil p)))
def c2435 : List Lit := [(1682, false), (1838, false)]
theorem step2435 (p : Nat → Bool) (h : Constraints p) : clause p c2435 = true :=
  Snake9.LocalRup.prove_clause [c1958, c1956] c2435 (by decide) p (sat_cons (step1958 p h) (sat_cons (step1956 p h) (sat_nil p)))
def c2436 : List Lit := [(1683, false), (1837, false)]
theorem step2436 (p : Nat → Bool) (h : Constraints p) : clause p c2436 = true :=
  Snake9.LocalRup.prove_clause [c1958, c1957] c2436 (by decide) p (sat_cons (step1958 p h) (sat_cons (step1957 p h) (sat_nil p)))
def c2437 : List Lit := [(939, true), (44, false), (47, false)]
theorem step2437 (p : Nat → Bool) (h : Constraints p) : clause p c2437 = true :=
  Snake9.LocalRup.prove_clause [c1402, c1403, c332] c2437 (by decide) p (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step332 p h) (sat_nil p))))
def c2438 : List Lit := [(59, false), (934, true), (40, false), (47, false)]
theorem step2438 (p : Nat → Bool) (h : Constraints p) : clause p c2438 = true :=
  Snake9.LocalRup.prove_clause [c308, c313, c1393] c2438 (by decide) p (sat_cons (step308 p h) (sat_cons (step313 p h) (sat_cons (step1393 p h) (sat_nil p))))
def c2439 : List Lit := [(973, false), (969, true), (943, false), (872, false), (40, false), (47, false), (1004, true), (984, true)]
theorem step2439 (p : Nat → Bool) (h : Constraints p) : clause p c2439 = true :=
  Snake9.LocalRup.prove_clause [c2173, c1394, c1421, c1492, c1425, c1395, c1397, c2438, c1486, c1522, c2183] c2439 (by decide) p (sat_cons (step2173 p h) (sat_cons (step1394 p h) (sat_cons (step1421 p h) (sat_cons (step1492 p h) (sat_cons (step1425 p h) (sat_cons (step1395 p h) (sat_cons (step1397 p h) (sat_cons (step2438 p h) (sat_cons (step1486 p h) (sat_cons (step1522 p h) (sat_cons (step2183 p h) (sat_nil p))))))))))))
def c2440 : List Lit := [(959, false), (943, false), (872, false), (40, false), (47, false), (1004, true), (984, true)]
theorem step2440 (p : Nat → Bool) (h : Constraints p) : clause p c2440 = true :=
  Snake9.LocalRup.prove_clause [c2173, c1394, c1421, c1487, c2069, c1496, c1467, c2439, c1430, c2070, c1466, c1448, c1457, c2066, c2064, c1452, c317, c2438, c1438, c1439, c1398, c1446, c2178, c1441, c2282, c408] c2440 (by decide) p (sat_cons (step2173 p h) (sat_cons (step1394 p h) (sat_cons (step1421 p h) (sat_cons (step1487 p h) (sat_cons (step2069 p h) (sat_cons (step1496 p h) (sat_cons (step1467 p h) (sat_cons (step2439 p h) (sat_cons (step1430 p h) (sat_cons (step2070 p h) (sat_cons (step1466 p h) (sat_cons (step1448 p h) (sat_cons (step1457 p h) (sat_cons (step2066 p h) (sat_cons (step2064 p h) (sat_cons (step1452 p h) (sat_cons (step317 p h) (sat_cons (step2438 p h) (sat_cons (step1438 p h) (sat_cons (step1439 p h) (sat_cons (step1398 p h) (sat_cons (step1446 p h) (sat_cons (step2178 p h) (sat_cons (step1441 p h) (sat_cons (step2282 p h) (sat_cons (step408 p h) (sat_nil p)))))))))))))))))))))))))))
def c2441 : List Lit := [(943, false), (872, false), (984, true), (40, false), (47, false), (1004, true)]
theorem step2441 (p : Nat → Bool) (h : Constraints p) : clause p c2441 = true :=
  Snake9.LocalRup.prove_clause [c2440, c1445, c1438, c307, c317, c312, c1452, c1393, c2066, c1395, c1463, c1425, c1496, c1492, c1491, c1430, c1464, c1522, c1398, c2183] c2441 (by decide) p (sat_cons (step2440 p h) (sat_cons (step1445 p h) (sat_cons (step1438 p h) (sat_cons (step307 p h) (sat_cons (step317 p h) (sat_cons (step312 p h) (sat_cons (step1452 p h) (sat_cons (step1393 p h) (sat_cons (step2066 p h) (sat_cons (step1395 p h) (sat_cons (step1463 p h) (sat_cons (step1425 p h) (sat_cons (step1496 p h) (sat_cons (step1492 p h) (sat_cons (step1491 p h) (sat_cons (step1430 p h) (sat_cons (step1464 p h) (sat_cons (step1522 p h) (sat_cons (step1398 p h) (sat_cons (step2183 p h) (sat_nil p)))))))))))))))))))))
def c2442 : List Lit := [(933, true), (59, false), (40, false)]
theorem step2442 (p : Nat → Bool) (h : Constraints p) : clause p c2442 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1392, c305] c2442 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1392 p h) (sat_cons (step305 p h) (sat_nil p))))
def c2443 : List Lit := [(931, false), (59, false), (944, false), (40, false), (984, true)]
theorem step2443 (p : Nat → Bool) (h : Constraints p) : clause p c2443 = true :=
  Snake9.LocalRup.prove_clause [c2442, c2075, c1431, c1398, c1397, c2185, c1426, c1438, c1496, c1445, c2069] c2443 (by decide) p (sat_cons (step2442 p h) (sat_cons (step2075 p h) (sat_cons (step1431 p h) (sat_cons (step1398 p h) (sat_cons (step1397 p h) (sat_cons (step2185 p h) (sat_cons (step1426 p h) (sat_cons (step1438 p h) (sat_cons (step1496 p h) (sat_cons (step1445 p h) (sat_cons (step2069 p h) (sat_nil p))))))))))))
def c2444 : List Lit := [(972, true), (931, true)]
theorem step2444 (p : Nat → Bool) (h : Constraints p) : clause p c2444 = true :=
  Snake9.LocalRup.prove_clause [c1463, c2069, c1457, c1443, c1445, c2064, c1441, c1437, c2178, c408, c2282] c2444 (by decide) p (sat_cons (step1463 p h) (sat_cons (step2069 p h) (sat_cons (step1457 p h) (sat_cons (step1443 p h) (sat_cons (step1445 p h) (sat_cons (step2064 p h) (sat_cons (step1441 p h) (sat_cons (step1437 p h) (sat_cons (step2178 p h) (sat_cons (step408 p h) (sat_cons (step2282 p h) (sat_nil p))))))))))))
def c2445 : List Lit := [(59, false), (944, false), (40, false), (984, true)]
theorem step2445 (p : Nat → Bool) (h : Constraints p) : clause p c2445 = true :=
  Snake9.LocalRup.prove_clause [c2442, c1394, c1422, c1492, c2070, c1448, c2443, c2444, c1496, c1426, c1395, c2185, c1438, c1439, c1445, c1446, c1466, c1441, c1457, c2064, c2178, c408, c2282] c2445 (by decide) p (sat_cons (step2442 p h) (sat_cons (step1394 p h) (sat_cons (step1422 p h) (sat_cons (step1492 p h) (sat_cons (step2070 p h) (sat_cons (step1448 p h) (sat_cons (step2443 p h) (sat_cons (step2444 p h) (sat_cons (step1496 p h) (sat_cons (step1426 p h) (sat_cons (step1395 p h) (sat_cons (step2185 p h) (sat_cons (step1438 p h) (sat_cons (step1439 p h) (sat_cons (step1445 p h) (sat_cons (step1446 p h) (sat_cons (step1466 p h) (sat_cons (step1441 p h) (sat_cons (step1457 p h) (sat_cons (step2064 p h) (sat_cons (step2178 p h) (sat_cons (step408 p h) (sat_cons (step2282 p h) (sat_nil p))))))))))))))))))))))))
def c2446 : List Lit := [(959, false), (931, true), (59, true), (974, true), (948, false), (872, false), (1004, true)]
theorem step2446 (p : Nat → Bool) (h : Constraints p) : clause p c2446 = true :=
  Snake9.LocalRup.prove_clause [c1452, c2066, c1467, c1466, c2183, c1486, c1522] c2446 (by decide) p (sat_cons (step1452 p h) (sat_cons (step2066 p h) (sat_cons (step1467 p h) (sat_cons (step1466 p h) (sat_cons (step2183 p h) (sat_cons (step1486 p h) (sat_cons (step1522 p h) (sat_nil p))))))))
def c2447 : List Lit := [(959, true), (57, true), (185, true), (189, true), (113, false)]
theorem step2447 (p : Nat → Bool) (h : Constraints p) : clause p c2447 = true :=
  Snake9.LocalRup.prove_clause [c1443, c1445, c1440, c1441, c1437, c2270, c418, c356, c2266, c2276, c408, c2278] c2447 (by decide) p (sat_cons (step1443 p h) (sat_cons (step1445 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1437 p h) (sat_cons (step2270 p h) (sat_cons (step418 p h) (sat_cons (step356 p h) (sat_cons (step2266 p h) (sat_cons (step2276 p h) (sat_cons (step408 p h) (sat_cons (step2278 p h) (sat_nil p)))))))))))))
def c2448 : List Lit := [(39, false), (41, true), (42, false), (956, true), (48, false), (40, false)]
theorem step2448 (p : Nat → Bool) (h : Constraints p) : clause p c2448 = true :=
  Snake9.LocalRup.prove_clause [c304, c2247, c1439, c369] c2448 (by decide) p (sat_cons (step304 p h) (sat_cons (step2247 p h) (sat_cons (step1439 p h) (sat_cons (step369 p h) (sat_nil p)))))
def c2449 : List Lit := [(955, false), (933, false), (23, true), (57, true), (54, true), (48, false), (884, false), (943, false), (1004, true), (984, true)]
theorem step2449 (p : Nat → Bool) (h : Constraints p) : clause p c2449 = true :=
  Snake9.LocalRup.prove_clause [c1394, c1421, c1487, c2071, c1441, c1447, c1446, c1442, c2070, c1471, c2269, c1492, c1486, c1457, c432, c1425, c1522, c2064, c1330, c1397, c1368, c2178, c1388, c1389, c1342, c2242, c261, c1327, c1336, c1335, c1331, c1346, c2239, c1318, c251, c1316] c2449 (by decide) p (sat_cons (step1394 p h) (sat_cons (step1421 p h) (sat_cons (step1487 p h) (sat_cons (step2071 p h) (sat_cons (step1441 p h) (sat_cons (step1447 p h) (sat_cons (step1446 p h) (sat_cons (step1442 p h) (sat_cons (step2070 p h) (sat_cons (step1471 p h) (sat_cons (step2269 p h) (sat_cons (step1492 p h) (sat_cons (step1486 p h) (sat_cons (step1457 p h) (sat_cons (step432 p h) (sat_cons (step1425 p h) (sat_cons (step1522 p h) (sat_cons (step2064 p h) (sat_cons (step1330 p h) (sat_cons (step1397 p h) (sat_cons (step1368 p h) (sat_cons (step2178 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1342 p h) (sat_cons (step2242 p h) (sat_cons (step261 p h) (sat_cons (step1327 p h) (sat_cons (step1336 p h) (sat_cons (step1335 p h) (sat_cons (step1331 p h) (sat_cons (step1346 p h) (sat_cons (step2239 p h) (sat_cons (step1318 p h) (sat_cons (step251 p h) (sat_cons (step1316 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c2450 : List Lit := [(59, false), (48, false), (933, false), (959, false), (884, false), (40, false), (941, false), (1004, true), (984, true)]
theorem step2450 (p : Nat → Bool) (h : Constraints p) : clause p c2450 = true :=
  Snake9.LocalRup.prove_clause [c1408, c2069, c1496, c1430, c2273, c2271, c2445, c1411, c1402, c1403, c2187, c2449, c1438, c2185, c1395, c1398, c1425, c1388, c1389, c1492, c1491, c2100, c2070, c1466, c1522, c1444, c1457, c1368, c1442, c2064, c1342, c2269, c2178, c432, c2242, c261, c1327, c1336, c1335, c1331, c1346, c2239, c1318, c251, c1316] c2450 (by decide) p (sat_cons (step1408 p h) (sat_cons (step2069 p h) (sat_cons (step1496 p h) (sat_cons (step1430 p h) (sat_cons (step2273 p h) (sat_cons (step2271 p h) (sat_cons (step2445 p h) (sat_cons (step1411 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step2187 p h) (sat_cons (step2449 p h) (sat_cons (step1438 p h) (sat_cons (step2185 p h) (sat_cons (step1395 p h) (sat_cons (step1398 p h) (sat_cons (step1425 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1492 p h) (sat_cons (step1491 p h) (sat_cons (step2100 p h) (sat_cons (step2070 p h) (sat_cons (step1466 p h) (sat_cons (step1522 p h) (sat_cons (step1444 p h) (sat_cons (step1457 p h) (sat_cons (step1368 p h) (sat_cons (step1442 p h) (sat_cons (step2064 p h) (sat_cons (step1342 p h) (sat_cons (step2269 p h) (sat_cons (step2178 p h) (sat_cons (step432 p h) (sat_cons (step2242 p h) (sat_cons (step261 p h) (sat_cons (step1327 p h) (sat_cons (step1336 p h) (sat_cons (step1335 p h) (sat_cons (step1331 p h) (sat_cons (step1346 p h) (sat_cons (step2239 p h) (sat_cons (step1318 p h) (sat_cons (step251 p h) (sat_cons (step1316 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))
def c2451 : List Lit := [(59, true), (933, false), (959, false), (872, false), (943, false), (1004, true), (984, true)]
theorem step2451 (p : Nat → Bool) (h : Constraints p) : clause p c2451 = true :=
  Snake9.LocalRup.prove_clause [c1394, c1421, c1487, c1452, c2446, c2066, c1397, c1466, c1425, c1492] c2451 (by decide) p (sat_cons (step1394 p h) (sat_cons (step1421 p h) (sat_cons (step1487 p h) (sat_cons (step1452 p h) (sat_cons (step2446 p h) (sat_cons (step2066 p h) (sat_cons (step1397 p h) (sat_cons (step1466 p h) (sat_cons (step1425 p h) (sat_cons (step1492 p h) (sat_nil p)))))))))))
def c2452 : List Lit := [(933, false), (959, false), (872, false), (40, false), (47, true), (1004, true), (984, true)]
theorem step2452 (p : Nat → Bool) (h : Constraints p) : clause p c2452 = true :=
  Snake9.LocalRup.prove_clause [c1301, c1406, c1408, c2451, c2445, c2450, c1409, c1407] c2452 (by decide) p (sat_cons (step1301 p h) (sat_cons (step1406 p h) (sat_cons (step1408 p h) (sat_cons (step2451 p h) (sat_cons (step2445 p h) (sat_cons (step2450 p h) (sat_cons (step1409 p h) (sat_cons (step1407 p h) (sat_nil p)))))))))
def c2453 : List Lit := [(957, false), (872, false), (40, false), (47, true), (1004, true), (984, true)]
theorem step2453 (p : Nat → Bool) (h : Constraints p) : clause p c2453 = true :=
  Snake9.LocalRup.prove_clause [c2418, c1443, c2452, c1391, c1392, c2442, c304, c1982, c1452, c1438, c2066, c1446, c1475, c1471, c1449, c1487, c2448, c1417, c1407, c1409] c2453 (by decide) p (sat_cons (step2418 p h) (sat_cons (step1443 p h) (sat_cons (step2452 p h) (sat_cons (step1391 p h) (sat_cons (step1392 p h) (sat_cons (step2442 p h) (sat_cons (step304 p h) (sat_cons (step1982 p h) (sat_cons (step1452 p h) (sat_cons (step1438 p h) (sat_cons (step2066 p h) (sat_cons (step1446 p h) (sat_cons (step1475 p h) (sat_cons (step1471 p h) (sat_cons (step1449 p h) (sat_cons (step1487 p h) (sat_cons (step2448 p h) (sat_cons (step1417 p h) (sat_cons (step1407 p h) (sat_cons (step1409 p h) (sat_nil p)))))))))))))))))))))
def c2454 : List Lit := [(944, false), (959, false), (59, true), (872, false), (1004, true), (984, true)]
theorem step2454 (p : Nat → Bool) (h : Constraints p) : clause p c2454 = true :=
  Snake9.LocalRup.prove_clause [c1452, c2066, c1466, c1492, c1417, c1422, c1487, c1396, c2446] c2454 (by decide) p (sat_cons (step1452 p h) (sat_cons (step2066 p h) (sat_cons (step1466 p h) (sat_cons (step1492 p h) (sat_cons (step1417 p h) (sat_cons (step1422 p h) (sat_cons (step1487 p h) (sat_cons (step1396 p h) (sat_cons (step2446 p h) (sat_nil p))))))))))
def c2455 : List Lit := [(944, true), (54, false), (47, true)]
theorem step2455 (p : Nat → Bool) (h : Constraints p) : clause p c2455 = true :=
  Snake9.LocalRup.prove_clause [c1406, c1409, c1411, c1407, c1402, c1403, c2187] c2455 (by decide) p (sat_cons (step1406 p h) (sat_cons (step1409 p h) (sat_cons (step1411 p h) (sat_cons (step1407 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step2187 p h) (sat_nil p))))))))
def c2456 : List Lit := [(46, false), (48, false), (60, false), (171, true), (54, false), (47, true)]
theorem step2456 (p : Nat → Bool) (h : Constraints p) : clause p c2456 = true :=
  Snake9.LocalRup.prove_clause [c2187, c353, c335, c2254] c2456 (by decide) p (sat_cons (step2187 p h) (sat_cons (step353 p h) (sat_cons (step335 p h) (sat_cons (step2254 p h) (sat_nil p)))))
def c2457 : List Lit := [(945, false), (59, true), (872, false), (1004, true), (984, true)]
theorem step2457 (p : Nat → Bool) (h : Constraints p) : clause p c2457 = true :=
  Snake9.LocalRup.prove_clause [c1452, c2066, c1463, c1496, c1418, c1423, c1492, c1491, c1396, c1464, c1522, c2183] c2457 (by decide) p (sat_cons (step1452 p h) (sat_cons (step2066 p h) (sat_cons (step1463 p h) (sat_cons (step1496 p h) (sat_cons (step1418 p h) (sat_cons (step1423 p h) (sat_cons (step1492 p h) (sat_cons (step1491 p h) (sat_cons (step1396 p h) (sat_cons (step1464 p h) (sat_cons (step1522 p h) (sat_cons (step2183 p h) (sat_nil p)))))))))))))
def c2458 : List Lit := [(48, false), (940, true), (60, false), (171, true), (54, false), (47, true)]
theorem step2458 (p : Nat → Bool) (h : Constraints p) : clause p c2458 = true :=
  Snake9.LocalRup.prove_clause [c2456, c1404, c350, c399, c2267] c2458 (by decide) p (sat_cons (step2456 p h) (sat_cons (step1404 p h) (sat_cons (step350 p h) (sat_cons (step399 p h) (sat_cons (step2267 p h) (sat_nil p))))))
def c2459 : List Lit := [(40, false), (47, true), (70, false), (7, true), (1004, true), (984, true)]
theorem step2459 (p : Nat → Bool) (h : Constraints p) : clause p c2459 = true :=
  Snake9.LocalRup.prove_clause [c1406, c2182, c2453, c1440, c1441, c2455, c2445, c2454, c2284, c1445, c1138, c1437, c1139, c1143, c1158, c1188, c1256, c2408, c1133, c1128, c1130, c1123, c1096, c1119, c1121, c1093, c1117, c1112, c1113, c1092, c1115, c1111, c1110, c1091, c416, c2270, c418, c2457, c1414, c2458, c1407, c1412, c1402, c353, c2266, c2276, c408, c2278] c2459 (by decide) p (sat_cons (step1406 p h) (sat_cons (step2182 p h) (sat_cons (step2453 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step2455 p h) (sat_cons (step2445 p h) (sat_cons (step2454 p h) (sat_cons (step2284 p h) (sat_cons (step1445 p h) (sat_cons (step1138 p h) (sat_cons (step1437 p h) (sat_cons (step1139 p h) (sat_cons (step1143 p h) (sat_cons (step1158 p h) (sat_cons (step1188 p h) (sat_cons (step1256 p h) (sat_cons (step2408 p h) (sat_cons (step1133 p h) (sat_cons (step1128 p h) (sat_cons (step1130 p h) (sat_cons (step1123 p h) (sat_cons (step1096 p h) (sat_cons (step1119 p h) (sat_cons (step1121 p h) (sat_cons (step1093 p h) (sat_cons (step1117 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step1092 p h) (sat_cons (step1115 p h) (sat_cons (step1111 p h) (sat_cons (step1110 p h) (sat_cons (step1091 p h) (sat_cons (step416 p h) (sat_cons (step2270 p h) (sat_cons (step418 p h) (sat_cons (step2457 p h) (sat_cons (step1414 p h) (sat_cons (step2458 p h) (sat_cons (step1407 p h) (sat_cons (step1412 p h) (sat_cons (step1402 p h) (sat_cons (step353 p h) (sat_cons (step2266 p h) (sat_cons (step2276 p h) (sat_cons (step408 p h) (sat_cons (step2278 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c2460 : List Lit := [(59, true), (62, false), (55, false), (48, true), (54, false), (56, false), (944, false), (984, true)]
theorem step2460 (p : Nat → Bool) (h : Constraints p) : clause p c2460 = true :=
  Snake9.LocalRup.prove_clause [c2284, c1452, c1138, c2066, c1139, c1143, c1158, c1188, c1256, c2408, c1133, c1128, c1123, c1119, c1121, c1117, c1113, c1114, c1115, c1110, c2278, c416, c408, c434, c2269, c1437, c433, c1445, c1466, c1492, c1422, c1396, c1388, c1389, c262, c2242] c2460 (by decide) p (sat_cons (step2284 p h) (sat_cons (step1452 p h) (sat_cons (step1138 p h) (sat_cons (step2066 p h) (sat_cons (step1139 p h) (sat_cons (step1143 p h) (sat_cons (step1158 p h) (sat_cons (step1188 p h) (sat_cons (step1256 p h) (sat_cons (step2408 p h) (sat_cons (step1133 p h) (sat_cons (step1128 p h) (sat_cons (step1123 p h) (sat_cons (step1119 p h) (sat_cons (step1121 p h) (sat_cons (step1117 p h) (sat_cons (step1113 p h) (sat_cons (step1114 p h) (sat_cons (step1115 p h) (sat_cons (step1110 p h) (sat_cons (step2278 p h) (sat_cons (step416 p h) (sat_cons (step408 p h) (sat_cons (step434 p h) (sat_cons (step2269 p h) (sat_cons (step1437 p h) (sat_cons (step433 p h) (sat_cons (step1445 p h) (sat_cons (step1466 p h) (sat_cons (step1492 p h) (sat_cons (step1422 p h) (sat_cons (step1396 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step262 p h) (sat_cons (step2242 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c2461 : List Lit := [(931, true), (30, false), (37, true)]
theorem step2461 (p : Nat → Bool) (h : Constraints p) : clause p c2461 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1389, c262, c2242] c2461 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step262 p h) (sat_cons (step2242 p h) (sat_nil p)))))
def c2462 : List Lit := [(26, true), (872, false), (919, true), (154, true), (23, false), (59, false)]
theorem step2462 (p : Nat → Bool) (h : Constraints p) : clause p c2462 = true :=
  Snake9.LocalRup.prove_clause [c1301, c1368, c1327, c232, c1334, c2119, c1350, c1329, c1319, c214, c211, c1317] c2462 (by decide) p (sat_cons (step1301 p h) (sat_cons (step1368 p h) (sat_cons (step1327 p h) (sat_cons (step232 p h) (sat_cons (step1334 p h) (sat_cons (step2119 p h) (sat_cons (step1350 p h) (sat_cons (step1329 p h) (sat_cons (step1319 p h) (sat_cons (step214 p h) (sat_cons (step211 p h) (sat_cons (step1317 p h) (sat_nil p)))))))))))))
def c2463 : List Lit := [(26, false), (30, false), (932, true), (5, true)]
theorem step2463 (p : Nat → Bool) (h : Constraints p) : clause p c2463 = true :=
  Snake9.LocalRup.prove_clause [c2234, c259, c260, c1390] c2463 (by decide) p (sat_cons (step2234 p h) (sat_cons (step259 p h) (sat_cons (step260 p h) (sat_cons (step1390 p h) (sat_nil p)))))
def c2464 : List Lit := [(872, true), (23, false), (70, false), (7, true)]
theorem step2464 (p : Nat → Bool) (h : Constraints p) : clause p c2464 = true :=
  Snake9.LocalRup.prove_clause [c1267, c1271, c1273, c1269, c1264, c1265, c22, c2144] c2464 (by decide) p (sat_cons (step1267 p h) (sat_cons (step1271 p h) (sat_cons (step1273 p h) (sat_cons (step1269 p h) (sat_cons (step1264 p h) (sat_cons (step1265 p h) (sat_cons (step22 p h) (sat_cons (step2144 p h) (sat_nil p)))))))))
def c2465 : List Lit := [(4, false), (910, true), (23, false), (932, true), (59, false), (5, true)]
theorem step2465 (p : Nat → Bool) (h : Constraints p) : clause p c2465 = true :=
  Snake9.LocalRup.prove_clause [c205, c203, c200, c1329, c1317, c1319, c1351, c1333, c1335, c1331, c1327, c2463] c2465 (by decide) p (sat_cons (step205 p h) (sat_cons (step203 p h) (sat_cons (step200 p h) (sat_cons (step1329 p h) (sat_cons (step1317 p h) (sat_cons (step1319 p h) (sat_cons (step1351 p h) (sat_cons (step1333 p h) (sat_cons (step1335 p h) (sat_cons (step1331 p h) (sat_cons (step1327 p h) (sat_cons (step2463 p h) (sat_nil p)))))))))))))
def c2466 : List Lit := [(904, false), (129, true), (13, false), (50, false), (909, true), (919, true), (4, true)]
theorem step2466 (p : Nat → Bool) (h : Constraints p) : clause p c2466 = true :=
  Snake9.LocalRup.prove_clause [c1341, c1346, c1374, c1320, c2149, c1312, c117] c2466 (by decide) p (sat_cons (step1341 p h) (sat_cons (step1346 p h) (sat_cons (step1374 p h) (sat_cons (step1320 p h) (sat_cons (step2149 p h) (sat_cons (step1312 p h) (sat_cons (step117 p h) (sat_nil p))))))))
def c2467 : List Lit := [(26, false), (51, true), (884, false), (63, false), (23, false), (972, false), (59, false), (5, true), (38, false), (48, true), (944, false), (40, true), (1004, true), (984, true)]
theorem step2467 (p : Nat → Bool) (h : Constraints p) : clause p c2467 = true :=
  Snake9.LocalRup.prove_clause [c1496, c1426, c1399, c1417, c1485, c1527, c1369, c2465, c2118, c2463, c1396, c1397, c1330, c433, c1422, c1391, c1392, c1332, c1114, c1492, c1491, c2249, c1117, c2070, c1522, c325, c1119, c1448, c1368, c1123, c1439, c1350, c1128, c2263, c1319, c2389, c1074, c1043, c1032, c1031, c1030, c2466, c1333, c1331, c214, c211, c1317] c2467 (by decide) p (sat_cons (step1496 p h) (sat_cons (step1426 p h) (sat_cons (step1399 p h) (sat_cons (step1417 p h) (sat_cons (step1485 p h) (sat_cons (step1527 p h) (sat_cons (step1369 p h) (sat_cons (step2465 p h) (sat_cons (step2118 p h) (sat_cons (step2463 p h) (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step1330 p h) (sat_cons (step433 p h) (sat_cons (step1422 p h) (sat_cons (step1391 p h) (sat_cons (step1392 p h) (sat_cons (step1332 p h) (sat_cons (step1114 p h) (sat_cons (step1492 p h) (sat_cons (step1491 p h) (sat_cons (step2249 p h) (sat_cons (step1117 p h) (sat_cons (step2070 p h) (sat_cons (step1522 p h) (sat_cons (step325 p h) (sat_cons (step1119 p h) (sat_cons (step1448 p h) (sat_cons (step1368 p h) (sat_cons (step1123 p h) (sat_cons (step1439 p h) (sat_cons (step1350 p h) (sat_cons (step1128 p h) (sat_cons (step2263 p h) (sat_cons (step1319 p h) (sat_cons (step2389 p h) (sat_cons (step1074 p h) (sat_cons (step1043 p h) (sat_cons (step1032 p h) (sat_cons (step1031 p h) (sat_cons (step1030 p h) (sat_cons (step2466 p h) (sat_cons (step1333 p h) (sat_cons (step1331 p h) (sat_cons (step214 p h) (sat_cons (step211 p h) (sat_cons (step1317 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c2468 : List Lit := [(33, false), (894, true), (23, false), (59, false)]
theorem step2468 (p : Nat → Bool) (h : Constraints p) : clause p c2468 = true :=
  Snake9.LocalRup.prove_clause [c214, c211, c1317] c2468 (by decide) p (sat_cons (step214 p h) (sat_cons (step211 p h) (sat_cons (step1317 p h) (sat_nil p))))
def c2469 : List Lit := [(154, true), (26, true), (37, true), (872, false), (23, false), (972, false), (59, false), (944, false), (1004, true)]
theorem step2469 (p : Nat → Bool) (h : Constraints p) : clause p c2469 = true :=
  Snake9.LocalRup.prove_clause [c1327, c1417, c1485, c1527, c1301, c1369, c1343, c232, c2462, c1522, c1491, c1422, c1396, c2461, c1330, c1335, c1351, c1319, c2468, c1331, c1339, c1336, c1328, c1347, c2236, c2238, c1318, c221, c1315] c2469 (by decide) p (sat_cons (step1327 p h) (sat_cons (step1417 p h) (sat_cons (step1485 p h) (sat_cons (step1527 p h) (sat_cons (step1301 p h) (sat_cons (step1369 p h) (sat_cons (step1343 p h) (sat_cons (step232 p h) (sat_cons (step2462 p h) (sat_cons (step1522 p h) (sat_cons (step1491 p h) (sat_cons (step1422 p h) (sat_cons (step1396 p h) (sat_cons (step2461 p h) (sat_cons (step1330 p h) (sat_cons (step1335 p h) (sat_cons (step1351 p h) (sat_cons (step1319 p h) (sat_cons (step2468 p h) (sat_cons (step1331 p h) (sat_cons (step1339 p h) (sat_cons (step1336 p h) (sat_cons (step1328 p h) (sat_cons (step1347 p h) (sat_cons (step2236 p h) (sat_cons (step2238 p h) (sat_cons (step1318 p h) (sat_cons (step221 p h) (sat_cons (step1315 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2470 : List Lit := [(64, false), (872, false), (63, false), (23, false), (972, false), (59, false), (62, false), (5, true), (55, false), (38, false), (48, true), (54, false), (944, false), (40, true), (1004, true), (984, true)]
theorem step2470 (p : Nat → Bool) (h : Constraints p) : clause p c2470 = true :=
  Snake9.TreeRup.prove_clause [c1496, c1426, c1399, c1417, c1485, c1527, c1301, c1369, c2465, c408, c434, c2467, c1327, c1334, c2469, c1059, c1060, c1067, c1068, c1072, c2381, c2389, c1043, c1128, c1130, c1032, c1123, c1125, c1098, c1031, c1119, c1108, c1085, c1030, c1117, c1101, c1083, c1114, c1100, c1082, c433, c283, c2461, c1396, c1397, c1422, c1392, c1491, c2249, c2248, c1522, c325, c373, c1368, c2263, c1350, c2466, c1319, c1335, c2468, c1329] c2470 (by decide) p (sat_cons (step1496 p h) (sat_cons (step1426 p h) (sat_cons (step1399 p h) (sat_cons (step1417 p h) (sat_cons (step1485 p h) (sat_cons (step1527 p h) (sat_cons (step1301 p h) (sat_cons (step1369 p h) (sat_cons (step2465 p h) (sat_cons (step408 p h) (sat_cons (step434 p h) (sat_cons (step2467 p h) (sat_cons (step1327 p h) (sat_cons (step1334 p h) (sat_cons (step2469 p h) (sat_cons (step1059 p h) (sat_cons (step1060 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_cons (step1072 p h) (sat_cons (step2381 p h) (sat_cons (step2389 p h) (sat_cons (step1043 p h) (sat_cons (step1128 p h) (sat_cons (step1130 p h) (sat_cons (step1032 p h) (sat_cons (step1123 p h) (sat_cons (step1125 p h) (sat_cons (step1098 p h) (sat_cons (step1031 p h) (sat_cons (step1119 p h) (sat_cons (step1108 p h) (sat_cons (step1085 p h) (sat_cons (step1030 p h) (sat_cons (step1117 p h) (sat_cons (step1101 p h) (sat_cons (step1083 p h) (sat_cons (step1114 p h) (sat_cons (step1100 p h) (sat_cons (step1082 p h) (sat_cons (step433 p h) (sat_cons (step283 p h) (sat_cons (step2461 p h) (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step1422 p h) (sat_cons (step1392 p h) (sat_cons (step1491 p h) (sat_cons (step2249 p h) (sat_cons (step2248 p h) (sat_cons (step1522 p h) (sat_cons (step325 p h) (sat_cons (step373 p h) (sat_cons (step1368 p h) (sat_cons (step2263 p h) (sat_cons (step1350 p h) (sat_cons (step2466 p h) (sat_cons (step1319 p h) (sat_cons (step1335 p h) (sat_cons (step2468 p h) (sat_cons (step1329 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2471 : List Lit := [(57, true), (959, false), (62, false), (5, true), (55, false), (38, false), (48, true), (54, false), (56, false), (944, false), (40, true), (70, false), (7, true), (1004, true), (984, true)]
theorem step2471 (p : Nat → Bool) (h : Constraints p) : clause p c2471 = true :=
  Snake9.LocalRup.prove_clause [c2069, c1496, c1426, c1399, c2460, c1417, c2274, c2269, c2464, c2470, c2064, c2278, c1457, c1115, c2385, c1466, c1117, c433, c1486, c1119, c2463, c1522, c1123, c2462, c1128, c1059, c2389, c1060, c1072, c1067, c1068] c2471 (by decide) p (sat_cons (step2069 p h) (sat_cons (step1496 p h) (sat_cons (step1426 p h) (sat_cons (step1399 p h) (sat_cons (step2460 p h) (sat_cons (step1417 p h) (sat_cons (step2274 p h) (sat_cons (step2269 p h) (sat_cons (step2464 p h) (sat_cons (step2470 p h) (sat_cons (step2064 p h) (sat_cons (step2278 p h) (sat_cons (step1457 p h) (sat_cons (step1115 p h) (sat_cons (step2385 p h) (sat_cons (step1466 p h) (sat_cons (step1117 p h) (sat_cons (step433 p h) (sat_cons (step1486 p h) (sat_cons (step1119 p h) (sat_cons (step2463 p h) (sat_cons (step1522 p h) (sat_cons (step1123 p h) (sat_cons (step2462 p h) (sat_cons (step1128 p h) (sat_cons (step1059 p h) (sat_cons (step2389 p h) (sat_cons (step1060 p h) (sat_cons (step1072 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2472 : List Lit := [(64, true), (872, false), (919, true), (26, true), (23, true), (959, false), (62, false), (944, false), (984, true)]
theorem step2472 (p : Nat → Bool) (h : Constraints p) : clause p c2472 = true :=
  Snake9.LocalRup.prove_clause [c2064, c2278, c1457, c1115, c1466, c1117, c1492, c1119, c1422, c1123, c1396, c1128, c1388, c2389, c2100, c1072, c2119, c1068, c232, c1067, c1059, c1060] c2472 (by decide) p (sat_cons (step2064 p h) (sat_cons (step2278 p h) (sat_cons (step1457 p h) (sat_cons (step1115 p h) (sat_cons (step1466 p h) (sat_cons (step1117 p h) (sat_cons (step1492 p h) (sat_cons (step1119 p h) (sat_cons (step1422 p h) (sat_cons (step1123 p h) (sat_cons (step1396 p h) (sat_cons (step1128 p h) (sat_cons (step1388 p h) (sat_cons (step2389 p h) (sat_cons (step2100 p h) (sat_cons (step1072 p h) (sat_cons (step2119 p h) (sat_cons (step1068 p h) (sat_cons (step232 p h) (sat_cons (step1067 p h) (sat_cons (step1059 p h) (sat_cons (step1060 p h) (sat_nil p)))))))))))))))))))))))
end B112E057
