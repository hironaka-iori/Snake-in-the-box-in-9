import B112E020Part0010
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2316 : List Lit := [(1655, true), (119, true), (55, true)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1284, c1280, c1276, c1277, c407, c1871] c2316 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1284 p h) (sat_cons (step1280 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step407 p h) (sat_cons (step1871 p h) (sat_nil p))))))))
def c2317 : List Lit := [(1597, false), (1630, true), (29, true)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c1989, c1110, c2047, c1213, c1207, c2309, c2057, c1232, c1111, c2051, c1968, c1732] c2317 (by decide) p (sat_cons (step1989 p h) (sat_cons (step1110 p h) (sat_cons (step2047 p h) (sat_cons (step1213 p h) (sat_cons (step1207 p h) (sat_cons (step2309 p h) (sat_cons (step2057 p h) (sat_cons (step1232 p h) (sat_cons (step1111 p h) (sat_cons (step2051 p h) (sat_cons (step1968 p h) (sat_cons (step1732 p h) (sat_nil p)))))))))))))
def c2318 : List Lit := [(1656, true), (67, false), (66, true), (1651, false), (29, false)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c1287, c1285, c1278, c1280, c397] c2318 (by decide) p (sat_cons (step1287 p h) (sat_cons (step1285 p h) (sat_cons (step1278 p h) (sat_cons (step1280 p h) (sat_cons (step397 p h) (sat_nil p))))))
def c2319 : List Lit := [(1648, true), (61, true), (69, false), (68, false), (67, true), (1645, false)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c1269, c1271, c1267, c1262, c1710] c2319 (by decide) p (sat_cons (step1269 p h) (sat_cons (step1271 p h) (sat_cons (step1267 p h) (sat_cons (step1262 p h) (sat_cons (step1710 p h) (sat_nil p))))))
def c2320 : List Lit := [(78, false), (1740, true), (115, false), (94, false)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c644, c643, c1439] c2320 (by decide) p (sat_cons (step644 p h) (sat_cons (step643 p h) (sat_cons (step1439 p h) (sat_nil p))))
def c2321 : List Lit := [(1739, true), (115, false), (94, false)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c1437, c1438, c656] c2321 (by decide) p (sat_cons (step1437 p h) (sat_cons (step1438 p h) (sat_cons (step656 p h) (sat_nil p))))
def c2322 : List Lit := [(1782, true), (1661, false), (1737, false), (115, false), (1741, false), (94, false), (1724, false), (1667, false)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c1320, c1341, c1362, c2321, c1446, c1467, c1489, c1530, c1490, c1468, c1449, c2320, c1316, c1534, c1321, c1363, c1345] c2322 (by decide) p (sat_cons (step1320 p h) (sat_cons (step1341 p h) (sat_cons (step1362 p h) (sat_cons (step2321 p h) (sat_cons (step1446 p h) (sat_cons (step1467 p h) (sat_cons (step1489 p h) (sat_cons (step1530 p h) (sat_cons (step1490 p h) (sat_cons (step1468 p h) (sat_cons (step1449 p h) (sat_cons (step2320 p h) (sat_cons (step1316 p h) (sat_cons (step1534 p h) (sat_cons (step1321 p h) (sat_cons (step1363 p h) (sat_cons (step1345 p h) (sat_nil p))))))))))))))))))
def c2323 : List Lit := [(1597, true), (1648, true), (103, false)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c1273, c1773, c2251, c2211, c1263, c1264, c1271, c269, c1265, c1853, c362] c2323 (by decide) p (sat_cons (step1273 p h) (sat_cons (step1773 p h) (sat_cons (step2251 p h) (sat_cons (step2211 p h) (sat_cons (step1263 p h) (sat_cons (step1264 p h) (sat_cons (step1271 p h) (sat_cons (step269 p h) (sat_cons (step1265 p h) (sat_cons (step1853 p h) (sat_cons (step362 p h) (sat_nil p))))))))))))
def c2324 : List Lit := [(1675, true), (120, true), (124, false), (82, true)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c1325, c1326, c477, c1895] c2324 (by decide) p (sat_cons (step1325 p h) (sat_cons (step1326 p h) (sat_cons (step477 p h) (sat_cons (step1895 p h) (sat_nil p)))))
def c2325 : List Lit := [(1750, true), (1741, false), (115, false), (94, false), (1731, false)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c2321, c1446, c1431, c1458, c1462, c1449, c1432, c1426, c654, c655, c1439] c2325 (by decide) p (sat_cons (step2321 p h) (sat_cons (step1446 p h) (sat_cons (step1431 p h) (sat_cons (step1458 p h) (sat_cons (step1462 p h) (sat_cons (step1449 p h) (sat_cons (step1432 p h) (sat_cons (step1426 p h) (sat_cons (step654 p h) (sat_cons (step655 p h) (sat_cons (step1439 p h) (sat_nil p))))))))))))
def c2326 : List Lit := [(111, false), (1742, true), (1721, true), (104, true), (110, true), (108, true), (109, false)]
theorem step2326 (p : Nat → Bool) (h : Constraints p) : clause p c2326 = true :=
  Snake9.LocalRup.prove_clause [c1930, c1929, c609, c612, c1398, c1442, c1403, c742, c1394] c2326 (by decide) p (sat_cons (step1930 p h) (sat_cons (step1929 p h) (sat_cons (step609 p h) (sat_cons (step612 p h) (sat_cons (step1398 p h) (sat_cons (step1442 p h) (sat_cons (step1403 p h) (sat_cons (step742 p h) (sat_cons (step1394 p h) (sat_nil p))))))))))
def c2327 : List Lit := [(78, false), (61, false), (79, false), (83, false), (1740, true), (115, false)]
theorem step2327 (p : Nat → Bool) (h : Constraints p) : clause p c2327 = true :=
  Snake9.LocalRup.prove_clause [c455, c630, c1439] c2327 (by decide) p (sat_cons (step455 p h) (sat_cons (step630 p h) (sat_cons (step1439 p h) (sat_nil p))))
def c2328 : List Lit := [(118, true), (1721, true), (61, false), (1751, true), (1741, false), (1740, true), (115, false), (104, true), (110, true), (108, true), (109, false), (1731, false)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c1437, c1439, c1446, c638, c1467, c1426, c1433, c1432, c1428, c1463, c2326, c1447] c2328 (by decide) p (sat_cons (step1437 p h) (sat_cons (step1439 p h) (sat_cons (step1446 p h) (sat_cons (step638 p h) (sat_cons (step1467 p h) (sat_cons (step1426 p h) (sat_cons (step1433 p h) (sat_cons (step1432 p h) (sat_cons (step1428 p h) (sat_cons (step1463 p h) (sat_cons (step2326 p h) (sat_cons (step1447 p h) (sat_nil p)))))))))))))
def c2329 : List Lit := [(1721, true), (61, false), (1731, false), (1751, true), (1741, false), (1740, true), (115, false), (104, true), (110, true), (108, true), (109, false)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c2328, c639, c640, c1426, c1438, c1432, c1446, c1463, c1467, c1447, c1433, c2326, c1428] c2329 (by decide) p (sat_cons (step2328 p h) (sat_cons (step639 p h) (sat_cons (step640 p h) (sat_cons (step1426 p h) (sat_cons (step1438 p h) (sat_cons (step1432 p h) (sat_cons (step1446 p h) (sat_cons (step1463 p h) (sat_cons (step1467 p h) (sat_cons (step1447 p h) (sat_cons (step1433 p h) (sat_cons (step2326 p h) (sat_cons (step1428 p h) (sat_nil p))))))))))))))
def c2330 : List Lit := [(113, false), (116, false), (119, true), (102, true), (103, false), (115, true)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c1934, c624] c2330 (by decide) p (sat_cons (step1934 p h) (sat_cons (step624 p h) (sat_nil p)))
def c2331 : List Lit := [(1684, true), (116, false), (1667, false), (82, true), (115, true)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c1320, c1345, c1342, c1321, c1333, c1316, c1326, c1891, c455] c2331 (by decide) p (sat_cons (step1320 p h) (sat_cons (step1345 p h) (sat_cons (step1342 p h) (sat_cons (step1321 p h) (sat_cons (step1333 p h) (sat_cons (step1316 p h) (sat_cons (step1326 p h) (sat_cons (step1891 p h) (sat_cons (step455 p h) (sat_nil p))))))))))
def c2332 : List Lit := [(1575, true), (1537, true), (26, false), (61, false), (29, true)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c1110, c2309, c2057, c1111, c2288, c147] c2332 (by decide) p (sat_cons (step1110 p h) (sat_cons (step2309 p h) (sat_cons (step2057 p h) (sat_cons (step1111 p h) (sat_cons (step2288 p h) (sat_cons (step147 p h) (sat_nil p)))))))
def c2333 : List Lit := [(56, false), (68, false), (109, false), (55, true)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c1860, c294] c2333 (by decide) p (sat_cons (step1860 p h) (sat_cons (step294 p h) (sat_nil p)))
def c2334 : List Lit := [(1601, true), (45, true), (46, false), (66, false), (1591, false)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c1716, c1173, c1196, c1199, c1176, c1167, c1762, c237, c1165, c1154] c2334 (by decide) p (sat_cons (step1716 p h) (sat_cons (step1173 p h) (sat_cons (step1196 p h) (sat_cons (step1199 p h) (sat_cons (step1176 p h) (sat_cons (step1167 p h) (sat_cons (step1762 p h) (sat_cons (step237 p h) (sat_cons (step1165 p h) (sat_cons (step1154 p h) (sat_nil p)))))))))))
def c2335 : List Lit := [(30, false), (1684, true), (26, false), (61, false), (107, false)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c2296, c153, c1316] c2335 (by decide) p (sat_cons (step2296 p h) (sat_cons (step153 p h) (sat_cons (step1316 p h) (sat_nil p))))
def c2336 : List Lit := [(1667, true), (74, false), (107, false)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c1312, c1313, c435] c2336 (by decide) p (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step435 p h) (sat_nil p))))
def c2337 : List Lit := [(1585, true), (47, true), (46, false), (66, false)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1159, c1161, c1157, c1153, c236] c2337 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1159 p h) (sat_cons (step1161 p h) (sat_cons (step1157 p h) (sat_cons (step1153 p h) (sat_cons (step236 p h) (sat_nil p)))))))
def c2338 : List Lit := [(119, false), (91, false), (74, false), (107, false)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c562, c564, c1904] c2338 (by decide) p (sat_cons (step562 p h) (sat_cons (step564 p h) (sat_cons (step1904 p h) (sat_nil p))))
def c2339 : List Lit := [(78, false), (1528, true), (1759, true), (64, true), (61, false)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c1750, c1864, c629, c630, c1438, c1439, c2298] c2339 (by decide) p (sat_cons (step1750 p h) (sat_cons (step1864 p h) (sat_cons (step629 p h) (sat_cons (step630 p h) (sat_cons (step1438 p h) (sat_cons (step1439 p h) (sat_cons (step2298 p h) (sat_nil p))))))))
def c2340 : List Lit := [(107, false), (19, true), (91, false), (1667, true)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c1313, c2336, c572, c1886] c2340 (by decide) p (sat_cons (step1313 p h) (sat_cons (step2336 p h) (sat_cons (step572 p h) (sat_cons (step1886 p h) (sat_nil p)))))
def c2341 : List Lit := [(1749, false), (1731, false), (1759, true), (61, false)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c1487, c1749, c2302] c2341 (by decide) p (sat_cons (step1487 p h) (sat_cons (step1749 p h) (sat_cons (step2302 p h) (sat_nil p))))
def c2342 : List Lit := [(113, true), (1749, true), (107, true), (1759, true), (75, false)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1465, c1433, c1426, c1428, c1435, c1432, c1425, c1460, c1461, c580, c1493, c1443, c1445, c1440, c1438, c2244, c715, c612, c1925] c2342 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1465 p h) (sat_cons (step1433 p h) (sat_cons (step1426 p h) (sat_cons (step1428 p h) (sat_cons (step1435 p h) (sat_cons (step1432 p h) (sat_cons (step1425 p h) (sat_cons (step1460 p h) (sat_cons (step1461 p h) (sat_cons (step580 p h) (sat_cons (step1493 p h) (sat_cons (step1443 p h) (sat_cons (step1445 p h) (sat_cons (step1440 p h) (sat_cons (step1438 p h) (sat_cons (step2244 p h) (sat_cons (step715 p h) (sat_cons (step612 p h) (sat_cons (step1925 p h) (sat_nil p)))))))))))))))))))))
def c2343 : List Lit := [(107, true), (1759, true), (80, false), (64, true), (61, false), (75, false)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1431, c2341, c1457, c2342, c2295, c1437, c1445, c1446, c1456, c1461, c1440, c1441, c1493, c1434, c2215, c2144, c2078, c1398] c2343 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1431 p h) (sat_cons (step2341 p h) (sat_cons (step1457 p h) (sat_cons (step2342 p h) (sat_cons (step2295 p h) (sat_cons (step1437 p h) (sat_cons (step1445 p h) (sat_cons (step1446 p h) (sat_cons (step1456 p h) (sat_cons (step1461 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step1493 p h) (sat_cons (step1434 p h) (sat_cons (step2215 p h) (sat_cons (step2144 p h) (sat_cons (step2078 p h) (sat_cons (step1398 p h) (sat_nil p))))))))))))))))))))
def c2344 : List Lit := [(1530, false), (1536, true)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c2285, c1076] c2344 (by decide) p (sat_cons (step2285 p h) (sat_cons (step1076 p h) (sat_nil p)))
def c2345 : List Lit := [(1537, true), (1531, false)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c2285, c1077] c2345 (by decide) p (sat_cons (step2285 p h) (sat_cons (step1077 p h) (sat_nil p)))
def c2346 : List Lit := [(1532, false), (1538, true)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c2285, c1078] c2346 (by decide) p (sat_cons (step2285 p h) (sat_cons (step1078 p h) (sat_nil p)))
def c2347 : List Lit := [(1514, false), (1547, true)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c2286, c1104] c2347 (by decide) p (sat_cons (step2286 p h) (sat_cons (step1104 p h) (sat_nil p)))
def c2348 : List Lit := [(107, false), (1759, false), (64, true), (1556, false), (1656, false), (1585, false), (60, true), (46, false), (66, false), (1546, false), (19, true), (1667, true)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c2047, c1262, c1270, c1296, c1313, c1312, c2340, c2336, c1328, c1890, c1777, c1363, c1532, c2019, c1234, c1209, c1717, c1190, c1765, c1177, c1167, c1168, c1174, c1175, c1189, c2211, c2257, c1264, c2018, c1273, c1536, c1301, c1368] c2348 (by decide) p (sat_cons (step2047 p h) (sat_cons (step1262 p h) (sat_cons (step1270 p h) (sat_cons (step1296 p h) (sat_cons (step1313 p h) (sat_cons (step1312 p h) (sat_cons (step2340 p h) (sat_cons (step2336 p h) (sat_cons (step1328 p h) (sat_cons (step1890 p h) (sat_cons (step1777 p h) (sat_cons (step1363 p h) (sat_cons (step1532 p h) (sat_cons (step2019 p h) (sat_cons (step1234 p h) (sat_cons (step1209 p h) (sat_cons (step1717 p h) (sat_cons (step1190 p h) (sat_cons (step1765 p h) (sat_cons (step1177 p h) (sat_cons (step1167 p h) (sat_cons (step1168 p h) (sat_cons (step1174 p h) (sat_cons (step1175 p h) (sat_cons (step1189 p h) (sat_cons (step2211 p h) (sat_cons (step2257 p h) (sat_cons (step1264 p h) (sat_cons (step2018 p h) (sat_cons (step1273 p h) (sat_cons (step1536 p h) (sat_cons (step1301 p h) (sat_cons (step1368 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c2349 : List Lit := [(1598, true), (1585, false), (46, false), (66, false)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c1193, c1189, c2053, c1174, c1167] c2349 (by decide) p (sat_cons (step1193 p h) (sat_cons (step1189 p h) (sat_cons (step2053 p h) (sat_cons (step1174 p h) (sat_cons (step1167 p h) (sat_nil p))))))
def c2350 : List Lit := [(113, true), (108, false), (75, false), (107, true), (1737, true)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1433, c1426, c1428, c1435, c580, c1425] c2350 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1433 p h) (sat_cons (step1426 p h) (sat_cons (step1428 p h) (sat_cons (step1435 p h) (sat_cons (step580 p h) (sat_cons (step1425 p h) (sat_nil p))))))))
def c2351 : List Lit := [(1736, false), (107, true), (103, true), (1760, true), (118, true), (1719, false)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c1437, c1445, c2073, c1461, c1440, c1441, c2221, c1494, c2105, c1396] c2351 (by decide) p (sat_cons (step1437 p h) (sat_cons (step1445 p h) (sat_cons (step2073 p h) (sat_cons (step1461 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step2221 p h) (sat_cons (step1494 p h) (sat_cons (step2105 p h) (sat_cons (step1396 p h) (sat_nil p)))))))))))
def c2352 : List Lit := [(1717, true), (111, false), (109, false)]
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c1396, c1397, c546, c1922, c609] c2352 (by decide) p (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step546 p h) (sat_cons (step1922 p h) (sat_cons (step609 p h) (sat_nil p))))))
def c2353 : List Lit := [(103, true), (1760, true), (118, true), (1715, false), (1732, true), (107, true)]
theorem step2353 (p : Nat → Bool) (h : Constraints p) : clause p c2353 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1431, c1437, c1445, c1456, c1499, c1401, c1425, c2351, c1432, c1426, c1427, c2352, c1402, c2118, c1440, c2221, c2240, c1494, c1698, c1439, c2188, c1414, c1403, c1398, c657, c2041] c2353 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1431 p h) (sat_cons (step1437 p h) (sat_cons (step1445 p h) (sat_cons (step1456 p h) (sat_cons (step1499 p h) (sat_cons (step1401 p h) (sat_cons (step1425 p h) (sat_cons (step2351 p h) (sat_cons (step1432 p h) (sat_cons (step1426 p h) (sat_cons (step1427 p h) (sat_cons (step2352 p h) (sat_cons (step1402 p h) (sat_cons (step2118 p h) (sat_cons (step1440 p h) (sat_cons (step2221 p h) (sat_cons (step2240 p h) (sat_cons (step1494 p h) (sat_cons (step1698 p h) (sat_cons (step1439 p h) (sat_cons (step2188 p h) (sat_cons (step1414 p h) (sat_cons (step1403 p h) (sat_cons (step1398 p h) (sat_cons (step657 p h) (sat_cons (step2041 p h) (sat_nil p))))))))))))))))))))))))))))
def c2354 : List Lit := [(111, false), (1741, true), (103, false), (109, false)]
theorem step2354 (p : Nat → Bool) (h : Constraints p) : clause p c2354 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1440, c589, c745, c612, c1928] c2354 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1440 p h) (sat_cons (step589 p h) (sat_cons (step745 p h) (sat_cons (step612 p h) (sat_cons (step1928 p h) (sat_nil p)))))))
def c2355 : List Lit := [(1720, false), (103, false), (1760, true), (118, true), (109, false), (1731, false)]
theorem step2355 (p : Nat → Bool) (h : Constraints p) : clause p c2355 = true :=
  Snake9.LocalRup.prove_clause [c1437, c1445, c1431, c2118, c2354, c1427, c1432, c1461, c2071, c1494] c2355 (by decide) p (sat_cons (step1437 p h) (sat_cons (step1445 p h) (sat_cons (step1431 p h) (sat_cons (step2118 p h) (sat_cons (step2354 p h) (sat_cons (step1427 p h) (sat_cons (step1432 p h) (sat_cons (step1461 p h) (sat_cons (step2071 p h) (sat_cons (step1494 p h) (sat_nil p)))))))))))
def c2356 : List Lit := [(1760, true), (118, true), (1715, false), (1732, true), (107, true)]
theorem step2356 (p : Nat → Bool) (h : Constraints p) : clause p c2356 = true :=
  Snake9.LocalRup.prove_clause [c1401, c1425, c1424, c2353, c2355, c1402, c1396, c1397, c2352, c543, c2068] c2356 (by decide) p (sat_cons (step1401 p h) (sat_cons (step1425 p h) (sat_cons (step1424 p h) (sat_cons (step2353 p h) (sat_cons (step2355 p h) (sat_cons (step1402 p h) (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step2352 p h) (sat_cons (step543 p h) (sat_cons (step2068 p h) (sat_nil p))))))))))))
def c2357 : List Lit := [(1761, true), (118, true), (1751, false), (1737, false), (1741, false), (1719, false)]
theorem step2357 (p : Nat → Bool) (h : Constraints p) : clause p c2357 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1483, c1489, c1468, c1412, c1449, c2188, c1439] c2357 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1483 p h) (sat_cons (step1489 p h) (sat_cons (step1468 p h) (sat_cons (step1412 p h) (sat_cons (step1449 p h) (sat_cons (step2188 p h) (sat_cons (step1439 p h) (sat_nil p)))))))))
def c2358 : List Lit := [(1569, true), (38, true), (89, false)]
theorem step2358 (p : Nat → Bool) (h : Constraints p) : clause p c2358 = true :=
  Snake9.LocalRup.prove_clause [c1127, c1130, c1766, c1132, c1128, c1123, c1835, c192] c2358 (by decide) p (sat_cons (step1127 p h) (sat_cons (step1130 p h) (sat_cons (step1766 p h) (sat_cons (step1132 p h) (sat_cons (step1128 p h) (sat_cons (step1123 p h) (sat_cons (step1835 p h) (sat_cons (step192 p h) (sat_nil p)))))))))
def c2359 : List Lit := [(19, false), (1512, true), (1536, true), (29, false)]
theorem step2359 (p : Nat → Bool) (h : Constraints p) : clause p c2359 = true :=
  Snake9.LocalRup.prove_clause [c1732, c1059, c73, c76, c1016, c1783, c1642, c1019, c1021, c1694, c1039, c1061, c1028, c121, c1797, c33, c1024, c1026, c1027, c1785, c1043, c1018, c1020] c2359 (by decide) p (sat_cons (step1732 p h) (sat_cons (step1059 p h) (sat_cons (step73 p h) (sat_cons (step76 p h) (sat_cons (step1016 p h) (sat_cons (step1783 p h) (sat_cons (step1642 p h) (sat_cons (step1019 p h) (sat_cons (step1021 p h) (sat_cons (step1694 p h) (sat_cons (step1039 p h) (sat_cons (step1061 p h) (sat_cons (step1028 p h) (sat_cons (step121 p h) (sat_cons (step1797 p h) (sat_cons (step33 p h) (sat_cons (step1024 p h) (sat_cons (step1026 p h) (sat_cons (step1027 p h) (sat_cons (step1785 p h) (sat_cons (step1043 p h) (sat_cons (step1018 p h) (sat_cons (step1020 p h) (sat_nil p))))))))))))))))))))))))
def c2360 : List Lit := [(1536, true), (1597, false), (1630, true)]
theorem step2360 (p : Nat → Bool) (h : Constraints p) : clause p c2360 = true :=
  Snake9.LocalRup.prove_clause [c2317, c1732, c1058, c1059, c2205, c1207, c1232, c1973, c2359, c1813, c1812, c1563] c2360 (by decide) p (sat_cons (step2317 p h) (sat_cons (step1732 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step2205 p h) (sat_cons (step1207 p h) (sat_cons (step1232 p h) (sat_cons (step1973 p h) (sat_cons (step2359 p h) (sat_cons (step1813 p h) (sat_cons (step1812 p h) (sat_cons (step1563 p h) (sat_nil p)))))))))))))
def c2361 : List Lit := [(31, true), (1574, true)]
theorem step2361 (p : Nat → Bool) (h : Constraints p) : clause p c2361 = true :=
  Snake9.LocalRup.prove_clause [c1977, c1116, c1113, c1114, c1115, c2048, c1141] c2361 (by decide) p (sat_cons (step1977 p h) (sat_cons (step1116 p h) (sat_cons (step1113 p h) (sat_cons (step1114 p h) (sat_cons (step1115 p h) (sat_cons (step2048 p h) (sat_cons (step1141 p h) (sat_nil p))))))))
def c2362 : List Lit := [(9, true), (19, true), (24, false), (1512, true), (29, false)]
theorem step2362 (p : Nat → Bool) (h : Constraints p) : clause p c2362 = true :=
  Snake9.LocalRup.prove_clause [c2259, c1021, c119, c1821, c28, c33, c1016, c1026, c1019, c1028, c1039] c2362 (by decide) p (sat_cons (step2259 p h) (sat_cons (step1021 p h) (sat_cons (step119 p h) (sat_cons (step1821 p h) (sat_cons (step28 p h) (sat_cons (step33 p h) (sat_cons (step1016 p h) (sat_cons (step1026 p h) (sat_cons (step1019 p h) (sat_cons (step1028 p h) (sat_cons (step1039 p h) (sat_nil p))))))))))))
def c2363 : List Lit := [(19, true), (31, false), (24, false), (1608, true), (1512, true), (29, false), (1586, true)]
theorem step2363 (p : Nat → Bool) (h : Constraints p) : clause p c2363 = true :=
  Snake9.LocalRup.prove_clause [c2362, c1785, c156, c1798, c1017, c1676, c1019, c1162, c2262, c1039, c1024, c1027, c1030, c1043, c1021, c1020, c119, c1018, c1821, c28] c2363 (by decide) p (sat_cons (step2362 p h) (sat_cons (step1785 p h) (sat_cons (step156 p h) (sat_cons (step1798 p h) (sat_cons (step1017 p h) (sat_cons (step1676 p h) (sat_cons (step1019 p h) (sat_cons (step1162 p h) (sat_cons (step2262 p h) (sat_cons (step1039 p h) (sat_cons (step1024 p h) (sat_cons (step1027 p h) (sat_cons (step1030 p h) (sat_cons (step1043 p h) (sat_cons (step1021 p h) (sat_cons (step1020 p h) (sat_cons (step119 p h) (sat_cons (step1018 p h) (sat_cons (step1821 p h) (sat_cons (step28 p h) (sat_nil p)))))))))))))))))))))
def c2364 : List Lit := [(9, false), (31, false), (24, false), (1608, true), (1512, true), (1526, true), (29, false), (1586, true)]
theorem step2364 (p : Nat → Bool) (h : Constraints p) : clause p c2364 = true :=
  Snake9.LocalRup.prove_clause [c2363, c1785, c156, c1798, c1828, c1826, c1676, c1564, c1162, c2262, c1060, c1024, c73, c1027, c1018, c1043, c1020] c2364 (by decide) p (sat_cons (step2363 p h) (sat_cons (step1785 p h) (sat_cons (step156 p h) (sat_cons (step1798 p h) (sat_cons (step1828 p h) (sat_cons (step1826 p h) (sat_cons (step1676 p h) (sat_cons (step1564 p h) (sat_cons (step1162 p h) (sat_cons (step2262 p h) (sat_cons (step1060 p h) (sat_cons (step1024 p h) (sat_cons (step73 p h) (sat_cons (step1027 p h) (sat_cons (step1018 p h) (sat_cons (step1043 p h) (sat_cons (step1020 p h) (sat_nil p))))))))))))))))))
def c2365 : List Lit := [(1597, false), (1630, true)]
theorem step2365 (p : Nat → Bool) (h : Constraints p) : clause p c2365 = true :=
  Snake9.LocalRup.prove_clause [c2241, c1193, c1980, c2317, c1239, c1969, c2345, c2267, c2360, c1968, c1096, c1232, c1207, c2287, c2361, c2363, c2364, c2259, c1021, c119, c1797, c1553, c33, c1016, c1026, c1019, c1028, c1039] c2365 (by decide) p (sat_cons (step2241 p h) (sat_cons (step1193 p h) (sat_cons (step1980 p h) (sat_cons (step2317 p h) (sat_cons (step1239 p h) (sat_cons (step1969 p h) (sat_cons (step2345 p h) (sat_cons (step2267 p h) (sat_cons (step2360 p h) (sat_cons (step1968 p h) (sat_cons (step1096 p h) (sat_cons (step1232 p h) (sat_cons (step1207 p h) (sat_cons (step2287 p h) (sat_cons (step2361 p h) (sat_cons (step2363 p h) (sat_cons (step2364 p h) (sat_cons (step2259 p h) (sat_cons (step1021 p h) (sat_cons (step119 p h) (sat_cons (step1797 p h) (sat_cons (step1553 p h) (sat_cons (step33 p h) (sat_cons (step1016 p h) (sat_cons (step1026 p h) (sat_cons (step1019 p h) (sat_cons (step1028 p h) (sat_cons (step1039 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2366 : List Lit := [(5, true), (1512, true), (9, true), (1583, true)]
theorem step2366 (p : Nat → Bool) (h : Constraints p) : clause p c2366 = true :=
  Snake9.LocalRup.prove_clause [c1016, c1783, c1019, c1703, c1039, c1026, c1028] c2366 (by decide) p (sat_cons (step1016 p h) (sat_cons (step1783 p h) (sat_cons (step1019 p h) (sat_cons (step1703 p h) (sat_cons (step1039 p h) (sat_cons (step1026 p h) (sat_cons (step1028 p h) (sat_nil p))))))))
def c2367 : List Lit := [(1505, false), (5, false), (1512, true), (1597, true)]
theorem step2367 (p : Nat → Bool) (h : Constraints p) : clause p c2367 = true :=
  Snake9.LocalRup.prove_clause [c1036, c1188, c2273, c1163, c1028, c1031, c1039, c1021, c1022, c1019, c29, c1017, c1796, c1791, c1788, c211, c13, c1153, c1154, c1160, c1161, c1185, c1155, c1174, c2276, c1167] c2367 (by decide) p (sat_cons (step1036 p h) (sat_cons (step1188 p h) (sat_cons (step2273 p h) (sat_cons (step1163 p h) (sat_cons (step1028 p h) (sat_cons (step1031 p h) (sat_cons (step1039 p h) (sat_cons (step1021 p h) (sat_cons (step1022 p h) (sat_cons (step1019 p h) (sat_cons (step29 p h) (sat_cons (step1017 p h) (sat_cons (step1796 p h) (sat_cons (step1791 p h) (sat_cons (step1788 p h) (sat_cons (step211 p h) (sat_cons (step13 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1185 p h) (sat_cons (step1155 p h) (sat_cons (step1174 p h) (sat_cons (step2276 p h) (sat_cons (step1167 p h) (sat_nil p)))))))))))))))))))))))))))
def c2368 : List Lit := [(1512, true), (9, true), (1597, true)]
theorem step2368 (p : Nat → Bool) (h : Constraints p) : clause p c2368 = true :=
  Snake9.LocalRup.prove_clause [c1188, c2273, c1159, c2366, c2367, c1026, c1805, c31] c2368 (by decide) p (sat_cons (step1188 p h) (sat_cons (step2273 p h) (sat_cons (step1159 p h) (sat_cons (step2366 p h) (sat_cons (step2367 p h) (sat_cons (step1026 p h) (sat_cons (step1805 p h) (sat_cons (step31 p h) (sat_nil p)))))))))
def c2369 : List Lit := [(1512, false), (1630, true)]
theorem step2369 (p : Nat → Bool) (h : Constraints p) : clause p c2369 = true :=
  Snake9.LocalRup.prove_clause [c2365, c2315, c1110, c2047, c1985, c1239, c1973, c1096, c1232, c1732, c1986, c2309, c2057, c1111, c2051] c2369 (by decide) p (sat_cons (step2365 p h) (sat_cons (step2315 p h) (sat_cons (step1110 p h) (sat_cons (step2047 p h) (sat_cons (step1985 p h) (sat_cons (step1239 p h) (sat_cons (step1973 p h) (sat_cons (step1096 p h) (sat_cons (step1232 p h) (sat_cons (step1732 p h) (sat_cons (step1986 p h) (sat_cons (step2309 p h) (sat_cons (step2057 p h) (sat_cons (step1111 p h) (sat_cons (step2051 p h) (sat_nil p))))))))))))))))
def c2370 : List Lit := [(31, false), (1685, true), (1536, true), (9, false)]
theorem step2370 (p : Nat → Bool) (h : Constraints p) : clause p c2370 = true :=
  Snake9.LocalRup.prove_clause [c1732, c1059, c1058, c80, c1828, c1811, c1813, c1827, c156, c158, c104, c1062, c1713, c1694, c77, c1642] c2370 (by decide) p (sat_cons (step1732 p h) (sat_cons (step1059 p h) (sat_cons (step1058 p h) (sat_cons (step80 p h) (sat_cons (step1828 p h) (sat_cons (step1811 p h) (sat_cons (step1813 p h) (sat_cons (step1827 p h) (sat_cons (step156 p h) (sat_cons (step158 p h) (sat_cons (step104 p h) (sat_cons (step1062 p h) (sat_cons (step1713 p h) (sat_cons (step1694 p h) (sat_cons (step77 p h) (sat_cons (step1642 p h) (sat_nil p)))))))))))))))))
def c2371 : List Lit := [(1557, false), (31, true), (1576, true)]
theorem step2371 (p : Nat → Bool) (h : Constraints p) : clause p c2371 = true :=
  Snake9.LocalRup.prove_clause [c1113, c1979, c1122, c1121, c1114, c1148, c2048] c2371 (by decide) p (sat_cons (step1113 p h) (sat_cons (step1979 p h) (sat_cons (step1122 p h) (sat_cons (step1121 p h) (sat_cons (step1114 p h) (sat_cons (step1148 p h) (sat_cons (step2048 p h) (sat_nil p))))))))
def c2372 : List Lit := [(24, true), (30, false), (1536, true)]
theorem step2372 (p : Nat → Bool) (h : Constraints p) : clause p c2372 = true :=
  Snake9.LocalRup.prove_clause [c2344, c1065, c1732, c1649, c1062, c1063, c1064, c1694, c1080, c1642, c1645, c1051, c63, c138, c1806] c2372 (by decide) p (sat_cons (step2344 p h) (sat_cons (step1065 p h) (sat_cons (step1732 p h) (sat_cons (step1649 p h) (sat_cons (step1062 p h) (sat_cons (step1063 p h) (sat_cons (step1064 p h) (sat_cons (step1694 p h) (sat_cons (step1080 p h) (sat_cons (step1642 p h) (sat_cons (step1645 p h) (sat_cons (step1051 p h) (sat_cons (step63 p h) (sat_cons (step138 p h) (sat_cons (step1806 p h) (sat_nil p))))))))))))))))
def c2373 : List Lit := [(1527, false), (30, false), (1536, true)]
theorem step2373 (p : Nat → Bool) (h : Constraints p) : clause p c2373 = true :=
  Snake9.LocalRup.prove_clause [c2372, c1732, c1649, c1064, c1694, c1080, c1642, c1645, c1051, c135, c50, c1807] c2373 (by decide) p (sat_cons (step2372 p h) (sat_cons (step1732 p h) (sat_cons (step1649 p h) (sat_cons (step1064 p h) (sat_cons (step1694 p h) (sat_cons (step1080 p h) (sat_cons (step1642 p h) (sat_cons (step1645 p h) (sat_cons (step1051 p h) (sat_cons (step135 p h) (sat_cons (step50 p h) (sat_cons (step1807 p h) (sat_nil p)))))))))))))
def c2374 : List Lit := [(1502, false), (1630, true)]
theorem step2374 (p : Nat → Bool) (h : Constraints p) : clause p c2374 = true :=
  Snake9.LocalRup.prove_clause [c2369, c2365, c2368, c1785, c1017, c1019, c1039, c1188, c2273, c1783, c1030, c1024, c1805, c31] c2374 (by decide) p (sat_cons (step2369 p h) (sat_cons (step2365 p h) (sat_cons (step2368 p h) (sat_cons (step1785 p h) (sat_cons (step1017 p h) (sat_cons (step1019 p h) (sat_cons (step1039 p h) (sat_cons (step1188 p h) (sat_cons (step2273 p h) (sat_cons (step1783 p h) (sat_cons (step1030 p h) (sat_cons (step1024 p h) (sat_cons (step1805 p h) (sat_cons (step31 p h) (sat_nil p)))))))))))))))
def c2375 : List Lit := [(1630, true)]
theorem step2375 (p : Nat → Bool) (h : Constraints p) : clause p c2375 = true :=
  Snake9.LocalRup.prove_clause [c2365, c1188, c1159, c1163, c2273, c2369, c2368, c1785, c2374, c1021, c1703, c1024, c1027, c1043, c1020, c1018, c29, c1796, c2282, c245, c211, c1153, c1154, c1160, c1161, c1185, c1155, c1174, c2284, c1167] c2375 (by decide) p (sat_cons (step2365 p h) (sat_cons (step1188 p h) (sat_cons (step1159 p h) (sat_cons (step1163 p h) (sat_cons (step2273 p h) (sat_cons (step2369 p h) (sat_cons (step2368 p h) (sat_cons (step1785 p h) (sat_cons (step2374 p h) (sat_cons (step1021 p h) (sat_cons (step1703 p h) (sat_cons (step1024 p h) (sat_cons (step1027 p h) (sat_cons (step1043 p h) (sat_cons (step1020 p h) (sat_cons (step1018 p h) (sat_cons (step29 p h) (sat_cons (step1796 p h) (sat_cons (step2282 p h) (sat_cons (step245 p h) (sat_cons (step211 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1185 p h) (sat_cons (step1155 p h) (sat_cons (step1174 p h) (sat_cons (step2284 p h) (sat_cons (step1167 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2376 : List Lit := [(1782, false)]
theorem step2376 (p : Nat → Bool) (h : Constraints p) : clause p c2376 = true :=
  Snake9.LocalRup.prove_clause [c2375, c2017] c2376 (by decide) p (sat_cons (step2375 p h) (sat_cons (step2017 p h) (sat_nil p)))
def c2377 : List Lit := [(1698, false)]
theorem step2377 (p : Nat → Bool) (h : Constraints p) : clause p c2377 = true :=
  Snake9.LocalRup.prove_clause [c2376, c2014] c2377 (by decide) p (sat_cons (step2376 p h) (sat_cons (step2014 p h) (sat_nil p)))
def c2378 : List Lit := [(1597, true), (9, false), (42, true), (43, false), (10, true), (47, false)]
theorem step2378 (p : Nat → Bool) (h : Constraints p) : clause p c2378 = true :=
  Snake9.LocalRup.prove_clause [c1153, c1160, c1188, c2282, c1185, c1163, c1161, c245, c1174, c1154, c1155, c1167, c2284] c2378 (by decide) p (sat_cons (step1153 p h) (sat_cons (step1160 p h) (sat_cons (step1188 p h) (sat_cons (step2282 p h) (sat_cons (step1185 p h) (sat_cons (step1163 p h) (sat_cons (step1161 p h) (sat_cons (step245 p h) (sat_cons (step1174 p h) (sat_cons (step1154 p h) (sat_cons (step1155 p h) (sat_cons (step1167 p h) (sat_cons (step2284 p h) (sat_nil p))))))))))))))
def c2379 : List Lit := [(32, false), (7, false), (22, false), (21, false)]
theorem step2379 (p : Nat → Bool) (h : Constraints p) : clause p c2379 = true :=
  Snake9.LocalRup.prove_clause [c94, c92, c1811] c2379 (by decide) p (sat_cons (step94 p h) (sat_cons (step92 p h) (sat_cons (step1811 p h) (sat_nil p))))
end B112E020
