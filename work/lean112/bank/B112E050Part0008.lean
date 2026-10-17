import B112E050Part0007
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2328 : List Lit := [(127, true), (1806, true), (125, false), (1812, true), (104, false)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c2317, c1589, c1600, c831, c1585] c2328 (by decide) p (sat_cons (step2317 p h) (sat_cons (step1589 p h) (sat_cons (step1600 p h) (sat_cons (step831 p h) (sat_cons (step1585 p h) (sat_nil p))))))
def c2329 : List Lit := [(102, true), (1731, false), (101, false), (97, false), (1752, true), (1742, false), (107, true)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c2134, c2133, c1791, c431, c435, c1422, c1435, c1428, c1446, c1460] c2329 (by decide) p (sat_cons (step2134 p h) (sat_cons (step2133 p h) (sat_cons (step1791 p h) (sat_cons (step431 p h) (sat_cons (step435 p h) (sat_cons (step1422 p h) (sat_cons (step1435 p h) (sat_cons (step1428 p h) (sat_cons (step1446 p h) (sat_cons (step1460 p h) (sat_nil p)))))))))))
def c2330 : List Lit := [(1579, false), (1588, false), (1597, true), (93, true)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1160, c1132, c1156, c1144, c1136, c1133, c1125, c1126, c2031, c55] c2330 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1160 p h) (sat_cons (step1132 p h) (sat_cons (step1156 p h) (sat_cons (step1144 p h) (sat_cons (step1136 p h) (sat_cons (step1133 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step2031 p h) (sat_cons (step55 p h) (sat_nil p))))))))))))
def c2331 : List Lit := [(1618, false), (39, true), (114, true), (123, false), (1636, true)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c1201, c1208, c1223, c1194, c1195, c1220, c1190, c1923, c2044] c2331 (by decide) p (sat_cons (step1201 p h) (sat_cons (step1208 p h) (sat_cons (step1223 p h) (sat_cons (step1194 p h) (sat_cons (step1195 p h) (sat_cons (step1220 p h) (sat_cons (step1190 p h) (sat_cons (step1923 p h) (sat_cons (step2044 p h) (sat_nil p))))))))))
def c2332 : List Lit := [(119, true), (93, true), (127, false), (1800, true)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1573, c1575, c1579, c1570, c1571, c701, c776, c2161] c2332 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1573 p h) (sat_cons (step1575 p h) (sat_cons (step1579 p h) (sat_cons (step1570 p h) (sat_cons (step1571 p h) (sat_cons (step701 p h) (sat_cons (step776 p h) (sat_cons (step2161 p h) (sat_nil p))))))))))
def c2333 : List Lit := [(35, false), (114, true), (123, false), (1636, true)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c1216, c2044, c2045, c152, c153, c1200, c1204, c1209, c1212, c1220, c1202, c1194, c99, c1186] c2333 (by decide) p (sat_cons (step1216 p h) (sat_cons (step2044 p h) (sat_cons (step2045 p h) (sat_cons (step152 p h) (sat_cons (step153 p h) (sat_cons (step1200 p h) (sat_cons (step1204 p h) (sat_cons (step1209 p h) (sat_cons (step1212 p h) (sat_cons (step1220 p h) (sat_cons (step1202 p h) (sat_cons (step1194 p h) (sat_cons (step99 p h) (sat_cons (step1186 p h) (sat_nil p)))))))))))))))
def c2334 : List Lit := [(33, false), (39, false), (35, true), (1636, true), (109, false)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c1961, c1191, c1193, c1223, c1206, c1942, c1204, c101] c2334 (by decide) p (sat_cons (step1961 p h) (sat_cons (step1191 p h) (sat_cons (step1193 p h) (sat_cons (step1223 p h) (sat_cons (step1206 p h) (sat_cons (step1942 p h) (sat_cons (step1204 p h) (sat_cons (step101 p h) (sat_nil p)))))))))
def c2335 : List Lit := [(48, false), (127, false), (35, true), (1636, true), (109, false)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c1190, c1192, c1220, c2309, c2334, c1186, c1195, c1223, c1206, c1208, c1203, c1200, c166] c2335 (by decide) p (sat_cons (step1190 p h) (sat_cons (step1192 p h) (sat_cons (step1220 p h) (sat_cons (step2309 p h) (sat_cons (step2334 p h) (sat_cons (step1186 p h) (sat_cons (step1195 p h) (sat_cons (step1223 p h) (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step1203 p h) (sat_cons (step1200 p h) (sat_cons (step166 p h) (sat_nil p))))))))))))))
def c2336 : List Lit := [(119, true), (117, false), (127, false), (1800, true)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c1577, c1573, c1575, c1579, c776, c1570] c2336 (by decide) p (sat_cons (step1577 p h) (sat_cons (step1573 p h) (sat_cons (step1575 p h) (sat_cons (step1579 p h) (sat_cons (step776 p h) (sat_cons (step1570 p h) (sat_nil p)))))))
def c2337 : List Lit := [(117, false), (127, false), (114, true), (1800, true), (109, false)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c2336, c2314, c777] c2337 (by decide) p (sat_cons (step2336 p h) (sat_cons (step2314 p h) (sat_cons (step777 p h) (sat_nil p))))
def c2338 : List Lit := [(106, false), (97, true), (127, false), (1777, true), (103, false)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c638, c635, c1522, c1520, c1530] c2338 (by decide) p (sat_cons (step638 p h) (sat_cons (step635 p h) (sat_cons (step1522 p h) (sat_cons (step1520 p h) (sat_cons (step1530 p h) (sat_nil p))))))
def c2339 : List Lit := [(119, false), (117, false), (1800, true), (127, true), (125, true), (123, false), (107, true), (1812, true), (109, false)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c2295, c2314, c775, c1574, c1579, c1571, c698, c2153, c2154, c796, c786, c1585, c2179, c1600, c1589, c1591] c2339 (by decide) p (sat_cons (step2295 p h) (sat_cons (step2314 p h) (sat_cons (step775 p h) (sat_cons (step1574 p h) (sat_cons (step1579 p h) (sat_cons (step1571 p h) (sat_cons (step698 p h) (sat_cons (step2153 p h) (sat_cons (step2154 p h) (sat_cons (step796 p h) (sat_cons (step786 p h) (sat_cons (step1585 p h) (sat_cons (step2179 p h) (sat_cons (step1600 p h) (sat_cons (step1589 p h) (sat_cons (step1591 p h) (sat_nil p)))))))))))))))))
def c2340 : List Lit := [(27, false), (102, false), (1774, true), (123, false)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c576, c574, c1523] c2340 (by decide) p (sat_cons (step576 p h) (sat_cons (step574 p h) (sat_cons (step1523 p h) (sat_nil p))))
def c2341 : List Lit := [(3, true), (1575, true), (4, true), (1556, false), (137, true), (10, true)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c1098, c2022, c1105, c2021, c1121, c1109, c1856] c2341 (by decide) p (sat_cons (step1098 p h) (sat_cons (step2022 p h) (sat_cons (step1105 p h) (sat_cons (step2021 p h) (sat_cons (step1121 p h) (sat_cons (step1109 p h) (sat_cons (step1856 p h) (sat_nil p))))))))
def c2342 : List Lit := [(39, true), (43, true), (48, false), (127, false), (1632, true)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1212, c1201, c1210, c1205, c166, c1202] c2342 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1212 p h) (sat_cons (step1201 p h) (sat_cons (step1210 p h) (sat_cons (step1205 p h) (sat_cons (step166 p h) (sat_cons (step1202 p h) (sat_nil p))))))))
def c2343 : List Lit := [(33, false), (34, false), (35, false), (48, false), (127, false), (1632, true)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c1951, c2342, c99] c2343 (by decide) p (sat_cons (step1951 p h) (sat_cons (step2342 p h) (sat_cons (step99 p h) (sat_nil p))))
def c2344 : List Lit := [(114, true), (106, true), (1800, true), (118, false), (127, false), (1636, true), (109, false)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c1216, c2337, c2175, c2335, c2044, c2045, c2343, c1758, c1186, c1204, c2342, c1206, c124, c123, c1223, c2047, c1195, c1189] c2344 (by decide) p (sat_cons (step1216 p h) (sat_cons (step2337 p h) (sat_cons (step2175 p h) (sat_cons (step2335 p h) (sat_cons (step2044 p h) (sat_cons (step2045 p h) (sat_cons (step2343 p h) (sat_cons (step1758 p h) (sat_cons (step1186 p h) (sat_cons (step1204 p h) (sat_cons (step2342 p h) (sat_cons (step1206 p h) (sat_cons (step124 p h) (sat_cons (step123 p h) (sat_cons (step1223 p h) (sat_cons (step2047 p h) (sat_cons (step1195 p h) (sat_cons (step1189 p h) (sat_nil p)))))))))))))))))))
def c2345 : List Lit := [(1795, true), (35, false), (114, false)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c1570, c1571, c731] c2345 (by decide) p (sat_cons (step1570 p h) (sat_cons (step1571 p h) (sat_cons (step731 p h) (sat_nil p))))
def c2346 : List Lit := [(35, false), (114, false), (1800, true)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c1581, c2345, c1579, c1573, c734, c732, c1572] c2346 (by decide) p (sat_cons (step1581 p h) (sat_cons (step2345 p h) (sat_cons (step1579 p h) (sat_cons (step1573 p h) (sat_cons (step734 p h) (sat_cons (step732 p h) (sat_cons (step1572 p h) (sat_nil p))))))))
def c2347 : List Lit := [(106, true), (1800, true), (109, false), (118, false), (127, false), (1636, true)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c2344, c2346, c2335, c2175, c2336, c785] c2347 (by decide) p (sat_cons (step2344 p h) (sat_cons (step2346 p h) (sat_cons (step2335 p h) (sat_cons (step2175 p h) (sat_cons (step2336 p h) (sat_cons (step785 p h) (sat_nil p)))))))
def c2348 : List Lit := [(110, false), (115, false), (1796, true), (109, false)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c700, c699, c1572] c2348 (by decide) p (sat_cons (step700 p h) (sat_cons (step699 p h) (sat_cons (step1572 p h) (sat_nil p))))
def c2349 : List Lit := [(114, false), (122, false), (117, true), (1800, true), (118, false), (109, false)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c1581, c2279, c2348, c2159, c706, c784, c1571, c1573, c1579] c2349 (by decide) p (sat_cons (step1581 p h) (sat_cons (step2279 p h) (sat_cons (step2348 p h) (sat_cons (step2159 p h) (sat_cons (step706 p h) (sat_cons (step784 p h) (sat_cons (step1571 p h) (sat_cons (step1573 p h) (sat_cons (step1579 p h) (sat_nil p))))))))))
def c2350 : List Lit := [(1735, true), (85, false), (503, false)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c1089, c2200, c1007, c956, c919, c917, c916, c913, c2024, c2199, c1047, c1028, c1026, c1018, c1017, c1427, c1945, c1419, c1420, c316, c364, c297, c2107] c2350 (by decide) p (sat_cons (step1089 p h) (sat_cons (step2200 p h) (sat_cons (step1007 p h) (sat_cons (step956 p h) (sat_cons (step919 p h) (sat_cons (step917 p h) (sat_cons (step916 p h) (sat_cons (step913 p h) (sat_cons (step2024 p h) (sat_cons (step2199 p h) (sat_cons (step1047 p h) (sat_cons (step1028 p h) (sat_cons (step1026 p h) (sat_cons (step1018 p h) (sat_cons (step1017 p h) (sat_cons (step1427 p h) (sat_cons (step1945 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step316 p h) (sat_cons (step364 p h) (sat_cons (step297 p h) (sat_cons (step2107 p h) (sat_nil p))))))))))))))))))))))))
def c2351 : List Lit := [(72, false), (78, true), (80, true), (1725, true), (113, false), (114, true)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c1387, c1389, c1407, c1376, c2095, c2094, c271, c1372, c1374, c1375, c276, c1403, c1388, c1390] c2351 (by decide) p (sat_cons (step1387 p h) (sat_cons (step1389 p h) (sat_cons (step1407 p h) (sat_cons (step1376 p h) (sat_cons (step2095 p h) (sat_cons (step2094 p h) (sat_cons (step271 p h) (sat_cons (step1372 p h) (sat_cons (step1374 p h) (sat_cons (step1375 p h) (sat_cons (step276 p h) (sat_cons (step1403 p h) (sat_cons (step1388 p h) (sat_cons (step1390 p h) (sat_nil p)))))))))))))))
def c2352 : List Lit := [(78, true), (80, true), (1725, true), (205, true), (113, false), (114, true)]
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c1399, c2351, c1384, c1393, c1388, c2104, c2103, c299, c1781] c2352 (by decide) p (sat_cons (step1399 p h) (sat_cons (step2351 p h) (sat_cons (step1384 p h) (sat_cons (step1393 p h) (sat_cons (step1388 p h) (sat_cons (step2104 p h) (sat_cons (step2103 p h) (sat_cons (step299 p h) (sat_cons (step1781 p h) (sat_nil p))))))))))
def c2353 : List Lit := [(1630, true), (48, false), (127, false)]
theorem step2353 (p : Nat → Bool) (h : Constraints p) : clause p c2353 = true :=
  Snake9.LocalRup.prove_clause [c1206, c1208, c1203, c1200, c166] c2353 (by decide) p (sat_cons (step1206 p h) (sat_cons (step1208 p h) (sat_cons (step1203 p h) (sat_cons (step1200 p h) (sat_cons (step166 p h) (sat_nil p))))))
def c2354 : List Lit := [(34, false), (35, true), (43, false), (1624, true), (39, false), (118, false)]
theorem step2354 (p : Nat → Bool) (h : Constraints p) : clause p c2354 = true :=
  Snake9.LocalRup.prove_clause [c124, c123, c101, c2047, c1186, c1191, c1196] c2354 (by decide) p (sat_cons (step124 p h) (sat_cons (step123 p h) (sat_cons (step101 p h) (sat_cons (step2047 p h) (sat_cons (step1186 p h) (sat_cons (step1191 p h) (sat_cons (step1196 p h) (sat_nil p))))))))
def c2355 : List Lit := [(35, true), (1623, true), (39, false), (109, false)]
theorem step2355 (p : Nat → Bool) (h : Constraints p) : clause p c2355 = true :=
  Snake9.LocalRup.prove_clause [c1193, c1190, c1191, c1195, c1961, c1186] c2355 (by decide) p (sat_cons (step1193 p h) (sat_cons (step1190 p h) (sat_cons (step1191 p h) (sat_cons (step1195 p h) (sat_cons (step1961 p h) (sat_cons (step1186 p h) (sat_nil p)))))))
def c2356 : List Lit := [(80, true), (1760, true), (1745, false), (114, true)]
theorem step2356 (p : Nat → Bool) (h : Constraints p) : clause p c2356 = true :=
  Snake9.LocalRup.prove_clause [c2266, c1420, c1419, c1945, c1454, c1485, c1406, c1936, c1376, c1383, c1384, c1955, c353, c2098, c2095, c2094, c1374, c263] c2356 (by decide) p (sat_cons (step2266 p h) (sat_cons (step1420 p h) (sat_cons (step1419 p h) (sat_cons (step1945 p h) (sat_cons (step1454 p h) (sat_cons (step1485 p h) (sat_cons (step1406 p h) (sat_cons (step1936 p h) (sat_cons (step1376 p h) (sat_cons (step1383 p h) (sat_cons (step1384 p h) (sat_cons (step1955 p h) (sat_cons (step353 p h) (sat_cons (step2098 p h) (sat_cons (step2095 p h) (sat_cons (step2094 p h) (sat_cons (step1374 p h) (sat_cons (step263 p h) (sat_nil p)))))))))))))))))))
def c2357 : List Lit := [(80, false), (1718, true), (72, false), (7, false)]
theorem step2357 (p : Nat → Bool) (h : Constraints p) : clause p c2357 = true :=
  Snake9.LocalRup.prove_clause [c311, c312, c1388] c2357 (by decide) p (sat_cons (step311 p h) (sat_cons (step312 p h) (sat_cons (step1388 p h) (sat_nil p))))
def c2358 : List Lit := [(113, true), (114, true), (1800, true), (109, false)]
theorem step2358 (p : Nat → Bool) (h : Constraints p) : clause p c2358 = true :=
  Snake9.LocalRup.prove_clause [c1570, c2314, c1579, c1573] c2358 (by decide) p (sat_cons (step1570 p h) (sat_cons (step2314 p h) (sat_cons (step1579 p h) (sat_cons (step1573 p h) (sat_nil p)))))
def c2359 : List Lit := [(1716, false), (1725, true)]
theorem step2359 (p : Nat → Bool) (h : Constraints p) : clause p c2359 = true :=
  Snake9.LocalRup.prove_clause [c1399, c1394, c1395, c1403, c1903, c1375] c2359 (by decide) p (sat_cons (step1399 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step1403 p h) (sat_cons (step1903 p h) (sat_cons (step1375 p h) (sat_nil p)))))))
def c2360 : List Lit := [(75, true), (73, false), (3, false), (8, false), (4, false)]
theorem step2360 (p : Nat → Bool) (h : Constraints p) : clause p c2360 = true :=
  Snake9.LocalRup.prove_clause [c2098, c2015, c16] c2360 (by decide) p (sat_cons (step2098 p h) (sat_cons (step2015 p h) (sat_cons (step16 p h) (sat_nil p))))
def c2361 : List Lit := [(1744, true), (110, true), (113, false), (114, true), (117, true), (109, false), (1741, false)]
theorem step2361 (p : Nat → Bool) (h : Constraints p) : clause p c2361 = true :=
  Snake9.LocalRup.prove_clause [c1442, c2261, c1434, c711, c418, c2155] c2361 (by decide) p (sat_cons (step1442 p h) (sat_cons (step2261 p h) (sat_cons (step1434 p h) (sat_cons (step711 p h) (sat_cons (step418 p h) (sat_cons (step2155 p h) (sat_nil p)))))))
def c2362 : List Lit := [(1739, true), (110, true), (113, false), (114, true), (117, true), (109, false)]
theorem step2362 (p : Nat → Bool) (h : Constraints p) : clause p c2362 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1434, c711, c418, c2155] c2362 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step711 p h) (sat_cons (step418 p h) (sat_cons (step2155 p h) (sat_nil p))))))
def c2363 : List Lit := [(87, true), (1736, true), (7, false), (1744, false), (1761, true)]
theorem step2363 (p : Nat → Bool) (h : Constraints p) : clause p c2363 = true :=
  Snake9.LocalRup.prove_clause [c1426, c1422, c1424, c1425, c1428, c1453, c1419, c1420, c1500, c364, c1400, c2106, c2110, c353, c316, c313, c318, c1385, c1388, c1396] c2363 (by decide) p (sat_cons (step1426 p h) (sat_cons (step1422 p h) (sat_cons (step1424 p h) (sat_cons (step1425 p h) (sat_cons (step1428 p h) (sat_cons (step1453 p h) (sat_cons (step1419 p h) (sat_cons (step1420 p h) (sat_cons (step1500 p h) (sat_cons (step364 p h) (sat_cons (step1400 p h) (sat_cons (step2106 p h) (sat_cons (step2110 p h) (sat_cons (step353 p h) (sat_cons (step316 p h) (sat_cons (step313 p h) (sat_cons (step318 p h) (sat_cons (step1385 p h) (sat_cons (step1388 p h) (sat_cons (step1396 p h) (sat_nil p)))))))))))))))))))))
def c2364 : List Lit := [(1709, true), (72, false), (113, false), (114, true)]
theorem step2364 (p : Nat → Bool) (h : Constraints p) : clause p c2364 = true :=
  Snake9.LocalRup.prove_clause [c1372, c1373, c274, c271, c2096] c2364 (by decide) p (sat_cons (step1372 p h) (sat_cons (step1373 p h) (sat_cons (step274 p h) (sat_cons (step271 p h) (sat_cons (step2096 p h) (sat_nil p))))))
def c2365 : List Lit := [(69, false), (72, false), (110, true), (113, false), (117, true), (109, false), (114, true)]
theorem step2365 (p : Nat → Bool) (h : Constraints p) : clause p c2365 = true :=
  Snake9.LocalRup.prove_clause [c710, c271, c2156] c2365 (by decide) p (sat_cons (step710 p h) (sat_cons (step271 p h) (sat_cons (step2156 p h) (sat_nil p))))
def c2366 : List Lit := [(70, false), (205, true), (80, false), (1718, true), (69, true), (72, false)]
theorem step2366 (p : Nat → Bool) (h : Constraints p) : clause p c2366 = true :=
  Snake9.LocalRup.prove_clause [c278, c1782, c1388, c299, c2105] c2366 (by decide) p (sat_cons (step278 p h) (sat_cons (step1782 p h) (sat_cons (step1388 p h) (sat_cons (step299 p h) (sat_cons (step2105 p h) (sat_nil p))))))
def c2367 : List Lit := [(1775, true), (89, false), (113, false)]
theorem step2367 (p : Nat → Bool) (h : Constraints p) : clause p c2367 = true :=
  Snake9.LocalRup.prove_clause [c1524, c1526, c1522, c1519, c425] c2367 (by decide) p (sat_cons (step1524 p h) (sat_cons (step1526 p h) (sat_cons (step1522 p h) (sat_cons (step1519 p h) (sat_cons (step425 p h) (sat_nil p))))))
def c2368 : List Lit := [(60, false), (59, true), (87, false), (68, false)]
theorem step2368 (p : Nat → Bool) (h : Constraints p) : clause p c2368 = true :=
  Snake9.LocalRup.prove_clause [c173, c2078] c2368 (by decide) p (sat_cons (step173 p h) (sat_cons (step2078 p h) (sat_nil p)))
def c2369 : List Lit := [(63, true), (1661, true), (87, false), (62, true), (68, false), (373, true)]
theorem step2369 (p : Nat → Bool) (h : Constraints p) : clause p c2369 = true :=
  Snake9.LocalRup.prove_clause [c993, c987, c986, c992, c991, c990, c216, c1251, c2368, c1246, c223, c1256, c1267, c1238, c1240, c1235, c1236, c1232, c167, c172, c2061] c2369 (by decide) p (sat_cons (step993 p h) (sat_cons (step987 p h) (sat_cons (step986 p h) (sat_cons (step992 p h) (sat_cons (step991 p h) (sat_cons (step990 p h) (sat_cons (step216 p h) (sat_cons (step1251 p h) (sat_cons (step2368 p h) (sat_cons (step1246 p h) (sat_cons (step223 p h) (sat_cons (step1256 p h) (sat_cons (step1267 p h) (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1235 p h) (sat_cons (step1236 p h) (sat_cons (step1232 p h) (sat_cons (step167 p h) (sat_cons (step172 p h) (sat_cons (step2061 p h) (sat_nil p))))))))))))))))))))))
def c2370 : List Lit := [(39, true), (109, false), (34, false), (46, false), (1636, true), (35, true), (162, true)]
theorem step2370 (p : Nat → Bool) (h : Constraints p) : clause p c2370 = true :=
  Snake9.LocalRup.prove_clause [c1201, c105, c1208, c1223, c1193, c1191, c92, c2049, c113] c2370 (by decide) p (sat_cons (step1201 p h) (sat_cons (step105 p h) (sat_cons (step1208 p h) (sat_cons (step1223 p h) (sat_cons (step1193 p h) (sat_cons (step1191 p h) (sat_cons (step92 p h) (sat_cons (step2049 p h) (sat_cons (step113 p h) (sat_nil p))))))))))
def c2371 : List Lit := [(1596, true), (87, false), (21, true)]
theorem step2371 (p : Nat → Bool) (h : Constraints p) : clause p c2371 = true :=
  Snake9.LocalRup.prove_clause [c1136, c1143, c1868, c1155, c1146, c1144, c1132, c1137, c1139, c1862, c29, c2026, c70] c2371 (by decide) p (sat_cons (step1136 p h) (sat_cons (step1143 p h) (sat_cons (step1868 p h) (sat_cons (step1155 p h) (sat_cons (step1146 p h) (sat_cons (step1144 p h) (sat_cons (step1132 p h) (sat_cons (step1137 p h) (sat_cons (step1139 p h) (sat_cons (step1862 p h) (sat_cons (step29 p h) (sat_cons (step2026 p h) (sat_cons (step70 p h) (sat_nil p))))))))))))))
def c2372 : List Lit := [(16, false), (25, false), (27, false), (87, false)]
theorem step2372 (p : Nat → Bool) (h : Constraints p) : clause p c2372 = true :=
  Snake9.LocalRup.prove_clause [c29, c2026, c70] c2372 (by decide) p (sat_cons (step29 p h) (sat_cons (step2026 p h) (sat_cons (step70 p h) (sat_nil p))))
def c2373 : List Lit := [(1807, true), (126, false)]
theorem step2373 (p : Nat → Bool) (h : Constraints p) : clause p c2373 = true :=
  Snake9.LocalRup.prove_clause [c1590, c1943, c1587] c2373 (by decide) p (sat_cons (step1590 p h) (sat_cons (step1943 p h) (sat_cons (step1587 p h) (sat_nil p))))
def c2374 : List Lit := [(1800, true), (117, false), (127, false)]
theorem step2374 (p : Nat → Bool) (h : Constraints p) : clause p c2374 = true :=
  Snake9.LocalRup.prove_clause [c2336, c777, c778, c1570, c1574, c1579] c2374 (by decide) p (sat_cons (step2336 p h) (sat_cons (step777 p h) (sat_cons (step778 p h) (sat_cons (step1570 p h) (sat_cons (step1574 p h) (sat_cons (step1579 p h) (sat_nil p)))))))
def c2375 : List Lit := [(1812, true), (123, true), (125, false), (46, false), (1805, false), (1807, false)]
theorem step2375 (p : Nat → Bool) (h : Constraints p) : clause p c2375 = true :=
  Snake9.LocalRup.prove_clause [c1584, c1600, c1603, c1593, c1586, c821] c2375 (by decide) p (sat_cons (step1584 p h) (sat_cons (step1600 p h) (sat_cons (step1603 p h) (sat_cons (step1593 p h) (sat_cons (step1586 p h) (sat_cons (step821 p h) (sat_nil p)))))))
def c2376 : List Lit := [(1658, true), (87, false)]
theorem step2376 (p : Nat → Bool) (h : Constraints p) : clause p c2376 = true :=
  Snake9.LocalRup.prove_clause [c1260, c1264, c1252, c1254, c1240, c1250, c1246, c1232, c221, c171, c2077] c2376 (by decide) p (sat_cons (step1260 p h) (sat_cons (step1264 p h) (sat_cons (step1252 p h) (sat_cons (step1254 p h) (sat_cons (step1240 p h) (sat_cons (step1250 p h) (sat_cons (step1246 p h) (sat_cons (step1232 p h) (sat_cons (step221 p h) (sat_cons (step171 p h) (sat_cons (step2077 p h) (sat_nil p))))))))))))
def c2377 : List Lit := [(51, false), (60, false), (62, false), (87, false)]
theorem step2377 (p : Nat → Bool) (h : Constraints p) : clause p c2377 = true :=
  Snake9.LocalRup.prove_clause [c221, c171, c2077] c2377 (by decide) p (sat_cons (step221 p h) (sat_cons (step171 p h) (sat_cons (step2077 p h) (sat_nil p))))
def c2378 : List Lit := [(1635, true), (1763, false), (1819, false), (1667, false)]
theorem step2378 (p : Nat → Bool) (h : Constraints p) : clause p c2378 = true :=
  Snake9.LocalRup.prove_clause [c1215, c1950, c1963, c1989, c1207, c1189, c1190, c1194, c1535, c1186, c1915, c1538, c1951, c1546, c1204, c1205, c1630, c1209, c1719, c1200, c1201, c2248, c1917, c99, c112, c1355, c1107, c2046, c2047, c1181, c1855, c139, c117, c1120, c1099, c1098, c1105] c2378 (by decide) p (sat_cons (step1215 p h) (sat_cons (step1950 p h) (sat_cons (step1963 p h) (sat_cons (step1989 p h) (sat_cons (step1207 p h) (sat_cons (step1189 p h) (sat_cons (step1190 p h) (sat_cons (step1194 p h) (sat_cons (step1535 p h) (sat_cons (step1186 p h) (sat_cons (step1915 p h) (sat_cons (step1538 p h) (sat_cons (step1951 p h) (sat_cons (step1546 p h) (sat_cons (step1204 p h) (sat_cons (step1205 p h) (sat_cons (step1630 p h) (sat_cons (step1209 p h) (sat_cons (step1719 p h) (sat_cons (step1200 p h) (sat_cons (step1201 p h) (sat_cons (step2248 p h) (sat_cons (step1917 p h) (sat_cons (step99 p h) (sat_cons (step112 p h) (sat_cons (step1355 p h) (sat_cons (step1107 p h) (sat_cons (step2046 p h) (sat_cons (step2047 p h) (sat_cons (step1181 p h) (sat_cons (step1855 p h) (sat_cons (step139 p h) (sat_cons (step117 p h) (sat_cons (step1120 p h) (sat_cons (step1099 p h) (sat_cons (step1098 p h) (sat_cons (step1105 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c2379 : List Lit := [(1596, true), (1744, true), (87, false)]
theorem step2379 (p : Nat → Bool) (h : Constraints p) : clause p c2379 = true :=
  Snake9.LocalRup.prove_clause [c1893, c1898, c2371, c1125, c1126, c55, c2033, c2031, c2028, c1753, c396, c1436, c1434, c1442] c2379 (by decide) p (sat_cons (step1893 p h) (sat_cons (step1898 p h) (sat_cons (step2371 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step55 p h) (sat_cons (step2033 p h) (sat_cons (step2031 p h) (sat_cons (step2028 p h) (sat_cons (step1753 p h) (sat_cons (step396 p h) (sat_cons (step1436 p h) (sat_cons (step1434 p h) (sat_cons (step1442 p h) (sat_nil p)))))))))))))))
def c2380 : List Lit := [(1596, false), (1690, true), (1658, false)]
theorem step2380 (p : Nat → Bool) (h : Constraints p) : clause p c2380 = true :=
  Snake9.LocalRup.prove_clause [c2206, c1347, c2202, c1176, c1339, c1896, c1290, c1099, c1215, c1950, c1963, c1190, c1194, c1186, c1951, c1204, c1209, c1200, c1201, c139, c99, c2046] c2380 (by decide) p (sat_cons (step2206 p h) (sat_cons (step1347 p h) (sat_cons (step2202 p h) (sat_cons (step1176 p h) (sat_cons (step1339 p h) (sat_cons (step1896 p h) (sat_cons (step1290 p h) (sat_cons (step1099 p h) (sat_cons (step1215 p h) (sat_cons (step1950 p h) (sat_cons (step1963 p h) (sat_cons (step1190 p h) (sat_cons (step1194 p h) (sat_cons (step1186 p h) (sat_cons (step1951 p h) (sat_cons (step1204 p h) (sat_cons (step1209 p h) (sat_cons (step1200 p h) (sat_cons (step1201 p h) (sat_cons (step139 p h) (sat_cons (step99 p h) (sat_cons (step2046 p h) (sat_nil p)))))))))))))))))))))))
def c2381 : List Lit := [(36, true), (7, false), (1618, false), (1636, true)]
theorem step2381 (p : Nat → Bool) (h : Constraints p) : clause p c2381 = true :=
  Snake9.LocalRup.prove_clause [c1226, c1196, c1189, c1191, c1195, c1932, c1223] c2381 (by decide) p (sat_cons (step1226 p h) (sat_cons (step1196 p h) (sat_cons (step1189 p h) (sat_cons (step1191 p h) (sat_cons (step1195 p h) (sat_cons (step1932 p h) (sat_cons (step1223 p h) (sat_nil p))))))))
def c2382 : List Lit := [(1690, true), (87, false)]
theorem step2382 (p : Nat → Bool) (h : Constraints p) : clause p c2382 = true :=
  Snake9.LocalRup.prove_clause [c1887, c2201, c2376, c1330, c1297, c1889, c2380, c1868, c1915, c1898, c2371, c1142, c1194, c1125, c1126, c1963, c55, c1290, c2030, c1339, c1175, c1896, c1099, c2381, c2264, c1188, c1913, c1138, c1140, c1141, c1144, c1155, c1135, c1132, c2372, c1862] c2382 (by decide) p (sat_cons (step1887 p h) (sat_cons (step2201 p h) (sat_cons (step2376 p h) (sat_cons (step1330 p h) (sat_cons (step1297 p h) (sat_cons (step1889 p h) (sat_cons (step2380 p h) (sat_cons (step1868 p h) (sat_cons (step1915 p h) (sat_cons (step1898 p h) (sat_cons (step2371 p h) (sat_cons (step1142 p h) (sat_cons (step1194 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step1963 p h) (sat_cons (step55 p h) (sat_cons (step1290 p h) (sat_cons (step2030 p h) (sat_cons (step1339 p h) (sat_cons (step1175 p h) (sat_cons (step1896 p h) (sat_cons (step1099 p h) (sat_cons (step2381 p h) (sat_cons (step2264 p h) (sat_cons (step1188 p h) (sat_cons (step1913 p h) (sat_cons (step1138 p h) (sat_cons (step1140 p h) (sat_cons (step1141 p h) (sat_cons (step1144 p h) (sat_cons (step1155 p h) (sat_cons (step1135 p h) (sat_cons (step1132 p h) (sat_cons (step2372 p h) (sat_cons (step1862 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c2383 : List Lit := [(96, false), (89, false), (93, false), (18, false), (19, false), (1645, true)]
theorem step2383 (p : Nat → Bool) (h : Constraints p) : clause p c2383 = true :=
  Snake9.LocalRup.prove_clause [c451, c393, c1237] c2383 (by decide) p (sat_cons (step451 p h) (sat_cons (step393 p h) (sat_cons (step1237 p h) (sat_nil p))))
def c2384 : List Lit := [(103, true), (107, true), (1780, true), (125, true), (233, true), (108, true), (95, true)]
theorem step2384 (p : Nat → Bool) (h : Constraints p) : clause p c2384 = true :=
  Snake9.LocalRup.prove_clause [c1534, c620, c2141] c2384 (by decide) p (sat_cons (step1534 p h) (sat_cons (step620 p h) (sat_cons (step2141 p h) (sat_nil p))))
def c2385 : List Lit := [(62, false), (1655, true), (1725, true), (53, false), (54, false)]
theorem step2385 (p : Nat → Bool) (h : Constraints p) : clause p c2385 = true :=
  Snake9.LocalRup.prove_clause [c1974, c1369, c1370, c1993, c201, c2088, c237, c238, c1247, c1249, c1255] c2385 (by decide) p (sat_cons (step1974 p h) (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step1993 p h) (sat_cons (step201 p h) (sat_cons (step2088 p h) (sat_cons (step237 p h) (sat_cons (step238 p h) (sat_cons (step1247 p h) (sat_cons (step1249 p h) (sat_cons (step1255 p h) (sat_nil p))))))))))))
def c2386 : List Lit := [(75, false), (3, false), (56, false), (1725, true)]
theorem step2386 (p : Nat → Bool) (h : Constraints p) : clause p c2386 = true :=
  Snake9.LocalRup.prove_clause [c2359, c292, c291, c1383, c1385, c1372, c1391, c1375, c1407, c1403, c1376, c1392, c1374, c1386, c1387, c276, c331, c2104] c2386 (by decide) p (sat_cons (step2359 p h) (sat_cons (step292 p h) (sat_cons (step291 p h) (sat_cons (step1383 p h) (sat_cons (step1385 p h) (sat_cons (step1372 p h) (sat_cons (step1391 p h) (sat_cons (step1375 p h) (sat_cons (step1407 p h) (sat_cons (step1403 p h) (sat_cons (step1376 p h) (sat_cons (step1392 p h) (sat_cons (step1374 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step276 p h) (sat_cons (step331 p h) (sat_cons (step2104 p h) (sat_nil p)))))))))))))))))))
def c2387 : List Lit := [(87, true), (1736, true), (1653, true)]
theorem step2387 (p : Nat → Bool) (h : Constraints p) : clause p c2387 = true :=
  Snake9.LocalRup.prove_clause [c1426, c1422, c1424, c1428, c1880] c2387 (by decide) p (sat_cons (step1426 p h) (sat_cons (step1422 p h) (sat_cons (step1424 p h) (sat_cons (step1428 p h) (sat_cons (step1880 p h) (sat_nil p))))))
def c2388 : List Lit := [(69, true), (80, true), (1707, false), (1725, true)]
theorem step2388 (p : Nat → Bool) (h : Constraints p) : clause p c2388 = true :=
  Snake9.LocalRup.prove_clause [c1971, c1384, c1411, c1379, c1372, c1374, c1378, c1407, c1389, c1386, c276, c2104] c2388 (by decide) p (sat_cons (step1971 p h) (sat_cons (step1384 p h) (sat_cons (step1411 p h) (sat_cons (step1379 p h) (sat_cons (step1372 p h) (sat_cons (step1374 p h) (sat_cons (step1378 p h) (sat_cons (step1407 p h) (sat_cons (step1389 p h) (sat_cons (step1386 p h) (sat_cons (step276 p h) (sat_cons (step2104 p h) (sat_nil p)))))))))))))
def c2389 : List Lit := [(1707, false), (1725, true), (85, false)]
theorem step2389 (p : Nat → Bool) (h : Constraints p) : clause p c2389 = true :=
  Snake9.LocalRup.prove_clause [c1377, c1971, c1403, c1384, c1390, c1900, c2388, c1973, c274, c277, c1373, c1386, c1378, c1389, c1407] c2389 (by decide) p (sat_cons (step1377 p h) (sat_cons (step1971 p h) (sat_cons (step1403 p h) (sat_cons (step1384 p h) (sat_cons (step1390 p h) (sat_cons (step1900 p h) (sat_cons (step2388 p h) (sat_cons (step1973 p h) (sat_cons (step274 p h) (sat_cons (step277 p h) (sat_cons (step1373 p h) (sat_cons (step1386 p h) (sat_cons (step1378 p h) (sat_cons (step1389 p h) (sat_cons (step1407 p h) (sat_nil p))))))))))))))))
def c2390 : List Lit := [(1707, true), (73, false), (63, false), (1732, true)]
theorem step2390 (p : Nat → Bool) (h : Constraints p) : clause p c2390 = true :=
  Snake9.LocalRup.prove_clause [c1369, c1370, c1899] c2390 (by decide) p (sat_cons (step1369 p h) (sat_cons (step1370 p h) (sat_cons (step1899 p h) (sat_nil p))))
def c2391 : List Lit := [(1811, true), (1779, true), (1781, true)]
theorem step2391 (p : Nat → Bool) (h : Constraints p) : clause p c2391 = true :=
  Snake9.LocalRup.prove_clause [c1533, c1536, c1532, c618, c1535, c2272, c2001, c2141, c1587, c675] c2391 (by decide) p (sat_cons (step1533 p h) (sat_cons (step1536 p h) (sat_cons (step1532 p h) (sat_cons (step618 p h) (sat_cons (step1535 p h) (sat_cons (step2272 p h) (sat_cons (step2001 p h) (sat_cons (step2141 p h) (sat_cons (step1587 p h) (sat_cons (step675 p h) (sat_nil p)))))))))))
end B112E050
