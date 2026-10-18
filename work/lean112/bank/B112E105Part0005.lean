import B112E105Part0004
namespace B112E105
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2249 : List Lit := [(1561, true), (1529, false)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c1980, c1360] c2249 (by decide) p (sat_cons (step1980 p h) (sat_cons (step1360 p h) (sat_nil p)))
def c2250 : List Lit := [(1585, false), (1617, true)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c1983, c1454] c2250 (by decide) p (sat_cons (step1983 p h) (sat_cons (step1454 p h) (sat_nil p)))
def c2251 : List Lit := [(1586, false), (1618, true)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c1983, c1459] c2251 (by decide) p (sat_cons (step1983 p h) (sat_cons (step1459 p h) (sat_nil p)))
def c2252 : List Lit := [(1587, false), (1619, true)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c1983, c1466] c2252 (by decide) p (sat_cons (step1983 p h) (sat_cons (step1466 p h) (sat_nil p)))
def c2253 : List Lit := [(1620, true), (1588, false)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c1983, c1472] c2253 (by decide) p (sat_cons (step1983 p h) (sat_cons (step1472 p h) (sat_nil p)))
def c2254 : List Lit := [(1621, true), (1589, false)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c1983, c1479] c2254 (by decide) p (sat_cons (step1983 p h) (sat_cons (step1479 p h) (sat_nil p)))
def c2255 : List Lit := [(1622, false), (1638, true)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c1979, c1483] c2255 (by decide) p (sat_cons (step1979 p h) (sat_cons (step1483 p h) (sat_nil p)))
def c2256 : List Lit := [(1620, false), (1637, true)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c1981, c1484] c2256 (by decide) p (sat_cons (step1981 p h) (sat_cons (step1484 p h) (sat_nil p)))
def c2257 : List Lit := [(1621, false), (1638, true)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c1981, c1485] c2257 (by decide) p (sat_cons (step1981 p h) (sat_cons (step1485 p h) (sat_nil p)))
def c2258 : List Lit := [(1622, false), (1639, true)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c1981, c1486] c2258 (by decide) p (sat_cons (step1981 p h) (sat_cons (step1486 p h) (sat_nil p)))
def c2259 : List Lit := [(1636, false), (1789, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1853] c2259 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1853 p h) (sat_nil p)))
def c2260 : List Lit := [(1637, false), (1788, false)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1854] c2260 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1854 p h) (sat_nil p)))
def c2261 : List Lit := [(1638, false), (1787, false)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1855] c2261 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1855 p h) (sat_nil p)))
def c2262 : List Lit := [(1639, false), (1786, false)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1856] c2262 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1856 p h) (sat_nil p)))
def c2263 : List Lit := [(1640, false), (1785, false)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1857] c2263 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1857 p h) (sat_nil p)))
def c2264 : List Lit := [(1641, false), (1784, false)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1858] c2264 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1858 p h) (sat_nil p)))
def c2265 : List Lit := [(1642, false), (1783, false)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1859] c2265 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1859 p h) (sat_nil p)))
def c2266 : List Lit := [(1643, false), (1782, false)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1860] c2266 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1860 p h) (sat_nil p)))
def c2267 : List Lit := [(1644, false), (1781, false)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c1862, c1861] c2267 (by decide) p (sat_cons (step1862 p h) (sat_cons (step1861 p h) (sat_nil p)))
def c2268 : List Lit := [(113, false), (119, true), (1741, true), (110, true), (112, true), (122, false), (117, false), (123, false)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c909, c939, c936, c1237, c2237, c1236, c924, c923, c709, c856, c1693, c1694, c1703] c2268 (by decide) p (sat_cons (step909 p h) (sat_cons (step939 p h) (sat_cons (step936 p h) (sat_cons (step1237 p h) (sat_cons (step2237 p h) (sat_cons (step1236 p h) (sat_cons (step924 p h) (sat_cons (step923 p h) (sat_cons (step709 p h) (sat_cons (step856 p h) (sat_cons (step1693 p h) (sat_cons (step1694 p h) (sat_cons (step1703 p h) (sat_nil p))))))))))))))
def c2269 : List Lit := [(1724, true), (74, false), (68, false), (102, true), (103, true)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c1656, c1666, c1664, c1657, c1658, c628, c405, c652, c398, c1204, c1129, c1209, c1130, c1212, c1133, c1216, c1152, c1252, c1187, c2241] c2269 (by decide) p (sat_cons (step1656 p h) (sat_cons (step1666 p h) (sat_cons (step1664 p h) (sat_cons (step1657 p h) (sat_cons (step1658 p h) (sat_cons (step628 p h) (sat_cons (step405 p h) (sat_cons (step652 p h) (sat_cons (step398 p h) (sat_cons (step1204 p h) (sat_cons (step1129 p h) (sat_cons (step1209 p h) (sat_cons (step1130 p h) (sat_cons (step1212 p h) (sat_cons (step1133 p h) (sat_cons (step1216 p h) (sat_cons (step1152 p h) (sat_cons (step1252 p h) (sat_cons (step1187 p h) (sat_cons (step2241 p h) (sat_nil p)))))))))))))))))))))
def c2270 : List Lit := [(105, false), (107, false), (70, true), (68, false), (103, true)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c628, c652, c398, c1204, c1129, c1209, c1130, c1212, c1133, c1216, c1152, c1252, c1187, c2241] c2270 (by decide) p (sat_cons (step628 p h) (sat_cons (step652 p h) (sat_cons (step398 p h) (sat_cons (step1204 p h) (sat_cons (step1129 p h) (sat_cons (step1209 p h) (sat_cons (step1130 p h) (sat_cons (step1212 p h) (sat_cons (step1133 p h) (sat_cons (step1216 p h) (sat_cons (step1152 p h) (sat_cons (step1252 p h) (sat_cons (step1187 p h) (sat_cons (step2241 p h) (sat_nil p)))))))))))))))
def c2271 : List Lit := [(1560, true), (1535, false), (305, true)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c2001, c1058, c1027, c1012, c1010, c1008, c18, c1273, c1279, c1056, c2244, c1350, c2000, c1286, c1274, c1270, c2007] c2271 (by decide) p (sat_cons (step2001 p h) (sat_cons (step1058 p h) (sat_cons (step1027 p h) (sat_cons (step1012 p h) (sat_cons (step1010 p h) (sat_cons (step1008 p h) (sat_cons (step18 p h) (sat_cons (step1273 p h) (sat_cons (step1279 p h) (sat_cons (step1056 p h) (sat_cons (step2244 p h) (sat_cons (step1350 p h) (sat_cons (step2000 p h) (sat_cons (step1286 p h) (sat_cons (step1274 p h) (sat_cons (step1270 p h) (sat_cons (step2007 p h) (sat_nil p))))))))))))))))))
def c2272 : List Lit := [(1597, false), (1623, true), (1574, false), (40, true), (60, true), (1601, false)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c1375, c1382, c1393, c1464, c1420, c1428, c1443, c1442, c1429, c1470, c1421, c2003] c2272 (by decide) p (sat_cons (step1375 p h) (sat_cons (step1382 p h) (sat_cons (step1393 p h) (sat_cons (step1464 p h) (sat_cons (step1420 p h) (sat_cons (step1428 p h) (sat_cons (step1443 p h) (sat_cons (step1442 p h) (sat_cons (step1429 p h) (sat_cons (step1470 p h) (sat_cons (step1421 p h) (sat_cons (step2003 p h) (sat_nil p)))))))))))))
def c2273 : List Lit := [(1748, true), (122, true), (117, false), (240, true), (104, true), (107, false), (115, false)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c1709, c1712, c1714, c1710, c1706, c2057, c775] c2273 (by decide) p (sat_cons (step1709 p h) (sat_cons (step1712 p h) (sat_cons (step1714 p h) (sat_cons (step1710 p h) (sat_cons (step1706 p h) (sat_cons (step2057 p h) (sat_cons (step775 p h) (sat_nil p))))))))
def c2274 : List Lit := [(116, false), (117, false), (240, true), (104, true), (107, false), (115, false)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c864, c801, c775] c2274 (by decide) p (sat_cons (step864 p h) (sat_cons (step801 p h) (sat_cons (step775 p h) (sat_nil p))))
def c2275 : List Lit := [(110, true), (123, false), (122, false), (1740, true), (1741, true), (107, false), (117, false)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c866, c1691, c1700, c1695, c749, c2268] c2275 (by decide) p (sat_cons (step866 p h) (sat_cons (step1691 p h) (sat_cons (step1700 p h) (sat_cons (step1695 p h) (sat_cons (step749 p h) (sat_cons (step2268 p h) (sat_nil p)))))))
def c2276 : List Lit := [(113, false), (110, false), (123, false), (118, true), (122, false), (121, true)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c710, c939, c918] c2276 (by decide) p (sat_cons (step710 p h) (sat_cons (step939 p h) (sat_cons (step918 p h) (sat_nil p))))
def c2277 : List Lit := [(123, false), (118, true), (122, false), (1740, true), (121, true), (1741, true), (107, false), (117, false)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c2275, c748, c2276, c1695, c1700, c1692, c708, c697, c926, c1221, c1236, c1222, c1239, c1232, c1241, c2239] c2277 (by decide) p (sat_cons (step2275 p h) (sat_cons (step748 p h) (sat_cons (step2276 p h) (sat_cons (step1695 p h) (sat_cons (step1700 p h) (sat_cons (step1692 p h) (sat_cons (step708 p h) (sat_cons (step697 p h) (sat_cons (step926 p h) (sat_cons (step1221 p h) (sat_cons (step1236 p h) (sat_cons (step1222 p h) (sat_cons (step1239 p h) (sat_cons (step1232 p h) (sat_cons (step1241 p h) (sat_cons (step2239 p h) (sat_nil p)))))))))))))))))
def c2278 : List Lit := [(122, false), (121, true), (1753, true), (1743, false), (107, false), (115, false), (117, false)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c1713, c1729, c1733, c856, c2277, c1708, c1714, c1725, c1697, c1699, c1695, c1691, c710, c747, c697, c926, c1221, c1236, c1222, c1239, c1232, c1241, c2239] c2278 (by decide) p (sat_cons (step1713 p h) (sat_cons (step1729 p h) (sat_cons (step1733 p h) (sat_cons (step856 p h) (sat_cons (step2277 p h) (sat_cons (step1708 p h) (sat_cons (step1714 p h) (sat_cons (step1725 p h) (sat_cons (step1697 p h) (sat_cons (step1699 p h) (sat_cons (step1695 p h) (sat_cons (step1691 p h) (sat_cons (step710 p h) (sat_cons (step747 p h) (sat_cons (step697 p h) (sat_cons (step926 p h) (sat_cons (step1221 p h) (sat_cons (step1236 p h) (sat_cons (step1222 p h) (sat_cons (step1239 p h) (sat_cons (step1232 p h) (sat_cons (step1241 p h) (sat_cons (step2239 p h) (sat_nil p))))))))))))))))))))))))
def c2279 : List Lit := [(1587, true), (1572, false), (40, true), (331, true)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c1375, c1382, c1078, c1071, c1070, c1077, c1076, c1073, c1390, c1397, c2029, c1370, c1372, c184, c2002] c2279 (by decide) p (sat_cons (step1375 p h) (sat_cons (step1382 p h) (sat_cons (step1078 p h) (sat_cons (step1071 p h) (sat_cons (step1070 p h) (sat_cons (step1077 p h) (sat_cons (step1076 p h) (sat_cons (step1073 p h) (sat_cons (step1390 p h) (sat_cons (step1397 p h) (sat_cons (step2029 p h) (sat_cons (step1370 p h) (sat_cons (step1372 p h) (sat_cons (step184 p h) (sat_cons (step2002 p h) (sat_nil p))))))))))))))))
def c2280 : List Lit := [(1665, true), (192, true), (104, true), (107, false)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c1540, c1544, c1532, c1521, c1530, c1518, c405, c398] c2280 (by decide) p (sat_cons (step1540 p h) (sat_cons (step1544 p h) (sat_cons (step1532 p h) (sat_cons (step1521 p h) (sat_cons (step1530 p h) (sat_cons (step1518 p h) (sat_cons (step405 p h) (sat_cons (step398 p h) (sat_nil p)))))))))
def c2281 : List Lit := [(115, false), (240, true), (1753, true), (1748, true), (121, true), (104, true), (107, false), (117, false)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c2274, c2273, c1706, c2278] c2281 (by decide) p (sat_cons (step2274 p h) (sat_cons (step2273 p h) (sat_cons (step1706 p h) (sat_cons (step2278 p h) (sat_nil p)))))
def c2282 : List Lit := [(111, true), (112, true), (110, false), (115, false), (1748, true), (121, true), (104, true), (107, false), (117, false)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c697, c1221, c1222, c1232, c2236, c2239, c1227, c1241, c1224, c1239, c2273, c1236, c856, c926] c2282 (by decide) p (sat_cons (step697 p h) (sat_cons (step1221 p h) (sat_cons (step1222 p h) (sat_cons (step1232 p h) (sat_cons (step2236 p h) (sat_cons (step2239 p h) (sat_cons (step1227 p h) (sat_cons (step1241 p h) (sat_cons (step1224 p h) (sat_cons (step1239 p h) (sat_cons (step2273 p h) (sat_cons (step1236 p h) (sat_cons (step856 p h) (sat_cons (step926 p h) (sat_nil p)))))))))))))))
def c2283 : List Lit := [(110, false), (113, false), (115, false), (1752, true), (121, true), (104, true), (107, false), (117, false)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c1720, c747, c2282, c710, c707, c1709, c1692, c1711, c1699, c1724] c2283 (by decide) p (sat_cons (step1720 p h) (sat_cons (step747 p h) (sat_cons (step2282 p h) (sat_cons (step710 p h) (sat_cons (step707 p h) (sat_cons (step1709 p h) (sat_cons (step1692 p h) (sat_cons (step1711 p h) (sat_cons (step1699 p h) (sat_cons (step1724 p h) (sat_nil p)))))))))))
def c2284 : List Lit := [(113, false), (115, false), (1752, true), (121, true), (104, true), (107, false), (117, false)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c1728, c1702, c2283, c1691, c2043, c1693, c1699, c917, c1724, c856, c709, c1711, c918, c1708, c939] c2284 (by decide) p (sat_cons (step1728 p h) (sat_cons (step1702 p h) (sat_cons (step2283 p h) (sat_cons (step1691 p h) (sat_cons (step2043 p h) (sat_cons (step1693 p h) (sat_cons (step1699 p h) (sat_cons (step917 p h) (sat_cons (step1724 p h) (sat_cons (step856 p h) (sat_cons (step709 p h) (sat_cons (step1711 p h) (sat_cons (step918 p h) (sat_cons (step1708 p h) (sat_cons (step939 p h) (sat_nil p))))))))))))))))
def c2285 : List Lit := [(115, false), (1752, true), (121, true), (104, true), (107, false), (117, false)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1728, c1720, c2284, c1695, c1697, c1700, c1724, c1691, c1692, c1711, c1708, c1709, c748, c708, c2282] c2285 (by decide) p (sat_cons (step1728 p h) (sat_cons (step1720 p h) (sat_cons (step2284 p h) (sat_cons (step1695 p h) (sat_cons (step1697 p h) (sat_cons (step1700 p h) (sat_cons (step1724 p h) (sat_cons (step1691 p h) (sat_cons (step1692 p h) (sat_cons (step1711 p h) (sat_cons (step1708 p h) (sat_cons (step1709 p h) (sat_cons (step748 p h) (sat_cons (step708 p h) (sat_cons (step2282 p h) (sat_nil p))))))))))))))))
def c2286 : List Lit := [(1752, true), (121, true), (104, true), (107, false), (117, false)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c1728, c1698, c2285, c1694, c1696, c1697, c1700, c1724, c1691, c1692, c1711, c747, c707, c1708, c1709, c2055, c939, c1237, c924, c2237, c1236] c2286 (by decide) p (sat_cons (step1728 p h) (sat_cons (step1698 p h) (sat_cons (step2285 p h) (sat_cons (step1694 p h) (sat_cons (step1696 p h) (sat_cons (step1697 p h) (sat_cons (step1700 p h) (sat_cons (step1724 p h) (sat_cons (step1691 p h) (sat_cons (step1692 p h) (sat_cons (step1711 p h) (sat_cons (step747 p h) (sat_cons (step707 p h) (sat_cons (step1708 p h) (sat_cons (step1709 p h) (sat_cons (step2055 p h) (sat_cons (step939 p h) (sat_cons (step1237 p h) (sat_cons (step924 p h) (sat_cons (step2237 p h) (sat_cons (step1236 p h) (sat_nil p))))))))))))))))))))))
def c2287 : List Lit := [(1690, true), (83, true), (209, true), (1672, false), (104, true), (107, false)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c1559, c1564, c1597, c1593, c1565, c1575, c1560, c1573, c486, c495] c2287 (by decide) p (sat_cons (step1559 p h) (sat_cons (step1564 p h) (sat_cons (step1597 p h) (sat_cons (step1593 p h) (sat_cons (step1565 p h) (sat_cons (step1575 p h) (sat_cons (step1560 p h) (sat_cons (step1573 p h) (sat_cons (step486 p h) (sat_cons (step495 p h) (sat_nil p)))))))))))
def c2288 : List Lit := [(72, false), (67, true), (81, false), (108, false), (196, true)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c422, c418] c2288 (by decide) p (sat_cons (step422 p h) (sat_cons (step418 p h) (sat_nil p)))
def c2289 : List Lit := [(76, false), (1562, true), (24, false), (1518, false), (59, false), (16, true)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c1989, c96, c102, c2001, c1265, c1276, c1361, c1268, c1281, c1288] c2289 (by decide) p (sat_cons (step1989 p h) (sat_cons (step96 p h) (sat_cons (step102 p h) (sat_cons (step2001 p h) (sat_cons (step1265 p h) (sat_cons (step1276 p h) (sat_cons (step1361 p h) (sat_cons (step1268 p h) (sat_cons (step1281 p h) (sat_cons (step1288 p h) (sat_nil p)))))))))))
def c2290 : List Lit := [(1528, true), (24, false), (1518, false), (59, false), (16, true)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c1274, c1280, c1284, c1287, c1281, c1268, c1276, c1265, c89] c2290 (by decide) p (sat_cons (step1274 p h) (sat_cons (step1280 p h) (sat_cons (step1284 p h) (sat_cons (step1287 p h) (sat_cons (step1281 p h) (sat_cons (step1268 p h) (sat_cons (step1276 p h) (sat_cons (step1265 p h) (sat_cons (step89 p h) (sat_nil p))))))))))
def c2291 : List Lit := [(1535, true), (24, false), (59, false)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c1298, c1299, c103] c2291 (by decide) p (sat_cons (step1298 p h) (sat_cons (step1299 p h) (sat_cons (step103 p h) (sat_nil p))))
def c2292 : List Lit := [(19, false), (1534, true), (74, false), (56, false)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c67, c70, c1297] c2292 (by decide) p (sat_cons (step67 p h) (sat_cons (step70 p h) (sat_cons (step1297 p h) (sat_nil p))))
def c2293 : List Lit := [(17, true), (152, true), (19, true), (1551, true), (1535, false)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c1336, c1307, c1296, c1297, c1304, c2031, c1333] c2293 (by decide) p (sat_cons (step1336 p h) (sat_cons (step1307 p h) (sat_cons (step1296 p h) (sat_cons (step1297 p h) (sat_cons (step1304 p h) (sat_cons (step2031 p h) (sat_cons (step1333 p h) (sat_nil p))))))))
def c2294 : List Lit := [(1727, true), (118, false), (60, false)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c1669, c1673, c1661, c1649, c1659, c1642, c827] c2294 (by decide) p (sat_cons (step1669 p h) (sat_cons (step1673 p h) (sat_cons (step1661 p h) (sat_cons (step1649 p h) (sat_cons (step1659 p h) (sat_cons (step1642 p h) (sat_cons (step827 p h) (sat_nil p))))))))
def c2295 : List Lit := [(1719, true), (229, true), (104, true), (115, false)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c1655, c1656, c652, c594] c2295 (by decide) p (sat_cons (step1655 p h) (sat_cons (step1656 p h) (sat_cons (step652 p h) (sat_cons (step594 p h) (sat_nil p)))))
def c2296 : List Lit := [(108, false), (113, false), (104, true), (102, false), (105, false)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c688, c593, c649] c2296 (by decide) p (sat_cons (step688 p h) (sat_cons (step593 p h) (sat_cons (step649 p h) (sat_nil p))))
def c2297 : List Lit := [(123, true), (121, false), (101, false), (1744, false), (1746, true), (108, true), (1756, true), (1737, false)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c1708, c1710, c1717, c901, c1736, c1693, c1703] c2297 (by decide) p (sat_cons (step1708 p h) (sat_cons (step1710 p h) (sat_cons (step1717 p h) (sat_cons (step901 p h) (sat_cons (step1736 p h) (sat_cons (step1693 p h) (sat_cons (step1703 p h) (sat_nil p))))))))
def c2298 : List Lit := [(121, false), (101, false), (1737, false), (1744, false), (1746, true), (108, true), (1756, true)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c2297, c905, c902, c1709, c1693, c1717, c1703, c1736] c2298 (by decide) p (sat_cons (step2297 p h) (sat_cons (step905 p h) (sat_cons (step902 p h) (sat_cons (step1709 p h) (sat_cons (step1693 p h) (sat_cons (step1717 p h) (sat_cons (step1703 p h) (sat_cons (step1736 p h) (sat_nil p)))))))))
def c2299 : List Lit := [(1715, true), (225, true), (1744, false), (1746, true), (108, true), (1756, true), (1737, false)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c1647, c1649, c1644, c1645, c1641, c545, c570, c2298] c2299 (by decide) p (sat_cons (step1647 p h) (sat_cons (step1649 p h) (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step1641 p h) (sat_cons (step545 p h) (sat_cons (step570 p h) (sat_cons (step2298 p h) (sat_nil p)))))))))
def c2300 : List Lit := [(1755, true), (1744, false), (108, true), (113, false), (118, true), (1737, false)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c1716, c1692, c1700, c1735, c1731, c1703, c1717, c1693, c1708, c1709, c908, c2276] c2300 (by decide) p (sat_cons (step1716 p h) (sat_cons (step1692 p h) (sat_cons (step1700 p h) (sat_cons (step1735 p h) (sat_cons (step1731 p h) (sat_cons (step1703 p h) (sat_cons (step1717 p h) (sat_cons (step1693 p h) (sat_cons (step1708 p h) (sat_cons (step1709 p h) (sat_cons (step908 p h) (sat_cons (step2276 p h) (sat_nil p)))))))))))))
def c2301 : List Lit := [(123, false), (122, false), (110, false), (121, true), (113, false)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c710, c750, c939, c697, c924, c1221, c1236, c1222, c1239, c1232, c1241, c2239] c2301 (by decide) p (sat_cons (step710 p h) (sat_cons (step750 p h) (sat_cons (step939 p h) (sat_cons (step697 p h) (sat_cons (step924 p h) (sat_cons (step1221 p h) (sat_cons (step1236 p h) (sat_cons (step1222 p h) (sat_cons (step1239 p h) (sat_cons (step1232 p h) (sat_cons (step1241 p h) (sat_cons (step2239 p h) (sat_nil p)))))))))))))
def c2302 : List Lit := [(1715, true), (225, true), (121, true)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c1647, c1649, c1644, c1645, c1641, c570, c545] c2302 (by decide) p (sat_cons (step1647 p h) (sat_cons (step1649 p h) (sat_cons (step1644 p h) (sat_cons (step1645 p h) (sat_cons (step1641 p h) (sat_cons (step570 p h) (sat_cons (step545 p h) (sat_nil p))))))))
def c2303 : List Lit := [(1606, true), (54, false), (64, false), (188, true), (61, true), (56, true)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c1419, c1417, c1426, c1428, c1421, c1418, c2040] c2303 (by decide) p (sat_cons (step1419 p h) (sat_cons (step1417 p h) (sat_cons (step1426 p h) (sat_cons (step1428 p h) (sat_cons (step1421 p h) (sat_cons (step1418 p h) (sat_cons (step2040 p h) (sat_nil p))))))))
def c2304 : List Lit := [(67, true), (83, true), (72, false), (196, true)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c418, c417, c2135, c1898] c2304 (by decide) p (sat_cons (step418 p h) (sat_cons (step417 p h) (sat_cons (step2135 p h) (sat_cons (step1898 p h) (sat_nil p)))))
def c2305 : List Lit := [(1560, true), (17, true), (76, false), (305, true)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c1296, c1303, c1056, c1053, c1037, c1034, c1031, c1051, c1049, c1042, c1041, c2244, c2271, c1329, c1298, c1299, c1989, c1320, c86, c76, c1310, c1311, c1317, c116, c115, c1333, c1867, c1306, c1297] c2305 (by decide) p (sat_cons (step1296 p h) (sat_cons (step1303 p h) (sat_cons (step1056 p h) (sat_cons (step1053 p h) (sat_cons (step1037 p h) (sat_cons (step1034 p h) (sat_cons (step1031 p h) (sat_cons (step1051 p h) (sat_cons (step1049 p h) (sat_cons (step1042 p h) (sat_cons (step1041 p h) (sat_cons (step2244 p h) (sat_cons (step2271 p h) (sat_cons (step1329 p h) (sat_cons (step1298 p h) (sat_cons (step1299 p h) (sat_cons (step1989 p h) (sat_cons (step1320 p h) (sat_cons (step86 p h) (sat_cons (step76 p h) (sat_cons (step1310 p h) (sat_cons (step1311 p h) (sat_cons (step1317 p h) (sat_cons (step116 p h) (sat_cons (step115 p h) (sat_cons (step1333 p h) (sat_cons (step1867 p h) (sat_cons (step1306 p h) (sat_cons (step1297 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2306 : List Lit := [(1676, true), (207, true), (117, false), (121, true)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c1561, c1563, c1559, c1556, c474, c444] c2306 (by decide) p (sat_cons (step1561 p h) (sat_cons (step1563 p h) (sat_cons (step1559 p h) (sat_cons (step1556 p h) (sat_cons (step474 p h) (sat_cons (step444 p h) (sat_nil p)))))))
def c2307 : List Lit := [(72, false), (67, true), (1673, true), (427, true), (117, false), (121, true)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c1187, c1150, c1148, c1139, c1138, c1185, c1182, c1164, c1162, c1159, c417, c2304, c460, c474, c1557, c444] c2307 (by decide) p (sat_cons (step1187 p h) (sat_cons (step1150 p h) (sat_cons (step1148 p h) (sat_cons (step1139 p h) (sat_cons (step1138 p h) (sat_cons (step1185 p h) (sat_cons (step1182 p h) (sat_cons (step1164 p h) (sat_cons (step1162 p h) (sat_cons (step1159 p h) (sat_cons (step417 p h) (sat_cons (step2304 p h) (sat_cons (step460 p h) (sat_cons (step474 p h) (sat_cons (step1557 p h) (sat_cons (step444 p h) (sat_nil p)))))))))))))))))
def c2308 : List Lit := [(1575, true), (38, false), (44, false), (1572, false)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c1370, c1372, c2002] c2308 (by decide) p (sat_cons (step1370 p h) (sat_cons (step1372 p h) (sat_cons (step2002 p h) (sat_nil p))))
def c2309 : List Lit := [(48, false), (52, false), (51, true), (172, true), (104, true)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c206, c204, c1877] c2309 (by decide) p (sat_cons (step206 p h) (sat_cons (step204 p h) (sat_cons (step1877 p h) (sat_nil p))))
def c2310 : List Lit := [(1551, true), (31, true), (17, true), (151, true)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c1312, c1315, c1296, c1303, c1329, c1333, c1316, c1318, c1306, c1314, c1309, c1297, c115, c121] c2310 (by decide) p (sat_cons (step1312 p h) (sat_cons (step1315 p h) (sat_cons (step1296 p h) (sat_cons (step1303 p h) (sat_cons (step1329 p h) (sat_cons (step1333 p h) (sat_cons (step1316 p h) (sat_cons (step1318 p h) (sat_cons (step1306 p h) (sat_cons (step1314 p h) (sat_cons (step1309 p h) (sat_cons (step1297 p h) (sat_cons (step115 p h) (sat_cons (step121 p h) (sat_nil p)))))))))))))))
def c2311 : List Lit := [(24, true), (3, false), (13, false), (6, false), (275, true)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c1027, c1012, c1010, c1008, c18, c1009, c1025, c1021, c1019, c1016, c16, c2067, c33, c7] c2311 (by decide) p (sat_cons (step1027 p h) (sat_cons (step1012 p h) (sat_cons (step1010 p h) (sat_cons (step1008 p h) (sat_cons (step18 p h) (sat_cons (step1009 p h) (sat_cons (step1025 p h) (sat_cons (step1021 p h) (sat_cons (step1019 p h) (sat_cons (step1016 p h) (sat_cons (step16 p h) (sat_cons (step2067 p h) (sat_cons (step33 p h) (sat_cons (step7 p h) (sat_nil p)))))))))))))))
def c2312 : List Lit := [(1527, true), (6, false), (32, true), (59, false), (275, true)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c1027, c1012, c1010, c1008, c18, c1273, c1279, c1013, c1006, c1005, c2000, c1286, c1275, c1270, c2060, c2311, c89] c2312 (by decide) p (sat_cons (step1027 p h) (sat_cons (step1012 p h) (sat_cons (step1010 p h) (sat_cons (step1008 p h) (sat_cons (step18 p h) (sat_cons (step1273 p h) (sat_cons (step1279 p h) (sat_cons (step1013 p h) (sat_cons (step1006 p h) (sat_cons (step1005 p h) (sat_cons (step2000 p h) (sat_cons (step1286 p h) (sat_cons (step1275 p h) (sat_cons (step1270 p h) (sat_cons (step2060 p h) (sat_cons (step2311 p h) (sat_cons (step89 p h) (sat_nil p))))))))))))))))))
end B112E105
