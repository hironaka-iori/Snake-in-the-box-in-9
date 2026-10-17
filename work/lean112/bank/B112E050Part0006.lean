import B112E050Part0005
namespace B112E050
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2200 : List Lit := [(379, false), (505, false)]
theorem step2200 (p : Nat → Bool) (h : Constraints p) : clause p c2200 = true :=
  Snake9.LocalRup.prove_clause [c1097, c1095] c2200 (by decide) p (sat_cons (step1097 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c2201 : List Lit := [(1595, false), (1606, true)]
theorem step2201 (p : Nat → Bool) (h : Constraints p) : clause p c2201 = true :=
  Snake9.LocalRup.prove_clause [c1883, c1169] c2201 (by decide) p (sat_cons (step1883 p h) (sat_cons (step1169 p h) (sat_nil p)))
def c2202 : List Lit := [(1596, false), (1607, true)]
theorem step2202 (p : Nat → Bool) (h : Constraints p) : clause p c2202 = true :=
  Snake9.LocalRup.prove_clause [c1883, c1170] c2202 (by decide) p (sat_cons (step1883 p h) (sat_cons (step1170 p h) (sat_nil p)))
def c2203 : List Lit := [(1597, false), (1608, true)]
theorem step2203 (p : Nat → Bool) (h : Constraints p) : clause p c2203 = true :=
  Snake9.LocalRup.prove_clause [c1883, c1171] c2203 (by decide) p (sat_cons (step1883 p h) (sat_cons (step1171 p h) (sat_nil p)))
def c2204 : List Lit := [(1598, false), (1609, true)]
theorem step2204 (p : Nat → Bool) (h : Constraints p) : clause p c2204 = true :=
  Snake9.LocalRup.prove_clause [c1883, c1172] c2204 (by decide) p (sat_cons (step1883 p h) (sat_cons (step1172 p h) (sat_nil p)))
def c2205 : List Lit := [(1600, false), (1611, true)]
theorem step2205 (p : Nat → Bool) (h : Constraints p) : clause p c2205 = true :=
  Snake9.LocalRup.prove_clause [c1883, c1173] c2205 (by decide) p (sat_cons (step1883 p h) (sat_cons (step1173 p h) (sat_nil p)))
def c2206 : List Lit := [(1658, false), (1667, true)]
theorem step2206 (p : Nat → Bool) (h : Constraints p) : clause p c2206 = true :=
  Snake9.LocalRup.prove_clause [c1881, c1284] c2206 (by decide) p (sat_cons (step1881 p h) (sat_cons (step1284 p h) (sat_nil p)))
def c2207 : List Lit := [(1659, false), (1668, true)]
theorem step2207 (p : Nat → Bool) (h : Constraints p) : clause p c2207 = true :=
  Snake9.LocalRup.prove_clause [c1881, c1285] c2207 (by decide) p (sat_cons (step1881 p h) (sat_cons (step1285 p h) (sat_nil p)))
def c2208 : List Lit := [(1660, false), (1669, true)]
theorem step2208 (p : Nat → Bool) (h : Constraints p) : clause p c2208 = true :=
  Snake9.LocalRup.prove_clause [c1881, c1286] c2208 (by decide) p (sat_cons (step1881 p h) (sat_cons (step1286 p h) (sat_nil p)))
def c2209 : List Lit := [(1661, false), (1670, true)]
theorem step2209 (p : Nat → Bool) (h : Constraints p) : clause p c2209 = true :=
  Snake9.LocalRup.prove_clause [c1881, c1287] c2209 (by decide) p (sat_cons (step1881 p h) (sat_cons (step1287 p h) (sat_nil p)))
def c2210 : List Lit := [(1662, false), (1671, true)]
theorem step2210 (p : Nat → Bool) (h : Constraints p) : clause p c2210 = true :=
  Snake9.LocalRup.prove_clause [c1881, c1288] c2210 (by decide) p (sat_cons (step1881 p h) (sat_cons (step1288 p h) (sat_nil p)))
def c2211 : List Lit := [(1667, false), (1687, true)]
theorem step2211 (p : Nat → Bool) (h : Constraints p) : clause p c2211 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1318] c2211 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1318 p h) (sat_nil p)))
def c2212 : List Lit := [(1668, false), (1688, true)]
theorem step2212 (p : Nat → Bool) (h : Constraints p) : clause p c2212 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1319] c2212 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1319 p h) (sat_nil p)))
def c2213 : List Lit := [(1669, false), (1689, true)]
theorem step2213 (p : Nat → Bool) (h : Constraints p) : clause p c2213 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1320] c2213 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1320 p h) (sat_nil p)))
def c2214 : List Lit := [(1670, false), (1690, true)]
theorem step2214 (p : Nat → Bool) (h : Constraints p) : clause p c2214 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1321] c2214 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1321 p h) (sat_nil p)))
def c2215 : List Lit := [(1671, false), (1691, true)]
theorem step2215 (p : Nat → Bool) (h : Constraints p) : clause p c2215 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1322] c2215 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1322 p h) (sat_nil p)))
def c2216 : List Lit := [(1672, false), (1692, true)]
theorem step2216 (p : Nat → Bool) (h : Constraints p) : clause p c2216 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1323] c2216 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1323 p h) (sat_nil p)))
def c2217 : List Lit := [(1673, false), (1693, true)]
theorem step2217 (p : Nat → Bool) (h : Constraints p) : clause p c2217 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1324] c2217 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1324 p h) (sat_nil p)))
def c2218 : List Lit := [(1674, false), (1694, true)]
theorem step2218 (p : Nat → Bool) (h : Constraints p) : clause p c2218 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1325] c2218 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1325 p h) (sat_nil p)))
def c2219 : List Lit := [(1675, false), (1695, true)]
theorem step2219 (p : Nat → Bool) (h : Constraints p) : clause p c2219 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1326] c2219 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1326 p h) (sat_nil p)))
def c2220 : List Lit := [(1606, false), (1687, true)]
theorem step2220 (p : Nat → Bool) (h : Constraints p) : clause p c2220 = true :=
  Snake9.LocalRup.prove_clause [c1882, c1327] c2220 (by decide) p (sat_cons (step1882 p h) (sat_cons (step1327 p h) (sat_nil p)))
def c2221 : List Lit := [(1607, false), (1688, true)]
theorem step2221 (p : Nat → Bool) (h : Constraints p) : clause p c2221 = true :=
  Snake9.LocalRup.prove_clause [c1882, c1337] c2221 (by decide) p (sat_cons (step1882 p h) (sat_cons (step1337 p h) (sat_nil p)))
def c2222 : List Lit := [(1608, false), (1689, true)]
theorem step2222 (p : Nat → Bool) (h : Constraints p) : clause p c2222 = true :=
  Snake9.LocalRup.prove_clause [c1882, c1346] c2222 (by decide) p (sat_cons (step1882 p h) (sat_cons (step1346 p h) (sat_nil p)))
def c2223 : List Lit := [(1609, false), (1690, true)]
theorem step2223 (p : Nat → Bool) (h : Constraints p) : clause p c2223 = true :=
  Snake9.LocalRup.prove_clause [c1882, c1354] c2223 (by decide) p (sat_cons (step1882 p h) (sat_cons (step1354 p h) (sat_nil p)))
def c2224 : List Lit := [(1610, false), (1691, true)]
theorem step2224 (p : Nat → Bool) (h : Constraints p) : clause p c2224 = true :=
  Snake9.LocalRup.prove_clause [c1882, c1361] c2224 (by decide) p (sat_cons (step1882 p h) (sat_cons (step1361 p h) (sat_nil p)))
def c2225 : List Lit := [(1747, false), (1756, true)]
theorem step2225 (p : Nat → Bool) (h : Constraints p) : clause p c2225 = true :=
  Snake9.LocalRup.prove_clause [c1878, c1473] c2225 (by decide) p (sat_cons (step1878 p h) (sat_cons (step1473 p h) (sat_nil p)))
def c2226 : List Lit := [(1748, false), (1757, true)]
theorem step2226 (p : Nat → Bool) (h : Constraints p) : clause p c2226 = true :=
  Snake9.LocalRup.prove_clause [c1878, c1474] c2226 (by decide) p (sat_cons (step1878 p h) (sat_cons (step1474 p h) (sat_nil p)))
def c2227 : List Lit := [(1749, false), (1758, true)]
theorem step2227 (p : Nat → Bool) (h : Constraints p) : clause p c2227 = true :=
  Snake9.LocalRup.prove_clause [c1878, c1475] c2227 (by decide) p (sat_cons (step1878 p h) (sat_cons (step1475 p h) (sat_nil p)))
def c2228 : List Lit := [(1750, false), (1759, true)]
theorem step2228 (p : Nat → Bool) (h : Constraints p) : clause p c2228 = true :=
  Snake9.LocalRup.prove_clause [c1878, c1476] c2228 (by decide) p (sat_cons (step1878 p h) (sat_cons (step1476 p h) (sat_nil p)))
def c2229 : List Lit := [(1751, false), (1760, true)]
theorem step2229 (p : Nat → Bool) (h : Constraints p) : clause p c2229 = true :=
  Snake9.LocalRup.prove_clause [c1878, c1477] c2229 (by decide) p (sat_cons (step1878 p h) (sat_cons (step1477 p h) (sat_nil p)))
def c2230 : List Lit := [(1752, false), (1761, true)]
theorem step2230 (p : Nat → Bool) (h : Constraints p) : clause p c2230 = true :=
  Snake9.LocalRup.prove_clause [c1878, c1478] c2230 (by decide) p (sat_cons (step1878 p h) (sat_cons (step1478 p h) (sat_nil p)))
def c2231 : List Lit := [(1753, false), (1762, true)]
theorem step2231 (p : Nat → Bool) (h : Constraints p) : clause p c2231 = true :=
  Snake9.LocalRup.prove_clause [c1878, c1479] c2231 (by decide) p (sat_cons (step1878 p h) (sat_cons (step1479 p h) (sat_nil p)))
def c2232 : List Lit := [(1754, false), (1763, true)]
theorem step2232 (p : Nat → Bool) (h : Constraints p) : clause p c2232 = true :=
  Snake9.LocalRup.prove_clause [c1878, c1480] c2232 (by decide) p (sat_cons (step1878 p h) (sat_cons (step1480 p h) (sat_nil p)))
def c2233 : List Lit := [(1816, true), (1810, false)]
theorem step2233 (p : Nat → Bool) (h : Constraints p) : clause p c2233 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1607] c2233 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1607 p h) (sat_nil p)))
def c2234 : List Lit := [(1817, true), (1811, false)]
theorem step2234 (p : Nat → Bool) (h : Constraints p) : clause p c2234 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1608] c2234 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1608 p h) (sat_nil p)))
def c2235 : List Lit := [(1812, false), (1818, true)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1609] c2235 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1609 p h) (sat_nil p)))
def c2236 : List Lit := [(1813, false), (1819, true)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1610] c2236 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1610 p h) (sat_nil p)))
def c2237 : List Lit := [(1827, true), (1789, false)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c1970, c1639] c2237 (by decide) p (sat_cons (step1970 p h) (sat_cons (step1639 p h) (sat_nil p)))
def c2238 : List Lit := [(1828, true), (1790, false)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c1970, c1646] c2238 (by decide) p (sat_cons (step1970 p h) (sat_cons (step1646 p h) (sat_nil p)))
def c2239 : List Lit := [(1829, true), (1791, false)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c1970, c1653] c2239 (by decide) p (sat_cons (step1970 p h) (sat_cons (step1653 p h) (sat_nil p)))
def c2240 : List Lit := [(1830, true), (1792, false)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c1970, c1659] c2240 (by decide) p (sat_cons (step1970 p h) (sat_cons (step1659 p h) (sat_nil p)))
def c2241 : List Lit := [(1793, false), (1831, true)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c1970, c1665] c2241 (by decide) p (sat_cons (step1970 p h) (sat_cons (step1665 p h) (sat_nil p)))
def c2242 : List Lit := [(1794, false), (1832, true)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c1970, c1670] c2242 (by decide) p (sat_cons (step1970 p h) (sat_cons (step1670 p h) (sat_nil p)))
def c2243 : List Lit := [(1765, false), (1832, false)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c1886, c1735] c2243 (by decide) p (sat_cons (step1886 p h) (sat_cons (step1735 p h) (sat_nil p)))
def c2244 : List Lit := [(1687, false), (1859, false)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1738] c2244 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1738 p h) (sat_nil p)))
def c2245 : List Lit := [(1688, false), (1858, false)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1739] c2245 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1739 p h) (sat_nil p)))
def c2246 : List Lit := [(1689, false), (1857, false)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1740] c2246 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1740 p h) (sat_nil p)))
def c2247 : List Lit := [(1690, false), (1856, false)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1741] c2247 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1741 p h) (sat_nil p)))
def c2248 : List Lit := [(1691, false), (1855, false)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1742] c2248 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1742 p h) (sat_nil p)))
def c2249 : List Lit := [(1692, false), (1854, false)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1743] c2249 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1743 p h) (sat_nil p)))
def c2250 : List Lit := [(1693, false), (1853, false)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1744] c2250 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1744 p h) (sat_nil p)))
def c2251 : List Lit := [(1694, false), (1852, false)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1745] c2251 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1745 p h) (sat_nil p)))
def c2252 : List Lit := [(1695, false), (1851, false)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1746] c2252 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1746 p h) (sat_nil p)))
def c2253 : List Lit := [(1696, false), (1850, false)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c1748, c1747] c2253 (by decide) p (sat_cons (step1748 p h) (sat_cons (step1747 p h) (sat_nil p)))
def c2254 : List Lit := [(94, true), (103, true), (1832, true), (1782, false), (96, true), (1774, false), (123, true)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1902] c2254 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1902 p h) (sat_nil p)))
def c2255 : List Lit := [(125, true), (1797, false), (1807, false), (1817, true)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c1960, c1944] c2255 (by decide) p (sat_cons (step1960 p h) (sat_cons (step1944 p h) (sat_nil p)))
def c2256 : List Lit := [(1588, true), (25, false), (16, false), (1619, true), (21, false)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c1138, c1139, c1913, c2013, c1188] c2256 (by decide) p (sat_cons (step1138 p h) (sat_cons (step1139 p h) (sat_cons (step1913 p h) (sat_cons (step2013 p h) (sat_cons (step1188 p h) (sat_nil p))))))
def c2257 : List Lit := [(47, true), (45, false), (42, false)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c2055, c2056, c1761] c2257 (by decide) p (sat_cons (step2055 p h) (sat_cons (step2056 p h) (sat_cons (step1761 p h) (sat_nil p))))
def c2258 : List Lit := [(123, false), (122, false), (1725, true), (102, false), (1707, false)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c1971, c1384, c1411, c1379, c806, c804, c2095, c2094, c1780, c1372, c1374, c1378, c276, c1407, c1386, c1389] c2258 (by decide) p (sat_cons (step1971 p h) (sat_cons (step1384 p h) (sat_cons (step1411 p h) (sat_cons (step1379 p h) (sat_cons (step806 p h) (sat_cons (step804 p h) (sat_cons (step2095 p h) (sat_cons (step2094 p h) (sat_cons (step1780 p h) (sat_cons (step1372 p h) (sat_cons (step1374 p h) (sat_cons (step1378 p h) (sat_cons (step276 p h) (sat_cons (step1407 p h) (sat_cons (step1386 p h) (sat_cons (step1389 p h) (sat_nil p)))))))))))))))))
def c2259 : List Lit := [(114, false), (1796, true), (72, false), (123, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c745, c743, c1572] c2259 (by decide) p (sat_cons (step745 p h) (sat_cons (step743 p h) (sat_cons (step1572 p h) (sat_nil p))))
def c2260 : List Lit := [(80, false), (1718, true), (72, false), (123, false)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c333, c335, c1388] c2260 (by decide) p (sat_cons (step333 p h) (sat_cons (step335 p h) (sat_cons (step1388 p h) (sat_nil p))))
def c2261 : List Lit := [(1744, true), (109, false), (91, true)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1444, c1442, c1435, c1437, c1957, c372] c2261 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1444 p h) (sat_cons (step1442 p h) (sat_cons (step1435 p h) (sat_cons (step1437 p h) (sat_cons (step1957 p h) (sat_cons (step372 p h) (sat_nil p))))))))
def c2262 : List Lit := [(1741, true), (1771, true)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1518, c1436, c1437, c491, c474, c2122] c2262 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1518 p h) (sat_cons (step1436 p h) (sat_cons (step1437 p h) (sat_cons (step491 p h) (sat_cons (step474 p h) (sat_cons (step2122 p h) (sat_nil p))))))))
def c2263 : List Lit := [(1773, true), (102, false), (123, false)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1522, c595] c2263 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step595 p h) (sat_nil p))))
end B112E050
