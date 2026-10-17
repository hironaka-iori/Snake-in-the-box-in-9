import B112E034Part0007
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2291 : List Lit := [(33, false), (1617, true), (43, true), (108, true)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c1985, c1891] c2291 (by decide) p (sat_cons (step1985 p h) (sat_cons (step1891 p h) (sat_nil p)))
def c2292 : List Lit := [(1604, false), (1610, true), (1623, true), (43, true), (108, true), (35, true)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c1194, c1200, c1201, c1230, c1196, c2291] c2292 (by decide) p (sat_cons (step1194 p h) (sat_cons (step1200 p h) (sat_cons (step1201 p h) (sat_cons (step1230 p h) (sat_cons (step1196 p h) (sat_cons (step2291 p h) (sat_nil p)))))))
def c2293 : List Lit := [(1616, true), (39, true)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c1211, c1213, c1209, c1205, c1206, c2000, c155] c2293 (by decide) p (sat_cons (step1211 p h) (sat_cons (step1213 p h) (sat_cons (step1209 p h) (sat_cons (step1205 p h) (sat_cons (step1206 p h) (sat_cons (step2000 p h) (sat_cons (step155 p h) (sat_nil p))))))))
def c2294 : List Lit := [(1740, true), (93, false), (108, true), (99, true)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1444, c1436, c1438, c1430, c1434, c415, c400, c2058] c2294 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1444 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1430 p h) (sat_cons (step1434 p h) (sat_cons (step415 p h) (sat_cons (step400 p h) (sat_cons (step2058 p h) (sat_nil p))))))))))
def c2295 : List Lit := [(1686, true), (1623, false), (1628, false)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1246, c2153, c1312, c1329, c1337, c1313, c2195, c2154, c1241, c1247] c2295 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1246 p h) (sat_cons (step2153 p h) (sat_cons (step1312 p h) (sat_cons (step1329 p h) (sat_cons (step1337 p h) (sat_cons (step1313 p h) (sat_cons (step2195 p h) (sat_cons (step2154 p h) (sat_cons (step1241 p h) (sat_cons (step1247 p h) (sat_nil p))))))))))))
def c2296 : List Lit := [(1740, true), (108, true), (99, true)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c1441, c2294, c1436, c1433] c2296 (by decide) p (sat_cons (step1441 p h) (sat_cons (step2294 p h) (sat_cons (step1436 p h) (sat_cons (step1433 p h) (sat_nil p)))))
def c2297 : List Lit := [(51, false), (1595, true), (1574, false), (21, true)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c1949, c1831, c1119, c1818, c1126, c1825, c1176, c1836, c1150, c1120, c1144, c1896, c1134] c2297 (by decide) p (sat_cons (step1949 p h) (sat_cons (step1831 p h) (sat_cons (step1119 p h) (sat_cons (step1818 p h) (sat_cons (step1126 p h) (sat_cons (step1825 p h) (sat_cons (step1176 p h) (sat_cons (step1836 p h) (sat_cons (step1150 p h) (sat_cons (step1120 p h) (sat_cons (step1144 p h) (sat_cons (step1896 p h) (sat_cons (step1134 p h) (sat_nil p))))))))))))))
def c2298 : List Lit := [(21, true), (1594, true), (1574, false)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c2144, c1133, c1836, c1141, c1893, c1122, c1889, c1175, c1825, c1818, c1895, c1119, c1120, c1126, c1896, c1150, c1134, c1144] c2298 (by decide) p (sat_cons (step2144 p h) (sat_cons (step1133 p h) (sat_cons (step1836 p h) (sat_cons (step1141 p h) (sat_cons (step1893 p h) (sat_cons (step1122 p h) (sat_cons (step1889 p h) (sat_cons (step1175 p h) (sat_cons (step1825 p h) (sat_cons (step1818 p h) (sat_cons (step1895 p h) (sat_cons (step1119 p h) (sat_cons (step1120 p h) (sat_cons (step1126 p h) (sat_cons (step1896 p h) (sat_cons (step1150 p h) (sat_cons (step1134 p h) (sat_cons (step1144 p h) (sat_nil p)))))))))))))))))))
def c2299 : List Lit := [(1594, true), (1633, true), (21, true)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c2195, c2298, c1938, c1135] c2299 (by decide) p (sat_cons (step2195 p h) (sat_cons (step2298 p h) (sat_cons (step1938 p h) (sat_cons (step1135 p h) (sat_nil p)))))
def c2300 : List Lit := [(1632, true), (48, false), (122, false), (46, false)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c1246, c2191, c1239, c2012, c197] c2300 (by decide) p (sat_cons (step1246 p h) (sat_cons (step2191 p h) (sat_cons (step1239 p h) (sat_cons (step2012 p h) (sat_cons (step197 p h) (sat_nil p))))))
def c2301 : List Lit := [(97, false), (99, true), (98, false), (100, false), (1738, true), (93, true)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c474, c2186, c2075] c2301 (by decide) p (sat_cons (step474 p h) (sat_cons (step2186 p h) (sat_cons (step2075 p h) (sat_nil p))))
def c2302 : List Lit := [(79, false), (1727, true), (120, false)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1420, c349, c2051, c2050, c1748] c2302 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1420 p h) (sat_cons (step349 p h) (sat_cons (step2051 p h) (sat_cons (step2050 p h) (sat_cons (step1748 p h) (sat_nil p)))))))
def c2303 : List Lit := [(1622, true), (108, true), (110, true), (39, true), (120, false), (117, false)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c1989, c1194, c1197, c2293, c1225, c2252, c2290, c2278, c174] c2303 (by decide) p (sat_cons (step1989 p h) (sat_cons (step1194 p h) (sat_cons (step1197 p h) (sat_cons (step2293 p h) (sat_cons (step1225 p h) (sat_cons (step2252 p h) (sat_cons (step2290 p h) (sat_cons (step2278 p h) (sat_cons (step174 p h) (sat_nil p))))))))))
def c2304 : List Lit := [(70, true), (76, false), (1714, true), (117, false)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c1396, c1386, c1387, c1394, c340, c1389] c2304 (by decide) p (sat_cons (step1396 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step1394 p h) (sat_cons (step340 p h) (sat_cons (step1389 p h) (sat_nil p)))))))
def c2305 : List Lit := [(77, false), (74, false), (70, false), (76, true)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c2048, c336] c2305 (by decide) p (sat_cons (step2048 p h) (sat_cons (step336 p h) (sat_nil p)))
def c2306 : List Lit := [(122, true), (1811, true), (114, true), (117, false)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c1580, c1576, c1577, c1583, c1571, c1572, c1568, c1569, c834, c840, c762, c2110] c2306 (by decide) p (sat_cons (step1580 p h) (sat_cons (step1576 p h) (sat_cons (step1577 p h) (sat_cons (step1583 p h) (sat_cons (step1571 p h) (sat_cons (step1572 p h) (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step834 p h) (sat_cons (step840 p h) (sat_cons (step762 p h) (sat_cons (step2110 p h) (sat_nil p)))))))))))))
def c2307 : List Lit := [(1748, true), (108, true), (84, true), (99, true), (1726, false)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c1428, c1883, c1465, c1436, c1438, c1448, c1433, c1434, c1432, c415, c400, c2058] c2307 (by decide) p (sat_cons (step1428 p h) (sat_cons (step1883 p h) (sat_cons (step1465 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1448 p h) (sat_cons (step1433 p h) (sat_cons (step1434 p h) (sat_cons (step1432 p h) (sat_cons (step415 p h) (sat_cons (step400 p h) (sat_cons (step2058 p h) (sat_nil p)))))))))))))
def c2308 : List Lit := [(1800, true), (112, true), (1795, false), (126, false), (74, false), (117, false)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1563, c1556, c1557, c695, c714, c2098] c2308 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1563 p h) (sat_cons (step1556 p h) (sat_cons (step1557 p h) (sat_cons (step695 p h) (sat_cons (step714 p h) (sat_cons (step2098 p h) (sat_nil p))))))))
def c2309 : List Lit := [(99, true), (108, true), (1748, true), (1726, false)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c2296, c2307, c1469, c1908, c1429] c2309 (by decide) p (sat_cons (step2296 p h) (sat_cons (step2307 p h) (sat_cons (step1469 p h) (sat_cons (step1908 p h) (sat_cons (step1429 p h) (sat_nil p))))))
def c2310 : List Lit := [(1632, true), (122, false)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c1244, c1246, c1242, c1238, c2300] c2310 (by decide) p (sat_cons (step1244 p h) (sat_cons (step1246 p h) (sat_cons (step1242 p h) (sat_cons (step1238 p h) (sat_cons (step2300 p h) (sat_nil p))))))
def c2311 : List Lit := [(1747, true), (1726, false)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c1428, c1468, c1464, c1429, c1444, c1908, c1431] c2311 (by decide) p (sat_cons (step1428 p h) (sat_cons (step1468 p h) (sat_cons (step1464 p h) (sat_cons (step1429 p h) (sat_cons (step1444 p h) (sat_cons (step1908 p h) (sat_cons (step1431 p h) (sat_nil p))))))))
def c2312 : List Lit := [(1622, true), (1617, true), (110, true), (1604, false), (115, true), (117, false), (1616, false)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c1216, c1229, c2252, c1200, c1891, c1194, c1996, c1989, c1207, c158] c2312 (by decide) p (sat_cons (step1216 p h) (sat_cons (step1229 p h) (sat_cons (step2252 p h) (sat_cons (step1200 p h) (sat_cons (step1891 p h) (sat_cons (step1194 p h) (sat_cons (step1996 p h) (sat_cons (step1989 p h) (sat_cons (step1207 p h) (sat_cons (step158 p h) (sat_nil p)))))))))))
def c2313 : List Lit := [(1622, false), (1688, true), (1646, false), (122, false)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1331, c2310, c1282, c1309, c1308, c1287, c1339, c1245, c2195, c1243, c1241, c1247, c1238, c1239, c197, c188, c2012] c2313 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1331 p h) (sat_cons (step2310 p h) (sat_cons (step1282 p h) (sat_cons (step1309 p h) (sat_cons (step1308 p h) (sat_cons (step1287 p h) (sat_cons (step1339 p h) (sat_cons (step1245 p h) (sat_cons (step2195 p h) (sat_cons (step1243 p h) (sat_cons (step1241 p h) (sat_cons (step1247 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step197 p h) (sat_cons (step188 p h) (sat_cons (step2012 p h) (sat_nil p)))))))))))))))))))
def c2314 : List Lit := [(1622, true), (72, false), (1604, false), (115, true), (117, false), (1616, false)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1225, c1229, c2312, c1200, c595, c1194] c2314 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1225 p h) (sat_cons (step1229 p h) (sat_cons (step2312 p h) (sat_cons (step1200 p h) (sat_cons (step595 p h) (sat_cons (step1194 p h) (sat_nil p))))))))
def c2315 : List Lit := [(1789, true), (1773, false), (104, true), (92, false), (89, false), (114, true), (117, false)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c1518, c1526, c1542, c2287, c1513, c2061, c1504, c403] c2315 (by decide) p (sat_cons (step1518 p h) (sat_cons (step1526 p h) (sat_cons (step1542 p h) (sat_cons (step2287 p h) (sat_cons (step1513 p h) (sat_cons (step2061 p h) (sat_cons (step1504 p h) (sat_cons (step403 p h) (sat_nil p)))))))))
def c2316 : List Lit := [(86, true), (1748, true), (1726, false)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c1428, c1465, c1448, c1430, c1432, c1444, c1908, c1469, c1429] c2316 (by decide) p (sat_cons (step1428 p h) (sat_cons (step1465 p h) (sat_cons (step1448 p h) (sat_cons (step1430 p h) (sat_cons (step1432 p h) (sat_cons (step1444 p h) (sat_cons (step1908 p h) (sat_cons (step1469 p h) (sat_cons (step1429 p h) (sat_nil p))))))))))
def c2317 : List Lit := [(1617, true), (33, false), (36, true), (115, true)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c1216, c1891, c1207, c1996] c2317 (by decide) p (sat_cons (step1216 p h) (sat_cons (step1891 p h) (sat_cons (step1207 p h) (sat_cons (step1996 p h) (sat_nil p)))))
def c2318 : List Lit := [(37, false), (38, false), (33, false), (115, true)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c1997, c1727] c2318 (by decide) p (sat_cons (step1997 p h) (sat_cons (step1727 p h) (sat_nil p)))
def c2319 : List Lit := [(57, true), (115, true), (70, false), (74, false)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c2044, c2043, c1743] c2319 (by decide) p (sat_cons (step2044 p h) (sat_cons (step2043 p h) (sat_cons (step1743 p h) (sat_nil p))))
def c2320 : List Lit := [(53, true), (1637, true), (57, false), (1646, true), (74, false)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c1252, c1269, c1254, c243, c238, c241, c1257, c1262] c2320 (by decide) p (sat_cons (step1252 p h) (sat_cons (step1269 p h) (sat_cons (step1254 p h) (sat_cons (step243 p h) (sat_cons (step238 p h) (sat_cons (step241 p h) (sat_cons (step1257 p h) (sat_cons (step1262 p h) (sat_nil p)))))))))
def c2321 : List Lit := [(1645, false), (1622, false), (1687, true), (20, false), (92, false), (1632, false)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1330, c1308, c1281, c1286, c1307, c1338, c2144, c2195, c2299, c2277, c1938, c63, c57, c1120, c1135, c1121, c1119, c1896, c1127, c1132, c1154, c1141] c2321 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1330 p h) (sat_cons (step1308 p h) (sat_cons (step1281 p h) (sat_cons (step1286 p h) (sat_cons (step1307 p h) (sat_cons (step1338 p h) (sat_cons (step2144 p h) (sat_cons (step2195 p h) (sat_cons (step2299 p h) (sat_cons (step2277 p h) (sat_cons (step1938 p h) (sat_cons (step63 p h) (sat_cons (step57 p h) (sat_cons (step1120 p h) (sat_cons (step1135 p h) (sat_cons (step1121 p h) (sat_cons (step1119 p h) (sat_cons (step1896 p h) (sat_cons (step1127 p h) (sat_cons (step1132 p h) (sat_cons (step1154 p h) (sat_cons (step1141 p h) (sat_nil p))))))))))))))))))))))))
def c2322 : List Lit := [(57, false), (53, true), (1645, true), (1646, true), (74, false)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c1923, c2320, c1271] c2322 (by decide) p (sat_cons (step1923 p h) (sat_cons (step2320 p h) (sat_cons (step1271 p h) (sat_nil p))))
def c2323 : List Lit := [(1644, true), (57, true), (1636, false), (86, false), (89, false), (70, false), (74, false)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c1857, c1267, c405, c293, c2015, c1260, c211] c2323 (by decide) p (sat_cons (step1857 p h) (sat_cons (step1267 p h) (sat_cons (step405 p h) (sat_cons (step293 p h) (sat_cons (step2015 p h) (sat_cons (step1260 p h) (sat_cons (step211 p h) (sat_nil p))))))))
def c2324 : List Lit := [(51, true), (1633, true), (122, false)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1241, c1243, c1247, c1238, c1239, c197, c188, c2012] c2324 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1241 p h) (sat_cons (step1243 p h) (sat_cons (step1247 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step197 p h) (sat_cons (step188 p h) (sat_cons (step2012 p h) (sat_nil p))))))))))
def c2325 : List Lit := [(35, true), (1623, true), (1604, false), (37, true), (114, true), (117, false)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c1205, c1194, c1200, c2257, c1230, c1216, c1214, c1207, c1209, c160] c2325 (by decide) p (sat_cons (step1205 p h) (sat_cons (step1194 p h) (sat_cons (step1200 p h) (sat_cons (step2257 p h) (sat_cons (step1230 p h) (sat_cons (step1216 p h) (sat_cons (step1214 p h) (sat_cons (step1207 p h) (sat_cons (step1209 p h) (sat_cons (step160 p h) (sat_nil p)))))))))))
def c2326 : List Lit := [(57, false), (1644, true), (74, false)]
theorem step2326 (p : Nat → Bool) (h : Constraints p) : clause p c2326 = true :=
  Snake9.LocalRup.prove_clause [c1264, c1259, c1857, c243, c241, c1257] c2326 (by decide) p (sat_cons (step1264 p h) (sat_cons (step1259 p h) (sat_cons (step1857 p h) (sat_cons (step243 p h) (sat_cons (step241 p h) (sat_cons (step1257 p h) (sat_nil p)))))))
def c2327 : List Lit := [(1644, true), (86, false), (89, false), (70, false), (74, false)]
theorem step2327 (p : Nat → Bool) (h : Constraints p) : clause p c2327 = true :=
  Snake9.LocalRup.prove_clause [c1857, c405, c293, c2326, c2323, c2015, c1252, c210] c2327 (by decide) p (sat_cons (step1857 p h) (sat_cons (step405 p h) (sat_cons (step293 p h) (sat_cons (step2326 p h) (sat_cons (step2323 p h) (sat_cons (step2015 p h) (sat_cons (step1252 p h) (sat_cons (step210 p h) (sat_nil p)))))))))
def c2328 : List Lit := [(1781, false), (1790, true), (101, false), (1771, false), (103, true), (126, false)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c1512, c1539, c1519, c1527, c1530, c1543, c1520, c1513, c506, c1508] c2328 (by decide) p (sat_cons (step1512 p h) (sat_cons (step1539 p h) (sat_cons (step1519 p h) (sat_cons (step1527 p h) (sat_cons (step1530 p h) (sat_cons (step1543 p h) (sat_cons (step1520 p h) (sat_cons (step1513 p h) (sat_cons (step506 p h) (sat_cons (step1508 p h) (sat_nil p)))))))))))
def c2329 : List Lit := [(1779, true), (97, true), (1777, true), (92, false), (126, false)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c1518, c1915, c1506, c1516, c1507, c1508, c1848, c506, c2085] c2329 (by decide) p (sat_cons (step1518 p h) (sat_cons (step1915 p h) (sat_cons (step1506 p h) (sat_cons (step1516 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step1848 p h) (sat_cons (step506 p h) (sat_cons (step2085 p h) (sat_nil p))))))))))
def c2330 : List Lit := [(120, false), (1775, true), (125, false)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c1510, c1508, c1507, c1512, c1504, c474, c760, c491, c2072] c2330 (by decide) p (sat_cons (step1510 p h) (sat_cons (step1508 p h) (sat_cons (step1507 p h) (sat_cons (step1512 p h) (sat_cons (step1504 p h) (sat_cons (step474 p h) (sat_cons (step760 p h) (sat_cons (step491 p h) (sat_cons (step2072 p h) (sat_nil p))))))))))
def c2331 : List Lit := [(77, false), (70, false), (1714, true), (74, false), (114, true), (117, false)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c2204, c336, c1389, c2251, c1394, c1385] c2331 (by decide) p (sat_cons (step2204 p h) (sat_cons (step336 p h) (sat_cons (step1389 p h) (sat_cons (step2251 p h) (sat_cons (step1394 p h) (sat_cons (step1385 p h) (sat_nil p)))))))
def c2332 : List Lit := [(1623, true), (1604, false), (110, true), (37, true), (114, true), (117, false)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c1199, c2325, c1226, c1989, c159, c158, c1209, c1207, c1217] c2332 (by decide) p (sat_cons (step1199 p h) (sat_cons (step2325 p h) (sat_cons (step1226 p h) (sat_cons (step1989 p h) (sat_cons (step159 p h) (sat_cons (step158 p h) (sat_cons (step1209 p h) (sat_cons (step1207 p h) (sat_cons (step1217 p h) (sat_nil p))))))))))
def c2333 : List Lit := [(119, true), (128, true), (114, true), (125, false), (126, false), (115, false)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c2110, c2111, c829] c2333 (by decide) p (sat_cons (step2110 p h) (sat_cons (step2111 p h) (sat_cons (step829 p h) (sat_nil p))))
def c2334 : List Lit := [(1634, true), (46, true), (45, false), (122, false), (51, true)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1241, c1250, c1248, c1240, c1243, c188] c2334 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1241 p h) (sat_cons (step1250 p h) (sat_cons (step1248 p h) (sat_cons (step1240 p h) (sat_cons (step1243 p h) (sat_cons (step188 p h) (sat_nil p))))))))
def c2335 : List Lit := [(1621, true), (1604, false)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1228, c1224, c1200, c2293, c1194, c1834] c2335 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1228 p h) (sat_cons (step1224 p h) (sat_cons (step1200 p h) (sat_cons (step2293 p h) (sat_cons (step1194 p h) (sat_cons (step1834 p h) (sat_nil p))))))))
def c2336 : List Lit := [(25, false), (1634, true), (45, false), (122, false), (51, true)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c187, c186, c1243, c1239, c1248] c2336 (by decide) p (sat_cons (step187 p h) (sat_cons (step186 p h) (sat_cons (step1243 p h) (sat_cons (step1239 p h) (sat_cons (step1248 p h) (sat_nil p))))))
def c2337 : List Lit := [(109, false), (122, false), (118, false), (117, false)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c713, c624, c2099] c2337 (by decide) p (sat_cons (step713 p h) (sat_cons (step624 p h) (sat_cons (step2099 p h) (sat_nil p))))
def c2338 : List Lit := [(1604, true), (98, false), (126, false)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1859, c501] c2338 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1859 p h) (sat_cons (step501 p h) (sat_nil p))))
def c2339 : List Lit := [(1604, true), (1780, true), (124, true), (114, true), (125, false), (126, false), (115, false), (117, false)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1859, c827, c502, c2109, c1520, c838] c2339 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1859 p h) (sat_cons (step827 p h) (sat_cons (step502 p h) (sat_cons (step2109 p h) (sat_cons (step1520 p h) (sat_cons (step838 p h) (sat_nil p))))))))
def c2340 : List Lit := [(1686, true), (1623, false), (122, false)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c2263, c2310, c2153, c1312, c1329, c1337, c1313, c2195, c2154, c2324] c2340 (by decide) p (sat_cons (step2263 p h) (sat_cons (step2310 p h) (sat_cons (step2153 p h) (sat_cons (step1312 p h) (sat_cons (step1329 p h) (sat_cons (step1337 p h) (sat_cons (step1313 p h) (sat_cons (step2195 p h) (sat_cons (step2154 p h) (sat_cons (step2324 p h) (sat_nil p)))))))))))
def c2341 : List Lit := [(1604, false), (1623, true), (1811, false), (1797, false), (37, true), (107, true), (1830, true), (114, true), (117, false)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c2332, c2325, c600, c598, c1555, c1523, c1563, c1843, c1601, c1630] c2341 (by decide) p (sat_cons (step2332 p h) (sat_cons (step2325 p h) (sat_cons (step600 p h) (sat_cons (step598 p h) (sat_cons (step1555 p h) (sat_cons (step1523 p h) (sat_cons (step1563 p h) (sat_cons (step1843 p h) (sat_cons (step1601 p h) (sat_cons (step1630 p h) (sat_nil p)))))))))))
def c2342 : List Lit := [(112, false), (122, false), (1804, true), (107, false)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c620, c1947, c2105] c2342 (by decide) p (sat_cons (step620 p h) (sat_cons (step1947 p h) (sat_cons (step2105 p h) (sat_nil p))))
def c2343 : List Lit := [(115, false), (1623, true), (121, false), (125, false), (126, false), (1789, true), (123, false), (107, false), (114, true), (117, false)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c840, c683, c2333, c761, c790, c1504, c2332, c1512, c1859, c1538, c826, c1529, c2339] c2343 (by decide) p (sat_cons (step840 p h) (sat_cons (step683 p h) (sat_cons (step2333 p h) (sat_cons (step761 p h) (sat_cons (step790 p h) (sat_cons (step1504 p h) (sat_cons (step2332 p h) (sat_cons (step1512 p h) (sat_cons (step1859 p h) (sat_cons (step1538 p h) (sat_cons (step826 p h) (sat_cons (step1529 p h) (sat_cons (step2339 p h) (sat_nil p))))))))))))))
def c2344 : List Lit := [(1604, true), (101, false), (121, false), (125, false), (126, false), (1789, true), (117, false)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c840, c1191, c2338, c502, c1508, c1518, c1510, c1526, c1538, c1542, c1527, c1513, c1521, c1504, c2242, c761] c2344 (by decide) p (sat_cons (step840 p h) (sat_cons (step1191 p h) (sat_cons (step2338 p h) (sat_cons (step502 p h) (sat_cons (step1508 p h) (sat_cons (step1518 p h) (sat_cons (step1510 p h) (sat_cons (step1526 p h) (sat_cons (step1538 p h) (sat_cons (step1542 p h) (sat_cons (step1527 p h) (sat_cons (step1513 p h) (sat_cons (step1521 p h) (sat_cons (step1504 p h) (sat_cons (step2242 p h) (sat_cons (step761 p h) (sat_nil p)))))))))))))))))
def c2345 : List Lit := [(37, true), (1604, false), (1623, true), (121, false), (114, true), (117, false)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c2332, c2325, c602] c2345 (by decide) p (sat_cons (step2332 p h) (sat_cons (step2325 p h) (sat_cons (step602 p h) (sat_nil p))))
def c2346 : List Lit := [(1623, true), (121, false), (1789, true), (1805, true), (123, false), (107, false), (114, true), (117, false)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c1572, c840, c1571, c2343, c1869, c1872, c1234, c2344, c1201, c2345, c1996, c2318, c1195, c1196, c1200, c602, c1230, c2103, c1877, c752] c2346 (by decide) p (sat_cons (step1572 p h) (sat_cons (step840 p h) (sat_cons (step1571 p h) (sat_cons (step2343 p h) (sat_cons (step1869 p h) (sat_cons (step1872 p h) (sat_cons (step1234 p h) (sat_cons (step2344 p h) (sat_cons (step1201 p h) (sat_cons (step2345 p h) (sat_cons (step1996 p h) (sat_cons (step2318 p h) (sat_cons (step1195 p h) (sat_cons (step1196 p h) (sat_cons (step1200 p h) (sat_cons (step602 p h) (sat_cons (step1230 p h) (sat_cons (step2103 p h) (sat_cons (step1877 p h) (sat_cons (step752 p h) (sat_nil p)))))))))))))))))))))
def c2347 : List Lit := [(86, false), (1773, true), (109, false)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c1508, c1507, c1916, c473] c2347 (by decide) p (sat_cons (step1508 p h) (sat_cons (step1507 p h) (sat_cons (step1916 p h) (sat_cons (step473 p h) (sat_nil p)))))
def c2348 : List Lit := [(92, false), (1584, true), (91, false), (94, true), (28, false), (16, true), (114, true)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c2061, c2062, c1782, c68, c65, c1120, c1133, c1121, c1130, c1140, c1159, c1163, c1862, c1131, c1123] c2348 (by decide) p (sat_cons (step2061 p h) (sat_cons (step2062 p h) (sat_cons (step1782 p h) (sat_cons (step68 p h) (sat_cons (step65 p h) (sat_cons (step1120 p h) (sat_cons (step1133 p h) (sat_cons (step1121 p h) (sat_cons (step1130 p h) (sat_cons (step1140 p h) (sat_cons (step1159 p h) (sat_cons (step1163 p h) (sat_cons (step1862 p h) (sat_cons (step1131 p h) (sat_cons (step1123 p h) (sat_nil p))))))))))))))))
def c2349 : List Lit := [(1779, true), (97, true), (101, false), (1777, true), (126, false), (117, false)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c1518, c1519, c506, c2250, c1508, c1506, c1516] c2349 (by decide) p (sat_cons (step1518 p h) (sat_cons (step1519 p h) (sat_cons (step506 p h) (sat_cons (step2250 p h) (sat_cons (step1508 p h) (sat_cons (step1506 p h) (sat_cons (step1516 p h) (sat_nil p))))))))
def c2350 : List Lit := [(1625, false), (1688, true), (122, false)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1331, c2310, c2153, c1321, c1339, c1322, c2195, c2154, c2324] c2350 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1331 p h) (sat_cons (step2310 p h) (sat_cons (step2153 p h) (sat_cons (step1321 p h) (sat_cons (step1339 p h) (sat_cons (step1322 p h) (sat_cons (step2195 p h) (sat_cons (step2154 p h) (sat_cons (step2324 p h) (sat_nil p)))))))))))
def c2351 : List Lit := [(1650, true), (1663, false), (1748, false), (1829, false), (115, true), (125, false), (122, false), (117, false)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c2310, c2154, c1280, c2324, c1264, c2195, c1338, c2177, c1691, c1487, c2163, c2249, c2238, c2319, c1887] c2351 (by decide) p (sat_cons (step2310 p h) (sat_cons (step2154 p h) (sat_cons (step1280 p h) (sat_cons (step2324 p h) (sat_cons (step1264 p h) (sat_cons (step2195 p h) (sat_cons (step1338 p h) (sat_cons (step2177 p h) (sat_cons (step1691 p h) (sat_cons (step1487 p h) (sat_cons (step2163 p h) (sat_cons (step2249 p h) (sat_cons (step2238 p h) (sat_cons (step2319 p h) (sat_cons (step1887 p h) (sat_nil p))))))))))))))))
def c2352 : List Lit := [(1624, false), (1748, false), (1829, false), (115, true), (125, false), (122, false), (117, false)]
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c2263, c2246, c1481, c1682, c2178, c1331, c2310, c2153, c1318, c1320, c2351, c1319, c1330, c1339, c2177, c2195, c1691, c2324, c1487, c1285, c2163, c1264, c2249, c2238, c2319, c1887] c2352 (by decide) p (sat_cons (step2263 p h) (sat_cons (step2246 p h) (sat_cons (step1481 p h) (sat_cons (step1682 p h) (sat_cons (step2178 p h) (sat_cons (step1331 p h) (sat_cons (step2310 p h) (sat_cons (step2153 p h) (sat_cons (step1318 p h) (sat_cons (step1320 p h) (sat_cons (step2351 p h) (sat_cons (step1319 p h) (sat_cons (step1330 p h) (sat_cons (step1339 p h) (sat_cons (step2177 p h) (sat_cons (step2195 p h) (sat_cons (step1691 p h) (sat_cons (step2324 p h) (sat_cons (step1487 p h) (sat_cons (step1285 p h) (sat_cons (step2163 p h) (sat_cons (step1264 p h) (sat_cons (step2249 p h) (sat_cons (step2238 p h) (sat_cons (step2319 p h) (sat_cons (step1887 p h) (sat_nil p)))))))))))))))))))))))))))
def c2353 : List Lit := [(110, true), (33, true), (115, true), (101, false), (1604, false), (121, false), (125, false), (126, false), (1789, true), (1818, false), (122, false), (117, false)]
theorem step2353 (p : Nat → Bool) (h : Constraints p) : clause p c2353 = true :=
  Snake9.LocalRup.prove_clause [c1195, c1200, c840, c1546, c2103, c761, c758, c752, c1504, c1417, c1877, c1512, c1538, c2349, c1526, c1527, c1537, c1542, c1521, c1624, c1513, c1508, c2347, c504, c1433, c1436, c2185, c2352, c1235, c1231, c1201, c1196, c1989, c159, c158, c1210, c1206, c1215] c2353 (by decide) p (sat_cons (step1195 p h) (sat_cons (step1200 p h) (sat_cons (step840 p h) (sat_cons (step1546 p h) (sat_cons (step2103 p h) (sat_cons (step761 p h) (sat_cons (step758 p h) (sat_cons (step752 p h) (sat_cons (step1504 p h) (sat_cons (step1417 p h) (sat_cons (step1877 p h) (sat_cons (step1512 p h) (sat_cons (step1538 p h) (sat_cons (step2349 p h) (sat_cons (step1526 p h) (sat_cons (step1527 p h) (sat_cons (step1537 p h) (sat_cons (step1542 p h) (sat_cons (step1521 p h) (sat_cons (step1624 p h) (sat_cons (step1513 p h) (sat_cons (step1508 p h) (sat_cons (step2347 p h) (sat_cons (step504 p h) (sat_cons (step1433 p h) (sat_cons (step1436 p h) (sat_cons (step2185 p h) (sat_cons (step2352 p h) (sat_cons (step1235 p h) (sat_cons (step1231 p h) (sat_cons (step1201 p h) (sat_cons (step1196 p h) (sat_cons (step1989 p h) (sat_cons (step159 p h) (sat_cons (step158 p h) (sat_cons (step1210 p h) (sat_cons (step1206 p h) (sat_cons (step1215 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c2354 : List Lit := [(119, true), (128, true), (1805, true), (114, true)]
theorem step2354 (p : Nat → Bool) (h : Constraints p) : clause p c2354 = true :=
  Snake9.LocalRup.prove_clause [c1572, c1571, c2111, c2110, c1778] c2354 (by decide) p (sat_cons (step1572 p h) (sat_cons (step1571 p h) (sat_cons (step2111 p h) (sat_cons (step2110 p h) (sat_cons (step1778 p h) (sat_nil p))))))
end B112E034
