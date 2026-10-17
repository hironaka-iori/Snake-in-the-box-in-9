import B112E004Part0007
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2246 : List Lit := [(42, true), (1509, false), (1549, true), (45, false), (55, true), (52, false), (1532, false), (40, false), (38, false), (51, false)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c2149, c1247, c1272, c1314, c2245, c179, c272, c275, c2244, c1212, c1201, c1214, c1203, c1232] c2246 (by decide) p (sat_cons (step2149 p h) (sat_cons (step1247 p h) (sat_cons (step1272 p h) (sat_cons (step1314 p h) (sat_cons (step2245 p h) (sat_cons (step179 p h) (sat_cons (step272 p h) (sat_cons (step275 p h) (sat_cons (step2244 p h) (sat_cons (step1212 p h) (sat_cons (step1201 p h) (sat_cons (step1214 p h) (sat_cons (step1203 p h) (sat_cons (step1232 p h) (sat_nil p)))))))))))))))
def c2247 : List Lit := [(1509, false), (49, true), (1549, true), (45, false), (55, true), (52, false), (56, true), (40, false), (38, false), (51, false)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c2149, c1247, c1253, c1261, c2246, c212, c246, c1947, c1945, c395, c2210, c1255, c1203, c1264, c1231, c1273, c1308] c2247 (by decide) p (sat_cons (step2149 p h) (sat_cons (step1247 p h) (sat_cons (step1253 p h) (sat_cons (step1261 p h) (sat_cons (step2246 p h) (sat_cons (step212 p h) (sat_cons (step246 p h) (sat_cons (step1947 p h) (sat_cons (step1945 p h) (sat_cons (step395 p h) (sat_cons (step2210 p h) (sat_cons (step1255 p h) (sat_cons (step1203 p h) (sat_cons (step1264 p h) (sat_cons (step1231 p h) (sat_cons (step1273 p h) (sat_cons (step1308 p h) (sat_nil p))))))))))))))))))
def c2248 : List Lit := [(1507, true), (1549, true), (45, false), (55, true), (52, false), (56, true), (40, false), (38, false), (51, false)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1211, c275, c1790, c270, c212, c246, c1241, c1828, c1947, c1250, c1301, c395, c1278, c1255, c1264] c2248 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1211 p h) (sat_cons (step275 p h) (sat_cons (step1790 p h) (sat_cons (step270 p h) (sat_cons (step212 p h) (sat_cons (step246 p h) (sat_cons (step1241 p h) (sat_cons (step1828 p h) (sat_cons (step1947 p h) (sat_cons (step1250 p h) (sat_cons (step1301 p h) (sat_cons (step395 p h) (sat_cons (step1278 p h) (sat_cons (step1255 p h) (sat_cons (step1264 p h) (sat_nil p)))))))))))))))))
def c2249 : List Lit := [(1549, true), (45, false), (55, true), (52, false), (56, true), (40, false), (38, false), (51, false)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c1253, c1261, c2248, c1213, c2147, c2246, c2247, c1301, c212, c246, c1947, c395, c1255, c1788, c1264, c1308, c1278, c1231, c1250, c1203, c2210, c2244, c1201, c273, c272, c1241] c2249 (by decide) p (sat_cons (step1253 p h) (sat_cons (step1261 p h) (sat_cons (step2248 p h) (sat_cons (step1213 p h) (sat_cons (step2147 p h) (sat_cons (step2246 p h) (sat_cons (step2247 p h) (sat_cons (step1301 p h) (sat_cons (step212 p h) (sat_cons (step246 p h) (sat_cons (step1947 p h) (sat_cons (step395 p h) (sat_cons (step1255 p h) (sat_cons (step1788 p h) (sat_cons (step1264 p h) (sat_cons (step1308 p h) (sat_cons (step1278 p h) (sat_cons (step1231 p h) (sat_cons (step1250 p h) (sat_cons (step1203 p h) (sat_cons (step2210 p h) (sat_cons (step2244 p h) (sat_cons (step1201 p h) (sat_cons (step273 p h) (sat_cons (step272 p h) (sat_cons (step1241 p h) (sat_nil p)))))))))))))))))))))))))))
def c2250 : List Lit := [(1501, true), (36, true), (40, false), (38, false), (51, false)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c2210, c1201, c2244] c2250 (by decide) p (sat_cons (step2210 p h) (sat_cons (step1201 p h) (sat_cons (step2244 p h) (sat_nil p))))
def c2251 : List Lit := [(1658, true), (1642, false), (97, true), (39, true), (1647, false), (100, false), (52, false)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1540, c1833, c1507, c1515, c1497, c660] c2251 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1540 p h) (sat_cons (step1833 p h) (sat_cons (step1507 p h) (sat_cons (step1515 p h) (sat_cons (step1497 p h) (sat_cons (step660 p h) (sat_nil p))))))))
def c2252 : List Lit := [(1595, true), (39, true), (1530, true), (1582, false), (51, false)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c1257, c2146, c1393, c1789, c1377, c1405, c1408, c1394, c1383, c1389, c1976, c523] c2252 (by decide) p (sat_cons (step1257 p h) (sat_cons (step2146 p h) (sat_cons (step1393 p h) (sat_cons (step1789 p h) (sat_cons (step1377 p h) (sat_cons (step1405 p h) (sat_cons (step1408 p h) (sat_cons (step1394 p h) (sat_cons (step1383 p h) (sat_cons (step1389 p h) (sat_cons (step1976 p h) (sat_cons (step523 p h) (sat_nil p)))))))))))))
def c2253 : List Lit := [(97, true), (98, true), (100, false), (52, false), (1658, true), (39, true)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c1502, c1849, c2251, c1515, c1512, c665] c2253 (by decide) p (sat_cons (step1502 p h) (sat_cons (step1849 p h) (sat_cons (step2251 p h) (sat_cons (step1515 p h) (sat_cons (step1512 p h) (sat_cons (step665 p h) (sat_nil p)))))))
def c2254 : List Lit := [(103, false), (1642, false), (100, false), (52, false), (1658, true)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c660, c665, c1497, c1512, c1507, c1519, c1540] c2254 (by decide) p (sat_cons (step660 p h) (sat_cons (step665 p h) (sat_cons (step1497 p h) (sat_cons (step1512 p h) (sat_cons (step1507 p h) (sat_cons (step1519 p h) (sat_cons (step1540 p h) (sat_nil p))))))))
def c2255 : List Lit := [(1642, false), (100, false), (52, false), (1658, true)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c1504, c1536, c2254, c1515, c1517, c1520, c1540, c1512, c1507, c659, c1497] c2255 (by decide) p (sat_cons (step1504 p h) (sat_cons (step1536 p h) (sat_cons (step2254 p h) (sat_cons (step1515 p h) (sat_cons (step1517 p h) (sat_cons (step1520 p h) (sat_cons (step1540 p h) (sat_cons (step1512 p h) (sat_cons (step1507 p h) (sat_cons (step659 p h) (sat_cons (step1497 p h) (sat_nil p))))))))))))
def c2256 : List Lit := [(1643, true), (1647, true), (44, false), (53, false)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c1512, c1511, c1503, c1505, c1500, c1497, c1498, c352, c668, c656, c2022, c597] c2256 (by decide) p (sat_cons (step1512 p h) (sat_cons (step1511 p h) (sat_cons (step1503 p h) (sat_cons (step1505 p h) (sat_cons (step1500 p h) (sat_cons (step1497 p h) (sat_cons (step1498 p h) (sat_cons (step352 p h) (sat_cons (step668 p h) (sat_cons (step656 p h) (sat_cons (step2022 p h) (sat_cons (step597 p h) (sat_nil p)))))))))))))
def c2257 : List Lit := [(73, false), (1525, true), (55, false), (53, false)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c437, c431, c1242, c1239, c1248] c2257 (by decide) p (sat_cons (step437 p h) (sat_cons (step431 p h) (sat_cons (step1242 p h) (sat_cons (step1239 p h) (sat_cons (step1248 p h) (sat_nil p))))))
def c2258 : List Lit := [(1524, true), (55, false), (53, false)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1247, c1242, c1239, c426] c2258 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1247 p h) (sat_cons (step1242 p h) (sat_cons (step1239 p h) (sat_cons (step426 p h) (sat_nil p))))))
def c2259 : List Lit := [(1618, false), (1630, true), (1488, false), (1692, false), (51, false), (1537, false), (73, true), (1580, false), (1585, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c1380, c1388, c1394, c1405, c1480, c1487, c1652, c1409, c1406, c2132, c1383, c1395, c1345, c1390, c1307, c523, c1872, c1976, c1211, c215, c209, c1207, c1200, c1216, c1202, c1227] c2259 (by decide) p (sat_cons (step1380 p h) (sat_cons (step1388 p h) (sat_cons (step1394 p h) (sat_cons (step1405 p h) (sat_cons (step1480 p h) (sat_cons (step1487 p h) (sat_cons (step1652 p h) (sat_cons (step1409 p h) (sat_cons (step1406 p h) (sat_cons (step2132 p h) (sat_cons (step1383 p h) (sat_cons (step1395 p h) (sat_cons (step1345 p h) (sat_cons (step1390 p h) (sat_cons (step1307 p h) (sat_cons (step523 p h) (sat_cons (step1872 p h) (sat_cons (step1976 p h) (sat_cons (step1211 p h) (sat_cons (step215 p h) (sat_cons (step209 p h) (sat_cons (step1207 p h) (sat_cons (step1200 p h) (sat_cons (step1216 p h) (sat_cons (step1202 p h) (sat_cons (step1227 p h) (sat_nil p)))))))))))))))))))))))))))
def c2260 : List Lit := [(39, false), (1515, true), (61, false), (1507, false), (51, false)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c215, c209, c1207, c1200, c1216, c1202, c1227] c2260 (by decide) p (sat_cons (step215 p h) (sat_cons (step209 p h) (sat_cons (step1207 p h) (sat_cons (step1200 p h) (sat_cons (step1216 p h) (sat_cons (step1202 p h) (sat_cons (step1227 p h) (sat_nil p))))))))
def c2261 : List Lit := [(1505, true), (1569, true), (1549, true), (51, false), (56, false), (55, false)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1208, c2231] c2261 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1208 p h) (sat_cons (step2231 p h) (sat_nil p))))
def c2262 : List Lit := [(1500, true), (39, true)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1200, c1936, c1935, c1690] c2262 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1200 p h) (sat_cons (step1936 p h) (sat_cons (step1935 p h) (sat_cons (step1690 p h) (sat_nil p))))))
def c2263 : List Lit := [(35, false), (46, false), (1506, true), (39, true)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c1935, c175, c174, c1209] c2263 (by decide) p (sat_cons (step1935 p h) (sat_cons (step175 p h) (sat_cons (step174 p h) (sat_cons (step1209 p h) (sat_nil p)))))
def c2264 : List Lit := [(1692, false), (1596, false), (1549, false), (1612, false)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c1439, c1485, c2113, c2132, c1652, c1646, c1486, c2133, c1444, c1346, c1420, c2089, c1774] c2264 (by decide) p (sat_cons (step1439 p h) (sat_cons (step1485 p h) (sat_cons (step2113 p h) (sat_cons (step2132 p h) (sat_cons (step1652 p h) (sat_cons (step1646 p h) (sat_cons (step1486 p h) (sat_cons (step2133 p h) (sat_cons (step1444 p h) (sat_cons (step1346 p h) (sat_cons (step1420 p h) (sat_cons (step2089 p h) (sat_cons (step1774 p h) (sat_nil p))))))))))))))
def c2265 : List Lit := [(1488, true), (15, true), (51, false), (39, true)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c1109, c1112, c2089, c2094, c1799, c1121, c1125, c1136, c1113, c1115, c1101, c1111, c1107, c1098, c10, c48, c1908] c2265 (by decide) p (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step2089 p h) (sat_cons (step2094 p h) (sat_cons (step1799 p h) (sat_cons (step1121 p h) (sat_cons (step1125 p h) (sat_cons (step1136 p h) (sat_cons (step1113 p h) (sat_cons (step1115 p h) (sat_cons (step1101 p h) (sat_cons (step1111 p h) (sat_cons (step1107 p h) (sat_cons (step1098 p h) (sat_cons (step10 p h) (sat_cons (step48 p h) (sat_cons (step1908 p h) (sat_nil p))))))))))))))))))
def c2266 : List Lit := [(1656, true), (1649, false), (53, false), (44, false)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c1517, c1526, c1530, c1520, c2256] c2266 (by decide) p (sat_cons (step1517 p h) (sat_cons (step1526 p h) (sat_cons (step1530 p h) (sat_cons (step1520 p h) (sat_cons (step2256 p h) (sat_nil p))))))
def c2267 : List Lit := [(1455, true), (15, true), (51, false), (39, true)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c1109, c1112, c1121, c1125, c1113, c1115, c1101, c1111, c1107, c1098, c7, c48, c1908] c2267 (by decide) p (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step1121 p h) (sat_cons (step1125 p h) (sat_cons (step1113 p h) (sat_cons (step1115 p h) (sat_cons (step1101 p h) (sat_cons (step1111 p h) (sat_cons (step1107 p h) (sat_cons (step1098 p h) (sat_cons (step7 p h) (sat_cons (step48 p h) (sat_cons (step1908 p h) (sat_nil p))))))))))))))
def c2268 : List Lit := [(1595, false), (1628, true), (1712, true), (1657, false), (38, false)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c1773, c1439, c1478, c1479, c1640, c1440, c1444, c1605, c1432, c1420, c2166, c1824, c1550] c2268 (by decide) p (sat_cons (step1773 p h) (sat_cons (step1439 p h) (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step1640 p h) (sat_cons (step1440 p h) (sat_cons (step1444 p h) (sat_cons (step1605 p h) (sat_cons (step1432 p h) (sat_cons (step1420 p h) (sat_cons (step2166 p h) (sat_cons (step1824 p h) (sat_cons (step1550 p h) (sat_nil p))))))))))))))
def c2269 : List Lit := [(1595, true), (72, false), (1590, false), (73, true), (51, false)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c1401, c1405, c1382, c522, c523, c1386, c1390, c1395] c2269 (by decide) p (sat_cons (step1401 p h) (sat_cons (step1405 p h) (sat_cons (step1382 p h) (sat_cons (step522 p h) (sat_cons (step523 p h) (sat_cons (step1386 p h) (sat_cons (step1390 p h) (sat_cons (step1395 p h) (sat_nil p)))))))))
def c2270 : List Lit := [(1617, true), (1610, false), (97, false), (101, false), (38, false), (56, false), (55, false)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c317, c1773, c1440, c1444, c1432, c1434, c1422, c2168, c1426, c1416, c1942, c1838, c450] c2270 (by decide) p (sat_cons (step317 p h) (sat_cons (step1773 p h) (sat_cons (step1440 p h) (sat_cons (step1444 p h) (sat_cons (step1432 p h) (sat_cons (step1434 p h) (sat_cons (step1422 p h) (sat_cons (step2168 p h) (sat_cons (step1426 p h) (sat_cons (step1416 p h) (sat_cons (step1942 p h) (sat_cons (step1838 p h) (sat_cons (step450 p h) (sat_nil p))))))))))))))
def c2271 : List Lit := [(1550, false), (1691, false), (1657, false), (1569, true), (1595, false), (38, false)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c1773, c2114, c1881, c1347, c2133, c1605, c2089, c1651, c2152, c1480] c2271 (by decide) p (sat_cons (step1773 p h) (sat_cons (step2114 p h) (sat_cons (step1881 p h) (sat_cons (step1347 p h) (sat_cons (step2133 p h) (sat_cons (step1605 p h) (sat_cons (step2089 p h) (sat_cons (step1651 p h) (sat_cons (step2152 p h) (sat_cons (step1480 p h) (sat_nil p)))))))))))
def c2272 : List Lit := [(53, false), (51, true), (1527, true), (46, true), (56, false), (55, false)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c436, c430, c1244, c1241, c1252] c2272 (by decide) p (sat_cons (step436 p h) (sat_cons (step430 p h) (sat_cons (step1244 p h) (sat_cons (step1241 p h) (sat_cons (step1252 p h) (sat_nil p))))))
def c2273 : List Lit := [(51, true), (1539, true), (46, true), (56, false), (55, false)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c1286, c1240, c1243, c2272, c1254, c1261, c1282, c1251, c1249, c1241, c1244, c427] c2273 (by decide) p (sat_cons (step1286 p h) (sat_cons (step1240 p h) (sat_cons (step1243 p h) (sat_cons (step2272 p h) (sat_cons (step1254 p h) (sat_cons (step1261 p h) (sat_cons (step1282 p h) (sat_cons (step1251 p h) (sat_cons (step1249 p h) (sat_cons (step1241 p h) (sat_cons (step1244 p h) (sat_cons (step427 p h) (sat_nil p)))))))))))))
def c2274 : List Lit := [(1596, true), (1530, true), (73, true), (51, false), (39, true)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c1789, c1377, c1380, c1388, c1257, c2146, c1394, c1409, c1406, c1383, c1395, c1976, c523, c1390] c2274 (by decide) p (sat_cons (step1789 p h) (sat_cons (step1377 p h) (sat_cons (step1380 p h) (sat_cons (step1388 p h) (sat_cons (step1257 p h) (sat_cons (step2146 p h) (sat_cons (step1394 p h) (sat_cons (step1409 p h) (sat_cons (step1406 p h) (sat_cons (step1383 p h) (sat_cons (step1395 p h) (sat_cons (step1976 p h) (sat_cons (step523 p h) (sat_cons (step1390 p h) (sat_nil p)))))))))))))))
def c2275 : List Lit := [(1691, false), (1713, true), (1549, false), (1596, false), (1612, false), (1455, false)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c1439, c1485, c1651, c1486, c1645, c1444, c2134, c1420, c1355, c1774, c1189] c2275 (by decide) p (sat_cons (step1439 p h) (sat_cons (step1485 p h) (sat_cons (step1651 p h) (sat_cons (step1486 p h) (sat_cons (step1645 p h) (sat_cons (step1444 p h) (sat_cons (step2134 p h) (sat_cons (step1420 p h) (sat_cons (step1355 p h) (sat_cons (step1774 p h) (sat_cons (step1189 p h) (sat_nil p))))))))))))
def c2276 : List Lit := [(1656, true), (50, true), (1649, false), (51, false)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c1517, c1526, c1530, c1520, c1503, c1505, c1511, c1512, c1500, c1497, c1498, c652, c668, c2022, c597] c2276 (by decide) p (sat_cons (step1517 p h) (sat_cons (step1526 p h) (sat_cons (step1530 p h) (sat_cons (step1520 p h) (sat_cons (step1503 p h) (sat_cons (step1505 p h) (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step1500 p h) (sat_cons (step1497 p h) (sat_cons (step1498 p h) (sat_cons (step652 p h) (sat_cons (step668 p h) (sat_cons (step2022 p h) (sat_cons (step597 p h) (sat_nil p))))))))))))))))
def c2277 : List Lit := [(1643, true), (99, true), (101, false), (50, true)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c1503, c1505, c1500, c1497, c1498, c668, c2022, c597] c2277 (by decide) p (sat_cons (step1503 p h) (sat_cons (step1505 p h) (sat_cons (step1500 p h) (sat_cons (step1497 p h) (sat_cons (step1498 p h) (sat_cons (step668 p h) (sat_cons (step2022 p h) (sat_cons (step597 p h) (sat_nil p)))))))))
def c2278 : List Lit := [(1643, false), (1647, false), (103, true), (1691, true)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c1515, c1520, c2126, c1531, c1532, c1604, c1521, c2120, c1516, c1554, c1821] c2278 (by decide) p (sat_cons (step1515 p h) (sat_cons (step1520 p h) (sat_cons (step2126 p h) (sat_cons (step1531 p h) (sat_cons (step1532 p h) (sat_cons (step1604 p h) (sat_cons (step1521 p h) (sat_cons (step2120 p h) (sat_cons (step1516 p h) (sat_cons (step1554 p h) (sat_cons (step1821 p h) (sat_nil p))))))))))))
def c2279 : List Lit := [(1643, true), (51, false), (39, true)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c1503, c1505, c1500, c1497, c1498, c647, c597, c2012] c2279 (by decide) p (sat_cons (step1503 p h) (sat_cons (step1505 p h) (sat_cons (step1500 p h) (sat_cons (step1497 p h) (sat_cons (step1498 p h) (sat_cons (step647 p h) (sat_cons (step597 p h) (sat_cons (step2012 p h) (sat_nil p)))))))))
def c2280 : List Lit := [(103, true), (56, false), (1691, true), (1643, false), (51, false)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c1515, c1517, c1530, c2278, c1599, c1511, c1512, c403, c652, c2030, c2192, c1821, c1516, c1518, c1531, c1604, c1575, c2120, c1892, c1552, c774, c1549] c2280 (by decide) p (sat_cons (step1515 p h) (sat_cons (step1517 p h) (sat_cons (step1530 p h) (sat_cons (step2278 p h) (sat_cons (step1599 p h) (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step403 p h) (sat_cons (step652 p h) (sat_cons (step2030 p h) (sat_cons (step2192 p h) (sat_cons (step1821 p h) (sat_cons (step1516 p h) (sat_cons (step1518 p h) (sat_cons (step1531 p h) (sat_cons (step1604 p h) (sat_cons (step1575 p h) (sat_cons (step2120 p h) (sat_cons (step1892 p h) (sat_cons (step1552 p h) (sat_cons (step774 p h) (sat_cons (step1549 p h) (sat_nil p)))))))))))))))))))))))
def c2281 : List Lit := [(1680, true), (120, false), (102, false)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c1575, c2120, c1892, c1552, c774, c1549] c2281 (by decide) p (sat_cons (step1575 p h) (sat_cons (step2120 p h) (sat_cons (step1892 p h) (sat_cons (step1552 p h) (sat_cons (step774 p h) (sat_cons (step1549 p h) (sat_nil p)))))))
def c2282 : List Lit := [(1681, true), (109, true), (1667, false), (120, false), (102, false)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c2121, c1578, c1553, c1892, c1551, c774] c2282 (by decide) p (sat_cons (step2121 p h) (sat_cons (step1578 p h) (sat_cons (step1553 p h) (sat_cons (step1892 p h) (sat_cons (step1551 p h) (sat_cons (step774 p h) (sat_nil p)))))))
def c2283 : List Lit := [(102, false), (1647, false), (99, true), (56, false), (1691, true), (1643, false), (51, false)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c1519, c1530, c1599, c403, c2030, c2281, c2192, c1604, c1821, c1531, c1514, c1520] c2283 (by decide) p (sat_cons (step1519 p h) (sat_cons (step1530 p h) (sat_cons (step1599 p h) (sat_cons (step403 p h) (sat_cons (step2030 p h) (sat_cons (step2281 p h) (sat_cons (step2192 p h) (sat_cons (step1604 p h) (sat_cons (step1821 p h) (sat_cons (step1531 p h) (sat_cons (step1514 p h) (sat_cons (step1520 p h) (sat_nil p)))))))))))))
def c2284 : List Lit := [(1647, true), (99, false), (51, false)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c1511, c1512, c652] c2284 (by decide) p (sat_cons (step1511 p h) (sat_cons (step1512 p h) (sat_cons (step652 p h) (sat_nil p))))
def c2285 : List Lit := [(1680, true), (102, false)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1575, c2120, c2281, c1892, c1552, c2055, c1549, c1550, c736] c2285 (by decide) p (sat_cons (step1575 p h) (sat_cons (step2120 p h) (sat_cons (step2281 p h) (sat_cons (step1892 p h) (sat_cons (step1552 p h) (sat_cons (step2055 p h) (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step736 p h) (sat_nil p))))))))))
def c2286 : List Lit := [(84, false), (110, true), (106, false), (1640, true), (109, false)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c709, c2042, c595, c593, c1499] c2286 (by decide) p (sat_cons (step709 p h) (sat_cons (step2042 p h) (sat_cons (step595 p h) (sat_cons (step593 p h) (sat_cons (step1499 p h) (sat_nil p))))))
def c2287 : List Lit := [(90, false), (101, false), (1644, true), (39, true), (51, false), (109, false)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c648, c2012, c598, c599, c1497, c1500, c1506] c2287 (by decide) p (sat_cons (step648 p h) (sat_cons (step2012 p h) (sat_cons (step598 p h) (sat_cons (step599 p h) (sat_cons (step1497 p h) (sat_cons (step1500 p h) (sat_cons (step1506 p h) (sat_nil p))))))))
def c2288 : List Lit := [(15, false), (1534, true), (1596, true), (39, true), (55, false), (103, false), (53, true), (51, false)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c424, c425, c1255, c2274, c1265] c2288 (by decide) p (sat_cons (step424 p h) (sat_cons (step425 p h) (sat_cons (step1255 p h) (sat_cons (step2274 p h) (sat_cons (step1265 p h) (sat_nil p))))))
def c2289 : List Lit := [(1690, true), (1663, false), (1643, false)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c1554, c2120, c1529, c1594, c1598, c2121, c1578, c1530, c1555, c1892, c1519, c1549, c1550, c736, c1511, c774, c2046] c2289 (by decide) p (sat_cons (step1554 p h) (sat_cons (step2120 p h) (sat_cons (step1529 p h) (sat_cons (step1594 p h) (sat_cons (step1598 p h) (sat_cons (step2121 p h) (sat_cons (step1578 p h) (sat_cons (step1530 p h) (sat_cons (step1555 p h) (sat_cons (step1892 p h) (sat_cons (step1519 p h) (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step736 p h) (sat_cons (step1511 p h) (sat_cons (step774 p h) (sat_cons (step2046 p h) (sat_nil p))))))))))))))))))
def c2290 : List Lit := [(1612, true), (108, false)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c1431, c1861, c1428, c1429, c588] c2290 (by decide) p (sat_cons (step1431 p h) (sat_cons (step1861 p h) (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step588 p h) (sat_nil p))))))
def c2291 : List Lit := [(1691, true), (109, true), (1663, false), (54, true), (99, true), (1643, false)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c1550, c1555, c2121, c1529, c1595, c1599, c2122, c1582, c1530, c1556, c1892, c1519, c1551, c1511, c2030, c774] c2291 (by decide) p (sat_cons (step1550 p h) (sat_cons (step1555 p h) (sat_cons (step2121 p h) (sat_cons (step1529 p h) (sat_cons (step1595 p h) (sat_cons (step1599 p h) (sat_cons (step2122 p h) (sat_cons (step1582 p h) (sat_cons (step1530 p h) (sat_cons (step1556 p h) (sat_cons (step1892 p h) (sat_cons (step1519 p h) (sat_cons (step1551 p h) (sat_cons (step1511 p h) (sat_cons (step2030 p h) (sat_cons (step774 p h) (sat_nil p)))))))))))))))))
def c2292 : List Lit := [(1604, false), (1691, false), (40, true), (1539, false), (1595, false), (1488, false), (1507, false), (1502, false)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c1207, c1216, c1227, c1309, c1347, c2134, c1645, c1479, c1443, c1478, c1639, c2135, c1444, c1348, c1773, c1316, c1209, c1228, c1219] c2292 (by decide) p (sat_cons (step1207 p h) (sat_cons (step1216 p h) (sat_cons (step1227 p h) (sat_cons (step1309 p h) (sat_cons (step1347 p h) (sat_cons (step2134 p h) (sat_cons (step1645 p h) (sat_cons (step1479 p h) (sat_cons (step1443 p h) (sat_cons (step1478 p h) (sat_cons (step1639 p h) (sat_cons (step2135 p h) (sat_cons (step1444 p h) (sat_cons (step1348 p h) (sat_cons (step1773 p h) (sat_cons (step1316 p h) (sat_cons (step1209 p h) (sat_cons (step1228 p h) (sat_cons (step1219 p h) (sat_nil p))))))))))))))))))))
def c2293 : List Lit := [(40, true), (1539, false), (1489, false), (1691, false), (1595, false), (1507, false), (1502, false)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c1477, c1633, c2136, c1357, c1316, c1228, c1219, c1207, c1209, c1216, c1773, c1227, c1439, c1309, c1478, c1356, c1639, c2135] c2293 (by decide) p (sat_cons (step1477 p h) (sat_cons (step1633 p h) (sat_cons (step2136 p h) (sat_cons (step1357 p h) (sat_cons (step1316 p h) (sat_cons (step1228 p h) (sat_cons (step1219 p h) (sat_cons (step1207 p h) (sat_cons (step1209 p h) (sat_cons (step1216 p h) (sat_cons (step1773 p h) (sat_cons (step1227 p h) (sat_cons (step1439 p h) (sat_cons (step1309 p h) (sat_cons (step1478 p h) (sat_cons (step1356 p h) (sat_cons (step1639 p h) (sat_cons (step2135 p h) (sat_nil p)))))))))))))))))))
def c2294 : List Lit := [(1539, true), (1530, false), (1522, false), (53, true), (55, false), (103, false)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c1254, c1262, c1245, c1274, c1278, c1265, c1248, c1255, c1239, c434] c2294 (by decide) p (sat_cons (step1254 p h) (sat_cons (step1262 p h) (sat_cons (step1245 p h) (sat_cons (step1274 p h) (sat_cons (step1278 p h) (sat_cons (step1265 p h) (sat_cons (step1248 p h) (sat_cons (step1255 p h) (sat_cons (step1239 p h) (sat_cons (step434 p h) (sat_nil p)))))))))))
def c2295 : List Lit := [(1550, true), (1539, false), (1530, false), (1522, false), (44, true), (53, true), (1502, false), (51, false)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c1210, c2147, c1213, c1302, c1309, c1231, c1227, c1203, c1214, c2193, c1216, c1212, c1255, c1207, c1208, c1265, c246, c2210, c1279, c1945, c1248, c1239, c1240, c309] c2295 (by decide) p (sat_cons (step1210 p h) (sat_cons (step2147 p h) (sat_cons (step1213 p h) (sat_cons (step1302 p h) (sat_cons (step1309 p h) (sat_cons (step1231 p h) (sat_cons (step1227 p h) (sat_cons (step1203 p h) (sat_cons (step1214 p h) (sat_cons (step2193 p h) (sat_cons (step1216 p h) (sat_cons (step1212 p h) (sat_cons (step1255 p h) (sat_cons (step1207 p h) (sat_cons (step1208 p h) (sat_cons (step1265 p h) (sat_cons (step246 p h) (sat_cons (step2210 p h) (sat_cons (step1279 p h) (sat_cons (step1945 p h) (sat_cons (step1248 p h) (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step309 p h) (sat_nil p)))))))))))))))))))))))))
def c2296 : List Lit := [(1515, true), (36, true), (46, false), (1507, false), (39, true)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c1213, c1223, c1231, c1219, c1203, c2263, c1201] c2296 (by decide) p (sat_cons (step1213 p h) (sat_cons (step1223 p h) (sat_cons (step1231 p h) (sat_cons (step1219 p h) (sat_cons (step1203 p h) (sat_cons (step2263 p h) (sat_cons (step1201 p h) (sat_nil p))))))))
def c2297 : List Lit := [(35, false), (40, false), (46, false), (39, true)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c1935, c175] c2297 (by decide) p (sat_cons (step1935 p h) (sat_cons (step175 p h) (sat_nil p)))
def c2298 : List Lit := [(1690, true), (1680, false), (1643, false)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c1598, c2289, c1530, c1821, c1517, c1514] c2298 (by decide) p (sat_cons (step1598 p h) (sat_cons (step2289 p h) (sat_cons (step1530 p h) (sat_cons (step1821 p h) (sat_cons (step1517 p h) (sat_cons (step1514 p h) (sat_nil p)))))))
def c2299 : List Lit := [(1691, false), (40, true), (1595, false), (1539, false), (1488, false), (1455, false), (1507, false), (1502, false)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c2292, c2293, c1420, c1189, c1774] c2299 (by decide) p (sat_cons (step2292 p h) (sat_cons (step2293 p h) (sat_cons (step1420 p h) (sat_cons (step1189 p h) (sat_cons (step1774 p h) (sat_nil p))))))
def c2300 : List Lit := [(1595, false), (1681, false), (1649, false), (1627, true), (1711, true)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c1477, c1478, c1634, c1439, c1605, c1868, c1844] c2300 (by decide) p (sat_cons (step1477 p h) (sat_cons (step1478 p h) (sat_cons (step1634 p h) (sat_cons (step1439 p h) (sat_cons (step1605 p h) (sat_cons (step1868 p h) (sat_cons (step1844 p h) (sat_nil p))))))))
def c2301 : List Lit := [(1505, false), (1552, true), (1534, false), (1529, false), (48, true), (59, true), (73, false), (1590, true), (1583, true), (1522, false), (44, true), (39, true), (51, false)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c1210, c2262, c1202, c1239, c1248, c1279, c1317, c1228, c1219, c1216, c1217, c1227, c1232, c1212, c1311, c1203, c1885, c1280, c1284, c1383, c1266, c1251, c1377, c1378, c1258, c1241, c495, c2263, c1979, c1201, c463] c2301 (by decide) p (sat_cons (step1210 p h) (sat_cons (step2262 p h) (sat_cons (step1202 p h) (sat_cons (step1239 p h) (sat_cons (step1248 p h) (sat_cons (step1279 p h) (sat_cons (step1317 p h) (sat_cons (step1228 p h) (sat_cons (step1219 p h) (sat_cons (step1216 p h) (sat_cons (step1217 p h) (sat_cons (step1227 p h) (sat_cons (step1232 p h) (sat_cons (step1212 p h) (sat_cons (step1311 p h) (sat_cons (step1203 p h) (sat_cons (step1885 p h) (sat_cons (step1280 p h) (sat_cons (step1284 p h) (sat_cons (step1383 p h) (sat_cons (step1266 p h) (sat_cons (step1251 p h) (sat_cons (step1377 p h) (sat_cons (step1378 p h) (sat_cons (step1258 p h) (sat_cons (step1241 p h) (sat_cons (step495 p h) (sat_cons (step2263 p h) (sat_cons (step1979 p h) (sat_cons (step1201 p h) (sat_cons (step463 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2302 : List Lit := [(38, false), (1617, true), (1711, true), (1657, false), (1594, false)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c1440, c1432, c1773, c1439, c1444, c1471, c1420, c1634, c1824, c1605, c1550, c2166] c2302 (by decide) p (sat_cons (step1440 p h) (sat_cons (step1432 p h) (sat_cons (step1773 p h) (sat_cons (step1439 p h) (sat_cons (step1444 p h) (sat_cons (step1471 p h) (sat_cons (step1420 p h) (sat_cons (step1634 p h) (sat_cons (step1824 p h) (sat_cons (step1605 p h) (sat_cons (step1550 p h) (sat_cons (step2166 p h) (sat_nil p)))))))))))))
def c2303 : List Lit := [(1691, true), (1644, false), (1657, false)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c2126, c1604, c1536, c2120, c2285, c1554, c1511, c1821, c1520, c1514] c2303 (by decide) p (sat_cons (step2126 p h) (sat_cons (step1604 p h) (sat_cons (step1536 p h) (sat_cons (step2120 p h) (sat_cons (step2285 p h) (sat_cons (step1554 p h) (sat_cons (step1511 p h) (sat_cons (step1821 p h) (sat_cons (step1520 p h) (sat_cons (step1514 p h) (sat_nil p)))))))))))
def c2304 : List Lit := [(1511, true), (56, false), (38, true), (44, true), (51, false)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c1208, c1210, c1219, c1217, c1209, c1212, c212, c249, c396, c1947] c2304 (by decide) p (sat_cons (step1208 p h) (sat_cons (step1210 p h) (sat_cons (step1219 p h) (sat_cons (step1217 p h) (sat_cons (step1209 p h) (sat_cons (step1212 p h) (sat_cons (step212 p h) (sat_cons (step249 p h) (sat_cons (step396 p h) (sat_cons (step1947 p h) (sat_nil p)))))))))))
def c2305 : List Lit := [(1585, true), (73, false), (1452, true), (56, false), (13, true), (1529, true)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c1385, c1386, c530, c1995, c2188, c1111, c1116, c1106, c306, c1988, c1987, c1721] c2305 (by decide) p (sat_cons (step1385 p h) (sat_cons (step1386 p h) (sat_cons (step530 p h) (sat_cons (step1995 p h) (sat_cons (step2188 p h) (sat_cons (step1111 p h) (sat_cons (step1116 p h) (sat_cons (step1106 p h) (sat_cons (step306 p h) (sat_cons (step1988 p h) (sat_cons (step1987 p h) (sat_cons (step1721 p h) (sat_nil p)))))))))))))
def c2306 : List Lit := [(1691, true), (1618, true), (1657, false)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c1604, c2303, c1575, c2120, c1822, c1508, c1892, c1552, c1554, c1549, c1550, c1546, c1547, c1824, c736, c720, c1420, c2286, c2041, c1445, c1425, c1434, c1428, c1429, c588] c2306 (by decide) p (sat_cons (step1604 p h) (sat_cons (step2303 p h) (sat_cons (step1575 p h) (sat_cons (step2120 p h) (sat_cons (step1822 p h) (sat_cons (step1508 p h) (sat_cons (step1892 p h) (sat_cons (step1552 p h) (sat_cons (step1554 p h) (sat_cons (step1549 p h) (sat_cons (step1550 p h) (sat_cons (step1546 p h) (sat_cons (step1547 p h) (sat_cons (step1824 p h) (sat_cons (step736 p h) (sat_cons (step720 p h) (sat_cons (step1420 p h) (sat_cons (step2286 p h) (sat_cons (step2041 p h) (sat_cons (step1445 p h) (sat_cons (step1425 p h) (sat_cons (step1434 p h) (sat_cons (step1428 p h) (sat_cons (step1429 p h) (sat_cons (step588 p h) (sat_nil p))))))))))))))))))))))))))
def c2307 : List Lit := [(1479, true), (1711, true), (1594, false), (1657, false)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c2125, c1644, c1473, c2306, c1639, c1472, c1448, c1421, c1774, c1799, c1420, c1136, c1443, c1444, c1827, c1471, c2290, c1550, c1634, c1546, c1605, c1555, c2121] c2307 (by decide) p (sat_cons (step2125 p h) (sat_cons (step1644 p h) (sat_cons (step1473 p h) (sat_cons (step2306 p h) (sat_cons (step1639 p h) (sat_cons (step1472 p h) (sat_cons (step1448 p h) (sat_cons (step1421 p h) (sat_cons (step1774 p h) (sat_cons (step1799 p h) (sat_cons (step1420 p h) (sat_cons (step1136 p h) (sat_cons (step1443 p h) (sat_cons (step1444 p h) (sat_cons (step1827 p h) (sat_cons (step1471 p h) (sat_cons (step2290 p h) (sat_cons (step1550 p h) (sat_cons (step1634 p h) (sat_cons (step1546 p h) (sat_cons (step1605 p h) (sat_cons (step1555 p h) (sat_cons (step2121 p h) (sat_nil p))))))))))))))))))))))))
def c2308 : List Lit := [(1616, true), (1668, true)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c1439, c1443, c2290, c1420, c1546, c1824, c1555, c1550] c2308 (by decide) p (sat_cons (step1439 p h) (sat_cons (step1443 p h) (sat_cons (step2290 p h) (sat_cons (step1420 p h) (sat_cons (step1546 p h) (sat_cons (step1824 p h) (sat_cons (step1555 p h) (sat_cons (step1550 p h) (sat_nil p)))))))))
def c2309 : List Lit := [(52, false), (1520, true), (56, false)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1240, c319, c427, c2149, c1954] c2309 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step319 p h) (sat_cons (step427 p h) (sat_cons (step2149 p h) (sat_cons (step1954 p h) (sat_nil p)))))))
end B112E004
