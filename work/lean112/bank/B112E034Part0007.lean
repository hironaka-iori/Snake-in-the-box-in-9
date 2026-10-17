import B112E034Part0006
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2227 : List Lit := [(104, false), (1774, true), (101, false), (29, false), (103, false), (102, false)]
theorem step2227 (p : Nat → Bool) (h : Constraints p) : clause p c2227 = true :=
  Snake9.LocalRup.prove_clause [c510, c500, c1509] c2227 (by decide) p (sat_cons (step510 p h) (sat_cons (step500 p h) (sat_cons (step1509 p h) (sat_nil p))))
def c2228 : List Lit := [(1776, false), (1779, false), (1790, true), (113, true), (1832, true), (1811, false), (1713, true)]
theorem step2228 (p : Nat → Bool) (h : Constraints p) : clause p c2228 = true :=
  Snake9.LocalRup.prove_clause [c1543, c2225] c2228 (by decide) p (sat_cons (step1543 p h) (sat_cons (step2225 p h) (sat_nil p)))
def c2229 : List Lit := [(107, false), (113, false), (1713, true)]
theorem step2229 (p : Nat → Bool) (h : Constraints p) : clause p c2229 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1388, c1389, c1393, c1386, c334, c296, c691, c2042] c2229 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1393 p h) (sat_cons (step1386 p h) (sat_cons (step334 p h) (sat_cons (step296 p h) (sat_cons (step691 p h) (sat_cons (step2042 p h) (sat_nil p))))))))))
def c2230 : List Lit := [(1812, true), (112, false), (1806, false), (72, false), (128, true)]
theorem step2230 (p : Nat → Bool) (h : Constraints p) : clause p c2230 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1581, c1584, c1578, c1568, c1945, c607, c2102] c2230 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1581 p h) (sat_cons (step1584 p h) (sat_cons (step1578 p h) (sat_cons (step1568 p h) (sat_cons (step1945 p h) (sat_cons (step607 p h) (sat_cons (step2102 p h) (sat_nil p)))))))))
def c2231 : List Lit := [(123, true), (1803, true), (1731, true), (1713, true), (128, true)]
theorem step2231 (p : Nat → Bool) (h : Constraints p) : clause p c2231 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1568, c1391, c1389, c1388, c1393, c1386, c334, c2041, c1385, c2194, c2102, c2101, c313, c756, c1852, c1419, c1429] c2231 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1568 p h) (sat_cons (step1391 p h) (sat_cons (step1389 p h) (sat_cons (step1388 p h) (sat_cons (step1393 p h) (sat_cons (step1386 p h) (sat_cons (step334 p h) (sat_cons (step2041 p h) (sat_cons (step1385 p h) (sat_cons (step2194 p h) (sat_cons (step2102 p h) (sat_cons (step2101 p h) (sat_cons (step313 p h) (sat_cons (step756 p h) (sat_cons (step1852 p h) (sat_cons (step1419 p h) (sat_cons (step1429 p h) (sat_nil p)))))))))))))))))))
def c2232 : List Lit := [(1616, true), (126, false), (74, false)]
theorem step2232 (p : Nat → Bool) (h : Constraints p) : clause p c2232 = true :=
  Snake9.LocalRup.prove_clause [c1213, c1869, c1205, c676] c2232 (by decide) p (sat_cons (step1213 p h) (sat_cons (step1869 p h) (sat_cons (step1205 p h) (sat_cons (step676 p h) (sat_nil p)))))
def c2233 : List Lit := [(1789, true), (1776, false), (101, false), (29, false), (86, false), (1771, false)]
theorem step2233 (p : Nat → Bool) (h : Constraints p) : clause p c2233 = true :=
  Snake9.LocalRup.prove_clause [c1546, c1542, c1514, c1526, c2226] c2233 (by decide) p (sat_cons (step1546 p h) (sat_cons (step1542 p h) (sat_cons (step1514 p h) (sat_cons (step1526 p h) (sat_cons (step2226 p h) (sat_nil p))))))
def c2234 : List Lit := [(1800, true), (107, false), (93, false), (113, true)]
theorem step2234 (p : Nat → Bool) (h : Constraints p) : clause p c2234 = true :=
  Snake9.LocalRup.prove_clause [c1554, c1565, c1563, c1556, c1557, c619, c698, c2100] c2234 (by decide) p (sat_cons (step1554 p h) (sat_cons (step1565 p h) (sat_cons (step1563 p h) (sat_cons (step1556 p h) (sat_cons (step1557 p h) (sat_cons (step619 p h) (sat_cons (step698 p h) (sat_cons (step2100 p h) (sat_nil p)))))))))
def c2235 : List Lit := [(122, true), (1813, true), (120, true), (119, false), (97, false), (126, true), (1805, false)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1585, c1577, c1578, c1588, c1573, c1570, c761] c2235 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1585 p h) (sat_cons (step1577 p h) (sat_cons (step1578 p h) (sat_cons (step1588 p h) (sat_cons (step1573 p h) (sat_cons (step1570 p h) (sat_cons (step761 p h) (sat_nil p)))))))))
def c2236 : List Lit := [(118, false), (122, false), (107, false), (93, false)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c698, c2100, c621] c2236 (by decide) p (sat_cons (step698 p h) (sat_cons (step2100 p h) (sat_cons (step621 p h) (sat_nil p))))
def c2237 : List Lit := [(1812, true), (120, true), (119, false), (97, false), (126, true), (1807, false)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c1569, c1587, c1584, c1570, c1575, c761, c1573] c2237 (by decide) p (sat_cons (step1569 p h) (sat_cons (step1587 p h) (sat_cons (step1584 p h) (sat_cons (step1570 p h) (sat_cons (step1575 p h) (sat_cons (step761 p h) (sat_cons (step1573 p h) (sat_nil p))))))))
def c2238 : List Lit := [(74, true), (125, false), (1714, true), (117, false)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c1392, c2184, c1390, c666] c2238 (by decide) p (sat_cons (step1392 p h) (sat_cons (step2184 p h) (sat_cons (step1390 p h) (sat_cons (step666 p h) (sat_nil p)))))
def c2239 : List Lit := [(1806, false), (1812, true), (97, false), (117, false)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c1581, c1575, c1578, c1584, c1945, c1568, c1569, c2187, c759] c2239 (by decide) p (sat_cons (step1581 p h) (sat_cons (step1575 p h) (sat_cons (step1578 p h) (sat_cons (step1584 p h) (sat_cons (step1945 p h) (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step2187 p h) (sat_cons (step759 p h) (sat_nil p))))))))))
def c2240 : List Lit := [(89, false), (1812, true), (97, false), (126, true), (1807, false), (1774, true), (86, false)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c401, c1913, c1509, c472, c2075, c2074, c489, c2237] c2240 (by decide) p (sat_cons (step401 p h) (sat_cons (step1913 p h) (sat_cons (step1509 p h) (sat_cons (step472 p h) (sat_cons (step2075 p h) (sat_cons (step2074 p h) (sat_cons (step489 p h) (sat_cons (step2237 p h) (sat_nil p)))))))))
def c2241 : List Lit := [(96, false), (97, false), (1774, true), (86, false)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c472, c471, c1509] c2241 (by decide) p (sat_cons (step472 p h) (sat_cons (step471 p h) (sat_cons (step1509 p h) (sat_nil p))))
def c2242 : List Lit := [(121, false), (119, true), (128, true), (109, false), (117, false)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c611, c2103] c2242 (by decide) p (sat_cons (step611 p h) (sat_cons (step2103 p h) (sat_nil p)))
def c2243 : List Lit := [(74, false), (115, false), (1800, true), (107, false)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c692, c691, c1557, c1554, c1563] c2243 (by decide) p (sat_cons (step692 p h) (sat_cons (step691 p h) (sat_cons (step1557 p h) (sat_cons (step1554 p h) (sat_cons (step1563 p h) (sat_nil p))))))
def c2244 : List Lit := [(113, true), (1800, true), (109, false), (107, false), (117, false)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1554, c1556, c1563, c616, c1557, c2099, c713] c2244 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1554 p h) (sat_cons (step1556 p h) (sat_cons (step1563 p h) (sat_cons (step616 p h) (sat_cons (step1557 p h) (sat_cons (step2099 p h) (sat_cons (step713 p h) (sat_nil p)))))))))
def c2245 : List Lit := [(72, false), (110, true), (71, true), (77, false), (117, false)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c341, c2035] c2245 (by decide) p (sat_cons (step341 p h) (sat_cons (step2035 p h) (sat_nil p)))
def c2246 : List Lit := [(1718, true), (117, false), (125, false)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c1399, c2162, c2238, c1391, c1393, c1389, c1386, c666, c2040, c334] c2246 (by decide) p (sat_cons (step1399 p h) (sat_cons (step2162 p h) (sat_cons (step2238 p h) (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step1389 p h) (sat_cons (step1386 p h) (sat_cons (step666 p h) (sat_cons (step2040 p h) (sat_cons (step334 p h) (sat_nil p)))))))))))
def c2247 : List Lit := [(1713, true), (74, false), (117, false), (125, false)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1393, c1389, c1386, c666, c2040, c334] c2247 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step1389 p h) (sat_cons (step1386 p h) (sat_cons (step666 p h) (sat_cons (step2040 p h) (sat_cons (step334 p h) (sat_nil p))))))))
def c2248 : List Lit := [(1727, true), (72, false), (109, false)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1852, c310] c2248 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1852 p h) (sat_cons (step310 p h) (sat_nil p))))
def c2249 : List Lit := [(70, true), (1714, true), (117, false), (125, false)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c1396, c1386, c1387, c1394, c1389, c666, c2039, c340] c2249 (by decide) p (sat_cons (step1396 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step1394 p h) (sat_cons (step1389 p h) (sat_cons (step666 p h) (sat_cons (step2039 p h) (sat_cons (step340 p h) (sat_nil p)))))))))
def c2250 : List Lit := [(95, false), (104, false), (117, false), (103, false)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c464, c531, c2069] c2250 (by decide) p (sat_cons (step464 p h) (sat_cons (step531 p h) (sat_cons (step2069 p h) (sat_nil p))))
def c2251 : List Lit := [(77, false), (72, false), (75, true), (117, false)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c2048, c341] c2251 (by decide) p (sat_cons (step2048 p h) (sat_cons (step341 p h) (sat_nil p)))
def c2252 : List Lit := [(1622, true), (1616, false), (33, true), (110, true), (117, false)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c1195, c1197, c1225, c1229, c1198, c1196, c1989, c158, c159, c1206, c1209, c1214] c2252 (by decide) p (sat_cons (step1195 p h) (sat_cons (step1197 p h) (sat_cons (step1225 p h) (sat_cons (step1229 p h) (sat_cons (step1198 p h) (sat_cons (step1196 p h) (sat_cons (step1989 p h) (sat_cons (step158 p h) (sat_cons (step159 p h) (sat_cons (step1206 p h) (sat_cons (step1209 p h) (sat_cons (step1214 p h) (sat_nil p)))))))))))))
def c2253 : List Lit := [(1583, true), (1565, false), (1604, true)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c1192, c1191, c1162, c1836, c1131, c2217, c94, c1121, c1123, c1130, c1861, c1158, c1138] c2253 (by decide) p (sat_cons (step1192 p h) (sat_cons (step1191 p h) (sat_cons (step1162 p h) (sat_cons (step1836 p h) (sat_cons (step1131 p h) (sat_cons (step2217 p h) (sat_cons (step94 p h) (sat_cons (step1121 p h) (sat_cons (step1123 p h) (sat_cons (step1130 p h) (sat_cons (step1861 p h) (sat_cons (step1158 p h) (sat_cons (step1138 p h) (sat_nil p))))))))))))))
def c2254 : List Lit := [(1806, false), (1809, true), (1813, true), (123, false), (112, false)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1578, c1588, c1947] c2254 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1578 p h) (sat_cons (step1588 p h) (sat_cons (step1947 p h) (sat_nil p)))))
def c2255 : List Lit := [(1787, true), (117, false)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c1532, c1536, c1526, c1512, c1518, c1519, c1505, c2250] c2255 (by decide) p (sat_cons (step1532 p h) (sat_cons (step1536 p h) (sat_cons (step1526 p h) (sat_cons (step1512 p h) (sat_cons (step1518 p h) (sat_cons (step1519 p h) (sat_cons (step1505 p h) (sat_cons (step2250 p h) (sat_nil p)))))))))
def c2256 : List Lit := [(1813, true), (1806, false), (1803, false), (123, false), (112, false)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c1585, c2254] c2256 (by decide) p (sat_cons (step1585 p h) (sat_cons (step2254 p h) (sat_nil p)))
def c2257 : List Lit := [(1623, true), (1604, false), (37, true), (35, true), (39, true), (114, true)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c1194, c1200, c1205, c1213, c1234, c1230, c1201, c1216, c1196, c1207, c1891, c1992] c2257 (by decide) p (sat_cons (step1194 p h) (sat_cons (step1200 p h) (sat_cons (step1205 p h) (sat_cons (step1213 p h) (sat_cons (step1234 p h) (sat_cons (step1230 p h) (sat_cons (step1201 p h) (sat_cons (step1216 p h) (sat_cons (step1196 p h) (sat_cons (step1207 p h) (sat_cons (step1891 p h) (sat_cons (step1992 p h) (sat_nil p)))))))))))))
def c2258 : List Lit := [(119, true), (1804, true), (1775, true), (109, false), (128, true), (117, false)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c1512, c1504, c1510, c1507, c1508, c474, c2242, c2072, c1570, c491] c2258 (by decide) p (sat_cons (step1512 p h) (sat_cons (step1504 p h) (sat_cons (step1510 p h) (sat_cons (step1507 p h) (sat_cons (step1508 p h) (sat_cons (step474 p h) (sat_cons (step2242 p h) (sat_cons (step2072 p h) (sat_cons (step1570 p h) (sat_cons (step491 p h) (sat_nil p)))))))))))
def c2259 : List Lit := [(1604, true), (104, false), (98, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1859, c500] c2259 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1859 p h) (sat_cons (step500 p h) (sat_nil p))))
def c2260 : List Lit := [(1685, true), (1623, false)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c2159, c2161, c1336, c1313, c2195, c2154, c1241, c1938, c1244, c1135, c2153, c1138, c1312, c1328, c2143, c2149, c1153, c1825, c1129, c1818, c1895, c1119, c1120, c1126, c1896, c1149, c1132, c1141] c2260 (by decide) p (sat_cons (step2159 p h) (sat_cons (step2161 p h) (sat_cons (step1336 p h) (sat_cons (step1313 p h) (sat_cons (step2195 p h) (sat_cons (step2154 p h) (sat_cons (step1241 p h) (sat_cons (step1938 p h) (sat_cons (step1244 p h) (sat_cons (step1135 p h) (sat_cons (step2153 p h) (sat_cons (step1138 p h) (sat_cons (step1312 p h) (sat_cons (step1328 p h) (sat_cons (step2143 p h) (sat_cons (step2149 p h) (sat_cons (step1153 p h) (sat_cons (step1825 p h) (sat_cons (step1129 p h) (sat_cons (step1818 p h) (sat_cons (step1895 p h) (sat_cons (step1119 p h) (sat_cons (step1120 p h) (sat_cons (step1126 p h) (sat_cons (step1896 p h) (sat_cons (step1149 p h) (sat_cons (step1132 p h) (sat_cons (step1141 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2261 : List Lit := [(1593, true), (1577, false)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c2143, c2149, c1149, c1825, c1126, c1818, c1119, c1895] c2261 (by decide) p (sat_cons (step2143 p h) (sat_cons (step2149 p h) (sat_cons (step1149 p h) (sat_cons (step1825 p h) (sat_cons (step1126 p h) (sat_cons (step1818 p h) (sat_cons (step1119 p h) (sat_cons (step1895 p h) (sat_nil p)))))))))
def c2262 : List Lit := [(1574, false), (1593, true)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c2149, c1825, c1818, c1895, c2261, c2143, c1138, c1141, c1153, c1132, c1129, c1896, c1120] c2262 (by decide) p (sat_cons (step2149 p h) (sat_cons (step1825 p h) (sat_cons (step1818 p h) (sat_cons (step1895 p h) (sat_cons (step2261 p h) (sat_cons (step2143 p h) (sat_cons (step1138 p h) (sat_cons (step1141 p h) (sat_cons (step1153 p h) (sat_cons (step1132 p h) (sat_cons (step1129 p h) (sat_cons (step1896 p h) (sat_cons (step1120 p h) (sat_nil p))))))))))))))
def c2263 : List Lit := [(1593, true)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c2143, c2149, c1157, c1825, c1818, c1895, c1119, c2262, c1861, c1122, c1127, c1130, c1153, c1120, c1140, c1896, c1132] c2263 (by decide) p (sat_cons (step2143 p h) (sat_cons (step2149 p h) (sat_cons (step1157 p h) (sat_cons (step1825 p h) (sat_cons (step1818 p h) (sat_cons (step1895 p h) (sat_cons (step1119 p h) (sat_cons (step2262 p h) (sat_cons (step1861 p h) (sat_cons (step1122 p h) (sat_cons (step1127 p h) (sat_cons (step1130 p h) (sat_cons (step1153 p h) (sat_cons (step1120 p h) (sat_cons (step1140 p h) (sat_cons (step1896 p h) (sat_cons (step1132 p h) (sat_nil p))))))))))))))))))
def c2264 : List Lit := [(1713, true), (74, false), (114, true)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1393, c1389, c1386, c2040, c334] c2264 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step1389 p h) (sat_cons (step1386 p h) (sat_cons (step2040 p h) (sat_cons (step334 p h) (sat_nil p)))))))
def c2265 : List Lit := [(61, false), (54, true), (1703, true)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c1375, c1374, c283, c2025] c2265 (by decide) p (sat_cons (step1375 p h) (sat_cons (step1374 p h) (sat_cons (step283 p h) (sat_cons (step2025 p h) (sat_nil p)))))
def c2266 : List Lit := [(61, false), (1703, true), (72, false), (51, false)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c1375, c1374, c283, c226, c2025] c2266 (by decide) p (sat_cons (step1375 p h) (sat_cons (step1374 p h) (sat_cons (step283 p h) (sat_cons (step226 p h) (sat_cons (step2025 p h) (sat_nil p))))))
def c2267 : List Lit := [(1574, false), (1582, true), (15, true)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c1119, c1126, c1149, c1138, c1153, c1141, c1129, c1132, c1120, c1896] c2267 (by decide) p (sat_cons (step1119 p h) (sat_cons (step1126 p h) (sat_cons (step1149 p h) (sat_cons (step1138 p h) (sat_cons (step1153 p h) (sat_cons (step1141 p h) (sat_cons (step1129 p h) (sat_cons (step1132 p h) (sat_cons (step1120 p h) (sat_cons (step1896 p h) (sat_nil p)))))))))))
def c2268 : List Lit := [(1582, true), (15, true)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c1119, c2267, c1157, c1861, c1122, c1130, c1127, c1120, c1153, c1896, c1140, c1132] c2268 (by decide) p (sat_cons (step1119 p h) (sat_cons (step2267 p h) (sat_cons (step1157 p h) (sat_cons (step1861 p h) (sat_cons (step1122 p h) (sat_cons (step1130 p h) (sat_cons (step1127 p h) (sat_cons (step1120 p h) (sat_cons (step1153 p h) (sat_cons (step1896 p h) (sat_cons (step1140 p h) (sat_cons (step1132 p h) (sat_nil p)))))))))))))
def c2269 : List Lit := [(1740, true), (100, false), (104, false), (98, false)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1444, c1436, c1438, c1430, c1433, c415, c473, c503, c2078] c2269 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1444 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1430 p h) (sat_cons (step1433 p h) (sat_cons (step415 p h) (sat_cons (step473 p h) (sat_cons (step503 p h) (sat_cons (step2078 p h) (sat_nil p)))))))))))
def c2270 : List Lit := [(1747, true), (1725, false), (100, false), (104, false), (98, false)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c1425, c2269, c1459, c1448, c1464, c1426, c1908, c1431, c1432, c1445, c473, c1436, c1438, c1433, c415, c503, c2078] c2270 (by decide) p (sat_cons (step1425 p h) (sat_cons (step2269 p h) (sat_cons (step1459 p h) (sat_cons (step1448 p h) (sat_cons (step1464 p h) (sat_cons (step1426 p h) (sat_cons (step1908 p h) (sat_cons (step1431 p h) (sat_cons (step1432 p h) (sat_cons (step1445 p h) (sat_cons (step473 p h) (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1433 p h) (sat_cons (step415 p h) (sat_cons (step503 p h) (sat_cons (step2078 p h) (sat_nil p))))))))))))))))))
def c2271 : List Lit := [(105, false), (63, false), (65, false), (68, false)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c289, c291, c2029] c2271 (by decide) p (sat_cons (step289 p h) (sat_cons (step291 p h) (sat_cons (step2029 p h) (sat_nil p))))
def c2272 : List Lit := [(85, false), (63, false), (65, false), (68, false)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c290, c288, c2029] c2272 (by decide) p (sat_cons (step290 p h) (sat_cons (step288 p h) (sat_cons (step2029 p h) (sat_nil p))))
def c2273 : List Lit := [(1628, true), (34, true), (124, false), (27, false)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1239, c190, c191, c2005] c2273 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step190 p h) (sat_cons (step191 p h) (sat_cons (step2005 p h) (sat_nil p))))))
def c2274 : List Lit := [(19, true), (1565, false), (1583, true)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c1162, c1131, c1121, c1123, c1130, c1861, c1158, c1138] c2274 (by decide) p (sat_cons (step1162 p h) (sat_cons (step1131 p h) (sat_cons (step1121 p h) (sat_cons (step1123 p h) (sat_cons (step1130 p h) (sat_cons (step1861 p h) (sat_cons (step1158 p h) (sat_cons (step1138 p h) (sat_nil p)))))))))
def c2275 : List Lit := [(93, false), (96, true), (86, false), (104, false), (98, false)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c503, c418, c2078] c2275 (by decide) p (sat_cons (step503 p h) (sat_cons (step418 p h) (sat_cons (step2078 p h) (sat_nil p))))
def c2276 : List Lit := [(87, false), (1739, true), (51, false), (93, true), (86, false)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c394, c395, c1440, c1435] c2276 (by decide) p (sat_cons (step394 p h) (sat_cons (step395 p h) (sat_cons (step1440 p h) (sat_cons (step1435 p h) (sat_nil p)))))
def c2277 : List Lit := [(1583, true), (20, false), (92, false), (1565, false)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c1836, c2274, c63] c2277 (by decide) p (sat_cons (step1836 p h) (sat_cons (step2274 p h) (sat_cons (step63 p h) (sat_nil p))))
def c2278 : List Lit := [(1617, true), (42, true), (39, true)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c1208, c1212, c1214, c1210, c1205, c1206, c2000, c155] c2278 (by decide) p (sat_cons (step1208 p h) (sat_cons (step1212 p h) (sat_cons (step1214 p h) (sat_cons (step1210 p h) (sat_cons (step1205 p h) (sat_cons (step1206 p h) (sat_cons (step2000 p h) (sat_cons (step155 p h) (sat_nil p)))))))))
def c2279 : List Lit := [(1805, true), (124, false), (46, false)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c1571, c1572, c808] c2279 (by decide) p (sat_cons (step1571 p h) (sat_cons (step1572 p h) (sat_cons (step808 p h) (sat_nil p))))
def c2280 : List Lit := [(1803, true), (110, true), (128, true)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1569, c2103, c2102, c1775] c2280 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1569 p h) (sat_cons (step2103 p h) (sat_cons (step2102 p h) (sat_cons (step1775 p h) (sat_nil p))))))
def c2281 : List Lit := [(113, true), (1782, true), (1800, true), (116, true)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1554, c1556, c1563, c1557, c2099, c1845] c2281 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1554 p h) (sat_cons (step1556 p h) (sat_cons (step1563 p h) (sat_cons (step1557 p h) (sat_cons (step2099 p h) (sat_cons (step1845 p h) (sat_nil p))))))))
def c2282 : List Lit := [(48, true), (1624, false), (1687, true)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1330, c1319, c2154, c1245, c1242, c1243, c1244, c2195, c2153, c1338, c1318] c2282 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1330 p h) (sat_cons (step1319 p h) (sat_cons (step2154 p h) (sat_cons (step1245 p h) (sat_cons (step1242 p h) (sat_cons (step1243 p h) (sat_cons (step1244 p h) (sat_cons (step2195 p h) (sat_cons (step2153 p h) (sat_cons (step1338 p h) (sat_cons (step1318 p h) (sat_nil p)))))))))))))
def c2283 : List Lit := [(42, false), (44, false), (46, false), (43, true)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c167, c2003] c2283 (by decide) p (sat_cons (step167 p h) (sat_cons (step2003 p h) (sat_nil p)))
def c2284 : List Lit := [(1604, false), (1610, true), (42, true), (1624, true), (43, true), (108, true), (35, true)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c1194, c1200, c1231, c1201, c1196, c1986, c1985, c1727, c1847] c2284 (by decide) p (sat_cons (step1194 p h) (sat_cons (step1200 p h) (sat_cons (step1231 p h) (sat_cons (step1201 p h) (sat_cons (step1196 p h) (sat_cons (step1986 p h) (sat_cons (step1985 p h) (sat_cons (step1727 p h) (sat_cons (step1847 p h) (sat_nil p))))))))))
def c2285 : List Lit := [(92, false), (1792, true), (1782, false), (1773, false), (104, true), (94, false), (117, false)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c463, c462, c1520, c1505, c1531, c1513, c1545] c2285 (by decide) p (sat_cons (step463 p h) (sat_cons (step462 p h) (sat_cons (step1520 p h) (sat_cons (step1505 p h) (sat_cons (step1531 p h) (sat_cons (step1513 p h) (sat_cons (step1545 p h) (sat_nil p))))))))
def c2286 : List Lit := [(1686, true), (1623, false), (48, true)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1242, c1244, c2153, c1312, c1329, c1337, c1313, c2195, c2154, c1243, c1245] c2286 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1242 p h) (sat_cons (step1244 p h) (sat_cons (step2153 p h) (sat_cons (step1312 p h) (sat_cons (step1329 p h) (sat_cons (step1337 p h) (sat_cons (step1313 p h) (sat_cons (step2195 p h) (sat_cons (step2154 p h) (sat_cons (step1243 p h) (sat_cons (step1245 p h) (sat_nil p)))))))))))))
def c2287 : List Lit := [(1789, true), (1773, false), (104, true), (94, false), (117, false)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c1510, c1518, c1526, c1542, c1538, c1513, c1529, c1505, c1520, c464] c2287 (by decide) p (sat_cons (step1510 p h) (sat_cons (step1518 p h) (sat_cons (step1526 p h) (sat_cons (step1542 p h) (sat_cons (step1538 p h) (sat_cons (step1513 p h) (sat_cons (step1529 p h) (sat_cons (step1505 p h) (sat_cons (step1520 p h) (sat_cons (step464 p h) (sat_nil p)))))))))))
def c2288 : List Lit := [(42, true), (1623, true), (43, true), (108, true), (35, true), (39, true)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c1194, c1197, c1226, c2278, c1230, c1198, c1196, c1986, c1985, c1727, c1847] c2288 (by decide) p (sat_cons (step1194 p h) (sat_cons (step1197 p h) (sat_cons (step1226 p h) (sat_cons (step2278 p h) (sat_cons (step1230 p h) (sat_cons (step1198 p h) (sat_cons (step1196 p h) (sat_cons (step1986 p h) (sat_cons (step1985 p h) (sat_cons (step1727 p h) (sat_cons (step1847 p h) (sat_nil p))))))))))))
def c2289 : List Lit := [(1685, true), (1621, false), (1628, false), (48, true)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c2263, c1242, c1247, c2154, c1299, c1336, c1328, c2195, c1300, c1243, c2155, c1248] c2289 (by decide) p (sat_cons (step2263 p h) (sat_cons (step1242 p h) (sat_cons (step1247 p h) (sat_cons (step2154 p h) (sat_cons (step1299 p h) (sat_cons (step1336 p h) (sat_cons (step1328 p h) (sat_cons (step2195 p h) (sat_cons (step1300 p h) (sat_cons (step1243 p h) (sat_cons (step2155 p h) (sat_cons (step1248 p h) (sat_nil p)))))))))))))
def c2290 : List Lit := [(1622, true), (1616, false), (43, true), (108, true), (1608, false), (110, true), (117, false)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c1225, c2252, c1891, c1985] c2290 (by decide) p (sat_cons (step1225 p h) (sat_cons (step2252 p h) (sat_cons (step1891 p h) (sat_cons (step1985 p h) (sat_nil p)))))
end B112E034
