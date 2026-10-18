import B112E034Part0005
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2163 : List Lit := [(1714, false), (1719, true)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1403] c2163 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1403 p h) (sat_nil p)))
def c2164 : List Lit := [(1715, false), (1720, true)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1404] c2164 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1404 p h) (sat_nil p)))
def c2165 : List Lit := [(1716, false), (1721, true)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1405] c2165 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1405 p h) (sat_nil p)))
def c2166 : List Lit := [(1745, false), (1755, true)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1472] c2166 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1472 p h) (sat_nil p)))
def c2167 : List Lit := [(1746, false), (1756, true)]
theorem step2167 (p : Nat → Bool) (h : Constraints p) : clause p c2167 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1473] c2167 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1473 p h) (sat_nil p)))
def c2168 : List Lit := [(1747, false), (1757, true)]
theorem step2168 (p : Nat → Bool) (h : Constraints p) : clause p c2168 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1474] c2168 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1474 p h) (sat_nil p)))
def c2169 : List Lit := [(1748, false), (1758, true)]
theorem step2169 (p : Nat → Bool) (h : Constraints p) : clause p c2169 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1475] c2169 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1475 p h) (sat_nil p)))
def c2170 : List Lit := [(1749, false), (1759, true)]
theorem step2170 (p : Nat → Bool) (h : Constraints p) : clause p c2170 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1476] c2170 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1476 p h) (sat_nil p)))
def c2171 : List Lit := [(1750, false), (1760, true)]
theorem step2171 (p : Nat → Bool) (h : Constraints p) : clause p c2171 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1477] c2171 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1477 p h) (sat_nil p)))
def c2172 : List Lit := [(1682, false), (1858, false)]
theorem step2172 (p : Nat → Bool) (h : Constraints p) : clause p c2172 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1709] c2172 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1709 p h) (sat_nil p)))
def c2173 : List Lit := [(1683, false), (1857, false)]
theorem step2173 (p : Nat → Bool) (h : Constraints p) : clause p c2173 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1710] c2173 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1710 p h) (sat_nil p)))
def c2174 : List Lit := [(1684, false), (1856, false)]
theorem step2174 (p : Nat → Bool) (h : Constraints p) : clause p c2174 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1711] c2174 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1711 p h) (sat_nil p)))
def c2175 : List Lit := [(1685, false), (1855, false)]
theorem step2175 (p : Nat → Bool) (h : Constraints p) : clause p c2175 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1712] c2175 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1712 p h) (sat_nil p)))
def c2176 : List Lit := [(1686, false), (1854, false)]
theorem step2176 (p : Nat → Bool) (h : Constraints p) : clause p c2176 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1713] c2176 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1713 p h) (sat_nil p)))
def c2177 : List Lit := [(1687, false), (1853, false)]
theorem step2177 (p : Nat → Bool) (h : Constraints p) : clause p c2177 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1714] c2177 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1714 p h) (sat_nil p)))
def c2178 : List Lit := [(1688, false), (1852, false)]
theorem step2178 (p : Nat → Bool) (h : Constraints p) : clause p c2178 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1715] c2178 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1715 p h) (sat_nil p)))
def c2179 : List Lit := [(1689, false), (1851, false)]
theorem step2179 (p : Nat → Bool) (h : Constraints p) : clause p c2179 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1716] c2179 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1716 p h) (sat_nil p)))
def c2180 : List Lit := [(1690, false), (1850, false)]
theorem step2180 (p : Nat → Bool) (h : Constraints p) : clause p c2180 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1717] c2180 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1717 p h) (sat_nil p)))
def c2181 : List Lit := [(1691, false), (1849, false)]
theorem step2181 (p : Nat → Bool) (h : Constraints p) : clause p c2181 = true :=
  Snake9.LocalRup.prove_clause [c1719, c1718] c2181 (by decide) p (sat_cons (step1719 p h) (sat_cons (step1718 p h) (sat_nil p)))
def c2182 : List Lit := [(1685, true), (1644, false), (1622, false), (1628, false)]
theorem step2182 (p : Nat → Bool) (h : Constraints p) : clause p c2182 = true :=
  Snake9.LocalRup.prove_clause [c1921, c1858] c2182 (by decide) p (sat_cons (step1921 p h) (sat_cons (step1858 p h) (sat_nil p)))
def c2183 : List Lit := [(118, false), (113, false), (111, true), (126, false)]
theorem step2183 (p : Nat → Bool) (h : Constraints p) : clause p c2183 = true :=
  Snake9.LocalRup.prove_clause [c706, c2100] c2183 (by decide) p (sat_cons (step706 p h) (sat_cons (step2100 p h) (sat_nil p)))
def c2184 : List Lit := [(1714, true), (114, true), (74, true), (117, false)]
theorem step2184 (p : Nat → Bool) (h : Constraints p) : clause p c2184 = true :=
  Snake9.LocalRup.prove_clause [c1388, c1392, c1394, c1390, c1385, c2039, c340] c2184 (by decide) p (sat_cons (step1388 p h) (sat_cons (step1392 p h) (sat_cons (step1394 p h) (sat_cons (step1390 p h) (sat_cons (step1385 p h) (sat_cons (step2039 p h) (sat_cons (step340 p h) (sat_nil p))))))))
def c2185 : List Lit := [(1748, true), (86, true), (1725, false), (1737, false)]
theorem step2185 (p : Nat → Bool) (h : Constraints p) : clause p c2185 = true :=
  Snake9.LocalRup.prove_clause [c1430, c1445, c1425, c1465, c1460, c1426, c1449, c1908, c1432] c2185 (by decide) p (sat_cons (step1430 p h) (sat_cons (step1445 p h) (sat_cons (step1425 p h) (sat_cons (step1465 p h) (sat_cons (step1460 p h) (sat_cons (step1426 p h) (sat_cons (step1449 p h) (sat_cons (step1908 p h) (sat_cons (step1432 p h) (sat_nil p))))))))))
def c2186 : List Lit := [(1738, true), (87, false), (97, false), (93, true)]
theorem step2186 (p : Nat → Bool) (h : Constraints p) : clause p c2186 = true :=
  Snake9.LocalRup.prove_clause [c1433, c1437, c1439, c1435, c403] c2186 (by decide) p (sat_cons (step1433 p h) (sat_cons (step1437 p h) (sat_cons (step1439 p h) (sat_cons (step1435 p h) (sat_cons (step403 p h) (sat_nil p))))))
def c2187 : List Lit := [(121, false), (123, true), (117, false), (119, true)]
theorem step2187 (p : Nat → Bool) (h : Constraints p) : clause p c2187 = true :=
  Snake9.LocalRup.prove_clause [c2104, c2101, c1769] c2187 (by decide) p (sat_cons (step2104 p h) (sat_cons (step2101 p h) (sat_cons (step1769 p h) (sat_nil p))))
def c2188 : List Lit := [(125, false), (120, false), (124, true), (114, true), (119, true), (126, false)]
theorem step2188 (p : Nat → Bool) (h : Constraints p) : clause p c2188 = true :=
  Snake9.LocalRup.prove_clause [c834, c2112] c2188 (by decide) p (sat_cons (step834 p h) (sat_cons (step2112 p h) (sat_nil p)))
def c2189 : List Lit := [(1811, true), (1805, false), (117, false), (119, true)]
theorem step2189 (p : Nat → Bool) (h : Constraints p) : clause p c2189 = true :=
  Snake9.LocalRup.prove_clause [c1574, c1580, c1577, c1583, c1568, c1945, c2187] c2189 (by decide) p (sat_cons (step1574 p h) (sat_cons (step1580 p h) (sat_cons (step1577 p h) (sat_cons (step1583 p h) (sat_cons (step1568 p h) (sat_cons (step1945 p h) (sat_cons (step2187 p h) (sat_nil p))))))))
def c2190 : List Lit := [(1781, true), (111, false), (122, false)]
theorem step2190 (p : Nat → Bool) (h : Constraints p) : clause p c2190 = true :=
  Snake9.LocalRup.prove_clause [c1521, c1522, c618] c2190 (by decide) p (sat_cons (step1521 p h) (sat_cons (step1522 p h) (sat_cons (step618 p h) (sat_nil p))))
def c2191 : List Lit := [(1632, true), (45, false), (122, false)]
theorem step2191 (p : Nat → Bool) (h : Constraints p) : clause p c2191 = true :=
  Snake9.LocalRup.prove_clause [c1244, c1246, c1242, c1239, c188] c2191 (by decide) p (sat_cons (step1244 p h) (sat_cons (step1246 p h) (sat_cons (step1242 p h) (sat_cons (step1239 p h) (sat_cons (step188 p h) (sat_nil p))))))
def c2192 : List Lit := [(35, true), (1623, true), (1604, false), (119, true), (120, false), (115, true)]
theorem step2192 (p : Nat → Bool) (h : Constraints p) : clause p c2192 = true :=
  Snake9.LocalRup.prove_clause [c1869, c1234, c1201, c1194, c1196, c1200, c1230, c1877, c174, c2001] c2192 (by decide) p (sat_cons (step1869 p h) (sat_cons (step1234 p h) (sat_cons (step1201 p h) (sat_cons (step1194 p h) (sat_cons (step1196 p h) (sat_cons (step1200 p h) (sat_cons (step1230 p h) (sat_cons (step1877 p h) (sat_cons (step174 p h) (sat_cons (step2001 p h) (sat_nil p)))))))))))
def c2193 : List Lit := [(1633, true), (46, true), (45, false), (122, false)]
theorem step2193 (p : Nat → Bool) (h : Constraints p) : clause p c2193 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1249, c1247, c1240, c1242, c188] c2193 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1249 p h) (sat_cons (step1247 p h) (sat_cons (step1240 p h) (sat_cons (step1242 p h) (sat_cons (step188 p h) (sat_nil p)))))))
def c2194 : List Lit := [(1713, true), (77, false)]
theorem step2194 (p : Nat → Bool) (h : Constraints p) : clause p c2194 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1393, c1388, c1389, c1385, c1919] c2194 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1385 p h) (sat_cons (step1919 p h) (sat_nil p)))))))
def c2195 : List Lit := [(1594, true), (51, false)]
theorem step2195 (p : Nat → Bool) (h : Constraints p) : clause p c2195 = true :=
  Snake9.LocalRup.prove_clause [c1881, c1873, c1132, c1896] c2195 (by decide) p (sat_cons (step1881 p h) (sat_cons (step1873 p h) (sat_cons (step1132 p h) (sat_cons (step1896 p h) (sat_nil p)))))
def c2196 : List Lit := [(1742, false), (1760, true), (79, true), (1727, false)]
theorem step2196 (p : Nat → Bool) (h : Constraints p) : clause p c2196 = true :=
  Snake9.LocalRup.prove_clause [c2171, c1417, c1426, c1466, c1482, c1471, c2162, c1429, c2194, c1419] c2196 (by decide) p (sat_cons (step2171 p h) (sat_cons (step1417 p h) (sat_cons (step1426 p h) (sat_cons (step1466 p h) (sat_cons (step1482 p h) (sat_cons (step1471 p h) (sat_cons (step2162 p h) (sat_cons (step1429 p h) (sat_cons (step2194 p h) (sat_cons (step1419 p h) (sat_nil p)))))))))))
def c2197 : List Lit := [(1790, true), (1775, false), (92, false), (1782, false)]
theorem step2197 (p : Nat → Bool) (h : Constraints p) : clause p c2197 = true :=
  Snake9.LocalRup.prove_clause [c1525, c1539, c1543, c1528, c1915, c1505, c1946, c1513, c1848, c1507] c2197 (by decide) p (sat_cons (step1525 p h) (sat_cons (step1539 p h) (sat_cons (step1543 p h) (sat_cons (step1528 p h) (sat_cons (step1915 p h) (sat_cons (step1505 p h) (sat_cons (step1946 p h) (sat_cons (step1513 p h) (sat_cons (step1848 p h) (sat_cons (step1507 p h) (sat_nil p)))))))))))
def c2198 : List Lit := [(98, false), (1758, true), (88, false), (89, false)]
theorem step2198 (p : Nat → Bool) (h : Constraints p) : clause p c2198 = true :=
  Snake9.LocalRup.prove_clause [c2169, c416, c421, c1433, c1436, c1849, c2185, c1480, c1418, c2162, c2194] c2198 (by decide) p (sat_cons (step2169 p h) (sat_cons (step416 p h) (sat_cons (step421 p h) (sat_cons (step1433 p h) (sat_cons (step1436 p h) (sat_cons (step1849 p h) (sat_cons (step2185 p h) (sat_cons (step1480 p h) (sat_cons (step1418 p h) (sat_cons (step2162 p h) (sat_cons (step2194 p h) (sat_nil p))))))))))))
def c2199 : List Lit := [(1737, false), (86, true), (1758, true)]
theorem step2199 (p : Nat → Bool) (h : Constraints p) : clause p c2199 = true :=
  Snake9.LocalRup.prove_clause [c2169, c1849, c2185, c1480, c1418, c2162, c2194] c2199 (by decide) p (sat_cons (step2169 p h) (sat_cons (step1849 p h) (sat_cons (step2185 p h) (sat_cons (step1480 p h) (sat_cons (step1418 p h) (sat_cons (step2162 p h) (sat_cons (step2194 p h) (sat_nil p))))))))
def c2200 : List Lit := [(1746, true), (86, true)]
theorem step2200 (p : Nat → Bool) (h : Constraints p) : clause p c2200 = true :=
  Snake9.LocalRup.prove_clause [c1430, c1444, c1453, c1458, c1448, c1423, c1432, c1908] c2200 (by decide) p (sat_cons (step1430 p h) (sat_cons (step1444 p h) (sat_cons (step1453 p h) (sat_cons (step1458 p h) (sat_cons (step1448 p h) (sat_cons (step1423 p h) (sat_cons (step1432 p h) (sat_cons (step1908 p h) (sat_nil p)))))))))
def c2201 : List Lit := [(1633, true), (51, true), (1604, true), (82, false), (113, false)]
theorem step2201 (p : Nat → Bool) (h : Constraints p) : clause p c2201 = true :=
  Snake9.LocalRup.prove_clause [c1241, c1192, c1191, c1245, c1247, c1243, c1238, c1239, c197, c805, c96, c2007] c2201 (by decide) p (sat_cons (step1241 p h) (sat_cons (step1192 p h) (sat_cons (step1191 p h) (sat_cons (step1245 p h) (sat_cons (step1247 p h) (sat_cons (step1243 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step197 p h) (sat_cons (step805 p h) (sat_cons (step96 p h) (sat_cons (step2007 p h) (sat_nil p)))))))))))))
def c2202 : List Lit := [(1713, true), (92, false), (113, false)]
theorem step2202 (p : Nat → Bool) (h : Constraints p) : clause p c2202 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1393, c1388, c1389, c1386, c661, c334, c2040] c2202 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1386 p h) (sat_cons (step661 p h) (sat_cons (step334 p h) (sat_cons (step2040 p h) (sat_nil p)))))))))
def c2203 : List Lit := [(100, false), (1779, true), (86, false)]
theorem step2203 (p : Nat → Bool) (h : Constraints p) : clause p c2203 = true :=
  Snake9.LocalRup.prove_clause [c1848, c2081, c2080, c1751] c2203 (by decide) p (sat_cons (step1848 p h) (sat_cons (step2081 p h) (sat_cons (step2080 p h) (sat_cons (step1751 p h) (sat_nil p)))))
def c2204 : List Lit := [(73, false), (114, true), (77, false)]
theorem step2204 (p : Nat → Bool) (h : Constraints p) : clause p c2204 = true :=
  Snake9.LocalRup.prove_clause [c2040, c2039, c1745] c2204 (by decide) p (sat_cons (step2040 p h) (sat_cons (step2039 p h) (sat_cons (step1745 p h) (sat_nil p))))
def c2205 : List Lit := [(28, false), (1585, true), (1574, false), (16, true), (18, true), (20, false), (92, false)]
theorem step2205 (p : Nat → Bool) (h : Constraints p) : clause p c2205 = true :=
  Snake9.LocalRup.prove_clause [c68, c65, c59, c1133, c1123, c1120, c1141, c1131, c1164] c2205 (by decide) p (sat_cons (step68 p h) (sat_cons (step65 p h) (sat_cons (step59 p h) (sat_cons (step1133 p h) (sat_cons (step1123 p h) (sat_cons (step1120 p h) (sat_cons (step1141 p h) (sat_cons (step1131 p h) (sat_cons (step1164 p h) (sat_nil p))))))))))
def c2206 : List Lit := [(1746, true), (1737, false)]
theorem step2206 (p : Nat → Bool) (h : Constraints p) : clause p c2206 = true :=
  Snake9.LocalRup.prove_clause [c1453, c1905] c2206 (by decide) p (sat_cons (step1453 p h) (sat_cons (step1905 p h) (sat_nil p)))
def c2207 : List Lit := [(1685, true), (1644, false), (1622, false), (1593, false)]
theorem step2207 (p : Nat → Bool) (h : Constraints p) : clause p c2207 = true :=
  Snake9.LocalRup.prove_clause [c1275, c1305, c1328, c1336, c1306, c2195, c1280, c1241, c1244] c2207 (by decide) p (sat_cons (step1275 p h) (sat_cons (step1305 p h) (sat_cons (step1328 p h) (sat_cons (step1336 p h) (sat_cons (step1306 p h) (sat_cons (step2195 p h) (sat_cons (step1280 p h) (sat_cons (step1241 p h) (sat_cons (step1244 p h) (sat_nil p))))))))))
def c2208 : List Lit := [(113, false), (46, false), (125, false), (107, false), (115, true), (86, false), (114, true)]
theorem step2208 (p : Nat → Bool) (h : Constraints p) : clause p c2208 = true :=
  Snake9.LocalRup.prove_clause [c806, c534, c2096] c2208 (by decide) p (sat_cons (step806 p h) (sat_cons (step534 p h) (sat_cons (step2096 p h) (sat_nil p))))
def c2209 : List Lit := [(128, false), (94, false), (103, false), (104, false)]
theorem step2209 (p : Nat → Bool) (h : Constraints p) : clause p c2209 = true :=
  Snake9.LocalRup.prove_clause [c522, c523, c2083] c2209 (by decide) p (sat_cons (step522 p h) (sat_cons (step523 p h) (sat_cons (step2083 p h) (sat_nil p))))
def c2210 : List Lit := [(1782, true), (113, false), (118, false), (112, false), (109, true)]
theorem step2210 (p : Nat → Bool) (h : Constraints p) : clause p c2210 = true :=
  Snake9.LocalRup.prove_clause [c1523, c1845, c703, c2100] c2210 (by decide) p (sat_cons (step1523 p h) (sat_cons (step1845 p h) (sat_cons (step703 p h) (sat_cons (step2100 p h) (sat_nil p)))))
def c2211 : List Lit := [(122, false), (121, false), (118, false), (112, false)]
theorem step2211 (p : Nat → Bool) (h : Constraints p) : clause p c2211 = true :=
  Snake9.LocalRup.prove_clause [c1931, c625] c2211 (by decide) p (sat_cons (step1931 p h) (sat_cons (step625 p h) (sat_nil p)))
def c2212 : List Lit := [(88, false), (106, false), (100, false), (86, false)]
theorem step2212 (p : Nat → Bool) (h : Constraints p) : clause p c2212 = true :=
  Snake9.LocalRup.prove_clause [c385, c384, c2082] c2212 (by decide) p (sat_cons (step385 p h) (sat_cons (step384 p h) (sat_cons (step2082 p h) (sat_nil p))))
def c2213 : List Lit := [(91, false), (128, true), (111, false), (121, false), (112, false)]
theorem step2213 (p : Nat → Bool) (h : Constraints p) : clause p c2213 = true :=
  Snake9.LocalRup.prove_clause [c633, c635, c2102] c2213 (by decide) p (sat_cons (step633 p h) (sat_cons (step635 p h) (sat_cons (step2102 p h) (sat_nil p))))
def c2214 : List Lit := [(18, false), (24, true), (154, true), (91, true)]
theorem step2214 (p : Nat → Bool) (h : Constraints p) : clause p c2214 = true :=
  Snake9.LocalRup.prove_clause [c1966, c1967, c85, c1723] c2214 (by decide) p (sat_cons (step1966 p h) (sat_cons (step1967 p h) (sat_cons (step85 p h) (sat_cons (step1723 p h) (sat_nil p)))))
def c2215 : List Lit := [(1622, false), (1661, true), (1684, true)]
theorem step2215 (p : Nat → Bool) (h : Constraints p) : clause p c2215 = true :=
  Snake9.LocalRup.prove_clause [c2158, c1305, c1335, c2153, c2195, c1244, c1241] c2215 (by decide) p (sat_cons (step2158 p h) (sat_cons (step1305 p h) (sat_cons (step1335 p h) (sat_cons (step2153 p h) (sat_cons (step2195 p h) (sat_cons (step1244 p h) (sat_cons (step1241 p h) (sat_nil p))))))))
def c2216 : List Lit := [(1684, true), (51, false), (1617, false)]
theorem step2216 (p : Nat → Bool) (h : Constraints p) : clause p c2216 = true :=
  Snake9.LocalRup.prove_clause [c1831, c1818, c1825, c1949, c1119, c1126, c2195, c1220, c2157, c1342, c1335, c1176, c2158, c1298, c1150, c1225, c2153, c1199, c1244, c1246, c1191, c1192, c1242, c1238, c1239, c96, c197, c1984, c2012, c109, c185, c1836, c1135, c1120, c1144, c1896, c1134] c2216 (by decide) p (sat_cons (step1831 p h) (sat_cons (step1818 p h) (sat_cons (step1825 p h) (sat_cons (step1949 p h) (sat_cons (step1119 p h) (sat_cons (step1126 p h) (sat_cons (step2195 p h) (sat_cons (step1220 p h) (sat_cons (step2157 p h) (sat_cons (step1342 p h) (sat_cons (step1335 p h) (sat_cons (step1176 p h) (sat_cons (step2158 p h) (sat_cons (step1298 p h) (sat_cons (step1150 p h) (sat_cons (step1225 p h) (sat_cons (step2153 p h) (sat_cons (step1199 p h) (sat_cons (step1244 p h) (sat_cons (step1246 p h) (sat_cons (step1191 p h) (sat_cons (step1192 p h) (sat_cons (step1242 p h) (sat_cons (step1238 p h) (sat_cons (step1239 p h) (sat_cons (step96 p h) (sat_cons (step197 p h) (sat_cons (step1984 p h) (sat_cons (step2012 p h) (sat_cons (step109 p h) (sat_cons (step185 p h) (sat_cons (step1836 p h) (sat_cons (step1135 p h) (sat_cons (step1120 p h) (sat_cons (step1144 p h) (sat_cons (step1896 p h) (sat_cons (step1134 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c2217 : List Lit := [(1604, true), (27, true), (21, false)]
theorem step2217 (p : Nat → Bool) (h : Constraints p) : clause p c2217 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1192, c109, c1984] c2217 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1192 p h) (sat_cons (step109 p h) (sat_cons (step1984 p h) (sat_nil p)))))
def c2218 : List Lit := [(1747, true), (1738, false)]
theorem step2218 (p : Nat → Bool) (h : Constraints p) : clause p c2218 = true :=
  Snake9.LocalRup.prove_clause [c1442, c1454, c1459, c1446, c1423, c1431, c1908] c2218 (by decide) p (sat_cons (step1442 p h) (sat_cons (step1454 p h) (sat_cons (step1459 p h) (sat_cons (step1446 p h) (sat_cons (step1423 p h) (sat_cons (step1431 p h) (sat_cons (step1908 p h) (sat_nil p))))))))
def c2219 : List Lit := [(107, false), (93, false), (1713, true)]
theorem step2219 (p : Nat → Bool) (h : Constraints p) : clause p c2219 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1388, c1389, c1393, c1386, c334, c687, c296, c2042] c2219 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1388 p h) (sat_cons (step1389 p h) (sat_cons (step1393 p h) (sat_cons (step1386 p h) (sat_cons (step334 p h) (sat_cons (step687 p h) (sat_cons (step296 p h) (sat_cons (step2042 p h) (sat_nil p))))))))))
def c2220 : List Lit := [(63, true), (67, true), (1702, true)]
theorem step2220 (p : Nat → Bool) (h : Constraints p) : clause p c2220 = true :=
  Snake9.LocalRup.prove_clause [c2027, c2024, c1373] c2220 (by decide) p (sat_cons (step2027 p h) (sat_cons (step2024 p h) (sat_cons (step1373 p h) (sat_nil p))))
def c2221 : List Lit := [(11, true), (1554, true), (138, true), (27, true)]
theorem step2221 (p : Nat → Bool) (h : Constraints p) : clause p c2221 = true :=
  Snake9.LocalRup.prove_clause [c1103, c1958, c1107, c1957, c1820] c2221 (by decide) p (sat_cons (step1103 p h) (sat_cons (step1958 p h) (sat_cons (step1107 p h) (sat_cons (step1957 p h) (sat_cons (step1820 p h) (sat_nil p))))))
def c2222 : List Lit := [(1737, true), (20, true), (86, false), (94, true)]
theorem step2222 (p : Nat → Bool) (h : Constraints p) : clause p c2222 = true :=
  Snake9.LocalRup.prove_clause [c1436, c1438, c1434, c400, c2064] c2222 (by decide) p (sat_cons (step1436 p h) (sat_cons (step1438 p h) (sat_cons (step1434 p h) (sat_cons (step400 p h) (sat_cons (step2064 p h) (sat_nil p))))))
def c2223 : List Lit := [(1818, true), (1782, true), (1805, false), (113, true), (117, true)]
theorem step2223 (p : Nat → Bool) (h : Constraints p) : clause p c2223 = true :=
  Snake9.LocalRup.prove_clause [c1574, c1579, c1558, c1554, c1563, c1606, c1601, c1566, c1564, c1580, c1583, c1556, c1559, c1577, c1568, c1845, c1931] c2223 (by decide) p (sat_cons (step1574 p h) (sat_cons (step1579 p h) (sat_cons (step1558 p h) (sat_cons (step1554 p h) (sat_cons (step1563 p h) (sat_cons (step1606 p h) (sat_cons (step1601 p h) (sat_cons (step1566 p h) (sat_cons (step1564 p h) (sat_cons (step1580 p h) (sat_cons (step1583 p h) (sat_cons (step1556 p h) (sat_cons (step1559 p h) (sat_cons (step1577 p h) (sat_cons (step1568 p h) (sat_cons (step1845 p h) (sat_cons (step1931 p h) (sat_nil p))))))))))))))))))
def c2224 : List Lit := [(1819, true), (1806, false), (113, true), (117, true)]
theorem step2224 (p : Nat → Bool) (h : Constraints p) : clause p c2224 = true :=
  Snake9.LocalRup.prove_clause [c1575, c1580, c1558, c1554, c1563, c1602, c1607, c1581, c1584, c1566, c1564, c1578, c1568, c1556, c1559, c2211] c2224 (by decide) p (sat_cons (step1575 p h) (sat_cons (step1580 p h) (sat_cons (step1558 p h) (sat_cons (step1554 p h) (sat_cons (step1563 p h) (sat_cons (step1602 p h) (sat_cons (step1607 p h) (sat_cons (step1581 p h) (sat_cons (step1584 p h) (sat_cons (step1566 p h) (sat_cons (step1564 p h) (sat_cons (step1578 p h) (sat_cons (step1568 p h) (sat_cons (step1556 p h) (sat_cons (step1559 p h) (sat_cons (step2211 p h) (sat_nil p)))))))))))))))))
def c2225 : List Lit := [(1779, false), (1784, true), (1776, false), (113, true), (1832, true), (1811, false), (1713, true)]
theorem step2225 (p : Nat → Bool) (h : Constraints p) : clause p c2225 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1389, c1388, c1393, c1386, c334, c2040, c2041, c1746, c1526, c1527, c1542, c1522, c1632, c296, c1613, c2034, c2042, c573, c692, c1556, c1559, c1567] c2225 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1389 p h) (sat_cons (step1388 p h) (sat_cons (step1393 p h) (sat_cons (step1386 p h) (sat_cons (step334 p h) (sat_cons (step2040 p h) (sat_cons (step2041 p h) (sat_cons (step1746 p h) (sat_cons (step1526 p h) (sat_cons (step1527 p h) (sat_cons (step1542 p h) (sat_cons (step1522 p h) (sat_cons (step1632 p h) (sat_cons (step296 p h) (sat_cons (step1613 p h) (sat_cons (step2034 p h) (sat_cons (step2042 p h) (sat_cons (step573 p h) (sat_cons (step692 p h) (sat_cons (step1556 p h) (sat_cons (step1559 p h) (sat_cons (step1567 p h) (sat_nil p))))))))))))))))))))))))
def c2226 : List Lit := [(1779, true), (1774, true), (101, false), (29, false), (86, false)]
theorem step2226 (p : Nat → Bool) (h : Constraints p) : clause p c2226 = true :=
  Snake9.LocalRup.prove_clause [c1518, c2203, c500, c1509] c2226 (by decide) p (sat_cons (step1518 p h) (sat_cons (step2203 p h) (sat_cons (step500 p h) (sat_cons (step1509 p h) (sat_nil p)))))
end B112E034
