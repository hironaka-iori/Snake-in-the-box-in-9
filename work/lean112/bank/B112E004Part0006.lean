import B112E004Part0005
namespace B112E004
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2118 : List Lit := [(1554, false), (1572, true)]
theorem step2118 (p : Nat → Bool) (h : Constraints p) : clause p c2118 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1341] c2118 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1341 p h) (sat_nil p)))
def c2119 : List Lit := [(1555, false), (1573, true)]
theorem step2119 (p : Nat → Bool) (h : Constraints p) : clause p c2119 = true :=
  Snake9.LocalRup.prove_clause [c1842, c1342] c2119 (by decide) p (sat_cons (step1842 p h) (sat_cons (step1342 p h) (sat_nil p)))
def c2120 : List Lit := [(1680, true), (1667, false)]
theorem step2120 (p : Nat → Bool) (h : Constraints p) : clause p c2120 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1577] c2120 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1577 p h) (sat_nil p)))
def c2121 : List Lit := [(1668, false), (1681, true)]
theorem step2121 (p : Nat → Bool) (h : Constraints p) : clause p c2121 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1581] c2121 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1581 p h) (sat_nil p)))
def c2122 : List Lit := [(1669, false), (1682, true)]
theorem step2122 (p : Nat → Bool) (h : Constraints p) : clause p c2122 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1586] c2122 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1586 p h) (sat_nil p)))
def c2123 : List Lit := [(1670, false), (1683, true)]
theorem step2123 (p : Nat → Bool) (h : Constraints p) : clause p c2123 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1590] c2123 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1590 p h) (sat_nil p)))
def c2124 : List Lit := [(1689, true), (1656, false)]
theorem step2124 (p : Nat → Bool) (h : Constraints p) : clause p c2124 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1597] c2124 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1597 p h) (sat_nil p)))
def c2125 : List Lit := [(1690, true), (1657, false)]
theorem step2125 (p : Nat → Bool) (h : Constraints p) : clause p c2125 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1603] c2125 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1603 p h) (sat_nil p)))
def c2126 : List Lit := [(1658, false), (1691, true)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1608] c2126 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1608 p h) (sat_nil p)))
def c2127 : List Lit := [(1659, false), (1692, true)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1613] c2127 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1613 p h) (sat_nil p)))
def c2128 : List Lit := [(1660, false), (1693, true)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c1814, c1617] c2128 (by decide) p (sat_cons (step1814 p h) (sat_cons (step1617 p h) (sat_nil p)))
def c2129 : List Lit := [(1564, false), (1717, false)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1666] c2129 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1666 p h) (sat_nil p)))
def c2130 : List Lit := [(1565, false), (1716, false)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1667] c2130 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1667 p h) (sat_nil p)))
def c2131 : List Lit := [(1566, false), (1715, false)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1668] c2131 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1668 p h) (sat_nil p)))
def c2132 : List Lit := [(1567, false), (1714, false)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1669] c2132 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1669 p h) (sat_nil p)))
def c2133 : List Lit := [(1568, false), (1713, false)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1670] c2133 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1670 p h) (sat_nil p)))
def c2134 : List Lit := [(1569, false), (1712, false)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1671] c2134 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1671 p h) (sat_nil p)))
def c2135 : List Lit := [(1570, false), (1711, false)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1672] c2135 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1672 p h) (sat_nil p)))
def c2136 : List Lit := [(1571, false), (1710, false)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1673] c2136 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1673 p h) (sat_nil p)))
def c2137 : List Lit := [(1572, false), (1709, false)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1674] c2137 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1674 p h) (sat_nil p)))
def c2138 : List Lit := [(1573, false), (1708, false)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1675] c2138 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1675 p h) (sat_nil p)))
def c2139 : List Lit := [(1574, false), (1707, false)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1676] c2139 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1676 p h) (sat_nil p)))
def c2140 : List Lit := [(1614, false), (1595, false), (1548, false), (1691, false), (109, false)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1829] c2140 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1829 p h) (sat_nil p)))
def c2141 : List Lit := [(1600, false), (1595, false), (1692, false), (1548, false), (109, false), (1612, false)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1839] c2141 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1839 p h) (sat_nil p)))
def c2142 : List Lit := [(1539, true), (53, true), (51, true), (55, false), (103, false)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c1254, c1261, c1899, c1278, c1282, c1264, c1898, c1255] c2142 (by decide) p (sat_cons (step1254 p h) (sat_cons (step1261 p h) (sat_cons (step1899 p h) (sat_cons (step1278 p h) (sat_cons (step1282 p h) (sat_cons (step1264 p h) (sat_cons (step1898 p h) (sat_cons (step1255 p h) (sat_nil p)))))))))
def c2143 : List Lit := [(1500, true), (38, false), (84, false)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1200, c154, c1937, c170] c2143 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1200 p h) (sat_cons (step154 p h) (sat_cons (step1937 p h) (sat_cons (step170 p h) (sat_nil p))))))
def c2144 : List Lit := [(98, false), (1505, false), (100, true), (51, false), (90, false), (1692, false), (1532, false), (1618, false), (89, true), (84, false), (1502, false)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c647, c2012, c2020, c2022, c221, c219, c201, c625, c359, c356, c337, c1382, c1098, c1212, c1389, c1242, c1110, c1101, c1217, c1391, c1245, c1112, c1125, c1228, c1404, c1272, c2094, c1314, c1473, c1346, c1646, c2133] c2144 (by decide) p (sat_cons (step647 p h) (sat_cons (step2012 p h) (sat_cons (step2020 p h) (sat_cons (step2022 p h) (sat_cons (step221 p h) (sat_cons (step219 p h) (sat_cons (step201 p h) (sat_cons (step625 p h) (sat_cons (step359 p h) (sat_cons (step356 p h) (sat_cons (step337 p h) (sat_cons (step1382 p h) (sat_cons (step1098 p h) (sat_cons (step1212 p h) (sat_cons (step1389 p h) (sat_cons (step1242 p h) (sat_cons (step1110 p h) (sat_cons (step1101 p h) (sat_cons (step1217 p h) (sat_cons (step1391 p h) (sat_cons (step1245 p h) (sat_cons (step1112 p h) (sat_cons (step1125 p h) (sat_cons (step1228 p h) (sat_cons (step1404 p h) (sat_cons (step1272 p h) (sat_cons (step2094 p h) (sat_cons (step1314 p h) (sat_cons (step1473 p h) (sat_cons (step1346 p h) (sat_cons (step1646 p h) (sat_cons (step2133 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c2145 : List Lit := [(56, false), (38, false), (42, false), (39, true), (51, false)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c396, c248, c1947] c2145 (by decide) p (sat_cons (step396 p h) (sat_cons (step248 p h) (sat_cons (step1947 p h) (sat_nil p))))
def c2146 : List Lit := [(59, false), (1585, true)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c1386, c1385, c1971, c509] c2146 (by decide) p (sat_cons (step1386 p h) (sat_cons (step1385 p h) (sat_cons (step1971 p h) (sat_cons (step509 p h) (sat_nil p)))))
def c2147 : List Lit := [(1514, true), (1507, false), (51, false)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c1213, c1222, c1226, c1804, c1216, c1202, c1207, c1848] c2147 (by decide) p (sat_cons (step1213 p h) (sat_cons (step1222 p h) (sat_cons (step1226 p h) (sat_cons (step1804 p h) (sat_cons (step1216 p h) (sat_cons (step1202 p h) (sat_cons (step1207 p h) (sat_cons (step1848 p h) (sat_nil p)))))))))
def c2148 : List Lit := [(1524, true), (50, true), (73, false)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c1245, c1247, c1242, c1239, c1240, c428, c277, c1964] c2148 (by decide) p (sat_cons (step1245 p h) (sat_cons (step1247 p h) (sat_cons (step1242 p h) (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step428 p h) (sat_cons (step277 p h) (sat_cons (step1964 p h) (sat_nil p)))))))))
def c2149 : List Lit := [(1520, true), (45, false), (52, false)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1240, c277] c2149 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1240 p h) (sat_cons (step277 p h) (sat_nil p))))
def c2150 : List Lit := [(1690, true), (100, false), (52, false)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c1873, c1859, c1515, c1500, c663] c2150 (by decide) p (sat_cons (step1873 p h) (sat_cons (step1859 p h) (sat_cons (step1515 p h) (sat_cons (step1500 p h) (sat_cons (step663 p h) (sat_nil p))))))
def c2151 : List Lit := [(1456, false), (1594, false), (1551, false), (1612, false), (1690, false)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c1439, c1471, c1632, c2137, c1365, c2095, c1357, c2136, c1638, c1472, c1444, c1194, c1420, c1774] c2151 (by decide) p (sat_cons (step1439 p h) (sat_cons (step1471 p h) (sat_cons (step1632 p h) (sat_cons (step2137 p h) (sat_cons (step1365 p h) (sat_cons (step2095 p h) (sat_cons (step1357 p h) (sat_cons (step2136 p h) (sat_cons (step1638 p h) (sat_cons (step1472 p h) (sat_cons (step1444 p h) (sat_cons (step1194 p h) (sat_cons (step1420 p h) (sat_cons (step1774 p h) (sat_nil p)))))))))))))))
def c2152 : List Lit := [(1618, true), (1681, true), (38, false), (1479, true)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c2121, c1773, c1799, c1136, c1774, c1420, c1449, c1445, c1421, c1432, c1827, c1550, c1552, c1555, c1578, c1878] c2152 (by decide) p (sat_cons (step2121 p h) (sat_cons (step1773 p h) (sat_cons (step1799 p h) (sat_cons (step1136 p h) (sat_cons (step1774 p h) (sat_cons (step1420 p h) (sat_cons (step1449 p h) (sat_cons (step1445 p h) (sat_cons (step1421 p h) (sat_cons (step1432 p h) (sat_cons (step1827 p h) (sat_cons (step1550 p h) (sat_cons (step1552 p h) (sat_cons (step1555 p h) (sat_cons (step1578 p h) (sat_cons (step1878 p h) (sat_nil p)))))))))))))))))
def c2153 : List Lit := [(1680, true), (1614, true), (38, false)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c2120, c1822, c1552, c1554, c1550, c1546, c1547, c1830, c2041, c720] c2153 (by decide) p (sat_cons (step2120 p h) (sat_cons (step1822 p h) (sat_cons (step1552 p h) (sat_cons (step1554 p h) (sat_cons (step1550 p h) (sat_cons (step1546 p h) (sat_cons (step1547 p h) (sat_cons (step1830 p h) (sat_cons (step2041 p h) (sat_cons (step720 p h) (sat_nil p)))))))))))
def c2154 : List Lit := [(51, false), (52, false), (100, true), (89, true), (90, false), (98, false)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c647, c356, c2022] c2154 (by decide) p (sat_cons (step647 p h) (sat_cons (step356 p h) (sat_cons (step2022 p h) (sat_nil p))))
def c2155 : List Lit := [(1589, false), (1620, false), (1691, false), (1514, false), (53, true), (51, true), (55, false), (103, false)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.LocalRup.prove_clause [c2142, c1301, c2113, c2132, c1655, c1475, c1399, c1404, c1468, c1380, c1651, c1377, c2133, c1789, c2114, c1900, c1302] c2155 (by decide) p (sat_cons (step2142 p h) (sat_cons (step1301 p h) (sat_cons (step2113 p h) (sat_cons (step2132 p h) (sat_cons (step1655 p h) (sat_cons (step1475 p h) (sat_cons (step1399 p h) (sat_cons (step1404 p h) (sat_cons (step1468 p h) (sat_cons (step1380 p h) (sat_cons (step1651 p h) (sat_cons (step1377 p h) (sat_cons (step2133 p h) (sat_cons (step1789 p h) (sat_cons (step2114 p h) (sat_cons (step1900 p h) (sat_cons (step1302 p h) (sat_nil p))))))))))))))))))
def c2156 : List Lit := [(1589, true), (1541, true), (53, true), (1523, false), (55, false), (103, false)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c1391, c1393, c1388, c2146, c445, c435, c1257, c1255, c1239, c1265, c1249, c1284] c2156 (by decide) p (sat_cons (step1391 p h) (sat_cons (step1393 p h) (sat_cons (step1388 p h) (sat_cons (step2146 p h) (sat_cons (step445 p h) (sat_cons (step435 p h) (sat_cons (step1257 p h) (sat_cons (step1255 p h) (sat_cons (step1239 p h) (sat_cons (step1265 p h) (sat_cons (step1249 p h) (sat_cons (step1284 p h) (sat_nil p)))))))))))))
def c2157 : List Lit := [(73, false), (1541, true), (1523, false), (1530, false), (53, true), (55, false), (103, false)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c445, c435, c1255, c1239, c1265, c1249, c1284] c2157 (by decide) p (sat_cons (step445 p h) (sat_cons (step435 p h) (sat_cons (step1255 p h) (sat_cons (step1239 p h) (sat_cons (step1265 p h) (sat_cons (step1249 p h) (sat_cons (step1284 p h) (sat_nil p))))))))
def c2158 : List Lit := [(39, false), (61, false), (1505, false), (90, false), (1515, true)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c220, c211, c1211, c1200, c1216, c1202, c1227] c2158 (by decide) p (sat_cons (step220 p h) (sat_cons (step211 p h) (sat_cons (step1211 p h) (sat_cons (step1200 p h) (sat_cons (step1216 p h) (sat_cons (step1202 p h) (sat_cons (step1227 p h) (sat_nil p))))))))
def c2159 : List Lit := [(1523, false), (53, true), (55, false), (103, false), (1530, false), (1541, true), (46, true)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c1254, c1262, c1288, c1240, c1249, c1252, c1284, c1241, c1265, c434, c1255] c2159 (by decide) p (sat_cons (step1254 p h) (sat_cons (step1262 p h) (sat_cons (step1288 p h) (sat_cons (step1240 p h) (sat_cons (step1249 p h) (sat_cons (step1252 p h) (sat_cons (step1284 p h) (sat_cons (step1241 p h) (sat_cons (step1265 p h) (sat_cons (step434 p h) (sat_cons (step1255 p h) (sat_nil p))))))))))))
def c2160 : List Lit := [(53, true), (55, false), (103, false), (51, true), (1530, false), (1541, true), (46, true)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c1243, c2159, c1244, c440, c429, c1255, c1241, c1265, c1251, c1284] c2160 (by decide) p (sat_cons (step1243 p h) (sat_cons (step2159 p h) (sat_cons (step1244 p h) (sat_cons (step440 p h) (sat_cons (step429 p h) (sat_cons (step1255 p h) (sat_cons (step1241 p h) (sat_cons (step1265 p h) (sat_cons (step1251 p h) (sat_cons (step1284 p h) (sat_nil p)))))))))))
def c2161 : List Lit := [(55, false), (103, false), (46, true), (51, true), (1530, false), (1541, true)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c2160, c438, c443, c432, c1244, c1253, c1241, c1262, c1252, c1288] c2161 (by decide) p (sat_cons (step2160 p h) (sat_cons (step438 p h) (sat_cons (step443 p h) (sat_cons (step432 p h) (sat_cons (step1244 p h) (sat_cons (step1253 p h) (sat_cons (step1241 p h) (sat_cons (step1262 p h) (sat_cons (step1252 p h) (sat_cons (step1288 p h) (sat_nil p)))))))))))
def c2162 : List Lit := [(1488, true), (9, true), (50, true), (32, false), (15, true)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c1109, c1112, c2089, c2094, c1162, c1799, c1121, c1125, c1135, c1136, c1113, c1115, c1101, c1926, c1111, c1107, c1098, c1857, c1915, c8] c2162 (by decide) p (sat_cons (step1109 p h) (sat_cons (step1112 p h) (sat_cons (step2089 p h) (sat_cons (step2094 p h) (sat_cons (step1162 p h) (sat_cons (step1799 p h) (sat_cons (step1121 p h) (sat_cons (step1125 p h) (sat_cons (step1135 p h) (sat_cons (step1136 p h) (sat_cons (step1113 p h) (sat_cons (step1115 p h) (sat_cons (step1101 p h) (sat_cons (step1926 p h) (sat_cons (step1111 p h) (sat_cons (step1107 p h) (sat_cons (step1098 p h) (sat_cons (step1857 p h) (sat_cons (step1915 p h) (sat_cons (step8 p h) (sat_nil p)))))))))))))))))))))
def c2163 : List Lit := [(1657, true), (90, false), (102, true), (1649, false)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c1511, c1520, c1527, c1531, c1523, c1503, c1505, c1513, c1500, c1497, c597, c1896] c2163 (by decide) p (sat_cons (step1511 p h) (sat_cons (step1520 p h) (sat_cons (step1527 p h) (sat_cons (step1531 p h) (sat_cons (step1523 p h) (sat_cons (step1503 p h) (sat_cons (step1505 p h) (sat_cons (step1513 p h) (sat_cons (step1500 p h) (sat_cons (step1497 p h) (sat_cons (step597 p h) (sat_cons (step1896 p h) (sat_nil p)))))))))))))
def c2164 : List Lit := [(98, false), (91, false), (90, false), (94, true), (50, true), (100, true)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c597, c2023] c2164 (by decide) p (sat_cons (step597 p h) (sat_cons (step2023 p h) (sat_nil p)))
def c2165 : List Lit := [(1648, false), (1643, false), (1680, false), (1712, true), (1594, false), (103, true), (1612, false)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c1439, c1471, c1635, c1614, c1533, c1515, c1523, c1524, c1532, c1516, c1609, c1610, c1821, c1640, c2121, c1472, c1555, c1444, c1550, c1420, c1824] c2165 (by decide) p (sat_cons (step1439 p h) (sat_cons (step1471 p h) (sat_cons (step1635 p h) (sat_cons (step1614 p h) (sat_cons (step1533 p h) (sat_cons (step1515 p h) (sat_cons (step1523 p h) (sat_cons (step1524 p h) (sat_cons (step1532 p h) (sat_cons (step1516 p h) (sat_cons (step1609 p h) (sat_cons (step1610 p h) (sat_cons (step1821 p h) (sat_cons (step1640 p h) (sat_cons (step2121 p h) (sat_cons (step1472 p h) (sat_cons (step1555 p h) (sat_cons (step1444 p h) (sat_cons (step1550 p h) (sat_cons (step1420 p h) (sat_cons (step1824 p h) (sat_nil p))))))))))))))))))))))
def c2166 : List Lit := [(1681, true), (1665, false), (1611, true), (38, false)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c1552, c2121, c1578, c1555, c1878] c2166 (by decide) p (sat_cons (step1552 p h) (sat_cons (step2121 p h) (sat_cons (step1578 p h) (sat_cons (step1555 p h) (sat_cons (step1878 p h) (sat_nil p))))))
def c2167 : List Lit := [(1614, false), (1657, false), (1712, true), (1594, false)]
theorem step2167 (p : Nat → Bool) (h : Constraints p) : clause p c2167 = true :=
  Snake9.LocalRup.prove_clause [c2125, c1650, c1474, c1441, c1446, c1473, c1420, c1645, c1824, c1604, c1550, c2120, c1552] c2167 (by decide) p (sat_cons (step2125 p h) (sat_cons (step1650 p h) (sat_cons (step1474 p h) (sat_cons (step1441 p h) (sat_cons (step1446 p h) (sat_cons (step1473 p h) (sat_cons (step1420 p h) (sat_cons (step1645 p h) (sat_cons (step1824 p h) (sat_cons (step1604 p h) (sat_cons (step1550 p h) (sat_cons (step2120 p h) (sat_cons (step1552 p h) (sat_nil p))))))))))))))
def c2168 : List Lit := [(97, false), (1611, true), (88, false), (38, false)]
theorem step2168 (p : Nat → Bool) (h : Constraints p) : clause p c2168 = true :=
  Snake9.LocalRup.prove_clause [c582, c584, c1430] c2168 (by decide) p (sat_cons (step582 p h) (sat_cons (step584 p h) (sat_cons (step1430 p h) (sat_nil p))))
def c2169 : List Lit := [(1614, true), (1693, true), (1608, false), (88, false), (1647, false), (1550, false), (1593, false), (39, true), (1649, false), (38, false)]
theorem step2169 (p : Nat → Bool) (h : Constraints p) : clause p c2169 = true :=
  Snake9.LocalRup.prove_clause [c1815, c1434, c2153, c1435, c2168, c1833, c1609, c1610, c1902, c2166, c1550] c2169 (by decide) p (sat_cons (step1815 p h) (sat_cons (step1434 p h) (sat_cons (step2153 p h) (sat_cons (step1435 p h) (sat_cons (step2168 p h) (sat_cons (step1833 p h) (sat_cons (step1609 p h) (sat_cons (step1610 p h) (sat_cons (step1902 p h) (sat_cons (step2166 p h) (sat_cons (step1550 p h) (sat_nil p))))))))))))
def c2170 : List Lit := [(1611, true), (1692, true), (88, false), (1647, false), (39, true), (1649, false), (38, false)]
theorem step2170 (p : Nat → Bool) (h : Constraints p) : clause p c2170 = true :=
  Snake9.LocalRup.prove_clause [c1783, c2168, c1546, c1833, c1554, c1609, c2120] c2170 (by decide) p (sat_cons (step1783 p h) (sat_cons (step2168 p h) (sat_cons (step1546 p h) (sat_cons (step1833 p h) (sat_cons (step1554 p h) (sat_cons (step1609 p h) (sat_cons (step2120 p h) (sat_nil p))))))))
def c2171 : List Lit := [(1659, true), (1653, false), (1650, false), (97, true), (39, true)]
theorem step2171 (p : Nat → Bool) (h : Constraints p) : clause p c2171 = true :=
  Snake9.LocalRup.prove_clause [c1501, c1503, c1533, c1537, c1524, c1795] c2171 (by decide) p (sat_cons (step1501 p h) (sat_cons (step1503 p h) (sat_cons (step1533 p h) (sat_cons (step1537 p h) (sat_cons (step1524 p h) (sat_cons (step1795 p h) (sat_nil p)))))))
def c2172 : List Lit := [(1595, true), (1530, true), (51, false), (42, false)]
theorem step2172 (p : Nat → Bool) (h : Constraints p) : clause p c2172 = true :=
  Snake9.LocalRup.prove_clause [c1789, c1377, c1380, c1257, c2146, c1393, c1408, c1405, c1383, c1885] c2172 (by decide) p (sat_cons (step1789 p h) (sat_cons (step1377 p h) (sat_cons (step1380 p h) (sat_cons (step1257 p h) (sat_cons (step2146 p h) (sat_cons (step1393 p h) (sat_cons (step1408 p h) (sat_cons (step1405 p h) (sat_cons (step1383 p h) (sat_cons (step1885 p h) (sat_nil p)))))))))))
def c2173 : List Lit := [(1455, false), (1595, false), (1547, false), (1614, false), (1692, false)]
theorem step2173 (p : Nat → Bool) (h : Constraints p) : clause p c2173 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1480, c1652, c2132, c1353, c2094, c1189, c1344, c1774, c2131, c1420, c1656, c1446, c1481] c2173 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1480 p h) (sat_cons (step1652 p h) (sat_cons (step2132 p h) (sat_cons (step1353 p h) (sat_cons (step2094 p h) (sat_cons (step1189 p h) (sat_cons (step1344 p h) (sat_cons (step1774 p h) (sat_cons (step2131 p h) (sat_cons (step1420 p h) (sat_cons (step1656 p h) (sat_cons (step1446 p h) (sat_cons (step1481 p h) (sat_nil p)))))))))))))))
def c2174 : List Lit := [(1548, false), (1692, false), (1595, false), (1614, false)]
theorem step2174 (p : Nat → Bool) (h : Constraints p) : clause p c2174 = true :=
  Snake9.LocalRup.prove_clause [c1441, c1480, c1652, c2132, c2112, c1345, c2131, c2089, c1656, c1774, c1481, c1420, c1446] c2174 (by decide) p (sat_cons (step1441 p h) (sat_cons (step1480 p h) (sat_cons (step1652 p h) (sat_cons (step2132 p h) (sat_cons (step2112 p h) (sat_cons (step1345 p h) (sat_cons (step2131 p h) (sat_cons (step2089 p h) (sat_cons (step1656 p h) (sat_cons (step1774 p h) (sat_cons (step1481 p h) (sat_cons (step1420 p h) (sat_cons (step1446 p h) (sat_nil p))))))))))))))
def c2175 : List Lit := [(48, false), (55, false), (1529, true), (15, false)]
theorem step2175 (p : Nat → Bool) (h : Constraints p) : clause p c2175 = true :=
  Snake9.LocalRup.prove_clause [c412, c413, c1255] c2175 (by decide) p (sat_cons (step412 p h) (sat_cons (step413 p h) (sat_cons (step1255 p h) (sat_nil p))))
def c2176 : List Lit := [(55, false), (1538, true), (1530, false), (15, false)]
theorem step2176 (p : Nat → Bool) (h : Constraints p) : clause p c2176 = true :=
  Snake9.LocalRup.prove_clause [c1269, c1265, c1259, c1277, c2175, c1239, c1247, c1248, c1273, c1242, c1262, c416, c1254] c2176 (by decide) p (sat_cons (step1269 p h) (sat_cons (step1265 p h) (sat_cons (step1259 p h) (sat_cons (step1277 p h) (sat_cons (step2175 p h) (sat_cons (step1239 p h) (sat_cons (step1247 p h) (sat_cons (step1248 p h) (sat_cons (step1273 p h) (sat_cons (step1242 p h) (sat_cons (step1262 p h) (sat_cons (step416 p h) (sat_cons (step1254 p h) (sat_nil p))))))))))))))
def c2177 : List Lit := [(12, true), (1455, true)]
theorem step2177 (p : Nat → Bool) (h : Constraints p) : clause p c2177 = true :=
  Snake9.LocalRup.prove_clause [c1128, c1121, c1786, c1797] c2177 (by decide) p (sat_cons (step1128 p h) (sat_cons (step1121 p h) (sat_cons (step1786 p h) (sat_cons (step1797 p h) (sat_nil p)))))
def c2178 : List Lit := [(1538, true), (1530, false), (12, false), (15, false), (51, false)]
theorem step2178 (p : Nat → Bool) (h : Constraints p) : clause p c2178 = true :=
  Snake9.LocalRup.prove_clause [c1269, c1265, c2176, c1918, c56, c1253, c1255, c1262, c1273, c1245, c1247, c1242, c2149, c354, c1964] c2178 (by decide) p (sat_cons (step1269 p h) (sat_cons (step1265 p h) (sat_cons (step2176 p h) (sat_cons (step1918 p h) (sat_cons (step56 p h) (sat_cons (step1253 p h) (sat_cons (step1255 p h) (sat_cons (step1262 p h) (sat_cons (step1273 p h) (sat_cons (step1245 p h) (sat_cons (step1247 p h) (sat_cons (step1242 p h) (sat_cons (step2149 p h) (sat_cons (step354 p h) (sat_cons (step1964 p h) (sat_nil p))))))))))))))))
def c2179 : List Lit := [(3, true), (121, true), (1444, true)]
theorem step2179 (p : Nat → Bool) (h : Constraints p) : clause p c2179 = true :=
  Snake9.LocalRup.prove_clause [c1099, c1, c1104, c1904] c2179 (by decide) p (sat_cons (step1099 p h) (sat_cons (step1 p h) (sat_cons (step1104 p h) (sat_cons (step1904 p h) (sat_nil p)))))
def c2180 : List Lit := [(82, false), (1468, true), (21, true), (13, false), (137, true), (143, true), (153, true)]
theorem step2180 (p : Nat → Bool) (h : Constraints p) : clause p c2180 = true :=
  Snake9.LocalRup.prove_clause [c2001, c112, c117, c64, c150, c1921, c1926, c1856] c2180 (by decide) p (sat_cons (step2001 p h) (sat_cons (step112 p h) (sat_cons (step117 p h) (sat_cons (step64 p h) (sat_cons (step150 p h) (sat_cons (step1921 p h) (sat_cons (step1926 p h) (sat_cons (step1856 p h) (sat_nil p)))))))))
def c2181 : List Lit := [(32, true), (1569, true), (1509, false), (1500, false), (21, true), (143, true), (153, true), (1538, false)]
theorem step2181 (p : Nat → Bool) (h : Constraints p) : clause p c2181 = true :=
  Snake9.LocalRup.prove_clause [c150, c1205, c1926, c1231, c81, c1137, c1308, c1922, c1355, c1132, c2090, c1142, c2087] c2181 (by decide) p (sat_cons (step150 p h) (sat_cons (step1205 p h) (sat_cons (step1926 p h) (sat_cons (step1231 p h) (sat_cons (step81 p h) (sat_cons (step1137 p h) (sat_cons (step1308 p h) (sat_cons (step1922 p h) (sat_cons (step1355 p h) (sat_cons (step1132 p h) (sat_cons (step2090 p h) (sat_cons (step1142 p h) (sat_cons (step2087 p h) (sat_nil p))))))))))))))
end B112E004
