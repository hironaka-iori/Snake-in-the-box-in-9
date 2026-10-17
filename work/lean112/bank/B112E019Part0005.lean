import B112E019Part0004
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2126 : List Lit := [(196, false), (197, false)]
theorem step2126 (p : Nat → Bool) (h : Constraints p) : clause p c2126 = true :=
  Snake9.LocalRup.prove_clause [c1858, c1060] c2126 (by decide) p (sat_cons (step1858 p h) (sat_cons (step1060 p h) (sat_nil p)))
def c2127 : List Lit := [(377, false), (383, false)]
theorem step2127 (p : Nat → Bool) (h : Constraints p) : clause p c2127 = true :=
  Snake9.LocalRup.prove_clause [c1830, c1066] c2127 (by decide) p (sat_cons (step1830 p h) (sat_cons (step1066 p h) (sat_nil p)))
def c2128 : List Lit := [(371, false), (385, false)]
theorem step2128 (p : Nat → Bool) (h : Constraints p) : clause p c2128 = true :=
  Snake9.LocalRup.prove_clause [c1819, c1071] c2128 (by decide) p (sat_cons (step1819 p h) (sat_cons (step1071 p h) (sat_nil p)))
def c2129 : List Lit := [(201, false), (202, false)]
theorem step2129 (p : Nat → Bool) (h : Constraints p) : clause p c2129 = true :=
  Snake9.LocalRup.prove_clause [c1857, c1075] c2129 (by decide) p (sat_cons (step1857 p h) (sat_cons (step1075 p h) (sat_nil p)))
def c2130 : List Lit := [(393, false), (395, false)]
theorem step2130 (p : Nat → Bool) (h : Constraints p) : clause p c2130 = true :=
  Snake9.LocalRup.prove_clause [c1845, c1079] c2130 (by decide) p (sat_cons (step1845 p h) (sat_cons (step1079 p h) (sat_nil p)))
def c2131 : List Lit := [(401, false), (403, false)]
theorem step2131 (p : Nat → Bool) (h : Constraints p) : clause p c2131 = true :=
  Snake9.LocalRup.prove_clause [c1844, c1087] c2131 (by decide) p (sat_cons (step1844 p h) (sat_cons (step1087 p h) (sat_nil p)))
def c2132 : List Lit := [(407, false), (409, false)]
theorem step2132 (p : Nat → Bool) (h : Constraints p) : clause p c2132 = true :=
  Snake9.LocalRup.prove_clause [c1843, c1092] c2132 (by decide) p (sat_cons (step1843 p h) (sat_cons (step1092 p h) (sat_nil p)))
def c2133 : List Lit := [(405, false), (411, false)]
theorem step2133 (p : Nat → Bool) (h : Constraints p) : clause p c2133 = true :=
  Snake9.LocalRup.prove_clause [c1828, c1096] c2133 (by decide) p (sat_cons (step1828 p h) (sat_cons (step1096 p h) (sat_nil p)))
def c2134 : List Lit := [(399, false), (413, false)]
theorem step2134 (p : Nat → Bool) (h : Constraints p) : clause p c2134 = true :=
  Snake9.LocalRup.prove_clause [c1818, c1101] c2134 (by decide) p (sat_cons (step1818 p h) (sat_cons (step1101 p h) (sat_nil p)))
def c2135 : List Lit := [(387, false), (415, false)]
theorem step2135 (p : Nat → Bool) (h : Constraints p) : clause p c2135 = true :=
  Snake9.LocalRup.prove_clause [c1813, c1106] c2135 (by decide) p (sat_cons (step1813 p h) (sat_cons (step1106 p h) (sat_nil p)))
def c2136 : List Lit := [(421, false), (427, false)]
theorem step2136 (p : Nat → Bool) (h : Constraints p) : clause p c2136 = true :=
  Snake9.LocalRup.prove_clause [c1827, c1117] c2136 (by decide) p (sat_cons (step1827 p h) (sat_cons (step1117 p h) (sat_nil p)))
def c2137 : List Lit := [(431, false), (433, false)]
theorem step2137 (p : Nat → Bool) (h : Constraints p) : clause p c2137 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1122] c2137 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1122 p h) (sat_nil p)))
def c2138 : List Lit := [(435, false), (441, false)]
theorem step2138 (p : Nat → Bool) (h : Constraints p) : clause p c2138 = true :=
  Snake9.LocalRup.prove_clause [c1826, c1127] c2138 (by decide) p (sat_cons (step1826 p h) (sat_cons (step1127 p h) (sat_nil p)))
def c2139 : List Lit := [(429, false), (443, false)]
theorem step2139 (p : Nat → Bool) (h : Constraints p) : clause p c2139 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1132] c2139 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1132 p h) (sat_nil p)))
def c2140 : List Lit := [(451, false), (453, false)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c1840, c1140] c2140 (by decide) p (sat_cons (step1840 p h) (sat_cons (step1140 p h) (sat_nil p)))
def c2141 : List Lit := [(459, false), (461, false)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c1839, c1148] c2141 (by decide) p (sat_cons (step1839 p h) (sat_cons (step1148 p h) (sat_nil p)))
def c2142 : List Lit := [(463, false), (469, false)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c1824, c1155] c2142 (by decide) p (sat_cons (step1824 p h) (sat_cons (step1155 p h) (sat_nil p)))
def c2143 : List Lit := [(457, false), (471, false)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c1816, c1160] c2143 (by decide) p (sat_cons (step1816 p h) (sat_cons (step1160 p h) (sat_nil p)))
def c2144 : List Lit := [(445, false), (473, false)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c1812, c1165] c2144 (by decide) p (sat_cons (step1812 p h) (sat_cons (step1165 p h) (sat_nil p)))
def c2145 : List Lit := [(417, false), (475, false)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c1810, c1170] c2145 (by decide) p (sat_cons (step1810 p h) (sat_cons (step1170 p h) (sat_nil p)))
def c2146 : List Lit := [(359, false), (477, false)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c1175, c1173] c2146 (by decide) p (sat_cons (step1175 p h) (sat_cons (step1173 p h) (sat_nil p)))
def c2147 : List Lit := [(1574, false), (1591, true)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c1868, c1381] c2147 (by decide) p (sat_cons (step1868 p h) (sat_cons (step1381 p h) (sat_nil p)))
def c2148 : List Lit := [(1575, false), (1592, true)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c1868, c1382] c2148 (by decide) p (sat_cons (step1868 p h) (sat_cons (step1382 p h) (sat_nil p)))
def c2149 : List Lit := [(1576, false), (1593, true)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c1868, c1383] c2149 (by decide) p (sat_cons (step1868 p h) (sat_cons (step1383 p h) (sat_nil p)))
def c2150 : List Lit := [(1577, false), (1594, true)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c1868, c1384] c2150 (by decide) p (sat_cons (step1868 p h) (sat_cons (step1384 p h) (sat_nil p)))
def c2151 : List Lit := [(1578, false), (1595, true)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c1868, c1385] c2151 (by decide) p (sat_cons (step1868 p h) (sat_cons (step1385 p h) (sat_nil p)))
def c2152 : List Lit := [(1579, false), (1596, true)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c1868, c1386] c2152 (by decide) p (sat_cons (step1868 p h) (sat_cons (step1386 p h) (sat_nil p)))
def c2153 : List Lit := [(1643, false), (1652, true)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1517] c2153 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1517 p h) (sat_nil p)))
def c2154 : List Lit := [(1644, false), (1653, true)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1518] c2154 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1518 p h) (sat_nil p)))
def c2155 : List Lit := [(1645, false), (1654, true)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1519] c2155 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1519 p h) (sat_nil p)))
def c2156 : List Lit := [(1646, false), (1655, true)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1520] c2156 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1520 p h) (sat_nil p)))
def c2157 : List Lit := [(1647, false), (1656, true)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1521] c2157 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1521 p h) (sat_nil p)))
def c2158 : List Lit := [(1648, false), (1657, true)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1522] c2158 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1522 p h) (sat_nil p)))
def c2159 : List Lit := [(1649, false), (1658, true)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c1863, c1523] c2159 (by decide) p (sat_cons (step1863 p h) (sat_cons (step1523 p h) (sat_nil p)))
def c2160 : List Lit := [(1717, false), (1733, true)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c1864, c1682] c2160 (by decide) p (sat_cons (step1864 p h) (sat_cons (step1682 p h) (sat_nil p)))
def c2161 : List Lit := [(1718, false), (1734, true)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c1864, c1683] c2161 (by decide) p (sat_cons (step1864 p h) (sat_cons (step1683 p h) (sat_nil p)))
def c2162 : List Lit := [(1719, false), (1735, true)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c1864, c1684] c2162 (by decide) p (sat_cons (step1864 p h) (sat_cons (step1684 p h) (sat_nil p)))
def c2163 : List Lit := [(1591, false), (1739, false)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1741] c2163 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1741 p h) (sat_nil p)))
def c2164 : List Lit := [(1592, false), (1738, false)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1742] c2164 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1742 p h) (sat_nil p)))
def c2165 : List Lit := [(1593, false), (1737, false)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1743] c2165 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1743 p h) (sat_nil p)))
def c2166 : List Lit := [(1594, false), (1736, false)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1744] c2166 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1744 p h) (sat_nil p)))
def c2167 : List Lit := [(1595, false), (1735, false)]
theorem step2167 (p : Nat → Bool) (h : Constraints p) : clause p c2167 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1745] c2167 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1745 p h) (sat_nil p)))
def c2168 : List Lit := [(1596, false), (1734, false)]
theorem step2168 (p : Nat → Bool) (h : Constraints p) : clause p c2168 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1746] c2168 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1746 p h) (sat_nil p)))
def c2169 : List Lit := [(1597, false), (1733, false)]
theorem step2169 (p : Nat → Bool) (h : Constraints p) : clause p c2169 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1747] c2169 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1747 p h) (sat_nil p)))
def c2170 : List Lit := [(1598, false), (1732, false)]
theorem step2170 (p : Nat → Bool) (h : Constraints p) : clause p c2170 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1748] c2170 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1748 p h) (sat_nil p)))
def c2171 : List Lit := [(1599, false), (1731, false)]
theorem step2171 (p : Nat → Bool) (h : Constraints p) : clause p c2171 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1749] c2171 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1749 p h) (sat_nil p)))
def c2172 : List Lit := [(1600, false), (1730, false)]
theorem step2172 (p : Nat → Bool) (h : Constraints p) : clause p c2172 = true :=
  Snake9.LocalRup.prove_clause [c1751, c1750] c2172 (by decide) p (sat_cons (step1751 p h) (sat_cons (step1750 p h) (sat_nil p)))
def c2173 : List Lit := [(1622, true), (1607, true), (63, true), (99, false), (67, true)]
theorem step2173 (p : Nat → Bool) (h : Constraints p) : clause p c2173 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1431, c1450, c1944, c1439, c323, c1433, c1965] c2173 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1431 p h) (sat_cons (step1450 p h) (sat_cons (step1944 p h) (sat_cons (step1439 p h) (sat_cons (step323 p h) (sat_cons (step1433 p h) (sat_cons (step1965 p h) (sat_nil p)))))))))
def c2174 : List Lit := [(58, false), (86, true), (76, false)]
theorem step2174 (p : Nat → Bool) (h : Constraints p) : clause p c2174 = true :=
  Snake9.LocalRup.prove_clause [c2031, c1808, c274, c1011, c1010, c2116] c2174 (by decide) p (sat_cons (step2031 p h) (sat_cons (step1808 p h) (sat_cons (step274 p h) (sat_cons (step1011 p h) (sat_cons (step1010 p h) (sat_cons (step2116 p h) (sat_nil p)))))))
def c2175 : List Lit := [(1643, true), (48, false), (110, false), (87, false)]
theorem step2175 (p : Nat → Bool) (h : Constraints p) : clause p c2175 = true :=
  Snake9.LocalRup.prove_clause [c1490, c1494, c1482, c1484, c1468, c1479, c1476, c1477, c1465, c431, c701, c463, c469, c477] c2175 (by decide) p (sat_cons (step1490 p h) (sat_cons (step1494 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1468 p h) (sat_cons (step1479 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step1465 p h) (sat_cons (step431 p h) (sat_cons (step701 p h) (sat_cons (step463 p h) (sat_cons (step469 p h) (sat_cons (step477 p h) (sat_nil p)))))))))))))))
def c2176 : List Lit := [(89, false), (82, false), (105, true), (85, false), (86, true), (48, false), (79, true), (110, false)]
theorem step2176 (p : Nat → Bool) (h : Constraints p) : clause p c2176 = true :=
  Snake9.LocalRup.prove_clause [c701, c469, c1906] c2176 (by decide) p (sat_cons (step701 p h) (sat_cons (step469 p h) (sat_cons (step1906 p h) (sat_nil p))))
def c2177 : List Lit := [(1544, true), (1551, true), (1531, false), (109, true), (94, false), (48, false), (41, true)]
theorem step2177 (p : Nat → Bool) (h : Constraints p) : clause p c2177 = true :=
  Snake9.LocalRup.prove_clause [c1320, c1319, c1288, c1296, c1308, c1311, c1299, c1297, c1284, c1290, c1292, c172, c246, c221, c991, c992, c1002, c2114, c1022, c998, c2119, c995, c986, c988, c243, c983, c971, c229, c976, c964, c1281, c1282, c973, c963, c1286, c156, c142, c149] c2177 (by decide) p (sat_cons (step1320 p h) (sat_cons (step1319 p h) (sat_cons (step1288 p h) (sat_cons (step1296 p h) (sat_cons (step1308 p h) (sat_cons (step1311 p h) (sat_cons (step1299 p h) (sat_cons (step1297 p h) (sat_cons (step1284 p h) (sat_cons (step1290 p h) (sat_cons (step1292 p h) (sat_cons (step172 p h) (sat_cons (step246 p h) (sat_cons (step221 p h) (sat_cons (step991 p h) (sat_cons (step992 p h) (sat_cons (step1002 p h) (sat_cons (step2114 p h) (sat_cons (step1022 p h) (sat_cons (step998 p h) (sat_cons (step2119 p h) (sat_cons (step995 p h) (sat_cons (step986 p h) (sat_cons (step988 p h) (sat_cons (step243 p h) (sat_cons (step983 p h) (sat_cons (step971 p h) (sat_cons (step229 p h) (sat_cons (step976 p h) (sat_cons (step964 p h) (sat_cons (step1281 p h) (sat_cons (step1282 p h) (sat_cons (step973 p h) (sat_cons (step963 p h) (sat_cons (step1286 p h) (sat_cons (step156 p h) (sat_cons (step142 p h) (sat_cons (step149 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c2178 : List Lit := [(1504, false), (1509, true), (1517, true)]
theorem step2178 (p : Nat → Bool) (h : Constraints p) : clause p c2178 = true :=
  Snake9.LocalRup.prove_clause [c1236, c1240, c1261, c1867] c2178 (by decide) p (sat_cons (step1236 p h) (sat_cons (step1240 p h) (sat_cons (step1261 p h) (sat_cons (step1867 p h) (sat_nil p)))))
def c2179 : List Lit := [(1504, true), (98, false), (38, false)]
theorem step2179 (p : Nat → Bool) (h : Constraints p) : clause p c2179 = true :=
  Snake9.LocalRup.prove_clause [c1228, c1230, c1225, c1226, c1222, c1223, c157, c111, c119, c155, c135, c973, c965, c976, c971, c983, c2111] c2179 (by decide) p (sat_cons (step1228 p h) (sat_cons (step1230 p h) (sat_cons (step1225 p h) (sat_cons (step1226 p h) (sat_cons (step1222 p h) (sat_cons (step1223 p h) (sat_cons (step157 p h) (sat_cons (step111 p h) (sat_cons (step119 p h) (sat_cons (step155 p h) (sat_cons (step135 p h) (sat_cons (step973 p h) (sat_cons (step965 p h) (sat_cons (step976 p h) (sat_cons (step971 p h) (sat_cons (step983 p h) (sat_cons (step2111 p h) (sat_nil p))))))))))))))))))
def c2180 : List Lit := [(1488, true), (3, false), (58, false)]
theorem step2180 (p : Nat → Bool) (h : Constraints p) : clause p c2180 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1203, c1193, c1180, c1185, c1178, c7] c2180 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1203 p h) (sat_cons (step1193 p h) (sat_cons (step1180 p h) (sat_cons (step1185 p h) (sat_cons (step1178 p h) (sat_cons (step7 p h) (sat_nil p))))))))
def c2181 : List Lit := [(1517, true), (1488, false), (1504, false)]
theorem step2181 (p : Nat → Bool) (h : Constraints p) : clause p c2181 = true :=
  Snake9.LocalRup.prove_clause [c2178, c1256] c2181 (by decide) p (sat_cons (step2178 p h) (sat_cons (step1256 p h) (sat_nil p)))
def c2182 : List Lit := [(29, true), (31, false), (152, true), (39, true)]
theorem step2182 (p : Nat → Bool) (h : Constraints p) : clause p c2182 = true :=
  Snake9.LocalRup.prove_clause [c133, c135, c2001, c1759] c2182 (by decide) p (sat_cons (step133 p h) (sat_cons (step135 p h) (sat_cons (step2001 p h) (sat_cons (step1759 p h) (sat_nil p)))))
def c2183 : List Lit := [(27, false), (26, false), (1497, false), (175, true), (1531, false), (31, false), (1502, false), (1488, false), (1594, true)]
theorem step2183 (p : Nat → Bool) (h : Constraints p) : clause p c2183 = true :=
  Snake9.LocalRup.prove_clause [c111, c114, c1223, c1292, c1231, c1294, c1241, c1307, c1257, c1923, c1397] c2183 (by decide) p (sat_cons (step111 p h) (sat_cons (step114 p h) (sat_cons (step1223 p h) (sat_cons (step1292 p h) (sat_cons (step1231 p h) (sat_cons (step1294 p h) (sat_cons (step1241 p h) (sat_cons (step1307 p h) (sat_cons (step1257 p h) (sat_cons (step1923 p h) (sat_cons (step1397 p h) (sat_nil p))))))))))))
def c2184 : List Lit := [(1529, true), (37, false), (38, false)]
theorem step2184 (p : Nat → Bool) (h : Constraints p) : clause p c2184 = true :=
  Snake9.LocalRup.prove_clause [c1280, c1281, c151] c2184 (by decide) p (sat_cons (step1280 p h) (sat_cons (step1281 p h) (sat_cons (step151 p h) (sat_nil p))))
def c2185 : List Lit := [(1510, false), (27, true), (1529, false), (29, false), (175, true), (154, true), (164, true), (31, false), (11, true), (7, false), (1488, false), (1594, true)]
theorem step2185 (p : Nat → Bool) (h : Constraints p) : clause p c2185 = true :=
  Snake9.LocalRup.prove_clause [c1874, c1306, c1257, c1397, c1357, c1923, c1346, c1310, c1307, c1327, c1294, c1292, c1286, c141, c2005, c122, c1317, c1318, c1324, c1325, c1342, c1319, c1320, c1356, c172, c246, c1402, c184, c1263, c35, c1200, c1187, c1196] c2185 (by decide) p (sat_cons (step1874 p h) (sat_cons (step1306 p h) (sat_cons (step1257 p h) (sat_cons (step1397 p h) (sat_cons (step1357 p h) (sat_cons (step1923 p h) (sat_cons (step1346 p h) (sat_cons (step1310 p h) (sat_cons (step1307 p h) (sat_cons (step1327 p h) (sat_cons (step1294 p h) (sat_cons (step1292 p h) (sat_cons (step1286 p h) (sat_cons (step141 p h) (sat_cons (step2005 p h) (sat_cons (step122 p h) (sat_cons (step1317 p h) (sat_cons (step1318 p h) (sat_cons (step1324 p h) (sat_cons (step1325 p h) (sat_cons (step1342 p h) (sat_cons (step1319 p h) (sat_cons (step1320 p h) (sat_cons (step1356 p h) (sat_cons (step172 p h) (sat_cons (step246 p h) (sat_cons (step1402 p h) (sat_cons (step184 p h) (sat_cons (step1263 p h) (sat_cons (step35 p h) (sat_cons (step1200 p h) (sat_cons (step1187 p h) (sat_cons (step1196 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c2186 : List Lit := [(10, false), (43, false), (1486, true), (11, true), (7, false)]
theorem step2186 (p : Nat → Bool) (h : Constraints p) : clause p c2186 = true :=
  Snake9.LocalRup.prove_clause [c35, c36, c1187, c1189, c1197] c2186 (by decide) p (sat_cons (step35 p h) (sat_cons (step36 p h) (sat_cons (step1187 p h) (sat_cons (step1189 p h) (sat_cons (step1197 p h) (sat_nil p))))))
def c2187 : List Lit := [(1551, true), (53, false), (43, false)]
theorem step2187 (p : Nat → Bool) (h : Constraints p) : clause p c2187 = true :=
  Snake9.LocalRup.prove_clause [c1319, c1320, c246] c2187 (by decide) p (sat_cons (step1319 p h) (sat_cons (step1320 p h) (sat_cons (step246 p h) (sat_nil p))))
def c2188 : List Lit := [(9, false), (14, false), (12, false), (10, true), (1498, true), (299, true), (2, false)]
theorem step2188 (p : Nat → Bool) (h : Constraints p) : clause p c2188 = true :=
  Snake9.LocalRup.prove_clause [c960, c929, c928, c924, c921, c958, c956, c941, c938, c937, c31, c33, c64, c26, c90, c1220, c1214] c2188 (by decide) p (sat_cons (step960 p h) (sat_cons (step929 p h) (sat_cons (step928 p h) (sat_cons (step924 p h) (sat_cons (step921 p h) (sat_cons (step958 p h) (sat_cons (step956 p h) (sat_cons (step941 p h) (sat_cons (step938 p h) (sat_cons (step937 p h) (sat_cons (step31 p h) (sat_cons (step33 p h) (sat_cons (step64 p h) (sat_cons (step26 p h) (sat_cons (step90 p h) (sat_cons (step1220 p h) (sat_cons (step1214 p h) (sat_nil p))))))))))))))))))
def c2189 : List Lit := [(43, false), (46, true), (1498, true), (27, true), (317, false), (11, true), (7, false), (2, false), (1509, false), (1594, true)]
theorem step2189 (p : Nat → Bool) (h : Constraints p) : clause p c2189 = true :=
  Snake9.LocalRup.prove_clause [c983, c2111, c971, c964, c963, c1874, c1306, c1317, c1324, c1342, c1356, c1402, c1268, c1201, c986, c1027, c2120, c960, c930, c918, c915, c914, c929, c928, c924, c921, c958, c956, c943, c935, c2110, c981, c978, c1975, c2186, c25, c1952, c1980, c2188, c1959, c1262, c1397, c1357, c1346, c1327, c1325, c1318, c1319, c2187, c172, c184] c2189 (by decide) p (sat_cons (step983 p h) (sat_cons (step2111 p h) (sat_cons (step971 p h) (sat_cons (step964 p h) (sat_cons (step963 p h) (sat_cons (step1874 p h) (sat_cons (step1306 p h) (sat_cons (step1317 p h) (sat_cons (step1324 p h) (sat_cons (step1342 p h) (sat_cons (step1356 p h) (sat_cons (step1402 p h) (sat_cons (step1268 p h) (sat_cons (step1201 p h) (sat_cons (step986 p h) (sat_cons (step1027 p h) (sat_cons (step2120 p h) (sat_cons (step960 p h) (sat_cons (step930 p h) (sat_cons (step918 p h) (sat_cons (step915 p h) (sat_cons (step914 p h) (sat_cons (step929 p h) (sat_cons (step928 p h) (sat_cons (step924 p h) (sat_cons (step921 p h) (sat_cons (step958 p h) (sat_cons (step956 p h) (sat_cons (step943 p h) (sat_cons (step935 p h) (sat_cons (step2110 p h) (sat_cons (step981 p h) (sat_cons (step978 p h) (sat_cons (step1975 p h) (sat_cons (step2186 p h) (sat_cons (step25 p h) (sat_cons (step1952 p h) (sat_cons (step1980 p h) (sat_cons (step2188 p h) (sat_cons (step1959 p h) (sat_cons (step1262 p h) (sat_cons (step1397 p h) (sat_cons (step1357 p h) (sat_cons (step1346 p h) (sat_cons (step1327 p h) (sat_cons (step1325 p h) (sat_cons (step1318 p h) (sat_cons (step1319 p h) (sat_cons (step2187 p h) (sat_cons (step172 p h) (sat_cons (step184 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))
end B112E019
