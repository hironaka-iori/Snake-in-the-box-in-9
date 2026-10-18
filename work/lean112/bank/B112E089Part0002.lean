import B112E089Part0001
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2140 : List Lit := [(1592, true), (14, false), (171, true)]
theorem step2140 (p : Nat → Bool) (h : Constraints p) : clause p c2140 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1469, c1465, c1461, c1462, c318, c326, c315] c2140 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step318 p h) (sat_cons (step326 p h) (sat_cons (step315 p h) (sat_nil p)))))))))
def c2141 : List Lit := [(48, true), (47, false), (50, false), (49, true)]
theorem step2141 (p : Nat → Bool) (h : Constraints p) : clause p c2141 = true :=
  Snake9.LocalRup.prove_clause [c2036, c352, c315, c1130, c1126, c1132, c1128, c1137] c2141 (by decide) p (sat_cons (step2036 p h) (sat_cons (step352 p h) (sat_cons (step315 p h) (sat_cons (step1130 p h) (sat_cons (step1126 p h) (sat_cons (step1132 p h) (sat_cons (step1128 p h) (sat_cons (step1137 p h) (sat_nil p)))))))))
def c2142 : List Lit := [(39, false), (1598, true), (163, true), (38, true), (49, true)]
theorem step2142 (p : Nat → Bool) (h : Constraints p) : clause p c2142 = true :=
  Snake9.LocalRup.prove_clause [c1479, c1478, c447, c220] c2142 (by decide) p (sat_cons (step1479 p h) (sat_cons (step1478 p h) (sat_cons (step447 p h) (sat_cons (step220 p h) (sat_nil p)))))
def c2143 : List Lit := [(105, true), (97, true), (98, false), (104, false)]
theorem step2143 (p : Nat → Bool) (h : Constraints p) : clause p c2143 = true :=
  Snake9.LocalRup.prove_clause [c2021, c834, c866, c1229, c1240, c1232, c1242, c1234, c1248, c1253] c2143 (by decide) p (sat_cons (step2021 p h) (sat_cons (step834 p h) (sat_cons (step866 p h) (sat_cons (step1229 p h) (sat_cons (step1240 p h) (sat_cons (step1232 p h) (sat_cons (step1242 p h) (sat_cons (step1234 p h) (sat_cons (step1248 p h) (sat_cons (step1253 p h) (sat_nil p)))))))))))
def c2144 : List Lit := [(475, true), (1738, true), (107, false), (122, true), (120, false)]
theorem step2144 (p : Nat → Bool) (h : Constraints p) : clause p c2144 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1272, c1267, c1266, c2091, c2090, c897] c2144 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1272 p h) (sat_cons (step1267 p h) (sat_cons (step1266 p h) (sat_cons (step2091 p h) (sat_cons (step2090 p h) (sat_cons (step897 p h) (sat_nil p))))))))
def c2145 : List Lit := [(1687, true), (1670, false)]
theorem step2145 (p : Nat → Bool) (h : Constraints p) : clause p c2145 = true :=
  Snake9.LocalRup.prove_clause [c1655, c1684, c1680, c1656, c1669, c1651, c2097] c2145 (by decide) p (sat_cons (step1655 p h) (sat_cons (step1684 p h) (sat_cons (step1680 p h) (sat_cons (step1656 p h) (sat_cons (step1669 p h) (sat_cons (step1651 p h) (sat_cons (step2097 p h) (sat_nil p))))))))
def c2146 : List Lit := [(62, false), (76, false), (121, true), (107, false), (120, false)]
theorem step2146 (p : Nat → Bool) (h : Constraints p) : clause p c2146 = true :=
  Snake9.LocalRup.prove_clause [c895, c711, c941] c2146 (by decide) p (sat_cons (step895 p h) (sat_cons (step711 p h) (sat_cons (step941 p h) (sat_nil p))))
def c2147 : List Lit := [(1650, true), (68, false), (45, false)]
theorem step2147 (p : Nat → Bool) (h : Constraints p) : clause p c2147 = true :=
  Snake9.LocalRup.prove_clause [c1606, c1607, c612] c2147 (by decide) p (sat_cons (step1606 p h) (sat_cons (step1607 p h) (sat_cons (step612 p h) (sat_nil p))))
def c2148 : List Lit := [(69, true), (1666, true), (68, false), (45, false), (62, true)]
theorem step2148 (p : Nat → Bool) (h : Constraints p) : clause p c2148 = true :=
  Snake9.LocalRup.prove_clause [c2147, c1612, c1639, c1625, c1614, c1622, c1643, c1613, c1616, c615, c613, c1608] c2148 (by decide) p (sat_cons (step2147 p h) (sat_cons (step1612 p h) (sat_cons (step1639 p h) (sat_cons (step1625 p h) (sat_cons (step1614 p h) (sat_cons (step1622 p h) (sat_cons (step1643 p h) (sat_cons (step1613 p h) (sat_cons (step1616 p h) (sat_cons (step615 p h) (sat_cons (step613 p h) (sat_cons (step1608 p h) (sat_nil p)))))))))))))
def c2149 : List Lit := [(1598, true), (49, true), (39, false), (42, false), (163, true)]
theorem step2149 (p : Nat → Bool) (h : Constraints p) : clause p c2149 = true :=
  Snake9.LocalRup.prove_clause [c1478, c1479, c447, c208, c221] c2149 (by decide) p (sat_cons (step1478 p h) (sat_cons (step1479 p h) (sat_cons (step447 p h) (sat_cons (step208 p h) (sat_cons (step221 p h) (sat_nil p))))))
def c2150 : List Lit := [(60, false), (1599, true), (39, false), (67, false)]
theorem step2150 (p : Nat → Bool) (h : Constraints p) : clause p c2150 = true :=
  Snake9.LocalRup.prove_clause [c451, c448, c1480] c2150 (by decide) p (sat_cons (step451 p h) (sat_cons (step448 p h) (sat_cons (step1480 p h) (sat_nil p))))
def c2151 : List Lit := [(415, true), (1679, true), (86, true), (84, true)]
theorem step2151 (p : Nat → Bool) (h : Constraints p) : clause p c2151 = true :=
  Snake9.LocalRup.prove_clause [c1209, c1210, c1208, c1206, c782, c778, c1663] c2151 (by decide) p (sat_cons (step1209 p h) (sat_cons (step1210 p h) (sat_cons (step1208 p h) (sat_cons (step1206 p h) (sat_cons (step782 p h) (sat_cons (step778 p h) (sat_cons (step1663 p h) (sat_nil p))))))))
def c2152 : List Lit := [(1750, true), (1733, false)]
theorem step2152 (p : Nat → Bool) (h : Constraints p) : clause p c2152 = true :=
  Snake9.LocalRup.prove_clause [c1805, c1831, c1828, c1806, c2138] c2152 (by decide) p (sat_cons (step1805 p h) (sat_cons (step1831 p h) (sat_cons (step1828 p h) (sat_cons (step1806 p h) (sat_cons (step2138 p h) (sat_nil p))))))
def c2153 : List Lit := [(1745, true), (72, false), (243, true)]
theorem step2153 (p : Nat → Bool) (h : Constraints p) : clause p c2153 = true :=
  Snake9.LocalRup.prove_clause [c1817, c1819, c1814, c1815, c1812, c968, c920, c938] c2153 (by decide) p (sat_cons (step1817 p h) (sat_cons (step1819 p h) (sat_cons (step1814 p h) (sat_cons (step1815 p h) (sat_cons (step1812 p h) (sat_cons (step968 p h) (sat_cons (step920 p h) (sat_cons (step938 p h) (sat_nil p)))))))))
def c2154 : List Lit := [(61, false), (1651, true), (68, false), (115, false)]
theorem step2154 (p : Nat → Bool) (h : Constraints p) : clause p c2154 = true :=
  Snake9.LocalRup.prove_clause [c620, c622, c1608] c2154 (by decide) p (sat_cons (step620 p h) (sat_cons (step622 p h) (sat_cons (step1608 p h) (sat_nil p))))
def c2155 : List Lit := [(1592, true), (39, false)]
theorem step2155 (p : Nat → Bool) (h : Constraints p) : clause p c2155 = true :=
  Snake9.LocalRup.prove_clause [c1467, c1469, c1465, c1461, c1462, c318, c332, c2141] c2155 (by decide) p (sat_cons (step1467 p h) (sat_cons (step1469 p h) (sat_cons (step1465 p h) (sat_cons (step1461 p h) (sat_cons (step1462 p h) (sat_cons (step318 p h) (sat_cons (step332 p h) (sat_cons (step2141 p h) (sat_nil p)))))))))
def c2156 : List Lit := [(50, false), (47, false), (46, false), (39, false)]
theorem step2156 (p : Nat → Bool) (h : Constraints p) : clause p c2156 = true :=
  Snake9.LocalRup.prove_clause [c318, c332, c2141] c2156 (by decide) p (sat_cons (step318 p h) (sat_cons (step332 p h) (sat_cons (step2141 p h) (sat_nil p))))
def c2157 : List Lit := [(51, false), (54, false), (1576, true)]
theorem step2157 (p : Nat → Bool) (h : Constraints p) : clause p c2157 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1428, c2082, c361] c2157 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1428 p h) (sat_cons (step2082 p h) (sat_cons (step361 p h) (sat_nil p)))))
def c2158 : List Lit := [(21, true), (20, true), (22, false), (60, true), (1568, true)]
theorem step2158 (p : Nat → Bool) (h : Constraints p) : clause p c2158 = true :=
  Snake9.LocalRup.prove_clause [c2026, c2015, c984, c116, c1067, c1068, c1069, c1086, c1087, c1088, c1080, c1163, c1077, c1157, c1076, c1123, c174, c1100, c176, c1095, c2086] c2158 (by decide) p (sat_cons (step2026 p h) (sat_cons (step2015 p h) (sat_cons (step984 p h) (sat_cons (step116 p h) (sat_cons (step1067 p h) (sat_cons (step1068 p h) (sat_cons (step1069 p h) (sat_cons (step1086 p h) (sat_cons (step1087 p h) (sat_cons (step1088 p h) (sat_cons (step1080 p h) (sat_cons (step1163 p h) (sat_cons (step1077 p h) (sat_cons (step1157 p h) (sat_cons (step1076 p h) (sat_cons (step1123 p h) (sat_cons (step174 p h) (sat_cons (step1100 p h) (sat_cons (step176 p h) (sat_cons (step1095 p h) (sat_cons (step2086 p h) (sat_nil p))))))))))))))))))))))
def c2159 : List Lit := [(1529, true), (60, true), (57, false), (1568, true), (27, true), (67, true)]
theorem step2159 (p : Nat → Bool) (h : Constraints p) : clause p c2159 = true :=
  Snake9.LocalRup.prove_clause [c984, c2015, c982, c1345, c1347, c1342, c1343, c1339, c1340, c100, c2158, c103, c104, c176, c2086, c1095, c1100, c1123, c1157, c1163, c1088, c1090, c1086, c1061, c1069, c1056, c1068, c1052, c1067, c1049, c115, c82, c156, c86] c2159 (by decide) p (sat_cons (step984 p h) (sat_cons (step2015 p h) (sat_cons (step982 p h) (sat_cons (step1345 p h) (sat_cons (step1347 p h) (sat_cons (step1342 p h) (sat_cons (step1343 p h) (sat_cons (step1339 p h) (sat_cons (step1340 p h) (sat_cons (step100 p h) (sat_cons (step2158 p h) (sat_cons (step103 p h) (sat_cons (step104 p h) (sat_cons (step176 p h) (sat_cons (step2086 p h) (sat_cons (step1095 p h) (sat_cons (step1100 p h) (sat_cons (step1123 p h) (sat_cons (step1157 p h) (sat_cons (step1163 p h) (sat_cons (step1088 p h) (sat_cons (step1090 p h) (sat_cons (step1086 p h) (sat_cons (step1061 p h) (sat_cons (step1069 p h) (sat_cons (step1056 p h) (sat_cons (step1068 p h) (sat_cons (step1052 p h) (sat_cons (step1067 p h) (sat_cons (step1049 p h) (sat_cons (step115 p h) (sat_cons (step82 p h) (sat_cons (step156 p h) (sat_cons (step86 p h) (sat_nil p)))))))))))))))))))))))))))))))))))
def c2160 : List Lit := [(1760, true), (103, true), (455, true), (43, true), (44, false), (117, true)]
theorem step2160 (p : Nat → Bool) (h : Constraints p) : clause p c2160 = true :=
  Snake9.LocalRup.prove_clause [c1021, c1764, c1772, c870, c1252, c1236, c1226, c1225, c1800, c1803, c1827, c924, c1857, c1780, c1788, c2092, c1768, c2115, c1776, c1758, c1766, c1750, c1751, c809, c830] c2160 (by decide) p (sat_cons (step1021 p h) (sat_cons (step1764 p h) (sat_cons (step1772 p h) (sat_cons (step870 p h) (sat_cons (step1252 p h) (sat_cons (step1236 p h) (sat_cons (step1226 p h) (sat_cons (step1225 p h) (sat_cons (step1800 p h) (sat_cons (step1803 p h) (sat_cons (step1827 p h) (sat_cons (step924 p h) (sat_cons (step1857 p h) (sat_cons (step1780 p h) (sat_cons (step1788 p h) (sat_cons (step2092 p h) (sat_cons (step1768 p h) (sat_cons (step2115 p h) (sat_cons (step1776 p h) (sat_cons (step1758 p h) (sat_cons (step1766 p h) (sat_cons (step1750 p h) (sat_cons (step1751 p h) (sat_cons (step809 p h) (sat_cons (step830 p h) (sat_nil p))))))))))))))))))))))))))
def c2161 : List Lit := [(1671, false), (1688, true)]
theorem step2161 (p : Nat → Bool) (h : Constraints p) : clause p c2161 = true :=
  Snake9.LocalRup.prove_clause [c1689, c1658, c1659, c1685, c1651, c1669, c2097] c2161 (by decide) p (sat_cons (step1689 p h) (sat_cons (step1658 p h) (sat_cons (step1659 p h) (sat_cons (step1685 p h) (sat_cons (step1651 p h) (sat_cons (step1669 p h) (sat_cons (step2097 p h) (sat_nil p))))))))
def c2162 : List Lit := [(116, true), (1745, true)]
theorem step2162 (p : Nat → Bool) (h : Constraints p) : clause p c2162 = true :=
  Snake9.LocalRup.prove_clause [c2028, c1817, c1815, c1819, c1812, c1814, c968, c957, c938, c1274, c1268, c1277, c1270, c1282] c2162 (by decide) p (sat_cons (step2028 p h) (sat_cons (step1817 p h) (sat_cons (step1815 p h) (sat_cons (step1819 p h) (sat_cons (step1812 p h) (sat_cons (step1814 p h) (sat_cons (step968 p h) (sat_cons (step957 p h) (sat_cons (step938 p h) (sat_cons (step1274 p h) (sat_cons (step1268 p h) (sat_cons (step1277 p h) (sat_cons (step1270 p h) (sat_cons (step1282 p h) (sat_nil p)))))))))))))))
def c2163 : List Lit := [(1681, false), (1688, true)]
theorem step2163 (p : Nat → Bool) (h : Constraints p) : clause p c2163 = true :=
  Snake9.LocalRup.prove_clause [c1677, c1668, c1671, c1681, c2097, c1653, c1651] c2163 (by decide) p (sat_cons (step1677 p h) (sat_cons (step1668 p h) (sat_cons (step1671 p h) (sat_cons (step1681 p h) (sat_cons (step2097 p h) (sat_cons (step1653 p h) (sat_cons (step1651 p h) (sat_nil p))))))))
def c2164 : List Lit := [(1672, true), (1683, true), (94, false), (96, false)]
theorem step2164 (p : Nat → Bool) (h : Constraints p) : clause p c2164 = true :=
  Snake9.LocalRup.prove_clause [c2046, c1650, c1651, c2097, c803, c1670, c817, c1664, c1228, c821, c1225, c828] c2164 (by decide) p (sat_cons (step2046 p h) (sat_cons (step1650 p h) (sat_cons (step1651 p h) (sat_cons (step2097 p h) (sat_cons (step803 p h) (sat_cons (step1670 p h) (sat_cons (step817 p h) (sat_cons (step1664 p h) (sat_cons (step1228 p h) (sat_cons (step821 p h) (sat_cons (step1225 p h) (sat_cons (step828 p h) (sat_nil p)))))))))))))
def c2165 : List Lit := [(94, false), (96, false), (1687, true)]
theorem step2165 (p : Nat → Bool) (h : Constraints p) : clause p c2165 = true :=
  Snake9.LocalRup.prove_clause [c2046, c1684, c1654, c1676, c2164, c1653, c1680, c1667, c1669, c1664, c2097, c806, c1652, c817, c821, c1228, c828, c1225] c2165 (by decide) p (sat_cons (step2046 p h) (sat_cons (step1684 p h) (sat_cons (step1654 p h) (sat_cons (step1676 p h) (sat_cons (step2164 p h) (sat_cons (step1653 p h) (sat_cons (step1680 p h) (sat_cons (step1667 p h) (sat_cons (step1669 p h) (sat_cons (step1664 p h) (sat_cons (step2097 p h) (sat_cons (step806 p h) (sat_cons (step1652 p h) (sat_cons (step817 p h) (sat_cons (step821 p h) (sat_cons (step1228 p h) (sat_cons (step828 p h) (sat_cons (step1225 p h) (sat_nil p)))))))))))))))))))
def c2166 : List Lit := [(1686, true)]
theorem step2166 (p : Nat → Bool) (h : Constraints p) : clause p c2166 = true :=
  Snake9.LocalRup.prove_clause [c1675, c1679, c1669, c1653, c2097, c1651] c2166 (by decide) p (sat_cons (step1675 p h) (sat_cons (step1679 p h) (sat_cons (step1669 p h) (sat_cons (step1653 p h) (sat_cons (step2097 p h) (sat_cons (step1651 p h) (sat_nil p)))))))
def c2167 : List Lit := [(1750, false), (1668, false), (1721, false), (1783, true)]
theorem step2167 (p : Nat → Bool) (h : Constraints p) : clause p c2167 = true :=
  Snake9.LocalRup.prove_clause [c2166, c1737, c1905, c1778, c1846, c1912, c1738, c1852, c1783, c1758, c1750, c1751, c2165] c2167 (by decide) p (sat_cons (step2166 p h) (sat_cons (step1737 p h) (sat_cons (step1905 p h) (sat_cons (step1778 p h) (sat_cons (step1846 p h) (sat_cons (step1912 p h) (sat_cons (step1738 p h) (sat_cons (step1852 p h) (sat_cons (step1783 p h) (sat_cons (step1758 p h) (sat_cons (step1750 p h) (sat_cons (step1751 p h) (sat_cons (step2165 p h) (sat_nil p))))))))))))))
def c2168 : List Lit := [(1671, false), (79, true), (1672, false), (1689, true), (94, false), (96, false)]
theorem step2168 (p : Nat → Bool) (h : Constraints p) : clause p c2168 = true :=
  Snake9.LocalRup.prove_clause [c2046, c1694, c1660, c1659, c1652, c1690, c1667, c1664, c806, c821, c817, c828, c1228, c1225] c2168 (by decide) p (sat_cons (step2046 p h) (sat_cons (step1694 p h) (sat_cons (step1660 p h) (sat_cons (step1659 p h) (sat_cons (step1652 p h) (sat_cons (step1690 p h) (sat_cons (step1667 p h) (sat_cons (step1664 p h) (sat_cons (step806 p h) (sat_cons (step821 p h) (sat_cons (step817 p h) (sat_cons (step828 p h) (sat_cons (step1228 p h) (sat_cons (step1225 p h) (sat_nil p)))))))))))))))
def c2169 : List Lit := [(43, false), (1579, true), (44, true), (64, false), (96, false)]
theorem step2169 (p : Nat → Bool) (h : Constraints p) : clause p c2169 = true :=
  Snake9.LocalRup.prove_clause [c279, c288, c285, c1432, c1429, c1440] c2169 (by decide) p (sat_cons (step279 p h) (sat_cons (step288 p h) (sat_cons (step285 p h) (sat_cons (step1432 p h) (sat_cons (step1429 p h) (sat_cons (step1440 p h) (sat_nil p)))))))
def c2170 : List Lit := [(1, false), (2, true), (18, true)]
theorem step2170 (p : Nat → Bool) (h : Constraints p) : clause p c2170 = true :=
  Snake9.LocalRup.prove_clause [c970, c2] c2170 (by decide) p (sat_cons (step970 p h) (sat_cons (step2 p h) (sat_nil p)))
def c2171 : List Lit := [(3, false), (5, true), (2, true), (79, true), (13, true)]
theorem step2171 (p : Nat → Bool) (h : Constraints p) : clause p c2171 = true :=
  Snake9.LocalRup.prove_clause [c971, c17] c2171 (by decide) p (sat_cons (step971 p h) (sat_cons (step17 p h) (sat_nil p)))
def c2172 : List Lit := [(4, false), (9, true), (5, true)]
theorem step2172 (p : Nat → Bool) (h : Constraints p) : clause p c2172 = true :=
  Snake9.LocalRup.prove_clause [c972, c19] c2172 (by decide) p (sat_cons (step972 p h) (sat_cons (step19 p h) (sat_nil p)))
def c2173 : List Lit := [(4, false), (9, true), (2, true)]
theorem step2173 (p : Nat → Bool) (h : Constraints p) : clause p c2173 = true :=
  Snake9.LocalRup.prove_clause [c972, c20] c2173 (by decide) p (sat_cons (step972 p h) (sat_cons (step20 p h) (sat_nil p)))
def c2174 : List Lit := [(4, false), (5, true), (2, true)]
theorem step2174 (p : Nat → Bool) (h : Constraints p) : clause p c2174 = true :=
  Snake9.LocalRup.prove_clause [c972, c21] c2174 (by decide) p (sat_cons (step972 p h) (sat_cons (step21 p h) (sat_nil p)))
def c2175 : List Lit := [(9, true), (6, false), (24, true), (2, true), (8, true)]
theorem step2175 (p : Nat → Bool) (h : Constraints p) : clause p c2175 = true :=
  Snake9.LocalRup.prove_clause [c973, c35] c2175 (by decide) p (sat_cons (step973 p h) (sat_cons (step35 p h) (sat_nil p)))
def c2176 : List Lit := [(81, true), (7, false), (42, true), (10, true)]
theorem step2176 (p : Nat → Bool) (h : Constraints p) : clause p c2176 = true :=
  Snake9.LocalRup.prove_clause [c974, c40] c2176 (by decide) p (sat_cons (step974 p h) (sat_cons (step40 p h) (sat_nil p)))
def c2177 : List Lit := [(8, true), (10, true), (7, false), (42, true)]
theorem step2177 (p : Nat → Bool) (h : Constraints p) : clause p c2177 = true :=
  Snake9.LocalRup.prove_clause [c974, c41] c2177 (by decide) p (sat_cons (step974 p h) (sat_cons (step41 p h) (sat_nil p)))
def c2178 : List Lit := [(13, true), (12, false), (14, true)]
theorem step2178 (p : Nat → Bool) (h : Constraints p) : clause p c2178 = true :=
  Snake9.LocalRup.prove_clause [c975, c68] c2178 (by decide) p (sat_cons (step975 p h) (sat_cons (step68 p h) (sat_nil p)))
def c2179 : List Lit := [(12, false), (11, true), (14, true)]
theorem step2179 (p : Nat → Bool) (h : Constraints p) : clause p c2179 = true :=
  Snake9.LocalRup.prove_clause [c975, c69] c2179 (by decide) p (sat_cons (step975 p h) (sat_cons (step69 p h) (sat_nil p)))
def c2180 : List Lit := [(11, true), (13, true), (12, false)]
theorem step2180 (p : Nat → Bool) (h : Constraints p) : clause p c2180 = true :=
  Snake9.LocalRup.prove_clause [c975, c70] c2180 (by decide) p (sat_cons (step975 p h) (sat_cons (step70 p h) (sat_nil p)))
def c2181 : List Lit := [(16, false), (15, true)]
theorem step2181 (p : Nat → Bool) (h : Constraints p) : clause p c2181 = true :=
  Snake9.LocalRup.prove_clause [c976, c84] c2181 (by decide) p (sat_cons (step976 p h) (sat_cons (step84 p h) (sat_nil p)))
def c2182 : List Lit := [(16, false), (9, true)]
theorem step2182 (p : Nat → Bool) (h : Constraints p) : clause p c2182 = true :=
  Snake9.LocalRup.prove_clause [c976, c85] c2182 (by decide) p (sat_cons (step976 p h) (sat_cons (step85 p h) (sat_nil p)))
def c2183 : List Lit := [(17, false), (15, true), (14, true)]
theorem step2183 (p : Nat → Bool) (h : Constraints p) : clause p c2183 = true :=
  Snake9.LocalRup.prove_clause [c977, c87] c2183 (by decide) p (sat_cons (step977 p h) (sat_cons (step87 p h) (sat_nil p)))
def c2184 : List Lit := [(17, false), (10, true), (14, true)]
theorem step2184 (p : Nat → Bool) (h : Constraints p) : clause p c2184 = true :=
  Snake9.LocalRup.prove_clause [c977, c88] c2184 (by decide) p (sat_cons (step977 p h) (sat_cons (step88 p h) (sat_nil p)))
def c2185 : List Lit := [(19, false), (2, true), (56, true), (18, true)]
theorem step2185 (p : Nat → Bool) (h : Constraints p) : clause p c2185 = true :=
  Snake9.LocalRup.prove_clause [c978, c99] c2185 (by decide) p (sat_cons (step978 p h) (sat_cons (step99 p h) (sat_nil p)))
def c2186 : List Lit := [(20, false), (18, true), (57, true)]
theorem step2186 (p : Nat → Bool) (h : Constraints p) : clause p c2186 = true :=
  Snake9.LocalRup.prove_clause [c979, c101] c2186 (by decide) p (sat_cons (step979 p h) (sat_cons (step101 p h) (sat_nil p)))
def c2187 : List Lit := [(20, false), (18, true), (22, true)]
theorem step2187 (p : Nat → Bool) (h : Constraints p) : clause p c2187 = true :=
  Snake9.LocalRup.prove_clause [c979, c102] c2187 (by decide) p (sat_cons (step979 p h) (sat_cons (step102 p h) (sat_nil p)))
def c2188 : List Lit := [(29, true), (22, true), (25, true), (21, false)]
theorem step2188 (p : Nat → Bool) (h : Constraints p) : clause p c2188 = true :=
  Snake9.LocalRup.prove_clause [c980, c107] c2188 (by decide) p (sat_cons (step980 p h) (sat_cons (step107 p h) (sat_nil p)))
def c2189 : List Lit := [(29, true), (18, true), (25, true), (21, false)]
theorem step2189 (p : Nat → Bool) (h : Constraints p) : clause p c2189 = true :=
  Snake9.LocalRup.prove_clause [c980, c108] c2189 (by decide) p (sat_cons (step980 p h) (sat_cons (step108 p h) (sat_nil p)))
def c2190 : List Lit := [(22, true), (21, false), (25, true), (18, true)]
theorem step2190 (p : Nat → Bool) (h : Constraints p) : clause p c2190 = true :=
  Snake9.LocalRup.prove_clause [c980, c109] c2190 (by decide) p (sat_cons (step980 p h) (sat_cons (step109 p h) (sat_nil p)))
def c2191 : List Lit := [(23, false), (18, true), (32, true), (25, true), (62, true)]
theorem step2191 (p : Nat → Bool) (h : Constraints p) : clause p c2191 = true :=
  Snake9.LocalRup.prove_clause [c981, c127] c2191 (by decide) p (sat_cons (step981 p h) (sat_cons (step127 p h) (sat_nil p)))
def c2192 : List Lit := [(23, false), (24, true), (25, true), (62, true), (18, true)]
theorem step2192 (p : Nat → Bool) (h : Constraints p) : clause p c2192 = true :=
  Snake9.LocalRup.prove_clause [c981, c128] c2192 (by decide) p (sat_cons (step981 p h) (sat_cons (step128 p h) (sat_nil p)))
def c2193 : List Lit := [(23, false), (24, true), (18, true), (32, true), (25, true)]
theorem step2193 (p : Nat → Bool) (h : Constraints p) : clause p c2193 = true :=
  Snake9.LocalRup.prove_clause [c981, c129] c2193 (by decide) p (sat_cons (step981 p h) (sat_cons (step129 p h) (sat_nil p)))
def c2194 : List Lit := [(23, false), (25, false), (21, false)]
theorem step2194 (p : Nat → Bool) (h : Constraints p) : clause p c2194 = true :=
  Snake9.LocalRup.prove_clause [c786, c138] c2194 (by decide) p (sat_cons (step786 p h) (sat_cons (step138 p h) (sat_nil p)))
def c2195 : List Lit := [(26, false), (25, false), (21, false)]
theorem step2195 (p : Nat → Bool) (h : Constraints p) : clause p c2195 = true :=
  Snake9.LocalRup.prove_clause [c786, c139] c2195 (by decide) p (sat_cons (step786 p h) (sat_cons (step139 p h) (sat_nil p)))
def c2196 : List Lit := [(65, false), (25, false), (21, false)]
theorem step2196 (p : Nat → Bool) (h : Constraints p) : clause p c2196 = true :=
  Snake9.LocalRup.prove_clause [c786, c140] c2196 (by decide) p (sat_cons (step786 p h) (sat_cons (step140 p h) (sat_nil p)))
def c2197 : List Lit := [(26, false), (23, false), (25, false)]
theorem step2197 (p : Nat → Bool) (h : Constraints p) : clause p c2197 = true :=
  Snake9.LocalRup.prove_clause [c786, c141] c2197 (by decide) p (sat_cons (step786 p h) (sat_cons (step141 p h) (sat_nil p)))
def c2198 : List Lit := [(23, false), (65, false), (25, false)]
theorem step2198 (p : Nat → Bool) (h : Constraints p) : clause p c2198 = true :=
  Snake9.LocalRup.prove_clause [c786, c142] c2198 (by decide) p (sat_cons (step786 p h) (sat_cons (step142 p h) (sat_nil p)))
def c2199 : List Lit := [(26, false), (65, false), (25, false)]
theorem step2199 (p : Nat → Bool) (h : Constraints p) : clause p c2199 = true :=
  Snake9.LocalRup.prove_clause [c786, c143] c2199 (by decide) p (sat_cons (step786 p h) (sat_cons (step143 p h) (sat_nil p)))
def c2200 : List Lit := [(22, true), (26, false), (27, true), (25, true), (67, true)]
theorem step2200 (p : Nat → Bool) (h : Constraints p) : clause p c2200 = true :=
  Snake9.LocalRup.prove_clause [c982, c155] c2200 (by decide) p (sat_cons (step982 p h) (sat_cons (step155 p h) (sat_nil p)))
def c2201 : List Lit := [(26, false), (10, true), (27, true), (25, true), (67, true)]
theorem step2201 (p : Nat → Bool) (h : Constraints p) : clause p c2201 = true :=
  Snake9.LocalRup.prove_clause [c982, c156] c2201 (by decide) p (sat_cons (step982 p h) (sat_cons (step156 p h) (sat_nil p)))
def c2202 : List Lit := [(22, true), (10, true), (27, true), (26, false), (67, true)]
theorem step2202 (p : Nat → Bool) (h : Constraints p) : clause p c2202 = true :=
  Snake9.LocalRup.prove_clause [c982, c157] c2202 (by decide) p (sat_cons (step982 p h) (sat_cons (step157 p h) (sat_nil p)))
def c2203 : List Lit := [(26, false), (10, true), (25, true), (22, true), (67, true)]
theorem step2203 (p : Nat → Bool) (h : Constraints p) : clause p c2203 = true :=
  Snake9.LocalRup.prove_clause [c982, c158] c2203 (by decide) p (sat_cons (step982 p h) (sat_cons (step158 p h) (sat_nil p)))
end B112E089
