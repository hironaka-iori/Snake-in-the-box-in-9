import B112E020Part0009
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2252 : List Lit := [(1652, false), (63, false), (58, true), (53, false), (1662, true)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c1263, c1270, c1297, c1287, c1288, c1301, c1280, c1273, c363, c1264] c2252 (by decide) p (sat_cons (step1263 p h) (sat_cons (step1270 p h) (sat_cons (step1297 p h) (sat_cons (step1287 p h) (sat_cons (step1288 p h) (sat_cons (step1301 p h) (sat_cons (step1280 p h) (sat_cons (step1273 p h) (sat_cons (step363 p h) (sat_cons (step1264 p h) (sat_nil p)))))))))))
def c2253 : List Lit := [(69, false), (63, false), (58, true), (53, false), (1649, true)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c364, c363, c1265, c1264, c1274] c2253 (by decide) p (sat_cons (step364 p h) (sat_cons (step363 p h) (sat_cons (step1265 p h) (sat_cons (step1264 p h) (sat_cons (step1274 p h) (sat_nil p))))))
def c2254 : List Lit := [(1675, true), (100, false), (124, false)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c1325, c1326, c477, c738, c1899] c2254 (by decide) p (sat_cons (step1325 p h) (sat_cons (step1326 p h) (sat_cons (step477 p h) (sat_cons (step738 p h) (sat_cons (step1899 p h) (sat_nil p))))))
def c2255 : List Lit := [(48, true), (60, false), (1590, false), (1598, true), (96, false)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c1172, c1189, c1159, c1155, c1158, c2233, c1186, c1175, c1167, c1161, c2055, c1157, c1153, c1837, c217] c2255 (by decide) p (sat_cons (step1172 p h) (sat_cons (step1189 p h) (sat_cons (step1159 p h) (sat_cons (step1155 p h) (sat_cons (step1158 p h) (sat_cons (step2233 p h) (sat_cons (step1186 p h) (sat_cons (step1175 p h) (sat_cons (step1167 p h) (sat_cons (step1161 p h) (sat_cons (step2055 p h) (sat_cons (step1157 p h) (sat_cons (step1153 p h) (sat_cons (step1837 p h) (sat_cons (step217 p h) (sat_nil p))))))))))))))))
def c2256 : List Lit := [(60, false), (63, false), (53, false), (1643, false), (1651, false), (1663, true), (61, true), (70, true), (122, true)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c2111, c362, c1280, c1267, c1285, c1272, c1306] c2256 (by decide) p (sat_cons (step2111 p h) (sat_cons (step362 p h) (sat_cons (step1280 p h) (sat_cons (step1267 p h) (sat_cons (step1285 p h) (sat_cons (step1272 p h) (sat_cons (step1306 p h) (sat_nil p))))))))
def c2257 : List Lit := [(1556, false), (1631, true), (1598, false), (77, false)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c1990, c1214, c2047, c2057, c1208, c1233, c1968, c1732, c1058, c1059, c80, c1827, c1811, c104] c2257 (by decide) p (sat_cons (step1990 p h) (sat_cons (step1214 p h) (sat_cons (step2047 p h) (sat_cons (step2057 p h) (sat_cons (step1208 p h) (sat_cons (step1233 p h) (sat_cons (step1968 p h) (sat_cons (step1732 p h) (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step80 p h) (sat_cons (step1827 p h) (sat_cons (step1811 p h) (sat_cons (step104 p h) (sat_nil p)))))))))))))))
def c2258 : List Lit := [(8, false), (43, true), (29, false), (60, false)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c123, c1795] c2258 (by decide) p (sat_cons (step123 p h) (sat_cons (step1795 p h) (sat_nil p)))
def c2259 : List Lit := [(1512, true), (9, true), (1502, false), (29, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c1036, c1783, c1031, c1026, c1805, c30] c2259 (by decide) p (sat_cons (step1036 p h) (sat_cons (step1783 p h) (sat_cons (step1031 p h) (sat_cons (step1026 p h) (sat_cons (step1805 p h) (sat_cons (step30 p h) (sat_nil p)))))))
def c2260 : List Lit := [(1725, true), (1715, false), (118, false), (96, true)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c1401, c1384, c1386, c1413, c1417, c1402, c1389, c2203, c1397, c1380, c653] c2260 (by decide) p (sat_cons (step1401 p h) (sat_cons (step1384 p h) (sat_cons (step1386 p h) (sat_cons (step1413 p h) (sat_cons (step1417 p h) (sat_cons (step1402 p h) (sat_cons (step1389 p h) (sat_cons (step2203 p h) (sat_cons (step1397 p h) (sat_cons (step1380 p h) (sat_cons (step653 p h) (sat_nil p))))))))))))
def c2261 : List Lit := [(103, false), (104, false), (1750, true), (1741, false), (118, false)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c1681, c1678, c658, c2248, c1426, c1446, c1432, c1462] c2261 (by decide) p (sat_cons (step1681 p h) (sat_cons (step1678 p h) (sat_cons (step658 p h) (sat_cons (step2248 p h) (sat_cons (step1426 p h) (sat_cons (step1446 p h) (sat_cons (step1432 p h) (sat_cons (step1462 p h) (sat_nil p)))))))))
def c2262 : List Lit := [(12, false), (1608, true), (29, false), (1583, true), (1580, false)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c1804, c1805, c36, c1156, c1157, c1161, c44, c1188, c1109, c1207, c2047] c2262 (by decide) p (sat_cons (step1804 p h) (sat_cons (step1805 p h) (sat_cons (step36 p h) (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step1161 p h) (sat_cons (step44 p h) (sat_cons (step1188 p h) (sat_cons (step1109 p h) (sat_cons (step1207 p h) (sat_cons (step2047 p h) (sat_nil p))))))))))))
def c2263 : List Lit := [(8, false), (47, false), (42, false), (29, false)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c211, c35, c1796] c2263 (by decide) p (sat_cons (step211 p h) (sat_cons (step35 p h) (sat_cons (step1796 p h) (sat_nil p))))
def c2264 : List Lit := [(1569, true), (35, true)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c1124, c1134, c1766, c1132, c1125, c1126, c1127, c1572, c1835] c2264 (by decide) p (sat_cons (step1124 p h) (sat_cons (step1134 p h) (sat_cons (step1766 p h) (sat_cons (step1132 p h) (sat_cons (step1125 p h) (sat_cons (step1126 p h) (sat_cons (step1127 p h) (sat_cons (step1572 p h) (sat_cons (step1835 p h) (sat_nil p))))))))))
def c2265 : List Lit := [(43, true), (46, true), (47, false), (29, false)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c1841, c1844, c1557] c2265 (by decide) p (sat_cons (step1841 p h) (sat_cons (step1844 p h) (sat_cons (step1557 p h) (sat_nil p))))
def c2266 : List Lit := [(1513, false), (1630, true)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c1996, c1974, c1101, c1239, c1732, c1985, c2205] c2266 (by decide) p (sat_cons (step1996 p h) (sat_cons (step1974 p h) (sat_cons (step1101 p h) (sat_cons (step1239 p h) (sat_cons (step1732 p h) (sat_cons (step1985 p h) (sat_cons (step2205 p h) (sat_nil p))))))))
def c2267 : List Lit := [(1526, false), (1531, true), (1537, true)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c1069, c1070, c1081, c1061, c1062, c1731] c2267 (by decide) p (sat_cons (step1069 p h) (sat_cons (step1070 p h) (sat_cons (step1081 p h) (sat_cons (step1061 p h) (sat_cons (step1062 p h) (sat_cons (step1731 p h) (sat_nil p)))))))
def c2268 : List Lit := [(10, true), (3, false), (1503, true), (5, false), (1537, true), (29, false)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c1788, c1789, c73, c71, c1059, c1642, c1055, c1077, c1068, c2267, c1060, c17, c1023, c1797, c119, c121, c1063] c2268 (by decide) p (sat_cons (step1788 p h) (sat_cons (step1789 p h) (sat_cons (step73 p h) (sat_cons (step71 p h) (sat_cons (step1059 p h) (sat_cons (step1642 p h) (sat_cons (step1055 p h) (sat_cons (step1077 p h) (sat_cons (step1068 p h) (sat_cons (step2267 p h) (sat_cons (step1060 p h) (sat_cons (step17 p h) (sat_cons (step1023 p h) (sat_cons (step1797 p h) (sat_cons (step119 p h) (sat_cons (step121 p h) (sat_cons (step1063 p h) (sat_nil p))))))))))))))))))
def c2269 : List Lit := [(47, true), (45, false), (1597, true), (1585, true)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c1159, c1156, c1157, c1158, c1161, c1185, c1153, c1174, c1167, c223, c235, c262, c1848] c2269 (by decide) p (sat_cons (step1159 p h) (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step1158 p h) (sat_cons (step1161 p h) (sat_cons (step1185 p h) (sat_cons (step1153 p h) (sat_cons (step1174 p h) (sat_cons (step1167 p h) (sat_cons (step223 p h) (sat_cons (step235 p h) (sat_cons (step262 p h) (sat_cons (step1848 p h) (sat_nil p))))))))))))))
def c2270 : List Lit := [(5, false), (47, false), (1502, false), (9, true), (1537, true), (1513, true), (29, false)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c1037, c32, c1805, c1026, c1031, c1034, c1040, c2268, c1019, c1017] c2270 (by decide) p (sat_cons (step1037 p h) (sat_cons (step32 p h) (sat_cons (step1805 p h) (sat_cons (step1026 p h) (sat_cons (step1031 p h) (sat_cons (step1034 p h) (sat_cons (step1040 p h) (sat_cons (step2268 p h) (sat_cons (step1019 p h) (sat_cons (step1017 p h) (sat_nil p)))))))))))
def c2271 : List Lit := [(47, false), (1502, false), (29, false), (9, true), (1537, true), (1513, true)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c2270, c2024, c1805, c36] c2271 (by decide) p (sat_cons (step2270 p h) (sat_cons (step2024 p h) (sat_cons (step1805 p h) (sat_cons (step36 p h) (sat_nil p)))))
def c2272 : List Lit := [(25, false), (8, false), (1512, false), (1630, true), (29, false)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c1996, c1097, c116, c119, c121, c1642, c1062, c1063, c1055, c1694, c1077, c1096, c1068, c1239, c2205, c1985] c2272 (by decide) p (sat_cons (step1996 p h) (sat_cons (step1097 p h) (sat_cons (step116 p h) (sat_cons (step119 p h) (sat_cons (step121 p h) (sat_cons (step1642 p h) (sat_cons (step1062 p h) (sat_cons (step1063 p h) (sat_cons (step1055 p h) (sat_cons (step1694 p h) (sat_cons (step1077 p h) (sat_cons (step1096 p h) (sat_cons (step1068 p h) (sat_cons (step1239 p h) (sat_cons (step2205 p h) (sat_cons (step1985 p h) (sat_nil p)))))))))))))))))
def c2273 : List Lit := [(47, true), (1597, true), (1585, true)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c1156, c2269, c1161, c1152] c2273 (by decide) p (sat_cons (step1156 p h) (sat_cons (step2269 p h) (sat_cons (step1161 p h) (sat_cons (step1152 p h) (sat_nil p)))))
def c2274 : List Lit := [(10, false), (1513, true), (47, false), (29, false)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c36, c32, c35, c2024, c1021] c2274 (by decide) p (sat_cons (step36 p h) (sat_cons (step32 p h) (sat_cons (step35 p h) (sat_cons (step2024 p h) (sat_cons (step1021 p h) (sat_nil p))))))
def c2275 : List Lit := [(45, true), (30, false), (1561, true), (22, false), (6, false), (1525, false), (9, false), (1537, true), (1597, true), (1585, true), (29, false)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c1116, c2273, c1163, c1152, c1154, c1160, c1161, c1185, c1155, c1174, c43, c232, c1167, c1792, c2265, c219, c214, c1798, c1722, c1114, c1827, c156, c91, c2056, c1809] c2275 (by decide) p (sat_cons (step1116 p h) (sat_cons (step2273 p h) (sat_cons (step1163 p h) (sat_cons (step1152 p h) (sat_cons (step1154 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1185 p h) (sat_cons (step1155 p h) (sat_cons (step1174 p h) (sat_cons (step43 p h) (sat_cons (step232 p h) (sat_cons (step1167 p h) (sat_cons (step1792 p h) (sat_cons (step2265 p h) (sat_cons (step219 p h) (sat_cons (step214 p h) (sat_cons (step1798 p h) (sat_cons (step1722 p h) (sat_cons (step1114 p h) (sat_cons (step1827 p h) (sat_cons (step156 p h) (sat_cons (step91 p h) (sat_cons (step2056 p h) (sat_cons (step1809 p h) (sat_nil p))))))))))))))))))))))))))
def c2276 : List Lit := [(49, false), (11, true), (48, false), (45, false), (47, false)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c238, c262, c1847] c2276 (by decide) p (sat_cons (step238 p h) (sat_cons (step262 p h) (sat_cons (step1847 p h) (sat_nil p))))
def c2277 : List Lit := [(48, false), (45, false), (22, false), (1574, true), (6, false), (1525, false), (9, false), (1537, true), (47, false), (1597, true)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c2047, c1109, c1977, c1116, c43, c1792, c2276, c1167, c1174, c1185, c1160, c1655, c1676, c1141, c1798, c2048, c1722, c1114, c1827, c156, c91, c2056, c1809] c2277 (by decide) p (sat_cons (step2047 p h) (sat_cons (step1109 p h) (sat_cons (step1977 p h) (sat_cons (step1116 p h) (sat_cons (step43 p h) (sat_cons (step1792 p h) (sat_cons (step2276 p h) (sat_cons (step1167 p h) (sat_cons (step1174 p h) (sat_cons (step1185 p h) (sat_cons (step1160 p h) (sat_cons (step1655 p h) (sat_cons (step1676 p h) (sat_cons (step1141 p h) (sat_cons (step1798 p h) (sat_cons (step2048 p h) (sat_cons (step1722 p h) (sat_cons (step1114 p h) (sat_cons (step1827 p h) (sat_cons (step156 p h) (sat_cons (step91 p h) (sat_cons (step2056 p h) (sat_cons (step1809 p h) (sat_nil p))))))))))))))))))))))))
def c2278 : List Lit := [(8, true), (1512, false), (1630, true), (1597, true), (1585, true), (29, false)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.TreeRup.prove_clause [c1996, c1097, c2273, c2266, c2274, c1805, c1024, c1773, c2251, c2211, c1170, c1169, c1021, c2271, c2024, c1785, c1789, c1017, c73, c71, c75, c1019, c1059, c1642, c1313, c1040, c1732, c1055, c1033, c1096, c1077, c1023, c1995, c1239, c2267, c2016, c1985, c1060, c2015, c1977, c2047, c308, c1116, c1109, c1855, c2275, c366, c367, c1267, c2277, c1155, c1158, c1161, c1185, c1153, c1676, c1174, c1798, c1167, c2055, c2265, c1842, c214, c217, c390, c389, c391, c1114, c1264, c1278, c1280, c158, c1275, c1288, c1315, c1311, c1321, c1379, c1345] c2278 (by decide) p (sat_cons (step1996 p h) (sat_cons (step1097 p h) (sat_cons (step2273 p h) (sat_cons (step2266 p h) (sat_cons (step2274 p h) (sat_cons (step1805 p h) (sat_cons (step1024 p h) (sat_cons (step1773 p h) (sat_cons (step2251 p h) (sat_cons (step2211 p h) (sat_cons (step1170 p h) (sat_cons (step1169 p h) (sat_cons (step1021 p h) (sat_cons (step2271 p h) (sat_cons (step2024 p h) (sat_cons (step1785 p h) (sat_cons (step1789 p h) (sat_cons (step1017 p h) (sat_cons (step73 p h) (sat_cons (step71 p h) (sat_cons (step75 p h) (sat_cons (step1019 p h) (sat_cons (step1059 p h) (sat_cons (step1642 p h) (sat_cons (step1313 p h) (sat_cons (step1040 p h) (sat_cons (step1732 p h) (sat_cons (step1055 p h) (sat_cons (step1033 p h) (sat_cons (step1096 p h) (sat_cons (step1077 p h) (sat_cons (step1023 p h) (sat_cons (step1995 p h) (sat_cons (step1239 p h) (sat_cons (step2267 p h) (sat_cons (step2016 p h) (sat_cons (step1985 p h) (sat_cons (step1060 p h) (sat_cons (step2015 p h) (sat_cons (step1977 p h) (sat_cons (step2047 p h) (sat_cons (step308 p h) (sat_cons (step1116 p h) (sat_cons (step1109 p h) (sat_cons (step1855 p h) (sat_cons (step2275 p h) (sat_cons (step366 p h) (sat_cons (step367 p h) (sat_cons (step1267 p h) (sat_cons (step2277 p h) (sat_cons (step1155 p h) (sat_cons (step1158 p h) (sat_cons (step1161 p h) (sat_cons (step1185 p h) (sat_cons (step1153 p h) (sat_cons (step1676 p h) (sat_cons (step1174 p h) (sat_cons (step1798 p h) (sat_cons (step1167 p h) (sat_cons (step2055 p h) (sat_cons (step2265 p h) (sat_cons (step1842 p h) (sat_cons (step214 p h) (sat_cons (step217 p h) (sat_cons (step390 p h) (sat_cons (step389 p h) (sat_cons (step391 p h) (sat_cons (step1114 p h) (sat_cons (step1264 p h) (sat_cons (step1278 p h) (sat_cons (step1280 p h) (sat_cons (step158 p h) (sat_cons (step1275 p h) (sat_cons (step1288 p h) (sat_cons (step1315 p h) (sat_cons (step1311 p h) (sat_cons (step1321 p h) (sat_cons (step1379 p h) (sat_cons (step1345 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2279 : List Lit := [(1512, false), (1630, true), (1597, true), (1585, true), (29, false)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c2273, c2266, c2274, c2278, c2272, c1797] c2279 (by decide) p (sat_cons (step2273 p h) (sat_cons (step2266 p h) (sat_cons (step2274 p h) (sat_cons (step2278 p h) (sat_cons (step2272 p h) (sat_cons (step1797 p h) (sat_nil p)))))))
def c2280 : List Lit := [(8, false), (1630, true), (1597, true), (1585, true), (29, false)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c2279, c2273, c2266, c2274, c1805, c1163, c2263, c1797, c1153, c1154, c1160, c1161, c1185, c1155, c1174, c1167, c238, c262, c1842, c1848, c163, c220, c1789, c1026, c1016, c1028, c1019, c1039] c2280 (by decide) p (sat_cons (step2279 p h) (sat_cons (step2273 p h) (sat_cons (step2266 p h) (sat_cons (step2274 p h) (sat_cons (step1805 p h) (sat_cons (step1163 p h) (sat_cons (step2263 p h) (sat_cons (step1797 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1185 p h) (sat_cons (step1155 p h) (sat_cons (step1174 p h) (sat_cons (step1167 p h) (sat_cons (step238 p h) (sat_cons (step262 p h) (sat_cons (step1842 p h) (sat_cons (step1848 p h) (sat_cons (step163 p h) (sat_cons (step220 p h) (sat_cons (step1789 p h) (sat_cons (step1026 p h) (sat_cons (step1016 p h) (sat_cons (step1028 p h) (sat_cons (step1019 p h) (sat_cons (step1039 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2281 : List Lit := [(1630, true), (1597, true), (1585, true), (29, false)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c2273, c2266, c2274, c1805, c1024, c2279, c2280, c1021, c2259, c1030, c1785, c1039, c1017, c1019] c2281 (by decide) p (sat_cons (step2273 p h) (sat_cons (step2266 p h) (sat_cons (step2274 p h) (sat_cons (step1805 p h) (sat_cons (step1024 p h) (sat_cons (step2279 p h) (sat_cons (step2280 p h) (sat_cons (step1021 p h) (sat_cons (step2259 p h) (sat_cons (step1030 p h) (sat_cons (step1785 p h) (sat_cons (step1039 p h) (sat_cons (step1017 p h) (sat_cons (step1019 p h) (sat_nil p)))))))))))))))
def c2282 : List Lit := [(67, true), (10, true), (1597, true), (1585, true)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c2273, c1842, c1843, c1573, c1153, c1160, c1161, c1185, c1155, c1174, c238, c1167] c2282 (by decide) p (sat_cons (step2273 p h) (sat_cons (step1842 p h) (sat_cons (step1843 p h) (sat_cons (step1573 p h) (sat_cons (step1153 p h) (sat_cons (step1160 p h) (sat_cons (step1161 p h) (sat_cons (step1185 p h) (sat_cons (step1155 p h) (sat_cons (step1174 p h) (sat_cons (step238 p h) (sat_cons (step1167 p h) (sat_nil p)))))))))))))
def c2283 : List Lit := [(1580, true), (1646, true), (9, false), (54, false)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c1152, c1676, c1839, c366, c367, c1267] c2283 (by decide) p (sat_cons (step1152 p h) (sat_cons (step1676 p h) (sat_cons (step1839 p h) (sat_cons (step366 p h) (sat_cons (step367 p h) (sat_cons (step1267 p h) (sat_nil p)))))))
def c2284 : List Lit := [(45, false), (46, true), (48, false), (49, false), (9, false)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c262, c220, c1848] c2284 (by decide) p (sat_cons (step262 p h) (sat_cons (step220 p h) (sat_cons (step1848 p h) (sat_nil p))))
def c2285 : List Lit := [(1522, true)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1644, c1055, c1049, c1050, c1642, c1810, c62] c2285 (by decide) p (sat_cons (step1644 p h) (sat_cons (step1055 p h) (sat_cons (step1049 p h) (sat_cons (step1050 p h) (sat_cons (step1642 p h) (sat_cons (step1810 p h) (sat_cons (step62 p h) (sat_nil p))))))))
def c2286 : List Lit := [(1534, true)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c2285, c1074] c2286 (by decide) p (sat_cons (step2285 p h) (sat_cons (step1074 p h) (sat_nil p)))
def c2287 : List Lit := [(1574, true), (24, true), (1537, true)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c2285, c1062, c1077, c2047, c2205, c1109, c1068, c1067, c2056, c1063, c1081, c1810, c1729, c64, c1056, c1642] c2287 (by decide) p (sat_cons (step2285 p h) (sat_cons (step1062 p h) (sat_cons (step1077 p h) (sat_cons (step2047 p h) (sat_cons (step2205 p h) (sat_cons (step1109 p h) (sat_cons (step1068 p h) (sat_cons (step1067 p h) (sat_cons (step2056 p h) (sat_cons (step1063 p h) (sat_cons (step1081 p h) (sat_cons (step1810 p h) (sat_cons (step1729 p h) (sat_cons (step64 p h) (sat_cons (step1056 p h) (sat_cons (step1642 p h) (sat_nil p)))))))))))))))))
def c2288 : List Lit := [(30, false), (24, true), (31, false), (1537, true)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c2285, c1062, c1077, c2051, c2056, c1068, c1067, c1810, c1063, c1081, c64, c1729, c1642, c1056] c2288 (by decide) p (sat_cons (step2285 p h) (sat_cons (step1062 p h) (sat_cons (step1077 p h) (sat_cons (step2051 p h) (sat_cons (step2056 p h) (sat_cons (step1068 p h) (sat_cons (step1067 p h) (sat_cons (step1810 p h) (sat_cons (step1063 p h) (sat_cons (step1081 p h) (sat_cons (step64 p h) (sat_cons (step1729 p h) (sat_cons (step1642 p h) (sat_cons (step1056 p h) (sat_nil p)))))))))))))))
def c2289 : List Lit := [(1525, true), (80, true), (31, false), (1685, true), (29, false)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c1058, c1059, c2049, c80, c1713, c1811, c1827, c104] c2289 (by decide) p (sat_cons (step1058 p h) (sat_cons (step1059 p h) (sat_cons (step2049 p h) (sat_cons (step80 p h) (sat_cons (step1713 p h) (sat_cons (step1811 p h) (sat_cons (step1827 p h) (sat_cons (step104 p h) (sat_nil p)))))))))
def c2290 : List Lit := [(27, false), (78, false), (83, false), (30, false)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c463, c453, c151, c1894] c2290 (by decide) p (sat_cons (step463 p h) (sat_cons (step453 p h) (sat_cons (step151 p h) (sat_cons (step1894 p h) (sat_nil p)))))
def c2291 : List Lit := [(42, true), (1657, false), (1644, false), (1782, true), (1597, true), (1581, true)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c2014, c1773, c1170, c1153, c1154, c1160, c1185, c1174, c1167, c1765, c366, c368, c367, c1267, c1275, c1311, c1377, c1378, c1540, c1338, c1341, c1333, c1318, c1320, c1326, c1316, c1312, c1313, c464, c1889, c2030, c435, c1424] c2291 (by decide) p (sat_cons (step2014 p h) (sat_cons (step1773 p h) (sat_cons (step1170 p h) (sat_cons (step1153 p h) (sat_cons (step1154 p h) (sat_cons (step1160 p h) (sat_cons (step1185 p h) (sat_cons (step1174 p h) (sat_cons (step1167 p h) (sat_cons (step1765 p h) (sat_cons (step366 p h) (sat_cons (step368 p h) (sat_cons (step367 p h) (sat_cons (step1267 p h) (sat_cons (step1275 p h) (sat_cons (step1311 p h) (sat_cons (step1377 p h) (sat_cons (step1378 p h) (sat_cons (step1540 p h) (sat_cons (step1338 p h) (sat_cons (step1341 p h) (sat_cons (step1333 p h) (sat_cons (step1318 p h) (sat_cons (step1320 p h) (sat_cons (step1326 p h) (sat_cons (step1316 p h) (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step464 p h) (sat_cons (step1889 p h) (sat_cons (step2030 p h) (sat_cons (step435 p h) (sat_cons (step1424 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c2292 : List Lit := [(5, false), (75, false), (10, true), (29, false)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c1789, c75] c2292 (by decide) p (sat_cons (step1789 p h) (sat_cons (step75 p h) (sat_nil p)))
def c2293 : List Lit := [(108, false), (1737, true), (107, true), (91, false), (75, false)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c573, c574, c1425, c1427, c1435] c2293 (by decide) p (sat_cons (step573 p h) (sat_cons (step574 p h) (sat_cons (step1425 p h) (sat_cons (step1427 p h) (sat_cons (step1435 p h) (sat_nil p))))))
def c2294 : List Lit := [(1736, false), (96, true), (1749, true), (1675, true), (1759, true)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c1460, c1461, c1493, c1443, c1445, c1440, c1437, c2254, c2260, c1394] c2294 (by decide) p (sat_cons (step1460 p h) (sat_cons (step1461 p h) (sat_cons (step1493 p h) (sat_cons (step1443 p h) (sat_cons (step1445 p h) (sat_cons (step1440 p h) (sat_cons (step1437 p h) (sat_cons (step2254 p h) (sat_cons (step2260 p h) (sat_cons (step1394 p h) (sat_nil p)))))))))))
def c2295 : List Lit := [(118, false), (113, false), (64, true), (61, false), (80, false)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c639, c675, c1942] c2295 (by decide) p (sat_cons (step639 p h) (sat_cons (step675 p h) (sat_cons (step1942 p h) (sat_nil p))))
def c2296 : List Lit := [(1684, true), (107, false), (30, false), (1669, false)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c1318, c1345, c1342, c1321, c1333, c1312, c1313, c1326, c435, c462, c1889] c2296 (by decide) p (sat_cons (step1318 p h) (sat_cons (step1345 p h) (sat_cons (step1342 p h) (sat_cons (step1321 p h) (sat_cons (step1333 p h) (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step1326 p h) (sat_cons (step435 p h) (sat_cons (step462 p h) (sat_cons (step1889 p h) (sat_nil p))))))))))))
def c2297 : List Lit := [(1719, false), (1759, true), (1740, false), (115, false), (61, false)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c1698, c1487, c1407, c1481, c2129, c1412, c1449, c1388, c1458, c1380, c1429, c632, c1426] c2297 (by decide) p (sat_cons (step1698 p h) (sat_cons (step1487 p h) (sat_cons (step1407 p h) (sat_cons (step1481 p h) (sat_cons (step2129 p h) (sat_cons (step1412 p h) (sat_cons (step1449 p h) (sat_cons (step1388 p h) (sat_cons (step1458 p h) (sat_cons (step1380 p h) (sat_cons (step1429 p h) (sat_cons (step632 p h) (sat_cons (step1426 p h) (sat_nil p))))))))))))))
def c2298 : List Lit := [(1759, true), (1740, false), (115, false), (61, false), (1739, false)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c2297, c1476, c2084] c2298 (by decide) p (sat_cons (step2297 p h) (sat_cons (step1476 p h) (sat_cons (step2084 p h) (sat_nil p))))
def c2299 : List Lit := [(115, false), (1759, true), (61, false), (1739, false), (118, false)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c1476, c2084, c1445, c637, c634, c639, c1397, c1380, c1426, c1388, c1429, c1412, c1683, c1456, c1487, c1493, c1461, c1413, c1430, c2190, c1428] c2299 (by decide) p (sat_cons (step1476 p h) (sat_cons (step2084 p h) (sat_cons (step1445 p h) (sat_cons (step637 p h) (sat_cons (step634 p h) (sat_cons (step639 p h) (sat_cons (step1397 p h) (sat_cons (step1380 p h) (sat_cons (step1426 p h) (sat_cons (step1388 p h) (sat_cons (step1429 p h) (sat_cons (step1412 p h) (sat_cons (step1683 p h) (sat_cons (step1456 p h) (sat_cons (step1487 p h) (sat_cons (step1493 p h) (sat_cons (step1461 p h) (sat_cons (step1413 p h) (sat_cons (step1430 p h) (sat_cons (step2190 p h) (sat_cons (step1428 p h) (sat_nil p))))))))))))))))))))))
def c2300 : List Lit := [(1759, true), (1645, true), (1739, false), (118, false)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c1266, c1265, c375, c1476, c2084, c1407, c1481, c2299, c1942, c1941, c1610, c1441, c1446, c1452, c1462, c1493, c1417, c2203, c678, c1426, c1429, c1432, c1458, c1457, c1423, c1447, c1487, c1442, c1408, c2151] c2300 (by decide) p (sat_cons (step1266 p h) (sat_cons (step1265 p h) (sat_cons (step375 p h) (sat_cons (step1476 p h) (sat_cons (step2084 p h) (sat_cons (step1407 p h) (sat_cons (step1481 p h) (sat_cons (step2299 p h) (sat_cons (step1942 p h) (sat_cons (step1941 p h) (sat_cons (step1610 p h) (sat_cons (step1441 p h) (sat_cons (step1446 p h) (sat_cons (step1452 p h) (sat_cons (step1462 p h) (sat_cons (step1493 p h) (sat_cons (step1417 p h) (sat_cons (step2203 p h) (sat_cons (step678 p h) (sat_cons (step1426 p h) (sat_cons (step1429 p h) (sat_cons (step1432 p h) (sat_cons (step1458 p h) (sat_cons (step1457 p h) (sat_cons (step1423 p h) (sat_cons (step1447 p h) (sat_cons (step1487 p h) (sat_cons (step1442 p h) (sat_cons (step1408 p h) (sat_cons (step2151 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2301 : List Lit := [(115, true), (99, false), (1724, true)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c1663, c1412, c1388, c1380, c1381, c1909, c513] c2301 (by decide) p (sat_cons (step1663 p h) (sat_cons (step1412 p h) (sat_cons (step1388 p h) (sat_cons (step1380 p h) (sat_cons (step1381 p h) (sat_cons (step1909 p h) (sat_cons (step513 p h) (sat_nil p))))))))
def c2302 : List Lit := [(1724, true), (61, false), (118, false)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c1757, c1383, c2301, c637, c634, c1397, c1380, c1399, c1388, c1412] c2302 (by decide) p (sat_cons (step1757 p h) (sat_cons (step1383 p h) (sat_cons (step2301 p h) (sat_cons (step637 p h) (sat_cons (step634 p h) (sat_cons (step1397 p h) (sat_cons (step1380 p h) (sat_cons (step1399 p h) (sat_cons (step1388 p h) (sat_cons (step1412 p h) (sat_nil p)))))))))))
def c2303 : List Lit := [(121, false), (84, false), (108, true), (111, false), (107, false)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c601, c739, c1929] c2303 (by decide) p (sat_cons (step601 p h) (sat_cons (step739 p h) (sat_cons (step1929 p h) (sat_nil p))))
def c2304 : List Lit := [(1760, false), (1546, false), (1661, false), (1669, false), (29, true), (1598, false), (107, false)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c1318, c1341, c1362, c1110, c2047, c1208, c1233, c2018, c1533, c1528, c1363, c2019, c2296, c1234, c1111, c1214, c1120, c1978, c1145, c1121, c2048, c1112] c2304 (by decide) p (sat_cons (step1318 p h) (sat_cons (step1341 p h) (sat_cons (step1362 p h) (sat_cons (step1110 p h) (sat_cons (step2047 p h) (sat_cons (step1208 p h) (sat_cons (step1233 p h) (sat_cons (step2018 p h) (sat_cons (step1533 p h) (sat_cons (step1528 p h) (sat_cons (step1363 p h) (sat_cons (step2019 p h) (sat_cons (step2296 p h) (sat_cons (step1234 p h) (sat_cons (step1111 p h) (sat_cons (step1214 p h) (sat_cons (step1120 p h) (sat_cons (step1978 p h) (sat_cons (step1145 p h) (sat_cons (step1121 p h) (sat_cons (step2048 p h) (sat_cons (step1112 p h) (sat_nil p)))))))))))))))))))))))
def c2305 : List Lit := [(118, true), (1720, false), (1760, true), (115, false), (1741, false), (61, false)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c2118, c1429, c1426, c638, c632, c1439, c1380, c1698, c1388, c1494, c1413] c2305 (by decide) p (sat_cons (step2118 p h) (sat_cons (step1429 p h) (sat_cons (step1426 p h) (sat_cons (step638 p h) (sat_cons (step632 p h) (sat_cons (step1439 p h) (sat_cons (step1380 p h) (sat_cons (step1698 p h) (sat_cons (step1388 p h) (sat_cons (step1494 p h) (sat_cons (step1413 p h) (sat_nil p))))))))))))
def c2306 : List Lit := [(1720, false), (1760, true), (61, false), (115, false), (1741, false)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c2305, c640, c634, c639, c1438, c1380, c1426, c1446, c1388, c1429, c1413, c1457, c1494] c2306 (by decide) p (sat_cons (step2305 p h) (sat_cons (step640 p h) (sat_cons (step634 p h) (sat_cons (step639 p h) (sat_cons (step1438 p h) (sat_cons (step1380 p h) (sat_cons (step1426 p h) (sat_cons (step1446 p h) (sat_cons (step1388 p h) (sat_cons (step1429 p h) (sat_cons (step1413 p h) (sat_cons (step1457 p h) (sat_cons (step1494 p h) (sat_nil p))))))))))))))
def c2307 : List Lit := [(115, false), (1741, false), (1720, true), (1750, true), (118, false), (61, false)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c637, c640, c639, c1397, c1438, c1426, c1446, c1462, c1430, c1432, c1428, c2190] c2307 (by decide) p (sat_cons (step637 p h) (sat_cons (step640 p h) (sat_cons (step639 p h) (sat_cons (step1397 p h) (sat_cons (step1438 p h) (sat_cons (step1426 p h) (sat_cons (step1446 p h) (sat_cons (step1462 p h) (sat_cons (step1430 p h) (sat_cons (step1432 p h) (sat_cons (step1428 p h) (sat_cons (step2190 p h) (sat_nil p)))))))))))))
def c2308 : List Lit := [(1736, true), (113, true), (1720, true)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c1426, c1430, c1432, c1428, c1423, c2159, c2190, c609, c1397, c1922, c546] c2308 (by decide) p (sat_cons (step1426 p h) (sat_cons (step1430 p h) (sat_cons (step1432 p h) (sat_cons (step1428 p h) (sat_cons (step1423 p h) (sat_cons (step2159 p h) (sat_cons (step2190 p h) (sat_cons (step609 p h) (sat_cons (step1397 p h) (sat_cons (step1922 p h) (sat_cons (step546 p h) (sat_nil p))))))))))))
def c2309 : List Lit := [(1557, false), (1575, true)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c1978, c1120, c1121, c1145, c1112, c2048] c2309 (by decide) p (sat_cons (step1978 p h) (sat_cons (step1120 p h) (sat_cons (step1121 p h) (sat_cons (step1145 p h) (sat_cons (step1112 p h) (sat_cons (step2048 p h) (sat_nil p)))))))
def c2310 : List Lit := [(1667, true), (83, false), (30, false), (107, false)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c1312, c1313, c462, c435, c1889] c2310 (by decide) p (sat_cons (step1312 p h) (sat_cons (step1313 p h) (sat_cons (step462 p h) (sat_cons (step435 p h) (sat_cons (step1889 p h) (sat_nil p))))))
def c2311 : List Lit := [(1717, true), (102, true), (109, false)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c1396, c1397, c546, c1921] c2311 (by decide) p (sat_cons (step1396 p h) (sat_cons (step1397 p h) (sat_cons (step546 p h) (sat_cons (step1921 p h) (sat_nil p)))))
def c2312 : List Lit := [(104, false), (103, false), (102, true), (109, false)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c541, c1921] c2312 (by decide) p (sat_cons (step541 p h) (sat_cons (step1921 p h) (sat_nil p)))
def c2313 : List Lit := [(115, true), (99, false), (94, false)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c1909, c1910, c1594] c2313 (by decide) p (sat_cons (step1909 p h) (sat_cons (step1910 p h) (sat_cons (step1594 p h) (sat_nil p))))
def c2314 : List Lit := [(1569, true), (57, false), (1564, false)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c1766, c1132, c1126, c1127, c1835, c195] c2314 (by decide) p (sat_cons (step1766 p h) (sat_cons (step1132 p h) (sat_cons (step1126 p h) (sat_cons (step1127 p h) (sat_cons (step1835 p h) (sat_cons (step195 p h) (sat_nil p)))))))
def c2315 : List Lit := [(1597, true), (29, false), (1630, true)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c1188, c2281] c2315 (by decide) p (sat_cons (step1188 p h) (sat_cons (step2281 p h) (sat_nil p)))
end B112E020
