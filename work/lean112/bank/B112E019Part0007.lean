import B112E019Part0006
namespace B112E019
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2254 : List Lit := [(3, false), (1594, true), (76, true), (58, false), (98, false), (38, false)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.TreeRup.prove_clause [c2179, c1236, c2192, c1306, c2253, c1237, c1240, c1229, c1217, c1219, c1957, c1214, c1215, c937, c85, c938, c2104, c89, c941, c936, c1994, c956, c84, c958, c68, c2120, c1188, c1025, c1027, c1020, c986, c1017, c982, c983, c1008, c981, c976, c1005, c978, c973, c155, c157, c1225, c1227, c1231, c8, c9, c1222, c1223, c1178, c1185, c1180, c1194, c1205, c1267, c1397, c1357, c1923, c1307, c1294, c1296, c1291, c1292, c1288, c112, c2196, c2238, c1356, c37, c1402, c1187, c1273, c1197, c1206] c2254 (by decide) p (sat_cons (step2179 p h) (sat_cons (step1236 p h) (sat_cons (step2192 p h) (sat_cons (step1306 p h) (sat_cons (step2253 p h) (sat_cons (step1237 p h) (sat_cons (step1240 p h) (sat_cons (step1229 p h) (sat_cons (step1217 p h) (sat_cons (step1219 p h) (sat_cons (step1957 p h) (sat_cons (step1214 p h) (sat_cons (step1215 p h) (sat_cons (step937 p h) (sat_cons (step85 p h) (sat_cons (step938 p h) (sat_cons (step2104 p h) (sat_cons (step89 p h) (sat_cons (step941 p h) (sat_cons (step936 p h) (sat_cons (step1994 p h) (sat_cons (step956 p h) (sat_cons (step84 p h) (sat_cons (step958 p h) (sat_cons (step68 p h) (sat_cons (step2120 p h) (sat_cons (step1188 p h) (sat_cons (step1025 p h) (sat_cons (step1027 p h) (sat_cons (step1020 p h) (sat_cons (step986 p h) (sat_cons (step1017 p h) (sat_cons (step982 p h) (sat_cons (step983 p h) (sat_cons (step1008 p h) (sat_cons (step981 p h) (sat_cons (step976 p h) (sat_cons (step1005 p h) (sat_cons (step978 p h) (sat_cons (step973 p h) (sat_cons (step155 p h) (sat_cons (step157 p h) (sat_cons (step1225 p h) (sat_cons (step1227 p h) (sat_cons (step1231 p h) (sat_cons (step8 p h) (sat_cons (step9 p h) (sat_cons (step1222 p h) (sat_cons (step1223 p h) (sat_cons (step1178 p h) (sat_cons (step1185 p h) (sat_cons (step1180 p h) (sat_cons (step1194 p h) (sat_cons (step1205 p h) (sat_cons (step1267 p h) (sat_cons (step1397 p h) (sat_cons (step1357 p h) (sat_cons (step1923 p h) (sat_cons (step1307 p h) (sat_cons (step1294 p h) (sat_cons (step1296 p h) (sat_cons (step1291 p h) (sat_cons (step1292 p h) (sat_cons (step1288 p h) (sat_cons (step112 p h) (sat_cons (step2196 p h) (sat_cons (step2238 p h) (sat_cons (step1356 p h) (sat_cons (step37 p h) (sat_cons (step1402 p h) (sat_cons (step1187 p h) (sat_cons (step1273 p h) (sat_cons (step1197 p h) (sat_cons (step1206 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2255 : List Lit := [(11, true), (1509, false), (5, true), (137, true), (1594, true), (98, false), (38, false)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c1178, c1180, c2192, c1306, c1355, c1407, c1274, c1185, c2207, c1990, c1179, c73, c1181, c1188, c1210, c1194] c2255 (by decide) p (sat_cons (step1178 p h) (sat_cons (step1180 p h) (sat_cons (step2192 p h) (sat_cons (step1306 p h) (sat_cons (step1355 p h) (sat_cons (step1407 p h) (sat_cons (step1274 p h) (sat_cons (step1185 p h) (sat_cons (step2207 p h) (sat_cons (step1990 p h) (sat_cons (step1179 p h) (sat_cons (step73 p h) (sat_cons (step1181 p h) (sat_cons (step1188 p h) (sat_cons (step1210 p h) (sat_cons (step1194 p h) (sat_nil p)))))))))))))))))
def c2256 : List Lit := [(11, false), (3, true), (132, true)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c43, c42, c1976, c1753] c2256 (by decide) p (sat_cons (step43 p h) (sat_cons (step42 p h) (sat_cons (step1976 p h) (sat_cons (step1753 p h) (sat_nil p)))))
def c2257 : List Lit := [(1594, true), (58, false), (98, false), (38, false), (86, true)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c2174, c2179, c2254, c275, c1010, c1013, c1015, c1020, c1025, c2120, c958, c960, c956, c929, c930, c941, c943, c928, c918, c938, c935, c923, c916, c937, c922, c913, c1957, c17, c1240, c2255, c2256] c2257 (by decide) p (sat_cons (step2174 p h) (sat_cons (step2179 p h) (sat_cons (step2254 p h) (sat_cons (step275 p h) (sat_cons (step1010 p h) (sat_cons (step1013 p h) (sat_cons (step1015 p h) (sat_cons (step1020 p h) (sat_cons (step1025 p h) (sat_cons (step2120 p h) (sat_cons (step958 p h) (sat_cons (step960 p h) (sat_cons (step956 p h) (sat_cons (step929 p h) (sat_cons (step930 p h) (sat_cons (step941 p h) (sat_cons (step943 p h) (sat_cons (step928 p h) (sat_cons (step918 p h) (sat_cons (step938 p h) (sat_cons (step935 p h) (sat_cons (step923 p h) (sat_cons (step916 p h) (sat_cons (step937 p h) (sat_cons (step922 p h) (sat_cons (step913 p h) (sat_cons (step1957 p h) (sat_cons (step17 p h) (sat_cons (step1240 p h) (sat_cons (step2255 p h) (sat_cons (step2256 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2258 : List Lit := [(3, true), (11, false), (58, false), (86, true)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c275, c2256, c1010, c922, c1013, c923, c1015, c928, c1020, c929, c1025, c960, c2120] c2258 (by decide) p (sat_cons (step275 p h) (sat_cons (step2256 p h) (sat_cons (step1010 p h) (sat_cons (step922 p h) (sat_cons (step1013 p h) (sat_cons (step923 p h) (sat_cons (step1015 p h) (sat_cons (step928 p h) (sat_cons (step1020 p h) (sat_cons (step929 p h) (sat_cons (step1025 p h) (sat_cons (step960 p h) (sat_cons (step2120 p h) (sat_nil p))))))))))))))
def c2259 : List Lit := [(1673, true), (100, false), (41, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1566, c574] c2259 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1566 p h) (sat_cons (step574 p h) (sat_nil p))))
def c2260 : List Lit := [(54, true), (1566, true), (172, true)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c2029, c1331, c1335, c1343, c1322, c1319, c1320, c237, c238, c1770] c2260 (by decide) p (sat_cons (step2029 p h) (sat_cons (step1331 p h) (sat_cons (step1335 p h) (sat_cons (step1343 p h) (sat_cons (step1322 p h) (sat_cons (step1319 p h) (sat_cons (step1320 p h) (sat_cons (step237 p h) (sat_cons (step238 p h) (sat_cons (step1770 p h) (sat_nil p)))))))))))
def c2261 : List Lit := [(1696, true), (116, false), (1703, true), (241, true), (98, false)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c1611, c1612, c1929, c845, c839, c830, c831, c1595, c1609, c1602, c1616, c1627] c2261 (by decide) p (sat_cons (step1611 p h) (sat_cons (step1612 p h) (sat_cons (step1929 p h) (sat_cons (step845 p h) (sat_cons (step839 p h) (sat_cons (step830 p h) (sat_cons (step831 p h) (sat_cons (step1595 p h) (sat_cons (step1609 p h) (sat_cons (step1602 p h) (sat_cons (step1616 p h) (sat_cons (step1627 p h) (sat_nil p)))))))))))))
def c2262 : List Lit := [(1703, true), (473, true), (98, false)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c1159, c1141, c1138, c1137, c1157, c1154, c1147, c1144, c1153, c1151, c1150, c1623, c1872, c2261, c1614, c1617, c1627, c1609, c1600, c1602, c1597, c1598, c1595, c739, c1942, c775] c2262 (by decide) p (sat_cons (step1159 p h) (sat_cons (step1141 p h) (sat_cons (step1138 p h) (sat_cons (step1137 p h) (sat_cons (step1157 p h) (sat_cons (step1154 p h) (sat_cons (step1147 p h) (sat_cons (step1144 p h) (sat_cons (step1153 p h) (sat_cons (step1151 p h) (sat_cons (step1150 p h) (sat_cons (step1623 p h) (sat_cons (step1872 p h) (sat_cons (step2261 p h) (sat_cons (step1614 p h) (sat_cons (step1617 p h) (sat_cons (step1627 p h) (sat_cons (step1609 p h) (sat_cons (step1600 p h) (sat_cons (step1602 p h) (sat_cons (step1597 p h) (sat_cons (step1598 p h) (sat_cons (step1595 p h) (sat_cons (step739 p h) (sat_cons (step1942 p h) (sat_cons (step775 p h) (sat_nil p)))))))))))))))))))))))))))
def c2263 : List Lit := [(100, true), (44, false), (41, false), (162, true)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c170, c169, c1761] c2263 (by decide) p (sat_cons (step170 p h) (sat_cons (step169 p h) (sat_cons (step1761 p h) (sat_nil p))))
def c2264 : List Lit := [(100, false), (1676, true), (41, false)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c1569, c2259, c1571, c1562, c572, c571, c1567] c2264 (by decide) p (sat_cons (step1569 p h) (sat_cons (step2259 p h) (sat_cons (step1571 p h) (sat_cons (step1562 p h) (sat_cons (step572 p h) (sat_cons (step571 p h) (sat_cons (step1567 p h) (sat_nil p))))))))
def c2265 : List Lit := [(1565, true), (41, false), (175, true)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c1339, c1342, c1335, c1324, c1331, c1317, c2203, c194, c255] c2265 (by decide) p (sat_cons (step1339 p h) (sat_cons (step1342 p h) (sat_cons (step1335 p h) (sat_cons (step1324 p h) (sat_cons (step1331 p h) (sat_cons (step1317 p h) (sat_cons (step2203 p h) (sat_cons (step194 p h) (sat_cons (step255 p h) (sat_nil p))))))))))
def c2266 : List Lit := [(1576, true), (1534, false), (43, true), (355, true), (1531, false)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c1292, c1297, c1308, c1294, c1307, c1022, c1000, c998, c996, c1020, c1017, c1008, c1005, c1373, c1364, c1369, c1309, c2260, c1339, c1342, c1298, c1335, c1324, c1293, c1317, c2203, c195, c255] c2266 (by decide) p (sat_cons (step1292 p h) (sat_cons (step1297 p h) (sat_cons (step1308 p h) (sat_cons (step1294 p h) (sat_cons (step1307 p h) (sat_cons (step1022 p h) (sat_cons (step1000 p h) (sat_cons (step998 p h) (sat_cons (step996 p h) (sat_cons (step1020 p h) (sat_cons (step1017 p h) (sat_cons (step1008 p h) (sat_cons (step1005 p h) (sat_cons (step1373 p h) (sat_cons (step1364 p h) (sat_cons (step1369 p h) (sat_cons (step1309 p h) (sat_cons (step2260 p h) (sat_cons (step1339 p h) (sat_cons (step1342 p h) (sat_cons (step1298 p h) (sat_cons (step1335 p h) (sat_cons (step1324 p h) (sat_cons (step1293 p h) (sat_cons (step1317 p h) (sat_cons (step2203 p h) (sat_cons (step195 p h) (sat_cons (step255 p h) (sat_nil p)))))))))))))))))))))))))))))
def c2267 : List Lit := [(1565, true), (355, true)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c1022, c1002, c992, c991, c1000, c998, c996, c1020, c1017, c1008, c1005, c1007, c1006, c1339, c1342, c1335, c1322, c1324, c1330, c1331, c1316, c1317, c2203, c255, c261, c195, c1912, c221, c222, c1768, c2020] c2267 (by decide) p (sat_cons (step1022 p h) (sat_cons (step1002 p h) (sat_cons (step992 p h) (sat_cons (step991 p h) (sat_cons (step1000 p h) (sat_cons (step998 p h) (sat_cons (step996 p h) (sat_cons (step1020 p h) (sat_cons (step1017 p h) (sat_cons (step1008 p h) (sat_cons (step1005 p h) (sat_cons (step1007 p h) (sat_cons (step1006 p h) (sat_cons (step1339 p h) (sat_cons (step1342 p h) (sat_cons (step1335 p h) (sat_cons (step1322 p h) (sat_cons (step1324 p h) (sat_cons (step1330 p h) (sat_cons (step1331 p h) (sat_cons (step1316 p h) (sat_cons (step1317 p h) (sat_cons (step2203 p h) (sat_cons (step255 p h) (sat_cons (step261 p h) (sat_cons (step195 p h) (sat_cons (step1912 p h) (sat_cons (step221 p h) (sat_cons (step222 p h) (sat_cons (step1768 p h) (sat_cons (step2020 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2268 : List Lit := [(1553, true), (49, false), (44, true), (339, true)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c1002, c992, c991, c1000, c998, c996, c1322, c1324, c1912, c1316, c221, c222, c1768, c2020] c2268 (by decide) p (sat_cons (step1002 p h) (sat_cons (step992 p h) (sat_cons (step991 p h) (sat_cons (step1000 p h) (sat_cons (step998 p h) (sat_cons (step996 p h) (sat_cons (step1322 p h) (sat_cons (step1324 p h) (sat_cons (step1912 p h) (sat_cons (step1316 p h) (sat_cons (step221 p h) (sat_cons (step222 p h) (sat_cons (step1768 p h) (sat_cons (step2020 p h) (sat_nil p)))))))))))))))
def c2269 : List Lit := [(42, false), (52, false), (49, false), (51, false), (172, true)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c241, c240, c239] c2269 (by decide) p (sat_cons (step241 p h) (sat_cons (step240 p h) (sat_cons (step239 p h) (sat_nil p))))
def c2270 : List Lit := [(48, false), (42, true), (44, true), (169, true)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c221, c222, c1768, c2020] c2270 (by decide) p (sat_cons (step221 p h) (sat_cons (step222 p h) (sat_cons (step1768 p h) (sat_cons (step2020 p h) (sat_nil p)))))
def c2271 : List Lit := [(1699, true), (115, true), (117, false)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c1609, c1619, c1617, c1610, c1929] c2271 (by decide) p (sat_cons (step1609 p h) (sat_cons (step1619 p h) (sat_cons (step1617 p h) (sat_cons (step1610 p h) (sat_cons (step1929 p h) (sat_nil p))))))
def c2272 : List Lit := [(1696, true), (117, false), (55, false)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c1611, c1612, c804] c2272 (by decide) p (sat_cons (step1611 p h) (sat_cons (step1612 p h) (sat_cons (step804 p h) (sat_nil p))))
def c2273 : List Lit := [(1694, true), (52, false), (117, false), (51, false), (236, true)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c1608, c1609, c232, c776, c777, c788] c2273 (by decide) p (sat_cons (step1608 p h) (sat_cons (step1609 p h) (sat_cons (step232 p h) (sat_cons (step776 p h) (sat_cons (step777 p h) (sat_cons (step788 p h) (sat_nil p)))))))
def c2274 : List Lit := [(1673, true), (112, false), (107, false), (110, false), (224, true)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1566, c693, c632, c596, c625] c2274 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1566 p h) (sat_cons (step693 p h) (sat_cons (step632 p h) (sat_cons (step596 p h) (sat_cons (step625 p h) (sat_nil p)))))))
def c2275 : List Lit := [(67, false), (110, false), (46, false), (188, true), (12, true)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c314, c658] c2275 (by decide) p (sat_cons (step314 p h) (sat_cons (step658 p h) (sat_nil p)))
def c2276 : List Lit := [(1668, true), (212, true), (98, false)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c1557, c1559, c1554, c1555, c526, c504, c496] c2276 (by decide) p (sat_cons (step1557 p h) (sat_cons (step1559 p h) (sat_cons (step1554 p h) (sat_cons (step1555 p h) (sat_cons (step526 p h) (sat_cons (step504 p h) (sat_cons (step496 p h) (sat_nil p))))))))
def c2277 : List Lit := [(1644, true), (210, true), (1627, false), (86, true)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c1470, c1499, c1495, c1471, c1482, c1484, c1465, c1479, c1476, c1477, c431, c1947] c2277 (by decide) p (sat_cons (step1470 p h) (sat_cons (step1499 p h) (sat_cons (step1495 p h) (sat_cons (step1471 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1465 p h) (sat_cons (step1479 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step431 p h) (sat_cons (step1947 p h) (sat_nil p)))))))))))))
def c2278 : List Lit := [(82, true), (1645, true), (102, false), (103, false), (201, true), (1627, false)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c1470, c1496, c1487, c1477, c1478, c1484, c1500, c1471, c1465, c1466, c386, c590, c403] c2278 (by decide) p (sat_cons (step1470 p h) (sat_cons (step1496 p h) (sat_cons (step1487 p h) (sat_cons (step1477 p h) (sat_cons (step1478 p h) (sat_cons (step1484 p h) (sat_cons (step1500 p h) (sat_cons (step1471 p h) (sat_cons (step1465 p h) (sat_cons (step1466 p h) (sat_cons (step386 p h) (sat_cons (step590 p h) (sat_cons (step403 p h) (sat_nil p))))))))))))))
def c2279 : List Lit := [(1669, true), (103, false), (95, true), (26, false), (212, true), (98, false)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c1554, c2222, c1560, c426] c2279 (by decide) p (sat_cons (step1554 p h) (sat_cons (step2222 p h) (sat_cons (step1560 p h) (sat_cons (step426 p h) (sat_nil p)))))
def c2280 : List Lit := [(1576, true), (1673, true), (43, true), (357, true), (1531, false)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c1025, c2267, c1027, c986, c983, c975, c974, c1369, c2266, c1308, c1288, c1295, c2259, c2263, c1293] c2280 (by decide) p (sat_cons (step1025 p h) (sat_cons (step2267 p h) (sat_cons (step1027 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step975 p h) (sat_cons (step974 p h) (sat_cons (step1369 p h) (sat_cons (step2266 p h) (sat_cons (step1308 p h) (sat_cons (step1288 p h) (sat_cons (step1295 p h) (sat_cons (step2259 p h) (sat_cons (step2263 p h) (sat_cons (step1293 p h) (sat_nil p))))))))))))))))
def c2281 : List Lit := [(80, false), (26, false), (1673, true), (201, true)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c1566, c1565, c590, c423, c402] c2281 (by decide) p (sat_cons (step1566 p h) (sat_cons (step1565 p h) (sat_cons (step590 p h) (sat_cons (step423 p h) (sat_cons (step402 p h) (sat_nil p))))))
def c2282 : List Lit := [(63, false), (1673, true), (184, true)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c1566, c1565, c292, c584] c2282 (by decide) p (sat_cons (step1566 p h) (sat_cons (step1565 p h) (sat_cons (step292 p h) (sat_cons (step584 p h) (sat_nil p)))))
def c2283 : List Lit := [(63, true), (1621, true), (1622, true), (377, true)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c1056, c1050, c1054, c1052, c1051, c1884, c1948, c338, c2043] c2283 (by decide) p (sat_cons (step1056 p h) (sat_cons (step1050 p h) (sat_cons (step1054 p h) (sat_cons (step1052 p h) (sat_cons (step1051 p h) (sat_cons (step1884 p h) (sat_cons (step1948 p h) (sat_cons (step338 p h) (sat_cons (step2043 p h) (sat_nil p))))))))))
def c2284 : List Lit := [(1704, true), (1686, false), (99, false), (100, true), (1696, false), (233, true)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c1602, c1614, c1632, c1628, c1603, c1617, c1597, c1598, c1608, c737, c750] c2284 (by decide) p (sat_cons (step1602 p h) (sat_cons (step1614 p h) (sat_cons (step1632 p h) (sat_cons (step1628 p h) (sat_cons (step1603 p h) (sat_cons (step1617 p h) (sat_cons (step1597 p h) (sat_cons (step1598 p h) (sat_cons (step1608 p h) (sat_cons (step737 p h) (sat_cons (step750 p h) (sat_nil p))))))))))))
def c2285 : List Lit := [(1576, true), (100, true), (43, true), (357, true), (1531, false)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1025, c2267, c1027, c986, c983, c975, c974, c1369, c2266, c1308, c1288, c1295, c2263, c1293] c2285 (by decide) p (sat_cons (step1025 p h) (sat_cons (step2267 p h) (sat_cons (step1027 p h) (sat_cons (step986 p h) (sat_cons (step983 p h) (sat_cons (step975 p h) (sat_cons (step974 p h) (sat_cons (step1369 p h) (sat_cons (step2266 p h) (sat_cons (step1308 p h) (sat_cons (step1288 p h) (sat_cons (step1295 p h) (sat_cons (step2263 p h) (sat_cons (step1293 p h) (sat_nil p)))))))))))))))
def c2286 : List Lit := [(1675, true), (100, false), (103, false)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1570, c1566, c1562, c593] c2286 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1570 p h) (sat_cons (step1566 p h) (sat_cons (step1562 p h) (sat_cons (step593 p h) (sat_nil p))))))
def c2287 : List Lit := [(1673, false), (1676, true), (1714, true), (1686, false), (100, true), (1696, false), (1668, false), (233, true)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c1568, c1571, c1581, c1562, c1656, c2284] c2287 (by decide) p (sat_cons (step1568 p h) (sat_cons (step1571 p h) (sat_cons (step1581 p h) (sat_cons (step1562 p h) (sat_cons (step1656 p h) (sat_cons (step2284 p h) (sat_nil p)))))))
def c2288 : List Lit := [(1621, true), (63, true), (190, true)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c1427, c1948, c1449, c1433, c1436] c2288 (by decide) p (sat_cons (step1427 p h) (sat_cons (step1948 p h) (sat_cons (step1449 p h) (sat_cons (step1433 p h) (sat_cons (step1436 p h) (sat_nil p))))))
def c2289 : List Lit := [(1676, true), (100, false), (103, true), (63, false)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1569, c1571, c1567, c1562, c581] c2289 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1569 p h) (sat_cons (step1571 p h) (sat_cons (step1567 p h) (sat_cons (step1562 p h) (sat_cons (step581 p h) (sat_nil p)))))))
def c2290 : List Lit := [(1543, true), (41, true)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c1288, c1296, c1303, c1307, c1299, c2192, c1290] c2290 (by decide) p (sat_cons (step1288 p h) (sat_cons (step1296 p h) (sat_cons (step1303 p h) (sat_cons (step1307 p h) (sat_cons (step1299 p h) (sat_cons (step2192 p h) (sat_cons (step1290 p h) (sat_nil p))))))))
def c2291 : List Lit := [(106, false), (1567, true), (76, false), (1640, true), (81, false), (102, false), (69, false), (67, false)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c1483, c657, c666, c1480, c1481, c1485, c1476, c1477, c461, c469, c431, c2174, c477, c1333, c696, c1334, c1318, c1347, c1327] c2291 (by decide) p (sat_cons (step1483 p h) (sat_cons (step657 p h) (sat_cons (step666 p h) (sat_cons (step1480 p h) (sat_cons (step1481 p h) (sat_cons (step1485 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step461 p h) (sat_cons (step469 p h) (sat_cons (step431 p h) (sat_cons (step2174 p h) (sat_cons (step477 p h) (sat_cons (step1333 p h) (sat_cons (step696 p h) (sat_cons (step1334 p h) (sat_cons (step1318 p h) (sat_cons (step1347 p h) (sat_cons (step1327 p h) (sat_nil p))))))))))))))))))))
def c2292 : List Lit := [(371, false), (64, false), (74, false), (76, false), (71, false), (69, false)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c1070, c2128, c1105, c1065, c1169, c1054, c2146, c1051, c1052, c1030, c338, c1025, c2043, c1020, c298, c1015, c344, c1012, c364, c1011, c1808] c2292 (by decide) p (sat_cons (step1070 p h) (sat_cons (step2128 p h) (sat_cons (step1105 p h) (sat_cons (step1065 p h) (sat_cons (step1169 p h) (sat_cons (step1054 p h) (sat_cons (step2146 p h) (sat_cons (step1051 p h) (sat_cons (step1052 p h) (sat_cons (step1030 p h) (sat_cons (step338 p h) (sat_cons (step1025 p h) (sat_cons (step2043 p h) (sat_cons (step1020 p h) (sat_cons (step298 p h) (sat_cons (step1015 p h) (sat_cons (step344 p h) (sat_cons (step1012 p h) (sat_cons (step364 p h) (sat_cons (step1011 p h) (sat_cons (step1808 p h) (sat_nil p))))))))))))))))))))))
def c2293 : List Lit := [(1682, true), (1674, false), (87, false), (99, true)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c1562, c1572, c1579, c1583, c1575, c1888, c1564] c2293 (by decide) p (sat_cons (step1562 p h) (sat_cons (step1572 p h) (sat_cons (step1579 p h) (sat_cons (step1583 p h) (sat_cons (step1575 p h) (sat_cons (step1888 p h) (sat_cons (step1564 p h) (sat_nil p))))))))
def c2294 : List Lit := [(371, false), (71, false), (77, true), (75, false), (76, false), (69, false), (64, false)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c2128, c2292, c1063, c363, c1061, c1059] c2294 (by decide) p (sat_cons (step2128 p h) (sat_cons (step2292 p h) (sat_cons (step1063 p h) (sat_cons (step363 p h) (sat_cons (step1061 p h) (sat_cons (step1059 p h) (sat_nil p)))))))
def c2295 : List Lit := [(1689, false), (118, true), (110, true), (72, false), (1707, true), (1694, false), (69, false), (64, false)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1617, c1643, c1594, c1604, c1639, c1618, c1607, c1613, c1596, c710, c1964] c2295 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1617 p h) (sat_cons (step1643 p h) (sat_cons (step1594 p h) (sat_cons (step1604 p h) (sat_cons (step1639 p h) (sat_cons (step1618 p h) (sat_cons (step1607 p h) (sat_cons (step1613 p h) (sat_cons (step1596 p h) (sat_cons (step710 p h) (sat_cons (step1964 p h) (sat_nil p)))))))))))))
def c2296 : List Lit := [(58, false), (85, false), (76, false), (87, false)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c2174, c457] c2296 (by decide) p (sat_cons (step2174 p h) (sat_cons (step457 p h) (sat_nil p)))
def c2297 : List Lit := [(373, false), (77, true), (72, false), (65, true), (1627, true)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1462, c1056, c2125, c1065, c2127, c1051, c1068, c1061, c344, c1105, c1059, c1169, c363, c2146, c364, c1030, c1808, c1025, c1011, c1020, c1012, c1015] c2297 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1462 p h) (sat_cons (step1056 p h) (sat_cons (step2125 p h) (sat_cons (step1065 p h) (sat_cons (step2127 p h) (sat_cons (step1051 p h) (sat_cons (step1068 p h) (sat_cons (step1061 p h) (sat_cons (step344 p h) (sat_cons (step1105 p h) (sat_cons (step1059 p h) (sat_cons (step1169 p h) (sat_cons (step363 p h) (sat_cons (step2146 p h) (sat_cons (step364 p h) (sat_cons (step1030 p h) (sat_cons (step1808 p h) (sat_cons (step1025 p h) (sat_cons (step1011 p h) (sat_cons (step1020 p h) (sat_cons (step1012 p h) (sat_cons (step1015 p h) (sat_nil p))))))))))))))))))))))))
def c2298 : List Lit := [(1643, true), (65, true), (67, false)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c1490, c1494, c1482, c1484, c1468, c1470, c1479, c1476, c1477, c1465, c1462, c1463, c469, c431, c461, c377, c487, c1088, c1091, c1093, c1098, c1103, c2135, c1169, c1068, c2146, c1063, c1065, c1030, c1061, c1054, c1025, c1059, c1051, c1052, c1020, c363, c361, c1015, c2048, c1012, c338, c1011, c2043, c1808, c344, c364] c2298 (by decide) p (sat_cons (step1490 p h) (sat_cons (step1494 p h) (sat_cons (step1482 p h) (sat_cons (step1484 p h) (sat_cons (step1468 p h) (sat_cons (step1470 p h) (sat_cons (step1479 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step1465 p h) (sat_cons (step1462 p h) (sat_cons (step1463 p h) (sat_cons (step469 p h) (sat_cons (step431 p h) (sat_cons (step461 p h) (sat_cons (step377 p h) (sat_cons (step487 p h) (sat_cons (step1088 p h) (sat_cons (step1091 p h) (sat_cons (step1093 p h) (sat_cons (step1098 p h) (sat_cons (step1103 p h) (sat_cons (step2135 p h) (sat_cons (step1169 p h) (sat_cons (step1068 p h) (sat_cons (step2146 p h) (sat_cons (step1063 p h) (sat_cons (step1065 p h) (sat_cons (step1030 p h) (sat_cons (step1061 p h) (sat_cons (step1054 p h) (sat_cons (step1025 p h) (sat_cons (step1059 p h) (sat_cons (step1051 p h) (sat_cons (step1052 p h) (sat_cons (step1020 p h) (sat_cons (step363 p h) (sat_cons (step361 p h) (sat_cons (step1015 p h) (sat_cons (step2048 p h) (sat_cons (step1012 p h) (sat_cons (step338 p h) (sat_cons (step1011 p h) (sat_cons (step2043 p h) (sat_cons (step1808 p h) (sat_cons (step344 p h) (sat_cons (step364 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))
def c2299 : List Lit := [(1635, true), (1519, true), (86, true), (89, false), (1631, true), (67, false)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c1470, c1463, c1462, c377, c1866, c1468, c1466, c1465, c1476, c1477, c391, c469, c431, c487, c1088, c1091, c1093, c1098, c2134, c1103, c2135, c1081, c1169, c1070, c1077, c2146, c1045, c1076, c1032, c1042, c417, c958, c960, c1041, c421, c956, c929, c315, c1222, c943, c928, c1230, c935, c924, c1240, c921, c1268, c1952] c2299 (by decide) p (sat_cons (step1470 p h) (sat_cons (step1463 p h) (sat_cons (step1462 p h) (sat_cons (step377 p h) (sat_cons (step1866 p h) (sat_cons (step1468 p h) (sat_cons (step1466 p h) (sat_cons (step1465 p h) (sat_cons (step1476 p h) (sat_cons (step1477 p h) (sat_cons (step391 p h) (sat_cons (step469 p h) (sat_cons (step431 p h) (sat_cons (step487 p h) (sat_cons (step1088 p h) (sat_cons (step1091 p h) (sat_cons (step1093 p h) (sat_cons (step1098 p h) (sat_cons (step2134 p h) (sat_cons (step1103 p h) (sat_cons (step2135 p h) (sat_cons (step1081 p h) (sat_cons (step1169 p h) (sat_cons (step1070 p h) (sat_cons (step1077 p h) (sat_cons (step2146 p h) (sat_cons (step1045 p h) (sat_cons (step1076 p h) (sat_cons (step1032 p h) (sat_cons (step1042 p h) (sat_cons (step417 p h) (sat_cons (step958 p h) (sat_cons (step960 p h) (sat_cons (step1041 p h) (sat_cons (step421 p h) (sat_cons (step956 p h) (sat_cons (step929 p h) (sat_cons (step315 p h) (sat_cons (step1222 p h) (sat_cons (step943 p h) (sat_cons (step928 p h) (sat_cons (step1230 p h) (sat_cons (step935 p h) (sat_cons (step924 p h) (sat_cons (step1240 p h) (sat_cons (step921 p h) (sat_cons (step1268 p h) (sat_cons (step1952 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))
def c2300 : List Lit := [(1504, true), (87, false), (149, true), (86, true), (81, false)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c1228, c1230, c1956, c1226, c1223, c117, c94] c2300 (by decide) p (sat_cons (step1228 p h) (sat_cons (step1230 p h) (sat_cons (step1956 p h) (sat_cons (step1226 p h) (sat_cons (step1223 p h) (sat_cons (step117 p h) (sat_cons (step94 p h) (sat_nil p))))))))
def c2301 : List Lit := [(1686, true), (109, false), (89, false)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c1594, c1595, c712] c2301 (by decide) p (sat_cons (step1594 p h) (sat_cons (step1595 p h) (sat_cons (step712 p h) (sat_nil p))))
def c2302 : List Lit := [(1705, true), (118, true), (109, false), (89, false), (1694, false)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c1612, c1617, c2301, c1602, c1633, c1629, c1605, c1618, c1871, c1613] c2302 (by decide) p (sat_cons (step1612 p h) (sat_cons (step1617 p h) (sat_cons (step2301 p h) (sat_cons (step1602 p h) (sat_cons (step1633 p h) (sat_cons (step1629 p h) (sat_cons (step1605 p h) (sat_cons (step1618 p h) (sat_cons (step1871 p h) (sat_cons (step1613 p h) (sat_nil p)))))))))))
def c2303 : List Lit := [(1674, false), (1682, true), (212, true), (99, true)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1562, c1572, c1583, c1575, c2276, c1564] c2303 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1562 p h) (sat_cons (step1572 p h) (sat_cons (step1583 p h) (sat_cons (step1575 p h) (sat_cons (step2276 p h) (sat_cons (step1564 p h) (sat_nil p))))))))
def c2304 : List Lit := [(1687, false), (116, true), (1692, true), (1705, true), (233, true), (118, false)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1606, c1633, c1597, c1598, c1619, c766, c1610, c748, c739] c2304 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1606 p h) (sat_cons (step1633 p h) (sat_cons (step1597 p h) (sat_cons (step1598 p h) (sat_cons (step1619 p h) (sat_cons (step766 p h) (sat_cons (step1610 p h) (sat_cons (step748 p h) (sat_cons (step739 p h) (sat_nil p)))))))))))
def c2305 : List Lit := [(67, false), (1490, true), (110, false), (475, false), (118, false)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c1167, c2146, c1032, c960, c929, c928, c924, c921, c958, c956, c943, c935, c2145, c1105, c1070, c1045, c1042, c1041, c671, c1952, c314] c2305 (by decide) p (sat_cons (step1167 p h) (sat_cons (step2146 p h) (sat_cons (step1032 p h) (sat_cons (step960 p h) (sat_cons (step929 p h) (sat_cons (step928 p h) (sat_cons (step924 p h) (sat_cons (step921 p h) (sat_cons (step958 p h) (sat_cons (step956 p h) (sat_cons (step943 p h) (sat_cons (step935 p h) (sat_cons (step2145 p h) (sat_cons (step1105 p h) (sat_cons (step1070 p h) (sat_cons (step1045 p h) (sat_cons (step1042 p h) (sat_cons (step1041 p h) (sat_cons (step671 p h) (sat_cons (step1952 p h) (sat_cons (step314 p h) (sat_nil p))))))))))))))))))))))
def c2306 : List Lit := [(1627, true), (196, true), (116, false), (118, false)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c1939, c1936] c2306 (by decide) p (sat_cons (step1939 p h) (sat_cons (step1936 p h) (sat_nil p)))
def c2307 : List Lit := [(44, false), (66, false), (40, true), (47, true), (165, true), (116, false)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c189, c639] c2307 (by decide) p (sat_cons (step189 p h) (sat_cons (step639 p h) (sat_nil p)))
def c2308 : List Lit := [(1557, true), (176, true), (116, false), (118, false)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1938, c802] c2308 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1938 p h) (sat_cons (step802 p h) (sat_nil p))))
def c2309 : List Lit := [(1544, true), (1536, false), (41, true)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c1288, c1297, c1304, c1308, c1300, c2192, c1290] c2309 (by decide) p (sat_cons (step1288 p h) (sat_cons (step1297 p h) (sat_cons (step1304 p h) (sat_cons (step1308 p h) (sat_cons (step1300 p h) (sat_cons (step2192 p h) (sat_cons (step1290 p h) (sat_nil p))))))))
def c2310 : List Lit := [(1531, true), (1551, true), (1541, true), (44, true), (41, true)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c1320, c1319, c1283, c1874, c2192, c1281, c963, c1290, c229, c964, c1301, c971, c1293, c988, c2187, c2119, c239, c1022, c996, c1000, c998] c2310 (by decide) p (sat_cons (step1320 p h) (sat_cons (step1319 p h) (sat_cons (step1283 p h) (sat_cons (step1874 p h) (sat_cons (step2192 p h) (sat_cons (step1281 p h) (sat_cons (step963 p h) (sat_cons (step1290 p h) (sat_cons (step229 p h) (sat_cons (step964 p h) (sat_cons (step1301 p h) (sat_cons (step971 p h) (sat_cons (step1293 p h) (sat_cons (step988 p h) (sat_cons (step2187 p h) (sat_cons (step2119 p h) (sat_cons (step239 p h) (sat_cons (step1022 p h) (sat_cons (step996 p h) (sat_cons (step1000 p h) (sat_cons (step998 p h) (sat_nil p))))))))))))))))))))))
def c2311 : List Lit := [(115, false), (112, false), (116, false), (50, true), (236, true)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c741, c777] c2311 (by decide) p (sat_cons (step741 p h) (sat_cons (step777 p h) (sat_nil p)))
def c2312 : List Lit := [(1703, true), (1694, false), (112, false), (116, false), (233, true)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c1616, c1623, c1617, c1627, c1612, c1600, c1597, c740, c766, c748] c2312 (by decide) p (sat_cons (step1616 p h) (sat_cons (step1623 p h) (sat_cons (step1617 p h) (sat_cons (step1627 p h) (sat_cons (step1612 p h) (sat_cons (step1600 p h) (sat_cons (step1597 p h) (sat_cons (step740 p h) (sat_cons (step766 p h) (sat_cons (step748 p h) (sat_nil p)))))))))))
def c2313 : List Lit := [(1686, true), (120, false), (241, true), (117, true), (118, false), (116, false)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c1594, c1595, c846, c830, c839] c2313 (by decide) p (sat_cons (step1594 p h) (sat_cons (step1595 p h) (sat_cons (step846 p h) (sat_cons (step830 p h) (sat_cons (step839 p h) (sat_nil p))))))
def c2314 : List Lit := [(1653, true), (1627, false), (190, true), (100, false), (112, false)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c1470, c1494, c2154, c1525, c1499, c2288, c1471, c580, c1466] c2314 (by decide) p (sat_cons (step1470 p h) (sat_cons (step1494 p h) (sat_cons (step2154 p h) (sat_cons (step1525 p h) (sat_cons (step1499 p h) (sat_cons (step2288 p h) (sat_cons (step1471 p h) (sat_cons (step580 p h) (sat_cons (step1466 p h) (sat_nil p))))))))))
def c2315 : List Lit := [(80, true), (1686, true), (1645, true), (1627, false)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c1466, c1883, c1471, c2301, c1500, c1479, c1482] c2315 (by decide) p (sat_cons (step1466 p h) (sat_cons (step1883 p h) (sat_cons (step1471 p h) (sat_cons (step2301 p h) (sat_cons (step1500 p h) (sat_cons (step1479 p h) (sat_cons (step1482 p h) (sat_nil p))))))))
def c2316 : List Lit := [(80, false), (1682, true), (212, true), (102, true), (100, false), (112, false)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c592, c589, c1567, c2303] c2316 (by decide) p (sat_cons (step592 p h) (sat_cons (step589 p h) (sat_cons (step1567 p h) (sat_cons (step2303 p h) (sat_nil p)))))
def c2317 : List Lit := [(1686, true), (1490, true), (1656, true), (63, true), (80, true), (1627, false), (188, true), (190, true), (130, true), (137, true), (46, false)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c1594, c2315, c1535, c1944, c1952, c2275] c2317 (by decide) p (sat_cons (step1594 p h) (sat_cons (step2315 p h) (sat_cons (step1535 p h) (sat_cons (step1944 p h) (sat_cons (step1952 p h) (sat_cons (step2275 p h) (sat_nil p)))))))
end B112E019
