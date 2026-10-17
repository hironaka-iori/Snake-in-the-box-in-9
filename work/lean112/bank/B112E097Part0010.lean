import B112E097Part0009
namespace B112E097
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2235 : List Lit := [(89, false), (95, false), (1034, true), (98, true), (123, true)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c2234, c1264, c1602, c432, c1951] c2235 (by decide) p (sat_cons (step2234 p h) (sat_cons (step1264 p h) (sat_cons (step1602 p h) (sat_cons (step432 p h) (sat_cons (step1951 p h) (sat_nil p))))))
def c2236 : List Lit := [(1043, true), (86, false)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1281, c1276, c1277, c1273, c1274, c523, c472, c2177] c2236 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step523 p h) (sat_cons (step472 p h) (sat_cons (step2177 p h) (sat_nil p))))))))))
def c2237 : List Lit := [(34, false), (1056, true), (107, false), (86, false)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c506, c505, c1309] c2237 (by decide) p (sat_cons (step506 p h) (sat_cons (step505 p h) (sat_cons (step1309 p h) (sat_nil p))))
def c2238 : List Lit := [(111, false), (1044, true), (107, false), (86, false)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c525, c527, c1274, c1276, c1282] c2238 (by decide) p (sat_cons (step525 p h) (sat_cons (step527 p h) (sat_cons (step1274 p h) (sat_cons (step1276 p h) (sat_cons (step1282 p h) (sat_nil p))))))
def c2239 : List Lit := [(1044, true), (1056, true), (107, false), (86, false)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c2238, c1309, c526, c524, c1276, c1274, c1282] c2239 (by decide) p (sat_cons (step2238 p h) (sat_cons (step1309 p h) (sat_cons (step526 p h) (sat_cons (step524 p h) (sat_cons (step1276 p h) (sat_cons (step1274 p h) (sat_cons (step1282 p h) (sat_nil p))))))))
def c2240 : List Lit := [(895, true), (112, true), (34, true)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c993, c996, c998, c994, c1865, c1866, c1549] c2240 (by decide) p (sat_cons (step993 p h) (sat_cons (step996 p h) (sat_cons (step998 p h) (sat_cons (step994 p h) (sat_cons (step1865 p h) (sat_cons (step1866 p h) (sat_cons (step1549 p h) (sat_nil p))))))))
def c2241 : List Lit := [(1017, true), (70, true)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1149, c1154, c1236, c1229, c2154, c1200, c1169, c1176] c2241 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1149 p h) (sat_cons (step1154 p h) (sat_cons (step1236 p h) (sat_cons (step1229 p h) (sat_cons (step2154 p h) (sat_cons (step1200 p h) (sat_cons (step1169 p h) (sat_cons (step1176 p h) (sat_nil p))))))))))
def c2242 : List Lit := [(1018, true), (1004, false), (70, true)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c1196, c1141, c1149, c1154, c1230, c1237, c1201, c2154, c1176, c1169] c2242 (by decide) p (sat_cons (step1196 p h) (sat_cons (step1141 p h) (sat_cons (step1149 p h) (sat_cons (step1154 p h) (sat_cons (step1230 p h) (sat_cons (step1237 p h) (sat_cons (step1201 p h) (sat_cons (step2154 p h) (sat_cons (step1176 p h) (sat_cons (step1169 p h) (sat_nil p)))))))))))
def c2243 : List Lit := [(992, true), (1068, true), (81, false), (987, true), (70, true)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1168, c1169, c2231, c1924, c1920, c1919, c2214, c1571, c1159, c1144, c1751, c1153, c1143] c2243 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1168 p h) (sat_cons (step1169 p h) (sat_cons (step2231 p h) (sat_cons (step1924 p h) (sat_cons (step1920 p h) (sat_cons (step1919 p h) (sat_cons (step2214 p h) (sat_cons (step1571 p h) (sat_cons (step1159 p h) (sat_cons (step1144 p h) (sat_cons (step1751 p h) (sat_cons (step1153 p h) (sat_cons (step1143 p h) (sat_nil p)))))))))))))))
def c2244 : List Lit := [(1004, false), (1061, false), (1050, false), (1106, true), (70, true)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c1141, c1149, c1154, c2022, c1385, c1428, c1231, c1196, c1711, c1206, c1244, c1172, c1179, c2242, c1420, c1386, c1347, c2243, c1176, c1201, c1238, c1155, c2154, c2214, c1170, c1924, c2231] c2244 (by decide) p (sat_cons (step1141 p h) (sat_cons (step1149 p h) (sat_cons (step1154 p h) (sat_cons (step2022 p h) (sat_cons (step1385 p h) (sat_cons (step1428 p h) (sat_cons (step1231 p h) (sat_cons (step1196 p h) (sat_cons (step1711 p h) (sat_cons (step1206 p h) (sat_cons (step1244 p h) (sat_cons (step1172 p h) (sat_cons (step1179 p h) (sat_cons (step2242 p h) (sat_cons (step1420 p h) (sat_cons (step1386 p h) (sat_cons (step1347 p h) (sat_cons (step2243 p h) (sat_cons (step1176 p h) (sat_cons (step1201 p h) (sat_cons (step1238 p h) (sat_cons (step1155 p h) (sat_cons (step2154 p h) (sat_cons (step2214 p h) (sat_cons (step1170 p h) (sat_cons (step1924 p h) (sat_cons (step2231 p h) (sat_nil p))))))))))))))))))))))))))))
def c2245 : List Lit := [(983, true), (74, true), (73, false), (81, false), (70, true)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c1144, c1141, c1151, c1153, c1146, c1143, c302] c2245 (by decide) p (sat_cons (step1144 p h) (sat_cons (step1141 p h) (sat_cons (step1151 p h) (sat_cons (step1153 p h) (sat_cons (step1146 p h) (sat_cons (step1143 p h) (sat_cons (step302 p h) (sat_nil p))))))))
def c2246 : List Lit := [(1106, true), (82, false), (987, false), (1033, false), (1074, false), (996, false), (1044, false)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c1200, c1244, c1265, c1293, c1378, c1437, c1428, c1245, c1385, c1201, c1298, c1188, c1268, c1185, c2211] c2246 (by decide) p (sat_cons (step1200 p h) (sat_cons (step1244 p h) (sat_cons (step1265 p h) (sat_cons (step1293 p h) (sat_cons (step1378 p h) (sat_cons (step1437 p h) (sat_cons (step1428 p h) (sat_cons (step1245 p h) (sat_cons (step1385 p h) (sat_cons (step1201 p h) (sat_cons (step1298 p h) (sat_cons (step1188 p h) (sat_cons (step1268 p h) (sat_cons (step1185 p h) (sat_cons (step2211 p h) (sat_nil p))))))))))))))))
def c2247 : List Lit := [(46, false), (123, false), (81, false), (1066, true)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c656, c657, c1326] c2247 (by decide) p (sat_cons (step656 p h) (sat_cons (step657 p h) (sat_cons (step1326 p h) (sat_nil p))))
def c2248 : List Lit := [(1044, false), (1049, true), (1061, false), (1086, true), (123, false), (81, false)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c1288, c1293, c1372, c1265, c1348, c1262, c1662] c2248 (by decide) p (sat_cons (step1288 p h) (sat_cons (step1293 p h) (sat_cons (step1372 p h) (sat_cons (step1265 p h) (sat_cons (step1348 p h) (sat_cons (step1262 p h) (sat_cons (step1662 p h) (sat_nil p))))))))
def c2249 : List Lit := [(100, false), (1066, true), (123, false), (81, false)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c670, c671, c1326] c2249 (by decide) p (sat_cons (step670 p h) (sat_cons (step671 p h) (sat_cons (step1326 p h) (sat_nil p))))
def c2250 : List Lit := [(122, true), (1068, true), (123, false), (81, false)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c1328, c1324, c1326, c1330, c675, c1321] c2250 (by decide) p (sat_cons (step1328 p h) (sat_cons (step1324 p h) (sat_cons (step1326 p h) (sat_cons (step1330 p h) (sat_cons (step675 p h) (sat_cons (step1321 p h) (sat_nil p)))))))
def c2251 : List Lit := [(1068, true), (123, false), (81, false)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c2250, c676, c677, c1321, c1325, c1330] c2251 (by decide) p (sat_cons (step2250 p h) (sat_cons (step676 p h) (sat_cons (step677 p h) (sat_cons (step1321 p h) (sat_cons (step1325 p h) (sat_cons (step1330 p h) (sat_nil p)))))))
def c2252 : List Lit := [(1085, true), (1061, false), (1035, false), (1065, false), (118, true), (122, false), (1068, false), (113, true)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c1347, c1291, c1364, c1371, c1348, c1351, c1292, c1333, c1279, c1281, c1323, c1276, c1277, c1273, c1274, c619, c472, c1692, c2177, c530, c1309, c1320, c1312, c634, c1968] c2252 (by decide) p (sat_cons (step1347 p h) (sat_cons (step1291 p h) (sat_cons (step1364 p h) (sat_cons (step1371 p h) (sat_cons (step1348 p h) (sat_cons (step1351 p h) (sat_cons (step1292 p h) (sat_cons (step1333 p h) (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_cons (step1323 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step619 p h) (sat_cons (step472 p h) (sat_cons (step1692 p h) (sat_cons (step2177 p h) (sat_cons (step530 p h) (sat_cons (step1309 p h) (sat_cons (step1320 p h) (sat_cons (step1312 p h) (sat_cons (step634 p h) (sat_cons (step1968 p h) (sat_nil p))))))))))))))))))))))))))
def c2253 : List Lit := [(1043, true), (1062, true), (115, false), (122, false), (113, true)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1281, c1276, c1277, c1273, c1274, c619, c472, c1692, c2177, c530, c1309, c1320, c1312, c634, c1968] c2253 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step619 p h) (sat_cons (step472 p h) (sat_cons (step1692 p h) (sat_cons (step2177 p h) (sat_cons (step530 p h) (sat_cons (step1309 p h) (sat_cons (step1320 p h) (sat_cons (step1312 p h) (sat_cons (step634 p h) (sat_cons (step1968 p h) (sat_nil p)))))))))))))))))
def c2254 : List Lit := [(1041, true), (116, true), (101, false), (105, false), (1062, true), (122, false), (113, true)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c1276, c1277, c472, c1692, c2177, c530, c1309, c1320, c1312, c634, c1968] c2254 (by decide) p (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step472 p h) (sat_cons (step1692 p h) (sat_cons (step2177 p h) (sat_cons (step530 p h) (sat_cons (step1309 p h) (sat_cons (step1320 p h) (sat_cons (step1312 p h) (sat_cons (step634 p h) (sat_cons (step1968 p h) (sat_nil p))))))))))))
def c2255 : List Lit := [(1004, false), (77, false), (994, false), (1019, true), (115, false), (981, false)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c1174, c1154, c1231, c1206, c1201, c1177, c1238, c1168, c1169, c1155, c1158, c318, c1751, c1144, c1142, c1150] c2255 (by decide) p (sat_cons (step1174 p h) (sat_cons (step1154 p h) (sat_cons (step1231 p h) (sat_cons (step1206 p h) (sat_cons (step1201 p h) (sat_cons (step1177 p h) (sat_cons (step1238 p h) (sat_cons (step1168 p h) (sat_cons (step1169 p h) (sat_cons (step1155 p h) (sat_cons (step1158 p h) (sat_cons (step318 p h) (sat_cons (step1751 p h) (sat_cons (step1144 p h) (sat_cons (step1142 p h) (sat_cons (step1150 p h) (sat_nil p)))))))))))))))))
def c2256 : List Lit := [(53, true), (52, true), (915, true), (906, false), (960, true), (974, true)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c1028, c1030, c2045, c1716, c1082, c1638, c1115, c1997] c2256 (by decide) p (sat_cons (step1028 p h) (sat_cons (step1030 p h) (sat_cons (step2045 p h) (sat_cons (step1716 p h) (sat_cons (step1082 p h) (sat_cons (step1638 p h) (sat_cons (step1115 p h) (sat_cons (step1997 p h) (sat_nil p)))))))))
def c2257 : List Lit := [(52, true), (915, true), (906, false), (70, false), (960, true), (974, true)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c1136, c1133, c2256, c294, c1884] c2257 (by decide) p (sat_cons (step1136 p h) (sat_cons (step1133 p h) (sat_cons (step2256 p h) (sat_cons (step294 p h) (sat_cons (step1884 p h) (sat_nil p))))))
def c2258 : List Lit := [(70, false), (53, false), (52, false), (926, true), (972, true)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c1134, c1133, c200, c294, c198, c1883, c1041, c262, c1051, c1043] c2258 (by decide) p (sat_cons (step1134 p h) (sat_cons (step1133 p h) (sat_cons (step200 p h) (sat_cons (step294 p h) (sat_cons (step198 p h) (sat_cons (step1883 p h) (sat_cons (step1041 p h) (sat_cons (step262 p h) (sat_cons (step1051 p h) (sat_cons (step1043 p h) (sat_nil p)))))))))))
def c2259 : List Lit := [(55, true), (922, false), (53, false), (52, false), (960, true), (916, false), (906, false)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c2013, c1083, c1059, c1051, c1039, c1041, c1048, c177, c1058, c924, c1082, c932, c1115, c1638, c1997] c2259 (by decide) p (sat_cons (step2013 p h) (sat_cons (step1083 p h) (sat_cons (step1059 p h) (sat_cons (step1051 p h) (sat_cons (step1039 p h) (sat_cons (step1041 p h) (sat_cons (step1048 p h) (sat_cons (step177 p h) (sat_cons (step1058 p h) (sat_cons (step924 p h) (sat_cons (step1082 p h) (sat_cons (step932 p h) (sat_cons (step1115 p h) (sat_cons (step1638 p h) (sat_cons (step1997 p h) (sat_nil p))))))))))))))))
def c2260 : List Lit := [(974, true), (922, true)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c1043, c1136, c1138, c1134, c2103, c243, c1898] c2260 (by decide) p (sat_cons (step1043 p h) (sat_cons (step1136 p h) (sat_cons (step1138 p h) (sat_cons (step1134 p h) (sat_cons (step2103 p h) (sat_cons (step243 p h) (sat_cons (step1898 p h) (sat_nil p))))))))
def c2261 : List Lit := [(61, false), (58, true), (922, true)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c2103, c1898] c2261 (by decide) p (sat_cons (step2103 p h) (sat_cons (step1898 p h) (sat_nil p)))
def c2262 : List Lit := [(377, false), (74, false), (76, true), (70, true)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c850, c1987, c1990, c847, c865, c846, c860, c845, c855, c312, c2168] c2262 (by decide) p (sat_cons (step850 p h) (sat_cons (step1987 p h) (sat_cons (step1990 p h) (sat_cons (step847 p h) (sat_cons (step865 p h) (sat_cons (step846 p h) (sat_cons (step860 p h) (sat_cons (step845 p h) (sat_cons (step855 p h) (sat_cons (step312 p h) (sat_cons (step2168 p h) (sat_nil p))))))))))))
def c2263 : List Lit := [(1055, true), (112, false), (72, false)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c1307, c1308, c582] c2263 (by decide) p (sat_cons (step1307 p h) (sat_cons (step1308 p h) (sat_cons (step582 p h) (sat_nil p))))
def c2264 : List Lit := [(70, true), (1005, false), (1021, true), (995, false)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c1175, c1207, c1240, c1141, c2154, c1149, c1169, c1154, c1178, c1233, c1212] c2264 (by decide) p (sat_cons (step1175 p h) (sat_cons (step1207 p h) (sat_cons (step1240 p h) (sat_cons (step1141 p h) (sat_cons (step2154 p h) (sat_cons (step1149 p h) (sat_cons (step1169 p h) (sat_cons (step1154 p h) (sat_cons (step1178 p h) (sat_cons (step1233 p h) (sat_cons (step1212 p h) (sat_nil p))))))))))))
def c2265 : List Lit := [(1043, true), (70, false)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1281, c1276, c1277, c1273, c1274, c517, c479, c472, c1959] c2265 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step517 p h) (sat_cons (step479 p h) (sat_cons (step472 p h) (sat_cons (step1959 p h) (sat_nil p)))))))))))
def c2266 : List Lit := [(81, false), (115, true), (1075, true), (123, false), (122, true), (100, false)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c2163, c668, c1341, c1311, c1313] c2266 (by decide) p (sat_cons (step2163 p h) (sat_cons (step668 p h) (sat_cons (step1341 p h) (sat_cons (step1311 p h) (sat_cons (step1313 p h) (sat_nil p))))))
def c2267 : List Lit := [(985, true), (198, true), (993, true)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c1154, c1157, c1147, c1149, c1144, c1141, c1142, c2183, c1751] c2267 (by decide) p (sat_cons (step1154 p h) (sat_cons (step1157 p h) (sat_cons (step1147 p h) (sat_cons (step1149 p h) (sat_cons (step1144 p h) (sat_cons (step1141 p h) (sat_cons (step1142 p h) (sat_cons (step2183 p h) (sat_cons (step1751 p h) (sat_nil p))))))))))
def c2268 : List Lit := [(986, true), (76, false), (979, false)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c1147, c1155, c1158, c1150, c1751, c1142] c2268 (by decide) p (sat_cons (step1147 p h) (sat_cons (step1155 p h) (sat_cons (step1158 p h) (sat_cons (step1150 p h) (sat_cons (step1751 p h) (sat_cons (step1142 p h) (sat_nil p)))))))
def c2269 : List Lit := [(108, true), (70, false), (1056, true), (1044, true), (89, false)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c1280, c1276, c1278, c1282, c1273, c1274, c479, c2212, c1309, c518, c476, c1958] c2269 (by decide) p (sat_cons (step1280 p h) (sat_cons (step1276 p h) (sat_cons (step1278 p h) (sat_cons (step1282 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step479 p h) (sat_cons (step2212 p h) (sat_cons (step1309 p h) (sat_cons (step518 p h) (sat_cons (step476 p h) (sat_cons (step1958 p h) (sat_nil p)))))))))))))
def c2270 : List Lit := [(1055, false), (108, false), (1063, false), (1040, true), (92, true), (122, true), (113, true), (1075, true)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c1324, c1330, c1347, c1311, c1317, c1316, c1312, c1344, c2051, c1970, c1331, c633, c1326] c2270 (by decide) p (sat_cons (step1324 p h) (sat_cons (step1330 p h) (sat_cons (step1347 p h) (sat_cons (step1311 p h) (sat_cons (step1317 p h) (sat_cons (step1316 p h) (sat_cons (step1312 p h) (sat_cons (step1344 p h) (sat_cons (step2051 p h) (sat_cons (step1970 p h) (sat_cons (step1331 p h) (sat_cons (step633 p h) (sat_cons (step1326 p h) (sat_nil p))))))))))))))
def c2271 : List Lit := [(108, false), (1040, true), (1063, false), (89, false), (92, true), (122, true), (113, true), (1075, true)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c2270, c1307, c1308, c1603, c588, c532, c1964] c2271 (by decide) p (sat_cons (step2270 p h) (sat_cons (step1307 p h) (sat_cons (step1308 p h) (sat_cons (step1603 p h) (sat_cons (step588 p h) (sat_cons (step532 p h) (sat_cons (step1964 p h) (sat_nil p))))))))
def c2272 : List Lit := [(1044, true), (1063, false), (89, false), (92, true), (122, true), (113, true), (1075, true)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c1311, c1324, c1330, c1347, c1319, c1280, c1284, c2271, c1276, c1278, c1282, c1273, c1274, c479, c2212, c1307, c1309, c1317, c1692, c1312, c473] c2272 (by decide) p (sat_cons (step1311 p h) (sat_cons (step1324 p h) (sat_cons (step1330 p h) (sat_cons (step1347 p h) (sat_cons (step1319 p h) (sat_cons (step1280 p h) (sat_cons (step1284 p h) (sat_cons (step2271 p h) (sat_cons (step1276 p h) (sat_cons (step1278 p h) (sat_cons (step1282 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step479 p h) (sat_cons (step2212 p h) (sat_cons (step1307 p h) (sat_cons (step1309 p h) (sat_cons (step1317 p h) (sat_cons (step1692 p h) (sat_cons (step1312 p h) (sat_cons (step473 p h) (sat_nil p))))))))))))))))))))))
def c2273 : List Lit := [(1035, true), (88, true), (1006, true), (86, true), (112, true), (106, false), (89, false), (92, true)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c1265, c1267, c1262, c1263, c1259, c2082, c434, c344, c1185, c1937, c1194, c375, c1184] c2273 (by decide) p (sat_cons (step1265 p h) (sat_cons (step1267 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step1259 p h) (sat_cons (step2082 p h) (sat_cons (step434 p h) (sat_cons (step344 p h) (sat_cons (step1185 p h) (sat_cons (step1937 p h) (sat_cons (step1194 p h) (sat_cons (step375 p h) (sat_cons (step1184 p h) (sat_nil p))))))))))))))
def c2274 : List Lit := [(1020, true), (1004, false), (70, true), (112, true), (106, false), (974, false), (82, true)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c1171, c1174, c1201, c1141, c1149, c1158, c1245, c1239, c1159, c1206, c1152, c1150, c1175, c1143, c1145, c1173, c282, c2214, c1910] c2274 (by decide) p (sat_cons (step1171 p h) (sat_cons (step1174 p h) (sat_cons (step1201 p h) (sat_cons (step1141 p h) (sat_cons (step1149 p h) (sat_cons (step1158 p h) (sat_cons (step1245 p h) (sat_cons (step1239 p h) (sat_cons (step1159 p h) (sat_cons (step1206 p h) (sat_cons (step1152 p h) (sat_cons (step1150 p h) (sat_cons (step1175 p h) (sat_cons (step1143 p h) (sat_cons (step1145 p h) (sat_cons (step1173 p h) (sat_cons (step282 p h) (sat_cons (step2214 p h) (sat_cons (step1910 p h) (sat_nil p))))))))))))))))))))
def c2275 : List Lit := [(1068, true), (79, false), (81, false)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c2251, c2231, c1922] c2275 (by decide) p (sat_cons (step2251 p h) (sat_cons (step2231 p h) (sat_cons (step1922 p h) (sat_nil p))))
def c2276 : List Lit := [(1049, true), (100, false), (1002, true), (1043, false), (1075, true), (92, true), (122, true), (123, true)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c1185, c2082, c1267, c1186, c2232, c1297, c1293, c1268, c2272, c1263, c378, c434, c1955] c2276 (by decide) p (sat_cons (step1185 p h) (sat_cons (step2082 p h) (sat_cons (step1267 p h) (sat_cons (step1186 p h) (sat_cons (step2232 p h) (sat_cons (step1297 p h) (sat_cons (step1293 p h) (sat_cons (step1268 p h) (sat_cons (step2272 p h) (sat_cons (step1263 p h) (sat_cons (step378 p h) (sat_cons (step434 p h) (sat_cons (step1955 p h) (sat_nil p))))))))))))))
def c2277 : List Lit := [(107, false), (86, false), (1044, true), (70, false)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c514, c513, c1276, c1274, c1282] c2277 (by decide) p (sat_cons (step514 p h) (sat_cons (step513 p h) (sat_cons (step1276 p h) (sat_cons (step1274 p h) (sat_cons (step1282 p h) (sat_nil p))))))
def c2278 : List Lit := [(108, true), (107, true), (1044, true), (1061, true), (89, false), (70, false)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c1280, c1276, c2269, c1278, c1282, c1319, c1273, c1274, c1310, c2177, c473] c2278 (by decide) p (sat_cons (step1280 p h) (sat_cons (step1276 p h) (sat_cons (step2269 p h) (sat_cons (step1278 p h) (sat_cons (step1282 p h) (sat_cons (step1319 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step1310 p h) (sat_cons (step2177 p h) (sat_cons (step473 p h) (sat_nil p))))))))))))
def c2279 : List Lit := [(102, true), (106, false), (101, false), (107, true)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c1959, c1960, c1584] c2279 (by decide) p (sat_cons (step1959 p h) (sat_cons (step1960 p h) (sat_cons (step1584 p h) (sat_nil p))))
def c2280 : List Lit := [(123, true), (113, false), (1068, true), (108, false)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c2232, c1330, c1324, c1325, c635, c553, c1979] c2280 (by decide) p (sat_cons (step2232 p h) (sat_cons (step1330 p h) (sat_cons (step1324 p h) (sat_cons (step1325 p h) (sat_cons (step635 p h) (sat_cons (step553 p h) (sat_cons (step1979 p h) (sat_nil p))))))))
def c2281 : List Lit := [(122, false), (123, false), (113, false), (1068, true), (106, false)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c1684, c686, c1330, c1325] c2281 (by decide) p (sat_cons (step1684 p h) (sat_cons (step686 p h) (sat_cons (step1330 p h) (sat_cons (step1325 p h) (sat_nil p)))))
def c2282 : List Lit := [(1056, false), (1075, true), (114, true), (106, false), (108, false)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c2023, c1310, c1319, c1320, c1347, c1312, c1328, c2280, c2281, c1324, c1326, c1330, c684, c1321] c2282 (by decide) p (sat_cons (step2023 p h) (sat_cons (step1310 p h) (sat_cons (step1319 p h) (sat_cons (step1320 p h) (sat_cons (step1347 p h) (sat_cons (step1312 p h) (sat_cons (step1328 p h) (sat_cons (step2280 p h) (sat_cons (step2281 p h) (sat_cons (step1324 p h) (sat_cons (step1326 p h) (sat_cons (step1330 p h) (sat_cons (step684 p h) (sat_cons (step1321 p h) (sat_nil p)))))))))))))))
def c2283 : List Lit := [(70, true), (1020, true), (1005, false), (994, false)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c1174, c1202, c1239, c1141, c2154, c1149, c1169, c1154, c1177, c1232, c1207] c2283 (by decide) p (sat_cons (step1174 p h) (sat_cons (step1202 p h) (sat_cons (step1239 p h) (sat_cons (step1141 p h) (sat_cons (step2154 p h) (sat_cons (step1149 p h) (sat_cons (step1169 p h) (sat_cons (step1154 p h) (sat_cons (step1177 p h) (sat_cons (step1232 p h) (sat_cons (step1207 p h) (sat_nil p))))))))))))
def c2284 : List Lit := [(894, true), (109, false), (106, false)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c995, c2220, c992, c570] c2284 (by decide) p (sat_cons (step995 p h) (sat_cons (step2220 p h) (sat_cons (step992 p h) (sat_cons (step570 p h) (sat_nil p)))))
def c2285 : List Lit := [(1002, true), (1037, true), (82, false), (86, false), (100, true)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1271, c1185, c1186, c2211, c2105, c1599, c1269, c400, c1264, c1261, c418, c432, c1952] c2285 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1271 p h) (sat_cons (step1185 p h) (sat_cons (step1186 p h) (sat_cons (step2211 p h) (sat_cons (step2105 p h) (sat_cons (step1599 p h) (sat_cons (step1269 p h) (sat_cons (step400 p h) (sat_cons (step1264 p h) (sat_cons (step1261 p h) (sat_cons (step418 p h) (sat_cons (step432 p h) (sat_cons (step1952 p h) (sat_nil p)))))))))))))))
def c2286 : List Lit := [(91, false), (89, false), (1037, true), (82, false), (86, false), (100, true)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c1599, c1262, c1271, c2211, c2105, c1269, c400, c1264, c1261, c418, c432, c1952] c2286 (by decide) p (sat_cons (step1599 p h) (sat_cons (step1262 p h) (sat_cons (step1271 p h) (sat_cons (step2211 p h) (sat_cons (step2105 p h) (sat_cons (step1269 p h) (sat_cons (step400 p h) (sat_cons (step1264 p h) (sat_cons (step1261 p h) (sat_cons (step418 p h) (sat_cons (step432 p h) (sat_cons (step1952 p h) (sat_nil p)))))))))))))
def c2287 : List Lit := [(1036, true), (91, false), (86, false), (100, true)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1266, c1268, c1264, c1259, c1260, c418, c404, c1940] c2287 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1266 p h) (sat_cons (step1268 p h) (sat_cons (step1264 p h) (sat_cons (step1259 p h) (sat_cons (step1260 p h) (sat_cons (step418 p h) (sat_cons (step404 p h) (sat_cons (step1940 p h) (sat_nil p))))))))))
def c2288 : List Lit := [(107, false), (86, false), (1056, true), (108, false)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c527, c526, c1309] c2288 (by decide) p (sat_cons (step527 p h) (sat_cons (step526 p h) (sat_cons (step1309 p h) (sat_nil p))))
def c2289 : List Lit := [(1102, true), (1085, false)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c2189, c1403] c2289 (by decide) p (sat_cons (step2189 p h) (sat_cons (step1403 p h) (sat_nil p)))
def c2290 : List Lit := [(1086, false), (1103, true)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c2189, c1404] c2290 (by decide) p (sat_cons (step2189 p h) (sat_cons (step1404 p h) (sat_nil p)))
def c2291 : List Lit := [(1087, false), (1104, true)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c2189, c1405] c2291 (by decide) p (sat_cons (step2189 p h) (sat_cons (step1405 p h) (sat_nil p)))
def c2292 : List Lit := [(1088, false), (1105, true)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c2189, c1406] c2292 (by decide) p (sat_cons (step2189 p h) (sat_cons (step1406 p h) (sat_nil p)))
def c2293 : List Lit := [(1089, false), (1106, true)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c2189, c1407] c2293 (by decide) p (sat_cons (step2189 p h) (sat_cons (step1407 p h) (sat_nil p)))
def c2294 : List Lit := [(1088, false), (1018, false)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c2153, c1421] c2294 (by decide) p (sat_cons (step2153 p h) (sat_cons (step1421 p h) (sat_nil p)))
def c2295 : List Lit := [(1087, false), (1019, false)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c2153, c1429] c2295 (by decide) p (sat_cons (step2153 p h) (sat_cons (step1429 p h) (sat_nil p)))
def c2296 : List Lit := [(1020, false), (1086, false)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c2153, c1438] c2296 (by decide) p (sat_cons (step2153 p h) (sat_cons (step1438 p h) (sat_nil p)))
def c2297 : List Lit := [(1021, false), (1085, false)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c2153, c1444] c2297 (by decide) p (sat_cons (step2153 p h) (sat_cons (step1444 p h) (sat_nil p)))
def c2298 : List Lit := [(1021, false), (1086, false)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c2117, c1445] c2298 (by decide) p (sat_cons (step2117 p h) (sat_cons (step1445 p h) (sat_nil p)))
end B112E097
