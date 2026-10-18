import B112E256Part0006
namespace B112E256
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2292 : List Lit := [(21, true), (882, false), (897, true), (128, true), (858, false), (6, true)]
theorem step2292 (p : Nat → Bool) (h : Constraints p) : clause p c2292 = true :=
  Snake9.LocalRup.prove_clause [c1921, c1142, c7, c1145, c1103, c1173, c1125, c1203] c2292 (by decide) p (sat_cons (step1921 p h) (sat_cons (step1142 p h) (sat_cons (step7 p h) (sat_cons (step1145 p h) (sat_cons (step1103 p h) (sat_cons (step1173 p h) (sat_cons (step1125 p h) (sat_cons (step1203 p h) (sat_nil p)))))))))
def c2293 : List Lit := [(21, true), (897, true), (859, false), (313, true), (6, true)]
theorem step2293 (p : Nat → Bool) (h : Constraints p) : clause p c2293 = true :=
  Snake9.LocalRup.prove_clause [c900, c897, c879, c876, c875, c153, c1154, c1161, c902, c866, c846, c837, c1921, c1142, c7, c1145, c1103, c1172, c1126, c1210] c2293 (by decide) p (sat_cons (step900 p h) (sat_cons (step897 p h) (sat_cons (step879 p h) (sat_cons (step876 p h) (sat_cons (step875 p h) (sat_cons (step153 p h) (sat_cons (step1154 p h) (sat_cons (step1161 p h) (sat_cons (step902 p h) (sat_cons (step866 p h) (sat_cons (step846 p h) (sat_cons (step837 p h) (sat_cons (step1921 p h) (sat_cons (step1142 p h) (sat_cons (step7 p h) (sat_cons (step1145 p h) (sat_cons (step1103 p h) (sat_cons (step1172 p h) (sat_cons (step1126 p h) (sat_cons (step1210 p h) (sat_nil p)))))))))))))))))))))
def c2294 : List Lit := [(879, true), (19, false), (64, false), (65, false), (155, true)]
theorem step2294 (p : Nat → Bool) (h : Constraints p) : clause p c2294 = true :=
  Snake9.LocalRup.prove_clause [c1156, c1157, c1820, c183, c172] c2294 (by decide) p (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step1820 p h) (sat_cons (step183 p h) (sat_cons (step172 p h) (sat_nil p))))))
def c2295 : List Lit := [(886, true), (65, true), (23, true), (129, true), (142, true), (152, true), (155, true), (157, true), (189, true), (146, true), (195, true), (91, false)]
theorem step2295 (p : Nat → Bool) (h : Constraints p) : clause p c2295 = true :=
  Snake9.LocalRup.prove_clause [c1154, c1161, c1168, c1172, c2283, c1164, c1162, c1145, c1147, c1155, c1156, c1157, c1143, c1139, c1140, c161, c172, c115, c140, c138, c100, c101, c1940, c1815, c1955, c1919, c2152] c2295 (by decide) p (sat_cons (step1154 p h) (sat_cons (step1161 p h) (sat_cons (step1168 p h) (sat_cons (step1172 p h) (sat_cons (step2283 p h) (sat_cons (step1164 p h) (sat_cons (step1162 p h) (sat_cons (step1145 p h) (sat_cons (step1147 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step1143 p h) (sat_cons (step1139 p h) (sat_cons (step1140 p h) (sat_cons (step161 p h) (sat_cons (step172 p h) (sat_cons (step115 p h) (sat_cons (step140 p h) (sat_cons (step138 p h) (sat_cons (step100 p h) (sat_cons (step101 p h) (sat_cons (step1940 p h) (sat_cons (step1815 p h) (sat_cons (step1955 p h) (sat_cons (step1919 p h) (sat_cons (step2152 p h) (sat_nil p))))))))))))))))))))))))))))
def c2296 : List Lit := [(869, true), (32, true), (142, true), (91, false)]
theorem step2296 (p : Nat → Bool) (h : Constraints p) : clause p c2296 = true :=
  Snake9.LocalRup.prove_clause [c1139, c1140, c115, c101] c2296 (by decide) p (sat_cons (step1139 p h) (sat_cons (step1140 p h) (sat_cons (step115 p h) (sat_cons (step101 p h) (sat_nil p)))))
def c2297 : List Lit := [(15, false), (18, false), (32, true), (142, true), (91, false)]
theorem step2297 (p : Nat → Bool) (h : Constraints p) : clause p c2297 = true :=
  Snake9.LocalRup.prove_clause [c101, c115] c2297 (by decide) p (sat_cons (step101 p h) (sat_cons (step115 p h) (sat_nil p)))
def c2298 : List Lit := [(34, true), (31, false), (66, true), (70, false), (26, false), (195, true)]
theorem step2298 (p : Nat → Bool) (h : Constraints p) : clause p c2298 = true :=
  Snake9.LocalRup.prove_clause [c1953, c1946, c492, c471] c2298 (by decide) p (sat_cons (step1953 p h) (sat_cons (step1946 p h) (sat_cons (step492 p h) (sat_cons (step471 p h) (sat_nil p)))))
def c2299 : List Lit := [(882, true), (37, false), (19, false), (65, true), (23, true), (129, true), (152, true), (155, true), (157, true), (146, true), (195, true), (74, true), (1004, true)]
theorem step2299 (p : Nat → Bool) (h : Constraints p) : clause p c2299 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1154, c1446, c1164, c1162, c1155, c1156, c1157, c161, c172, c183, c182, c140, c138, c1951, c1940, c2170, c1919, c1448, c226, c2112, c192, c2298, c2199, c196, c1441, c1443, c1468, c1452] c2299 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1154 p h) (sat_cons (step1446 p h) (sat_cons (step1164 p h) (sat_cons (step1162 p h) (sat_cons (step1155 p h) (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step161 p h) (sat_cons (step172 p h) (sat_cons (step183 p h) (sat_cons (step182 p h) (sat_cons (step140 p h) (sat_cons (step138 p h) (sat_cons (step1951 p h) (sat_cons (step1940 p h) (sat_cons (step2170 p h) (sat_cons (step1919 p h) (sat_cons (step1448 p h) (sat_cons (step226 p h) (sat_cons (step2112 p h) (sat_cons (step192 p h) (sat_cons (step2298 p h) (sat_cons (step2199 p h) (sat_cons (step196 p h) (sat_cons (step1441 p h) (sat_cons (step1443 p h) (sat_cons (step1468 p h) (sat_cons (step1452 p h) (sat_nil p))))))))))))))))))))))))))))))
def c2300 : List Lit := [(70, false), (31, false), (66, true), (26, false), (30, false), (60, false), (988, false), (189, true), (195, true), (995, false), (1004, true)]
theorem step2300 (p : Nat → Bool) (h : Constraints p) : clause p c2300 = true :=
  Snake9.LocalRup.prove_clause [c2298, c196, c1443, c1452, c1468, c1441, c2204, c397] c2300 (by decide) p (sat_cons (step2298 p h) (sat_cons (step196 p h) (sat_cons (step1443 p h) (sat_cons (step1452 p h) (sat_cons (step1468 p h) (sat_cons (step1441 p h) (sat_cons (step2204 p h) (sat_cons (step397 p h) (sat_nil p)))))))))
def c2301 : List Lit := [(993, true), (66, false), (30, false)]
theorem step2301 (p : Nat → Bool) (h : Constraints p) : clause p c2301 = true :=
  Snake9.LocalRup.prove_clause [c1443, c1444, c444] c2301 (by decide) p (sat_cons (step1443 p h) (sat_cons (step1444 p h) (sat_cons (step444 p h) (sat_nil p))))
def c2302 : List Lit := [(66, false), (30, false), (65, true), (995, false), (1004, true)]
theorem step2302 (p : Nat → Bool) (h : Constraints p) : clause p c2302 = true :=
  Snake9.LocalRup.prove_clause [c1435, c1438, c1464, c1455, c2301, c1452, c1468, c1439, c1437, c442, c441, c1445] c2302 (by decide) p (sat_cons (step1435 p h) (sat_cons (step1438 p h) (sat_cons (step1464 p h) (sat_cons (step1455 p h) (sat_cons (step2301 p h) (sat_cons (step1452 p h) (sat_cons (step1468 p h) (sat_cons (step1439 p h) (sat_cons (step1437 p h) (sat_cons (step442 p h) (sat_cons (step441 p h) (sat_cons (step1445 p h) (sat_nil p)))))))))))))
def c2303 : List Lit := [(28, false), (67, false), (63, false), (27, true), (155, true)]
theorem step2303 (p : Nat → Bool) (h : Constraints p) : clause p c2303 = true :=
  Snake9.LocalRup.prove_clause [c182, c422] c2303 (by decide) p (sat_cons (step182 p h) (sat_cons (step422 p h) (sat_nil p)))
def c2304 : List Lit := [(888, true), (879, false), (30, false), (66, true), (27, true), (871, false), (23, true), (142, true), (152, true), (157, true), (189, true), (195, true), (91, false)]
theorem step2304 (p : Nat → Bool) (h : Constraints p) : clause p c2304 = true :=
  Snake9.LocalRup.prove_clause [c1154, c1162, c1145, c1174, c1165, c1178, c1155, c1148, c161, c2296, c2132] c2304 (by decide) p (sat_cons (step1154 p h) (sat_cons (step1162 p h) (sat_cons (step1145 p h) (sat_cons (step1174 p h) (sat_cons (step1165 p h) (sat_cons (step1178 p h) (sat_cons (step1155 p h) (sat_cons (step1148 p h) (sat_cons (step161 p h) (sat_cons (step2296 p h) (sat_cons (step2132 p h) (sat_nil p))))))))))))
def c2305 : List Lit := [(989, false), (60, false), (189, true), (74, true), (1004, true)]
theorem step2305 (p : Nat → Bool) (h : Constraints p) : clause p c2305 = true :=
  Snake9.LocalRup.prove_clause [c1446, c1449, c1472, c1439, c1442, c1468, c1450, c1452, c1448, c1443, c397, c492, c413] c2305 (by decide) p (sat_cons (step1446 p h) (sat_cons (step1449 p h) (sat_cons (step1472 p h) (sat_cons (step1439 p h) (sat_cons (step1442 p h) (sat_cons (step1468 p h) (sat_cons (step1450 p h) (sat_cons (step1452 p h) (sat_cons (step1448 p h) (sat_cons (step1443 p h) (sat_cons (step397 p h) (sat_cons (step492 p h) (sat_cons (step413 p h) (sat_nil p))))))))))))))
def c2306 : List Lit := [(30, false), (864, true), (27, false), (63, false), (129, true), (856, false)]
theorem step2306 (p : Nat → Bool) (h : Constraints p) : clause p c2306 = true :=
  Snake9.LocalRup.prove_clause [c174, c171, c1939, c1106, c1920, c1115, c1099, c1126, c1101] c2306 (by decide) p (sat_cons (step174 p h) (sat_cons (step171 p h) (sat_cons (step1939 p h) (sat_cons (step1106 p h) (sat_cons (step1920 p h) (sat_cons (step1115 p h) (sat_cons (step1099 p h) (sat_cons (step1126 p h) (sat_cons (step1101 p h) (sat_nil p))))))))))
def c2307 : List Lit := [(201, true), (1026, true), (74, false), (78, false)]
theorem step2307 (p : Nat → Bool) (h : Constraints p) : clause p c2307 = true :=
  Snake9.LocalRup.prove_clause [c498, c1903, c560, c1494, c2282] c2307 (by decide) p (sat_cons (step498 p h) (sat_cons (step1903 p h) (sat_cons (step560 p h) (sat_cons (step1494 p h) (sat_cons (step2282 p h) (sat_nil p))))))
def c2308 : List Lit := [(1026, true), (74, false), (78, false), (6, true)]
theorem step2308 (p : Nat → Bool) (h : Constraints p) : clause p c2308 = true :=
  Snake9.LocalRup.prove_clause [c2307, c988, c989, c2059, c992, c991, c514, c2287, c560, c1494, c2282] c2308 (by decide) p (sat_cons (step2307 p h) (sat_cons (step988 p h) (sat_cons (step989 p h) (sat_cons (step2059 p h) (sat_cons (step992 p h) (sat_cons (step991 p h) (sat_cons (step514 p h) (sat_cons (step2287 p h) (sat_cons (step560 p h) (sat_cons (step1494 p h) (sat_cons (step2282 p h) (sat_nil p))))))))))))
def c2309 : List Lit := [(932, true), (18, false), (176, true), (67, false), (65, false)]
theorem step2309 (p : Nat → Bool) (h : Constraints p) : clause p c2309 = true :=
  Snake9.LocalRup.prove_clause [c1282, c1284, c1279, c1280, c1276, c1277, c325, c309, c365, c334] c2309 (by decide) p (sat_cons (step1282 p h) (sat_cons (step1284 p h) (sat_cons (step1279 p h) (sat_cons (step1280 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step325 p h) (sat_cons (step309 p h) (sat_cons (step365 p h) (sat_cons (step334 p h) (sat_nil p)))))))))))
def c2310 : List Lit := [(956, false), (973, true)]
theorem step2310 (p : Nat → Bool) (h : Constraints p) : clause p c2310 = true :=
  Snake9.LocalRup.prove_clause [c2128, c1372] c2310 (by decide) p (sat_cons (step2128 p h) (sat_cons (step1372 p h) (sat_nil p)))
def c2311 : List Lit := [(957, false), (974, true)]
theorem step2311 (p : Nat → Bool) (h : Constraints p) : clause p c2311 = true :=
  Snake9.LocalRup.prove_clause [c2128, c1373] c2311 (by decide) p (sat_cons (step2128 p h) (sat_cons (step1373 p h) (sat_nil p)))
def c2312 : List Lit := [(958, false), (975, true)]
theorem step2312 (p : Nat → Bool) (h : Constraints p) : clause p c2312 = true :=
  Snake9.LocalRup.prove_clause [c2128, c1374] c2312 (by decide) p (sat_cons (step2128 p h) (sat_cons (step1374 p h) (sat_nil p)))
def c2313 : List Lit := [(959, false), (976, true)]
theorem step2313 (p : Nat → Bool) (h : Constraints p) : clause p c2313 = true :=
  Snake9.LocalRup.prove_clause [c2128, c1375] c2313 (by decide) p (sat_cons (step2128 p h) (sat_cons (step1375 p h) (sat_nil p)))
def c2314 : List Lit := [(960, false), (977, true)]
theorem step2314 (p : Nat → Bool) (h : Constraints p) : clause p c2314 = true :=
  Snake9.LocalRup.prove_clause [c2128, c1376] c2314 (by decide) p (sat_cons (step2128 p h) (sat_cons (step1376 p h) (sat_nil p)))
def c2315 : List Lit := [(961, false), (978, true)]
theorem step2315 (p : Nat → Bool) (h : Constraints p) : clause p c2315 = true :=
  Snake9.LocalRup.prove_clause [c2128, c1377] c2315 (by decide) p (sat_cons (step2128 p h) (sat_cons (step1377 p h) (sat_nil p)))
def c2316 : List Lit := [(1033, true), (1001, false)]
theorem step2316 (p : Nat → Bool) (h : Constraints p) : clause p c2316 = true :=
  Snake9.LocalRup.prove_clause [c2172, c1530] c2316 (by decide) p (sat_cons (step2172 p h) (sat_cons (step1530 p h) (sat_nil p)))
def c2317 : List Lit := [(1034, true), (1002, false)]
theorem step2317 (p : Nat → Bool) (h : Constraints p) : clause p c2317 = true :=
  Snake9.LocalRup.prove_clause [c2172, c1536] c2317 (by decide) p (sat_cons (step2172 p h) (sat_cons (step1536 p h) (sat_nil p)))
def c2318 : List Lit := [(1035, true), (1003, false)]
theorem step2318 (p : Nat → Bool) (h : Constraints p) : clause p c2318 = true :=
  Snake9.LocalRup.prove_clause [c2172, c1542] c2318 (by decide) p (sat_cons (step2172 p h) (sat_cons (step1542 p h) (sat_nil p)))
def c2319 : List Lit := [(1004, false), (1036, true)]
theorem step2319 (p : Nat → Bool) (h : Constraints p) : clause p c2319 = true :=
  Snake9.LocalRup.prove_clause [c2172, c1548] c2319 (by decide) p (sat_cons (step2172 p h) (sat_cons (step1548 p h) (sat_nil p)))
def c2320 : List Lit := [(1005, false), (1037, true)]
theorem step2320 (p : Nat → Bool) (h : Constraints p) : clause p c2320 = true :=
  Snake9.LocalRup.prove_clause [c2172, c1553] c2320 (by decide) p (sat_cons (step2172 p h) (sat_cons (step1553 p h) (sat_nil p)))
def c2321 : List Lit := [(1006, false), (1038, true)]
theorem step2321 (p : Nat → Bool) (h : Constraints p) : clause p c2321 = true :=
  Snake9.LocalRup.prove_clause [c2172, c1558] c2321 (by decide) p (sat_cons (step2172 p h) (sat_cons (step1558 p h) (sat_nil p)))
def c2322 : List Lit := [(1115, true), (1033, false)]
theorem step2322 (p : Nat → Bool) (h : Constraints p) : clause p c2322 = true :=
  Snake9.LocalRup.prove_clause [c2219, c1688] c2322 (by decide) p (sat_cons (step2219 p h) (sat_cons (step1688 p h) (sat_nil p)))
def c2323 : List Lit := [(1116, true), (1034, false)]
theorem step2323 (p : Nat → Bool) (h : Constraints p) : clause p c2323 = true :=
  Snake9.LocalRup.prove_clause [c2219, c1692] c2323 (by decide) p (sat_cons (step2219 p h) (sat_cons (step1692 p h) (sat_nil p)))
def c2324 : List Lit := [(1117, true), (1035, false)]
theorem step2324 (p : Nat → Bool) (h : Constraints p) : clause p c2324 = true :=
  Snake9.LocalRup.prove_clause [c2219, c1699] c2324 (by decide) p (sat_cons (step2219 p h) (sat_cons (step1699 p h) (sat_nil p)))
def c2325 : List Lit := [(1118, true), (1036, false)]
theorem step2325 (p : Nat → Bool) (h : Constraints p) : clause p c2325 = true :=
  Snake9.LocalRup.prove_clause [c2219, c1707] c2325 (by decide) p (sat_cons (step2219 p h) (sat_cons (step1707 p h) (sat_nil p)))
def c2326 : List Lit := [(1119, true), (1037, false)]
theorem step2326 (p : Nat → Bool) (h : Constraints p) : clause p c2326 = true :=
  Snake9.LocalRup.prove_clause [c2219, c1712] c2326 (by decide) p (sat_cons (step2219 p h) (sat_cons (step1712 p h) (sat_nil p)))
def c2327 : List Lit := [(1038, false), (1120, true)]
theorem step2327 (p : Nat → Bool) (h : Constraints p) : clause p c2327 = true :=
  Snake9.LocalRup.prove_clause [c2219, c1718] c2327 (by decide) p (sat_cons (step2219 p h) (sat_cons (step1718 p h) (sat_nil p)))
def c2328 : List Lit := [(1039, false), (1121, true)]
theorem step2328 (p : Nat → Bool) (h : Constraints p) : clause p c2328 = true :=
  Snake9.LocalRup.prove_clause [c2219, c1724] c2328 (by decide) p (sat_cons (step2219 p h) (sat_cons (step1724 p h) (sat_nil p)))
def c2329 : List Lit := [(869, true), (142, true), (91, false), (70, false)]
theorem step2329 (p : Nat → Bool) (h : Constraints p) : clause p c2329 = true :=
  Snake9.LocalRup.prove_clause [c1139, c1140, c2296, c115, c100, c1815] c2329 (by decide) p (sat_cons (step1139 p h) (sat_cons (step1140 p h) (sat_cons (step2296 p h) (sat_cons (step115 p h) (sat_cons (step100 p h) (sat_cons (step1815 p h) (sat_nil p)))))))
def c2330 : List Lit := [(5, false), (44, true), (1, false), (919, true), (132, true), (6, true)]
theorem step2330 (p : Nat → Bool) (h : Constraints p) : clause p c2330 = true :=
  Snake9.LocalRup.prove_clause [c2098, c22, c65, c2227, c1248, c1253] c2330 (by decide) p (sat_cons (step2098 p h) (sat_cons (step22 p h) (sat_cons (step65 p h) (sat_cons (step2227 p h) (sat_cons (step1248 p h) (sat_cons (step1253 p h) (sat_nil p)))))))
def c2331 : List Lit := [(155, true), (886, true), (877, false), (65, false)]
theorem step2331 (p : Nat → Bool) (h : Constraints p) : clause p c2331 = true :=
  Snake9.LocalRup.prove_clause [c1161, c1172, c1145, c1143, c1168, c1162, c2283, c2294] c2331 (by decide) p (sat_cons (step1161 p h) (sat_cons (step1172 p h) (sat_cons (step1145 p h) (sat_cons (step1143 p h) (sat_cons (step1168 p h) (sat_cons (step1162 p h) (sat_cons (step2283 p h) (sat_cons (step2294 p h) (sat_nil p)))))))))
def c2332 : List Lit := [(932, false), (911, false), (939, false), (915, false), (184, true), (38, false), (2, false), (43, false), (947, true), (958, true), (30, false), (941, false)]
theorem step2332 (p : Nat → Bool) (h : Constraints p) : clause p c2332 = true :=
  Snake9.LocalRup.prove_clause [c1315, c1287, c1310, c1311, c1354, c1300, c1268, c1291, c1252, c1243, c245, c1278, c433, c254, c387] c2332 (by decide) p (sat_cons (step1315 p h) (sat_cons (step1287 p h) (sat_cons (step1310 p h) (sat_cons (step1311 p h) (sat_cons (step1354 p h) (sat_cons (step1300 p h) (sat_cons (step1268 p h) (sat_cons (step1291 p h) (sat_cons (step1252 p h) (sat_cons (step1243 p h) (sat_cons (step245 p h) (sat_cons (step1278 p h) (sat_cons (step433 p h) (sat_cons (step254 p h) (sat_cons (step387 p h) (sat_nil p))))))))))))))))
def c2333 : List Lit := [(43, false), (66, true), (57, false), (932, true)]
theorem step2333 (p : Nat → Bool) (h : Constraints p) : clause p c2333 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1276, c1282, c1280, c1279, c322, c350, c254, c317, c387, c922, c942, c923, c945, c927, c958, c931, c961, c2054] c2333 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1276 p h) (sat_cons (step1282 p h) (sat_cons (step1280 p h) (sat_cons (step1279 p h) (sat_cons (step322 p h) (sat_cons (step350 p h) (sat_cons (step254 p h) (sat_cons (step317 p h) (sat_cons (step387 p h) (sat_cons (step922 p h) (sat_cons (step942 p h) (sat_cons (step923 p h) (sat_cons (step945 p h) (sat_cons (step927 p h) (sat_cons (step958 p h) (sat_cons (step931 p h) (sat_cons (step961 p h) (sat_cons (step2054 p h) (sat_nil p))))))))))))))))))))
def c2334 : List Lit := [(44, false), (932, true), (27, true), (28, false)]
theorem step2334 (p : Nat → Bool) (h : Constraints p) : clause p c2334 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1276, c1282, c1280, c1279, c322, c1277, c2239, c2091, c920, c924, c927, c931, c967, c2054, c2055, c963, c900, c941, c895, c937, c891, c936, c889, c335, c334, c886, c1808, c309, c183, c1951] c2334 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1276 p h) (sat_cons (step1282 p h) (sat_cons (step1280 p h) (sat_cons (step1279 p h) (sat_cons (step322 p h) (sat_cons (step1277 p h) (sat_cons (step2239 p h) (sat_cons (step2091 p h) (sat_cons (step920 p h) (sat_cons (step924 p h) (sat_cons (step927 p h) (sat_cons (step931 p h) (sat_cons (step967 p h) (sat_cons (step2054 p h) (sat_cons (step2055 p h) (sat_cons (step963 p h) (sat_cons (step900 p h) (sat_cons (step941 p h) (sat_cons (step895 p h) (sat_cons (step937 p h) (sat_cons (step891 p h) (sat_cons (step936 p h) (sat_cons (step889 p h) (sat_cons (step335 p h) (sat_cons (step334 p h) (sat_cons (step886 p h) (sat_cons (step1808 p h) (sat_cons (step309 p h) (sat_cons (step183 p h) (sat_cons (step1951 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2335 : List Lit := [(1, false), (3, true), (36, true), (128, true)]
theorem step2335 (p : Nat → Bool) (h : Constraints p) : clause p c2335 = true :=
  Snake9.LocalRup.prove_clause [c7, c6, c1802, c1958] c2335 (by decide) p (sat_cons (step7 p h) (sat_cons (step6 p h) (sat_cons (step1802 p h) (sat_cons (step1958 p h) (sat_nil p)))))
def c2336 : List Lit := [(866, true), (1, true), (60, true), (2, true), (10, true), (11, true), (313, true)]
theorem step2336 (p : Nat → Bool) (h : Constraints p) : clause p c2336 = true :=
  Snake9.LocalRup.prove_clause [c1099, c1104, c1110, c1106, c1115, c902, c866, c844, c841, c840, c900, c897, c879, c876, c875, c1136, c1105, c1100, c1132, c1118, c1116, c1108, c1111, c38, c63, c153, c1943] c2336 (by decide) p (sat_cons (step1099 p h) (sat_cons (step1104 p h) (sat_cons (step1110 p h) (sat_cons (step1106 p h) (sat_cons (step1115 p h) (sat_cons (step902 p h) (sat_cons (step866 p h) (sat_cons (step844 p h) (sat_cons (step841 p h) (sat_cons (step840 p h) (sat_cons (step900 p h) (sat_cons (step897 p h) (sat_cons (step879 p h) (sat_cons (step876 p h) (sat_cons (step875 p h) (sat_cons (step1136 p h) (sat_cons (step1105 p h) (sat_cons (step1100 p h) (sat_cons (step1132 p h) (sat_cons (step1118 p h) (sat_cons (step1116 p h) (sat_cons (step1108 p h) (sat_cons (step1111 p h) (sat_cons (step38 p h) (sat_cons (step63 p h) (sat_cons (step153 p h) (sat_cons (step1943 p h) (sat_nil p))))))))))))))))))))))))))))
def c2337 : List Lit := [(993, false), (998, true), (1037, true), (1008, false), (201, true), (991, false)]
theorem step2337 (p : Nat → Bool) (h : Constraints p) : clause p c2337 = true :=
  Snake9.LocalRup.prove_clause [c1451, c1452, c1467, c1446, c1544, c1903, c2262, c1494] c2337 (by decide) p (sat_cons (step1451 p h) (sat_cons (step1452 p h) (sat_cons (step1467 p h) (sat_cons (step1446 p h) (sat_cons (step1544 p h) (sat_cons (step1903 p h) (sat_cons (step2262 p h) (sat_cons (step1494 p h) (sat_nil p)))))))))
def c2338 : List Lit := [(61, false), (33, false), (67, false)]
theorem step2338 (p : Nat → Bool) (h : Constraints p) : clause p c2338 = true :=
  Snake9.LocalRup.prove_clause [c407, c485] c2338 (by decide) p (sat_cons (step407 p h) (sat_cons (step485 p h) (sat_nil p)))
def c2339 : List Lit := [(1003, true), (195, true), (30, false), (989, false)]
theorem step2339 (p : Nat → Bool) (h : Constraints p) : clause p c2339 = true :=
  Snake9.LocalRup.prove_clause [c1439, c1471, c1467, c1442, c2141] c2339 (by decide) p (sat_cons (step1439 p h) (sat_cons (step1471 p h) (sat_cons (step1467 p h) (sat_cons (step1442 p h) (sat_cons (step2141 p h) (sat_nil p))))))
def c2340 : List Lit := [(2, false), (36, false), (20, true), (42, false)]
theorem step2340 (p : Nat → Bool) (h : Constraints p) : clause p c2340 = true :=
  Snake9.LocalRup.prove_clause [c1918, c243] c2340 (by decide) p (sat_cons (step1918 p h) (sat_cons (step243 p h) (sat_nil p)))
def c2341 : List Lit := [(933, true), (53, true), (11, false), (172, true), (36, true), (2, true)]
theorem step2341 (p : Nat → Bool) (h : Constraints p) : clause p c2341 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1283, c1285, c1281, c1277, c303, c300, c302, c2164] c2341 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1283 p h) (sat_cons (step1285 p h) (sat_cons (step1281 p h) (sat_cons (step1277 p h) (sat_cons (step303 p h) (sat_cons (step300 p h) (sat_cons (step302 p h) (sat_cons (step2164 p h) (sat_nil p))))))))))
def c2342 : List Lit := [(47, false), (57, false), (30, false), (184, true), (43, false)]
theorem step2342 (p : Nat → Bool) (h : Constraints p) : clause p c2342 = true :=
  Snake9.LocalRup.prove_clause [c433, c254, c387] c2342 (by decide) p (sat_cons (step433 p h) (sat_cons (step254 p h) (sat_cons (step387 p h) (sat_nil p))))
def c2343 : List Lit := [(44, false), (49, true), (53, true), (171, true)]
theorem step2343 (p : Nat → Bool) (h : Constraints p) : clause p c2343 = true :=
  Snake9.LocalRup.prove_clause [c294, c2176, c1975] c2343 (by decide) p (sat_cons (step294 p h) (sat_cons (step2176 p h) (sat_cons (step1975 p h) (sat_nil p))))
def c2344 : List Lit := [(120, true), (1089, true), (1071, false), (243, true)]
theorem step2344 (p : Nat → Bool) (h : Constraints p) : clause p c2344 = true :=
  Snake9.LocalRup.prove_clause [c1619, c1643, c1635, c1625, c1626, c1632, c1633, c1647, c1627, c1628, c1620, c768, c1615, c708] c2344 (by decide) p (sat_cons (step1619 p h) (sat_cons (step1643 p h) (sat_cons (step1635 p h) (sat_cons (step1625 p h) (sat_cons (step1626 p h) (sat_cons (step1632 p h) (sat_cons (step1633 p h) (sat_cons (step1647 p h) (sat_cons (step1627 p h) (sat_cons (step1628 p h) (sat_cons (step1620 p h) (sat_cons (step768 p h) (sat_cons (step1615 p h) (sat_cons (step708 p h) (sat_nil p)))))))))))))))
def c2345 : List Lit := [(122, false), (124, false), (126, false), (120, false), (1074, true), (497, true)]
theorem step2345 (p : Nat → Bool) (h : Constraints p) : clause p c2345 = true :=
  Snake9.LocalRup.prove_clause [c743, c1916] c2345 (by decide) p (sat_cons (step743 p h) (sat_cons (step1916 p h) (sat_nil p)))
def c2346 : List Lit := [(124, false), (126, false), (1089, true), (1071, false), (497, true)]
theorem step2346 (p : Nat → Bool) (h : Constraints p) : clause p c2346 = true :=
  Snake9.LocalRup.prove_clause [c1080, c1062, c1060, c1057, c2344, c1651, c1621, c2345, c1624, c1632, c1647, c1620, c1615, c708, c767] c2346 (by decide) p (sat_cons (step1080 p h) (sat_cons (step1062 p h) (sat_cons (step1060 p h) (sat_cons (step1057 p h) (sat_cons (step2344 p h) (sat_cons (step1651 p h) (sat_cons (step1621 p h) (sat_cons (step2345 p h) (sat_cons (step1624 p h) (sat_cons (step1632 p h) (sat_cons (step1647 p h) (sat_cons (step1620 p h) (sat_cons (step1615 p h) (sat_cons (step708 p h) (sat_cons (step767 p h) (sat_nil p))))))))))))))))
def c2347 : List Lit := [(126, false), (119, true), (1089, true), (1071, false), (497, true)]
theorem step2347 (p : Nat → Bool) (h : Constraints p) : clause p c2347 = true :=
  Snake9.LocalRup.prove_clause [c1080, c1062, c1060, c1057, c2344, c1619, c1643, c1078, c1075, c1067, c1066, c2346, c1628, c1630, c1633, c1647, c1624, c1620, c743, c1615, c747, c766] c2347 (by decide) p (sat_cons (step1080 p h) (sat_cons (step1062 p h) (sat_cons (step1060 p h) (sat_cons (step1057 p h) (sat_cons (step2344 p h) (sat_cons (step1619 p h) (sat_cons (step1643 p h) (sat_cons (step1078 p h) (sat_cons (step1075 p h) (sat_cons (step1067 p h) (sat_cons (step1066 p h) (sat_cons (step2346 p h) (sat_cons (step1628 p h) (sat_cons (step1630 p h) (sat_cons (step1633 p h) (sat_cons (step1647 p h) (sat_cons (step1624 p h) (sat_cons (step1620 p h) (sat_cons (step743 p h) (sat_cons (step1615 p h) (sat_cons (step747 p h) (sat_cons (step766 p h) (sat_nil p)))))))))))))))))))))))
def c2348 : List Lit := [(126, true), (1089, true), (1071, false), (243, true)]
theorem step2348 (p : Nat → Bool) (h : Constraints p) : clause p c2348 = true :=
  Snake9.LocalRup.prove_clause [c1619, c1643, c1631, c1627, c1629, c1630, c1633, c1647, c1624, c1620, c1615, c708, c765] c2348 (by decide) p (sat_cons (step1619 p h) (sat_cons (step1643 p h) (sat_cons (step1631 p h) (sat_cons (step1627 p h) (sat_cons (step1629 p h) (sat_cons (step1630 p h) (sat_cons (step1633 p h) (sat_cons (step1647 p h) (sat_cons (step1624 p h) (sat_cons (step1620 p h) (sat_cons (step1615 p h) (sat_cons (step708 p h) (sat_cons (step765 p h) (sat_nil p))))))))))))))
def c2349 : List Lit := [(1089, true), (1071, false), (65, false), (497, true)]
theorem step2349 (p : Nat → Bool) (h : Constraints p) : clause p c2349 = true :=
  Snake9.LocalRup.prove_clause [c1619, c1080, c1062, c1060, c1057, c1643, c2348, c2346, c2347, c1628, c1630, c1633, c1647, c1624, c1620, c720, c1614] c2349 (by decide) p (sat_cons (step1619 p h) (sat_cons (step1080 p h) (sat_cons (step1062 p h) (sat_cons (step1060 p h) (sat_cons (step1057 p h) (sat_cons (step1643 p h) (sat_cons (step2348 p h) (sat_cons (step2346 p h) (sat_cons (step2347 p h) (sat_cons (step1628 p h) (sat_cons (step1630 p h) (sat_cons (step1633 p h) (sat_cons (step1647 p h) (sat_cons (step1624 p h) (sat_cons (step1620 p h) (sat_cons (step720 p h) (sat_cons (step1614 p h) (sat_nil p))))))))))))))))))
def c2350 : List Lit := [(1089, false), (106, true), (1055, false), (1099, true), (1002, false), (1119, true), (467, true)]
theorem step2350 (p : Nat → Bool) (h : Constraints p) : clause p c2350 = true :=
  Snake9.LocalRup.prove_clause [c1584, c1590, c1052, c1035, c1033, c1032, c1050, c1048, c1041, c1038, c1659, c1665, c1708, c1591, c1594, c1538, c1587, c1585, c1568, c1570, c1578, c1579, c1580, c1565, c1563, c658, c681, c2187, c2282, c1494] c2350 (by decide) p (sat_cons (step1584 p h) (sat_cons (step1590 p h) (sat_cons (step1052 p h) (sat_cons (step1035 p h) (sat_cons (step1033 p h) (sat_cons (step1032 p h) (sat_cons (step1050 p h) (sat_cons (step1048 p h) (sat_cons (step1041 p h) (sat_cons (step1038 p h) (sat_cons (step1659 p h) (sat_cons (step1665 p h) (sat_cons (step1708 p h) (sat_cons (step1591 p h) (sat_cons (step1594 p h) (sat_cons (step1538 p h) (sat_cons (step1587 p h) (sat_cons (step1585 p h) (sat_cons (step1568 p h) (sat_cons (step1570 p h) (sat_cons (step1578 p h) (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step1565 p h) (sat_cons (step1563 p h) (sat_cons (step658 p h) (sat_cons (step681 p h) (sat_cons (step2187 p h) (sat_cons (step2282 p h) (sat_cons (step1494 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c2351 : List Lit := [(1047, true), (80, false), (105, false), (103, true), (109, false), (1002, false), (1059, false), (1119, true), (232, true), (497, true)]
theorem step2351 (p : Nat → Bool) (h : Constraints p) : clause p c2351 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1568, c1594, c1563, c2187, c522, c1494, c1476, c2262, c1538, c1708, c1664, c2212, c1638, c1642, c1669, c1617, c1599, c1615, c1569, c2103, c1567] c2351 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1568 p h) (sat_cons (step1594 p h) (sat_cons (step1563 p h) (sat_cons (step2187 p h) (sat_cons (step522 p h) (sat_cons (step1494 p h) (sat_cons (step1476 p h) (sat_cons (step2262 p h) (sat_cons (step1538 p h) (sat_cons (step1708 p h) (sat_cons (step1664 p h) (sat_cons (step2212 p h) (sat_cons (step1638 p h) (sat_cons (step1642 p h) (sat_cons (step1669 p h) (sat_cons (step1617 p h) (sat_cons (step1599 p h) (sat_cons (step1615 p h) (sat_cons (step1569 p h) (sat_cons (step2103 p h) (sat_cons (step1567 p h) (sat_nil p)))))))))))))))))))))))
def c2352 : List Lit := [(1047, false), (103, true), (1059, false), (1099, true), (497, true)]
theorem step2352 (p : Nat → Bool) (h : Constraints p) : clause p c2352 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1080, c1062, c1060, c1057, c1571, c1599, c1670, c2212, c1638, c1642, c1675, c1617, c1604, c1615, c1572, c709, c708, c1567, c1841] c2352 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1080 p h) (sat_cons (step1062 p h) (sat_cons (step1060 p h) (sat_cons (step1057 p h) (sat_cons (step1571 p h) (sat_cons (step1599 p h) (sat_cons (step1670 p h) (sat_cons (step2212 p h) (sat_cons (step1638 p h) (sat_cons (step1642 p h) (sat_cons (step1675 p h) (sat_cons (step1617 p h) (sat_cons (step1604 p h) (sat_cons (step1615 p h) (sat_cons (step1572 p h) (sat_cons (step709 p h) (sat_cons (step708 p h) (sat_cons (step1567 p h) (sat_cons (step1841 p h) (sat_nil p)))))))))))))))))))))
def c2353 : List Lit := [(105, false), (1047, true), (103, true), (114, true), (109, false), (1002, false), (1059, false), (1119, true), (232, true), (497, true)]
theorem step2353 (p : Nat → Bool) (h : Constraints p) : clause p c2353 = true :=
  Snake9.LocalRup.prove_clause [c663, c2351] c2353 (by decide) p (sat_cons (step663 p h) (sat_cons (step2351 p h) (sat_nil p)))
def c2354 : List Lit := [(1057, true), (1002, false), (106, true), (1059, false), (1099, true), (1119, true), (467, true), (497, true), (1071, true)]
theorem step2354 (p : Nat → Bool) (h : Constraints p) : clause p c2354 = true :=
  Snake9.LocalRup.prove_clause [c1052, c1035, c1033, c1032, c1050, c1048, c1041, c1038, c1612, c1611, c1579, c1580, c703, c1912, c1565, c1568, c2352, c1563, c2353, c1578, c1587, c1595, c1670, c2212, c1638, c1642, c1675, c1617, c1600, c1615, c1569, c2103, c1567] c2354 (by decide) p (sat_cons (step1052 p h) (sat_cons (step1035 p h) (sat_cons (step1033 p h) (sat_cons (step1032 p h) (sat_cons (step1050 p h) (sat_cons (step1048 p h) (sat_cons (step1041 p h) (sat_cons (step1038 p h) (sat_cons (step1612 p h) (sat_cons (step1611 p h) (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step703 p h) (sat_cons (step1912 p h) (sat_cons (step1565 p h) (sat_cons (step1568 p h) (sat_cons (step2352 p h) (sat_cons (step1563 p h) (sat_cons (step2353 p h) (sat_cons (step1578 p h) (sat_cons (step1587 p h) (sat_cons (step1595 p h) (sat_cons (step1670 p h) (sat_cons (step2212 p h) (sat_cons (step1638 p h) (sat_cons (step1642 p h) (sat_cons (step1675 p h) (sat_cons (step1617 p h) (sat_cons (step1600 p h) (sat_cons (step1615 p h) (sat_cons (step1569 p h) (sat_cons (step2103 p h) (sat_cons (step1567 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c2355 : List Lit := [(1060, false), (1099, true), (103, true), (1047, true), (497, true)]
theorem step2355 (p : Nat → Bool) (h : Constraints p) : clause p c2355 = true :=
  Snake9.LocalRup.prove_clause [c1565, c1568, c1563, c1595, c1670, c2212, c1638, c1642, c1675, c1617, c1600, c1615, c1569, c2103, c1567] c2355 (by decide) p (sat_cons (step1565 p h) (sat_cons (step1568 p h) (sat_cons (step1563 p h) (sat_cons (step1595 p h) (sat_cons (step1670 p h) (sat_cons (step2212 p h) (sat_cons (step1638 p h) (sat_cons (step1642 p h) (sat_cons (step1675 p h) (sat_cons (step1617 p h) (sat_cons (step1600 p h) (sat_cons (step1615 p h) (sat_cons (step1569 p h) (sat_cons (step2103 p h) (sat_cons (step1567 p h) (sat_nil p))))))))))))))))
end B112E256
