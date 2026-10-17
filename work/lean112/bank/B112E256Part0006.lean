import B112E256Part0005
namespace B112E256
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2228 : List Lit := [(73, false), (31, false), (142, true), (34, false), (15, false)]
theorem step2228 (p : Nat → Bool) (h : Constraints p) : clause p c2228 = true :=
  Snake9.LocalRup.prove_clause [c212, c218, c101] c2228 (by decide) p (sat_cons (step212 p h) (sat_cons (step218 p h) (sat_cons (step101 p h) (sat_nil p))))
def c2229 : List Lit := [(62, false), (73, true), (189, true), (34, false), (25, false)]
theorem step2229 (p : Nat → Bool) (h : Constraints p) : clause p c2229 = true :=
  Snake9.LocalRup.prove_clause [c163, c414] c2229 (by decide) p (sat_cons (step163 p h) (sat_cons (step414 p h) (sat_nil p)))
def c2230 : List Lit := [(1025, true), (87, false), (14, false)]
theorem step2230 (p : Nat → Bool) (h : Constraints p) : clause p c2230 = true :=
  Snake9.LocalRup.prove_clause [c2173, c2180, c1494, c1476, c553] c2230 (by decide) p (sat_cons (step2173 p h) (sat_cons (step2180 p h) (sat_cons (step1494 p h) (sat_cons (step1476 p h) (sat_cons (step553 p h) (sat_nil p))))))
def c2231 : List Lit := [(921, true), (850, true), (129, true), (8, false), (25, false)]
theorem step2231 (p : Nat → Bool) (h : Constraints p) : clause p c2231 = true :=
  Snake9.LocalRup.prove_clause [c1257, c1908, c1249, c1100, c1247, c65] c2231 (by decide) p (sat_cons (step1257 p h) (sat_cons (step1908 p h) (sat_cons (step1249 p h) (sat_cons (step1100 p h) (sat_cons (step1247 p h) (sat_cons (step65 p h) (sat_nil p)))))))
def c2232 : List Lit := [(15, false), (17, true), (142, true), (42, false), (45, false)]
theorem step2232 (p : Nat → Bool) (h : Constraints p) : clause p c2232 = true :=
  Snake9.LocalRup.prove_clause [c344, c100] c2232 (by decide) p (sat_cons (step344 p h) (sat_cons (step100 p h) (sat_nil p)))
def c2233 : List Lit := [(23, false), (1025, true), (41, false)]
theorem step2233 (p : Nat → Bool) (h : Constraints p) : clause p c2233 = true :=
  Snake9.LocalRup.prove_clause [c2180, c1476, c2173, c1494, c57, c153, c875, c876, c879, c897, c900, c972, c2072, c1090, c1026, c999, c995, c992, c991, c514, c515, c1836] c2233 (by decide) p (sat_cons (step2180 p h) (sat_cons (step1476 p h) (sat_cons (step2173 p h) (sat_cons (step1494 p h) (sat_cons (step57 p h) (sat_cons (step153 p h) (sat_cons (step875 p h) (sat_cons (step876 p h) (sat_cons (step879 p h) (sat_cons (step897 p h) (sat_cons (step900 p h) (sat_cons (step972 p h) (sat_cons (step2072 p h) (sat_cons (step1090 p h) (sat_cons (step1026 p h) (sat_cons (step999 p h) (sat_cons (step995 p h) (sat_cons (step992 p h) (sat_cons (step991 p h) (sat_cons (step514 p h) (sat_cons (step515 p h) (sat_cons (step1836 p h) (sat_nil p)))))))))))))))))))))))
def c2234 : List Lit := [(205, true), (6, true), (1025, true)]
theorem step2234 (p : Nat → Bool) (h : Constraints p) : clause p c2234 = true :=
  Snake9.LocalRup.prove_clause [c2180, c1476, c2173, c1494, c514, c515, c1836] c2234 (by decide) p (sat_cons (step2180 p h) (sat_cons (step1476 p h) (sat_cons (step2173 p h) (sat_cons (step1494 p h) (sat_cons (step514 p h) (sat_cons (step515 p h) (sat_cons (step1836 p h) (sat_nil p))))))))
def c2235 : List Lit := [(2, false), (915, false), (938, false), (47, true), (129, true), (146, true), (956, true), (27, true)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c1249, c1257, c1276, c1284, c1296, c1309, c1346, c1919, c1920, c2089, c1939, c1299, c138, c1291, c370, c1235, c1238, c1263, c1262, c1252, c1340, c1243, c1314, c245, c1287, c1278] c2235 (by decide) p (sat_cons (step1249 p h) (sat_cons (step1257 p h) (sat_cons (step1276 p h) (sat_cons (step1284 p h) (sat_cons (step1296 p h) (sat_cons (step1309 p h) (sat_cons (step1346 p h) (sat_cons (step1919 p h) (sat_cons (step1920 p h) (sat_cons (step2089 p h) (sat_cons (step1939 p h) (sat_cons (step1299 p h) (sat_cons (step138 p h) (sat_cons (step1291 p h) (sat_cons (step370 p h) (sat_cons (step1235 p h) (sat_cons (step1238 p h) (sat_cons (step1263 p h) (sat_cons (step1262 p h) (sat_cons (step1252 p h) (sat_cons (step1340 p h) (sat_cons (step1243 p h) (sat_cons (step1314 p h) (sat_cons (step245 p h) (sat_cons (step1287 p h) (sat_cons (step1278 p h) (sat_nil p)))))))))))))))))))))))))))
def c2236 : List Lit := [(869, true), (908, true), (45, false), (42, false)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c1235, c246, c1236, c1139, c1140, c344, c114, c301, c100, c919, c854, c924, c857, c927, c859, c931, c864, c967, c902, c2055] c2236 (by decide) p (sat_cons (step1235 p h) (sat_cons (step246 p h) (sat_cons (step1236 p h) (sat_cons (step1139 p h) (sat_cons (step1140 p h) (sat_cons (step344 p h) (sat_cons (step114 p h) (sat_cons (step301 p h) (sat_cons (step100 p h) (sat_cons (step919 p h) (sat_cons (step854 p h) (sat_cons (step924 p h) (sat_cons (step857 p h) (sat_cons (step927 p h) (sat_cons (step859 p h) (sat_cons (step931 p h) (sat_cons (step864 p h) (sat_cons (step967 p h) (sat_cons (step902 p h) (sat_cons (step2055 p h) (sat_nil p)))))))))))))))))))))
def c2237 : List Lit := [(61, false), (33, false), (53, false)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c407, c483] c2237 (by decide) p (sat_cons (step407 p h) (sat_cons (step483 p h) (sat_nil p)))
def c2238 : List Lit := [(171, false), (49, false), (45, false), (42, false), (27, true), (28, false)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c920, c2045, c924, c927, c931, c967, c2055, c900, c895, c891, c889, c886, c183, c182, c1820, c1951, c303, c302, c300, c1825] c2238 (by decide) p (sat_cons (step920 p h) (sat_cons (step2045 p h) (sat_cons (step924 p h) (sat_cons (step927 p h) (sat_cons (step931 p h) (sat_cons (step967 p h) (sat_cons (step2055 p h) (sat_cons (step900 p h) (sat_cons (step895 p h) (sat_cons (step891 p h) (sat_cons (step889 p h) (sat_cons (step886 p h) (sat_cons (step183 p h) (sat_cons (step182 p h) (sat_cons (step1820 p h) (sat_cons (step1951 p h) (sat_cons (step303 p h) (sat_cons (step302 p h) (sat_cons (step300 p h) (sat_cons (step1825 p h) (sat_nil p)))))))))))))))))))))
def c2239 : List Lit := [(44, false), (171, true), (930, true)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c2091, c294] c2239 (by decide) p (sat_cons (step2091 p h) (sat_cons (step294 p h) (sat_nil p)))
def c2240 : List Lit := [(50, true), (1, false), (40, true), (41, false), (168, true)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c275, c274, c1802] c2240 (by decide) p (sat_cons (step275 p h) (sat_cons (step274 p h) (sat_cons (step1802 p h) (sat_nil p))))
def c2241 : List Lit := [(858, true), (5, false), (1, false), (9, true), (134, true)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c1112, c1114, c1109, c1107, c24, c64] c2241 (by decide) p (sat_cons (step1112 p h) (sat_cons (step1114 p h) (sat_cons (step1109 p h) (sat_cons (step1107 p h) (sat_cons (step24 p h) (sat_cons (step64 p h) (sat_nil p)))))))
def c2242 : List Lit := [(1035, true), (405, true), (1008, false), (1025, false)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c1001, c985, c982, c977, c1901, c999, c997, c989, c988, c1484, c1537, c1532, c2188, c1510, c1903, c498, c1494, c1496, c1499, c1514, c1490, c1485, c563, c1479] c2242 (by decide) p (sat_cons (step1001 p h) (sat_cons (step985 p h) (sat_cons (step982 p h) (sat_cons (step977 p h) (sat_cons (step1901 p h) (sat_cons (step999 p h) (sat_cons (step997 p h) (sat_cons (step989 p h) (sat_cons (step988 p h) (sat_cons (step1484 p h) (sat_cons (step1537 p h) (sat_cons (step1532 p h) (sat_cons (step2188 p h) (sat_cons (step1510 p h) (sat_cons (step1903 p h) (sat_cons (step498 p h) (sat_cons (step1494 p h) (sat_cons (step1496 p h) (sat_cons (step1499 p h) (sat_cons (step1514 p h) (sat_cons (step1490 p h) (sat_cons (step1485 p h) (sat_cons (step563 p h) (sat_cons (step1479 p h) (sat_nil p)))))))))))))))))))))))))
def c2243 : List Lit := [(1016, true), (1051, false), (1020, false), (1098, true), (1036, true), (501, true), (1008, false)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c1090, c1026, c1001, c985, c982, c977, c999, c997, c989, c988, c1088, c1083, c1490, c1491, c2008, c2006, c1576, c1479, c1584, c1485, c1594, c1514, c1664, c1538, c2212, c2188, c1642, c498, c566, c1619, c1612] c2243 (by decide) p (sat_cons (step1090 p h) (sat_cons (step1026 p h) (sat_cons (step1001 p h) (sat_cons (step985 p h) (sat_cons (step982 p h) (sat_cons (step977 p h) (sat_cons (step999 p h) (sat_cons (step997 p h) (sat_cons (step989 p h) (sat_cons (step988 p h) (sat_cons (step1088 p h) (sat_cons (step1083 p h) (sat_cons (step1490 p h) (sat_cons (step1491 p h) (sat_cons (step2008 p h) (sat_cons (step2006 p h) (sat_cons (step1576 p h) (sat_cons (step1479 p h) (sat_cons (step1584 p h) (sat_cons (step1485 p h) (sat_cons (step1594 p h) (sat_cons (step1514 p h) (sat_cons (step1664 p h) (sat_cons (step1538 p h) (sat_cons (step2212 p h) (sat_cons (step2188 p h) (sat_cons (step1642 p h) (sat_cons (step498 p h) (sat_cons (step566 p h) (sat_cons (step1619 p h) (sat_cons (step1612 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2244 : List Lit := [(1018, false), (1098, true), (1036, true), (501, true), (42, false), (1008, false)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c1484, c1090, c1026, c1001, c985, c982, c977, c1901, c1533, c1511, c999, c997, c989, c988, c1024, c1022, c1011, c1007, c1004, c1496, c2155, c1502, c518, c654, c1565, c1568, c2243, c1499, c1510, c1515, c1538, c1485, c2188, c1479, c498, c2006, c563, c1492] c2244 (by decide) p (sat_cons (step1484 p h) (sat_cons (step1090 p h) (sat_cons (step1026 p h) (sat_cons (step1001 p h) (sat_cons (step985 p h) (sat_cons (step982 p h) (sat_cons (step977 p h) (sat_cons (step1901 p h) (sat_cons (step1533 p h) (sat_cons (step1511 p h) (sat_cons (step999 p h) (sat_cons (step997 p h) (sat_cons (step989 p h) (sat_cons (step988 p h) (sat_cons (step1024 p h) (sat_cons (step1022 p h) (sat_cons (step1011 p h) (sat_cons (step1007 p h) (sat_cons (step1004 p h) (sat_cons (step1496 p h) (sat_cons (step2155 p h) (sat_cons (step1502 p h) (sat_cons (step518 p h) (sat_cons (step654 p h) (sat_cons (step1565 p h) (sat_cons (step1568 p h) (sat_cons (step2243 p h) (sat_cons (step1499 p h) (sat_cons (step1510 p h) (sat_cons (step1515 p h) (sat_cons (step1538 p h) (sat_cons (step1485 p h) (sat_cons (step2188 p h) (sat_cons (step1479 p h) (sat_cons (step498 p h) (sat_cons (step2006 p h) (sat_cons (step563 p h) (sat_cons (step1492 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c2245 : List Lit := [(1047, true), (101, false), (98, false), (220, true), (223, true), (83, false), (90, false)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c1562, c1563, c1911, c637, c539, c612, c650] c2245 (by decide) p (sat_cons (step1562 p h) (sat_cons (step1563 p h) (sat_cons (step1911 p h) (sat_cons (step637 p h) (sat_cons (step539 p h) (sat_cons (step612 p h) (sat_cons (step650 p h) (sat_nil p))))))))
def c2246 : List Lit := [(866, false), (881, false), (917, false), (974, true), (42, false)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c1257, c1330, c1411, c1167, c1223, c1224, c1402, c1172, c1337, c1331, c1147, c1262, c1308, c1238, c1284, c2236, c1277] c2246 (by decide) p (sat_cons (step1257 p h) (sat_cons (step1330 p h) (sat_cons (step1411 p h) (sat_cons (step1167 p h) (sat_cons (step1223 p h) (sat_cons (step1224 p h) (sat_cons (step1402 p h) (sat_cons (step1172 p h) (sat_cons (step1337 p h) (sat_cons (step1331 p h) (sat_cons (step1147 p h) (sat_cons (step1262 p h) (sat_cons (step1308 p h) (sat_cons (step1238 p h) (sat_cons (step1284 p h) (sat_cons (step2236 p h) (sat_cons (step1277 p h) (sat_nil p))))))))))))))))))
def c2247 : List Lit := [(928, false), (954, true), (917, false)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c1257, c1332, c1313, c1284, c1285, c1308, c1309, c1279, c1338, c1296, c1262, c1293, c1240, c407, c483] c2247 (by decide) p (sat_cons (step1257 p h) (sat_cons (step1332 p h) (sat_cons (step1313 p h) (sat_cons (step1284 p h) (sat_cons (step1285 p h) (sat_cons (step1308 p h) (sat_cons (step1309 p h) (sat_cons (step1279 p h) (sat_cons (step1338 p h) (sat_cons (step1296 p h) (sat_cons (step1262 p h) (sat_cons (step1293 p h) (sat_cons (step1240 p h) (sat_cons (step407 p h) (sat_cons (step483 p h) (sat_nil p))))))))))))))))
def c2248 : List Lit := [(2, false), (45, false), (46, true), (42, false)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c245, c1919, c302, c835, c919, c836, c924, c846, c927, c866, c931, c902, c967, c2055] c2248 (by decide) p (sat_cons (step245 p h) (sat_cons (step1919 p h) (sat_cons (step302 p h) (sat_cons (step835 p h) (sat_cons (step919 p h) (sat_cons (step836 p h) (sat_cons (step924 p h) (sat_cons (step846 p h) (sat_cons (step927 p h) (sat_cons (step866 p h) (sat_cons (step931 p h) (sat_cons (step902 p h) (sat_cons (step967 p h) (sat_cons (step2055 p h) (sat_nil p)))))))))))))))
def c2249 : List Lit := [(67, false), (1086, true), (121, false), (122, true), (96, false), (124, true)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c732, c734, c1626, c1629, c1637] c2249 (by decide) p (sat_cons (step732 p h) (sat_cons (step734 p h) (sat_cons (step1626 p h) (sat_cons (step1629 p h) (sat_cons (step1637 p h) (sat_nil p))))))
def c2250 : List Lit := [(61, false), (53, false), (67, false)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c407, c486] c2250 (by decide) p (sat_cons (step407 p h) (sat_cons (step486 p h) (sat_nil p)))
def c2251 : List Lit := [(403, true), (77, true), (99, true), (74, false)]
theorem step2251 (p : Nat → Bool) (h : Constraints p) : clause p c2251 = true :=
  Snake9.LocalRup.prove_clause [c995, c997, c993, c989, c990, c988, c506, c1903, c499, c1995] c2251 (by decide) p (sat_cons (step995 p h) (sat_cons (step997 p h) (sat_cons (step993 p h) (sat_cons (step989 p h) (sat_cons (step990 p h) (sat_cons (step988 p h) (sat_cons (step506 p h) (sat_cons (step1903 p h) (sat_cons (step499 p h) (sat_cons (step1995 p h) (sat_nil p)))))))))))
def c2252 : List Lit := [(19, false), (63, false), (20, true), (146, true)]
theorem step2252 (p : Nat → Bool) (h : Constraints p) : clause p c2252 = true :=
  Snake9.LocalRup.prove_clause [c139, c1817, c140] c2252 (by decide) p (sat_cons (step139 p h) (sat_cons (step1817 p h) (sat_cons (step140 p h) (sat_nil p))))
def c2253 : List Lit := [(880, false), (898, true), (873, false), (858, false), (849, false), (150, true)]
theorem step2253 (p : Nat → Bool) (h : Constraints p) : clause p c2253 = true :=
  Snake9.LocalRup.prove_clause [c1101, c1125, c1204, c1174, c1160, c1163, c1173, c1154, c1211, c2201, c1130, c1104] c2253 (by decide) p (sat_cons (step1101 p h) (sat_cons (step1125 p h) (sat_cons (step1204 p h) (sat_cons (step1174 p h) (sat_cons (step1160 p h) (sat_cons (step1163 p h) (sat_cons (step1173 p h) (sat_cons (step1154 p h) (sat_cons (step1211 p h) (sat_cons (step2201 p h) (sat_cons (step1130 p h) (sat_cons (step1104 p h) (sat_nil p)))))))))))))
def c2254 : List Lit := [(1003, true), (988, false), (59, true), (189, true), (74, true)]
theorem step2254 (p : Nat → Bool) (h : Constraints p) : clause p c2254 = true :=
  Snake9.LocalRup.prove_clause [c1438, c1446, c1449, c1463, c1467, c1450, c1452, c1441, c1448, c1443, c413, c492] c2254 (by decide) p (sat_cons (step1438 p h) (sat_cons (step1446 p h) (sat_cons (step1449 p h) (sat_cons (step1463 p h) (sat_cons (step1467 p h) (sat_cons (step1450 p h) (sat_cons (step1452 p h) (sat_cons (step1441 p h) (sat_cons (step1448 p h) (sat_cons (step1443 p h) (sat_cons (step413 p h) (sat_cons (step492 p h) (sat_nil p)))))))))))))
def c2255 : List Lit := [(87, false), (1026, true), (14, false), (78, false)]
theorem step2255 (p : Nat → Bool) (h : Constraints p) : clause p c2255 = true :=
  Snake9.LocalRup.prove_clause [c551, c552, c553, c1479, c1490, c1494, c1482, c1499, c1510] c2255 (by decide) p (sat_cons (step551 p h) (sat_cons (step552 p h) (sat_cons (step553 p h) (sat_cons (step1479 p h) (sat_cons (step1490 p h) (sat_cons (step1494 p h) (sat_cons (step1482 p h) (sat_cons (step1499 p h) (sat_cons (step1510 p h) (sat_nil p))))))))))
def c2256 : List Lit := [(1065, true), (1017, true), (1047, false), (105, true), (230, true)]
theorem step2256 (p : Nat → Bool) (h : Constraints p) : clause p c2256 = true :=
  Snake9.LocalRup.prove_clause [c1570, c1577, c1584, c1599, c1595, c1571, c1587, c1585, c1565, c1578, c1580, c658, c2008, c681, c1492] c2256 (by decide) p (sat_cons (step1570 p h) (sat_cons (step1577 p h) (sat_cons (step1584 p h) (sat_cons (step1599 p h) (sat_cons (step1595 p h) (sat_cons (step1571 p h) (sat_cons (step1587 p h) (sat_cons (step1585 p h) (sat_cons (step1565 p h) (sat_cons (step1578 p h) (sat_cons (step1580 p h) (sat_cons (step658 p h) (sat_cons (step2008 p h) (sat_cons (step681 p h) (sat_cons (step1492 p h) (sat_nil p))))))))))))))))
def c2257 : List Lit := [(58, false), (1003, true), (60, false), (24, false), (185, true), (189, true), (74, true)]
theorem step2257 (p : Nat → Bool) (h : Constraints p) : clause p c2257 = true :=
  Snake9.LocalRup.prove_clause [c392, c401, c378, c2254, c1435] c2257 (by decide) p (sat_cons (step392 p h) (sat_cons (step401 p h) (sat_cons (step378 p h) (sat_cons (step2254 p h) (sat_cons (step1435 p h) (sat_nil p))))))
def c2258 : List Lit := [(87, true), (1002, true), (78, false), (6, true)]
theorem step2258 (p : Nat → Bool) (h : Constraints p) : clause p c2258 = true :=
  Snake9.LocalRup.prove_clause [c514, c991, c992, c995, c2059, c2060, c989, c985, c988, c982, c498, c977, c2188] c2258 (by decide) p (sat_cons (step514 p h) (sat_cons (step991 p h) (sat_cons (step992 p h) (sat_cons (step995 p h) (sat_cons (step2059 p h) (sat_cons (step2060 p h) (sat_cons (step989 p h) (sat_cons (step985 p h) (sat_cons (step988 p h) (sat_cons (step982 p h) (sat_cons (step498 p h) (sat_cons (step977 p h) (sat_cons (step2188 p h) (sat_nil p))))))))))))))
def c2259 : List Lit := [(203, true), (76, false), (75, true)]
theorem step2259 (p : Nat → Bool) (h : Constraints p) : clause p c2259 = true :=
  Snake9.LocalRup.prove_clause [c508, c507, c1997, c1835] c2259 (by decide) p (sat_cons (step508 p h) (sat_cons (step507 p h) (sat_cons (step1997 p h) (sat_cons (step1835 p h) (sat_nil p)))))
def c2260 : List Lit := [(1002, true), (14, false), (78, false), (6, true), (1036, true)]
theorem step2260 (p : Nat → Bool) (h : Constraints p) : clause p c2260 = true :=
  Snake9.LocalRup.prove_clause [c2258, c551, c546, c552, c553, c1479, c1446, c2188, c1490, c1494, c1996, c1449, c977, c1499, c1457, c982, c1533, c985, c1515, c2060, c1485, c995, c1477, c993, c990, c2259] c2260 (by decide) p (sat_cons (step2258 p h) (sat_cons (step551 p h) (sat_cons (step546 p h) (sat_cons (step552 p h) (sat_cons (step553 p h) (sat_cons (step1479 p h) (sat_cons (step1446 p h) (sat_cons (step2188 p h) (sat_cons (step1490 p h) (sat_cons (step1494 p h) (sat_cons (step1996 p h) (sat_cons (step1449 p h) (sat_cons (step977 p h) (sat_cons (step1499 p h) (sat_cons (step1457 p h) (sat_cons (step982 p h) (sat_cons (step1533 p h) (sat_cons (step985 p h) (sat_cons (step1515 p h) (sat_cons (step2060 p h) (sat_cons (step1485 p h) (sat_cons (step995 p h) (sat_cons (step1477 p h) (sat_cons (step993 p h) (sat_cons (step990 p h) (sat_cons (step2259 p h) (sat_nil p)))))))))))))))))))))))))))
def c2261 : List Lit := [(75, false), (16, false), (74, true), (80, false)]
theorem step2261 (p : Nat → Bool) (h : Constraints p) : clause p c2261 = true :=
  Snake9.LocalRup.prove_clause [c1996, c584] c2261 (by decide) p (sat_cons (step1996 p h) (sat_cons (step584 p h) (sat_nil p)))
def c2262 : List Lit := [(1018, false), (1008, false), (1026, true)]
theorem step2262 (p : Nat → Bool) (h : Constraints p) : clause p c2262 = true :=
  Snake9.LocalRup.prove_clause [c1484, c1510, c1496, c1499, c1514, c1491, c1485, c2006, c1479] c2262 (by decide) p (sat_cons (step1484 p h) (sat_cons (step1510 p h) (sat_cons (step1496 p h) (sat_cons (step1499 p h) (sat_cons (step1514 p h) (sat_cons (step1491 p h) (sat_cons (step1485 p h) (sat_cons (step2006 p h) (sat_cons (step1479 p h) (sat_nil p))))))))))
def c2263 : List Lit := [(65, true), (56, false), (1003, true), (189, true), (74, true)]
theorem step2263 (p : Nat → Bool) (h : Constraints p) : clause p c2263 = true :=
  Snake9.LocalRup.prove_clause [c1446, c1449, c1467, c1435, c1981, c1438, c2254, c1441, c1463, c397, c1450, c1448] c2263 (by decide) p (sat_cons (step1446 p h) (sat_cons (step1449 p h) (sat_cons (step1467 p h) (sat_cons (step1435 p h) (sat_cons (step1981 p h) (sat_cons (step1438 p h) (sat_cons (step2254 p h) (sat_cons (step1441 p h) (sat_cons (step1463 p h) (sat_cons (step397 p h) (sat_cons (step1450 p h) (sat_cons (step1448 p h) (sat_nil p)))))))))))))
def c2264 : List Lit := [(1008, false), (1065, true), (230, true), (80, false), (1026, true), (78, false)]
theorem step2264 (p : Nat → Bool) (h : Constraints p) : clause p c2264 = true :=
  Snake9.LocalRup.prove_clause [c1484, c2262, c1510, c1494, c1501, c521, c520, c2256, c1563] c2264 (by decide) p (sat_cons (step1484 p h) (sat_cons (step2262 p h) (sat_cons (step1510 p h) (sat_cons (step1494 p h) (sat_cons (step1501 p h) (sat_cons (step521 p h) (sat_cons (step520 p h) (sat_cons (step2256 p h) (sat_cons (step1563 p h) (sat_nil p))))))))))
def c2265 : List Lit := [(1065, true), (230, true), (203, true), (80, false), (1026, true), (74, true), (78, false)]
theorem step2265 (p : Nat → Bool) (h : Constraints p) : clause p c2265 = true :=
  Snake9.LocalRup.prove_clause [c2264, c1477, c2259, c1996, c521, c520, c1563, c1570, c2256, c1595, c1501, c1587, c1510, c1578, c1482, c2007, c1479] c2265 (by decide) p (sat_cons (step2264 p h) (sat_cons (step1477 p h) (sat_cons (step2259 p h) (sat_cons (step1996 p h) (sat_cons (step521 p h) (sat_cons (step520 p h) (sat_cons (step1563 p h) (sat_cons (step1570 p h) (sat_cons (step2256 p h) (sat_cons (step1595 p h) (sat_cons (step1501 p h) (sat_cons (step1587 p h) (sat_cons (step1510 p h) (sat_cons (step1578 p h) (sat_cons (step1482 p h) (sat_cons (step2007 p h) (sat_cons (step1479 p h) (sat_nil p))))))))))))))))))
def c2266 : List Lit := [(88, false), (77, false), (92, true), (85, true), (99, true), (1055, false), (93, true), (223, true), (230, true), (215, true), (1066, true), (87, true)]
theorem step2266 (p : Nat → Bool) (h : Constraints p) : clause p c2266 = true :=
  Snake9.LocalRup.prove_clause [c1997, c582, c1907, c648, c1564, c612] c2266 (by decide) p (sat_cons (step1997 p h) (sat_cons (step582 p h) (sat_cons (step1907 p h) (sat_cons (step648 p h) (sat_cons (step1564 p h) (sat_cons (step612 p h) (sat_nil p)))))))
def c2267 : List Lit := [(105, true), (1065, true), (80, false), (76, false), (1017, true), (75, true), (90, true), (87, false)]
theorem step2267 (p : Nat → Bool) (h : Constraints p) : clause p c2267 = true :=
  Snake9.LocalRup.prove_clause [c2259, c990, c993, c995, c999, c1026, c2071, c1085, c1052, c1036, c1030, c1029, c1035, c1033, c1032, c2062, c1021, c1019, c1018, c1017, c1998, c2256, c1562, c627, c505, c605, c1997, c646, c610, c612, c1837, c1844, c2010] c2267 (by decide) p (sat_cons (step2259 p h) (sat_cons (step990 p h) (sat_cons (step993 p h) (sat_cons (step995 p h) (sat_cons (step999 p h) (sat_cons (step1026 p h) (sat_cons (step2071 p h) (sat_cons (step1085 p h) (sat_cons (step1052 p h) (sat_cons (step1036 p h) (sat_cons (step1030 p h) (sat_cons (step1029 p h) (sat_cons (step1035 p h) (sat_cons (step1033 p h) (sat_cons (step1032 p h) (sat_cons (step2062 p h) (sat_cons (step1021 p h) (sat_cons (step1019 p h) (sat_cons (step1018 p h) (sat_cons (step1017 p h) (sat_cons (step1998 p h) (sat_cons (step2256 p h) (sat_cons (step1562 p h) (sat_cons (step627 p h) (sat_cons (step505 p h) (sat_cons (step605 p h) (sat_cons (step1997 p h) (sat_cons (step646 p h) (sat_cons (step610 p h) (sat_cons (step612 p h) (sat_cons (step1837 p h) (sat_cons (step1844 p h) (sat_cons (step2010 p h) (sat_nil p))))))))))))))))))))))))))))))))))
def c2268 : List Lit := [(1016, true), (1047, false), (1065, true), (230, true)]
theorem step2268 (p : Nat → Bool) (h : Constraints p) : clause p c2268 = true :=
  Snake9.LocalRup.prove_clause [c1570, c1595, c1490, c1491, c2008, c1576, c1584, c1585, c1599, c1580, c1571, c1565, c658, c681] c2268 (by decide) p (sat_cons (step1570 p h) (sat_cons (step1595 p h) (sat_cons (step1490 p h) (sat_cons (step1491 p h) (sat_cons (step2008 p h) (sat_cons (step1576 p h) (sat_cons (step1584 p h) (sat_cons (step1585 p h) (sat_cons (step1599 p h) (sat_cons (step1580 p h) (sat_cons (step1571 p h) (sat_cons (step1565 p h) (sat_cons (step658 p h) (sat_cons (step681 p h) (sat_nil p)))))))))))))))
def c2269 : List Lit := [(83, false), (1017, true), (87, false), (78, false)]
theorem step2269 (p : Nat → Bool) (h : Constraints p) : clause p c2269 = true :=
  Snake9.LocalRup.prove_clause [c2006, c568, c1492] c2269 (by decide) p (sat_cons (step2006 p h) (sat_cons (step568 p h) (sat_cons (step1492 p h) (sat_nil p))))
def c2270 : List Lit := [(1065, true), (1057, false), (1016, true), (230, true), (80, false), (106, true), (78, false)]
theorem step2270 (p : Nat → Bool) (h : Constraints p) : clause p c2270 = true :=
  Snake9.LocalRup.prove_clause [c1592, c2268, c1588, c1563, c1578, c522] c2270 (by decide) p (sat_cons (step1592 p h) (sat_cons (step2268 p h) (sat_cons (step1588 p h) (sat_cons (step1563 p h) (sat_cons (step1578 p h) (sat_cons (step522 p h) (sat_nil p)))))))
def c2271 : List Lit := [(109, false), (931, true), (96, false), (66, true), (64, true), (67, false), (194, true)]
theorem step2271 (p : Nat → Bool) (h : Constraints p) : clause p c2271 = true :=
  Snake9.LocalRup.prove_clause [c731, c465, c329, c330, c1281] c2271 (by decide) p (sat_cons (step731 p h) (sat_cons (step465 p h) (sat_cons (step329 p h) (sat_cons (step330 p h) (sat_cons (step1281 p h) (sat_nil p))))))
def c2272 : List Lit := [(897, true), (864, false), (855, false), (877, false), (155, true), (65, false), (67, false), (14, true), (989, true)]
theorem step2272 (p : Nat → Bool) (h : Constraints p) : clause p c2272 = true :=
  Snake9.LocalRup.prove_clause [c1161, c1167, c1216, c1210, c1123, c1168, c1119, c1162, c1111, c1156, c1157, c2179, c184] c2272 (by decide) p (sat_cons (step1161 p h) (sat_cons (step1167 p h) (sat_cons (step1216 p h) (sat_cons (step1210 p h) (sat_cons (step1123 p h) (sat_cons (step1168 p h) (sat_cons (step1119 p h) (sat_cons (step1162 p h) (sat_cons (step1111 p h) (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step2179 p h) (sat_cons (step184 p h) (sat_nil p))))))))))))))
def c2273 : List Lit := [(44, false), (7, true), (171, true)]
theorem step2273 (p : Nat → Bool) (h : Constraints p) : clause p c2273 = true :=
  Snake9.LocalRup.prove_clause [c2176, c295, c1928] c2273 (by decide) p (sat_cons (step2176 p h) (sat_cons (step295 p h) (sat_cons (step1928 p h) (sat_nil p))))
def c2274 : List Lit := [(941, true), (65, false), (371, true)]
theorem step2274 (p : Nat → Bool) (h : Constraints p) : clause p c2274 = true :=
  Snake9.LocalRup.prove_clause [c956, c953, c947, c408, c1293, c958, c944, c943, c1297, c1299, c1295, c1290, c378, c392] c2274 (by decide) p (sat_cons (step956 p h) (sat_cons (step953 p h) (sat_cons (step947 p h) (sat_cons (step408 p h) (sat_cons (step1293 p h) (sat_cons (step958 p h) (sat_cons (step944 p h) (sat_cons (step943 p h) (sat_cons (step1297 p h) (sat_cons (step1299 p h) (sat_cons (step1295 p h) (sat_cons (step1290 p h) (sat_cons (step378 p h) (sat_cons (step392 p h) (sat_nil p)))))))))))))))
def c2275 : List Lit := [(886, true), (30, false), (64, true), (877, false), (155, true)]
theorem step2275 (p : Nat → Bool) (h : Constraints p) : clause p c2275 = true :=
  Snake9.LocalRup.prove_clause [c1161, c1168, c1172, c1162, c1145, c1157, c1143, c182, c172] c2275 (by decide) p (sat_cons (step1161 p h) (sat_cons (step1168 p h) (sat_cons (step1172 p h) (sat_cons (step1162 p h) (sat_cons (step1145 p h) (sat_cons (step1157 p h) (sat_cons (step1143 p h) (sat_cons (step182 p h) (sat_cons (step172 p h) (sat_nil p))))))))))
def c2276 : List Lit := [(864, true), (377, true), (10, true), (1003, true), (74, true), (856, false), (6, true)]
theorem step2276 (p : Nat → Bool) (h : Constraints p) : clause p c2276 = true :=
  Snake9.LocalRup.prove_clause [c972, c900, c897, c879, c876, c875, c153, c902, c866, c844, c841, c840, c877, c874, c970, c965, c961, c958, c944, c943, c956, c952, c951, c846, c837, c1106, c1115, c1122, c1126, c1118, c1103, c1108, c7, c63, c1921, c1943, c146, c2257, c1941] c2276 (by decide) p (sat_cons (step972 p h) (sat_cons (step900 p h) (sat_cons (step897 p h) (sat_cons (step879 p h) (sat_cons (step876 p h) (sat_cons (step875 p h) (sat_cons (step153 p h) (sat_cons (step902 p h) (sat_cons (step866 p h) (sat_cons (step844 p h) (sat_cons (step841 p h) (sat_cons (step840 p h) (sat_cons (step877 p h) (sat_cons (step874 p h) (sat_cons (step970 p h) (sat_cons (step965 p h) (sat_cons (step961 p h) (sat_cons (step958 p h) (sat_cons (step944 p h) (sat_cons (step943 p h) (sat_cons (step956 p h) (sat_cons (step952 p h) (sat_cons (step951 p h) (sat_cons (step846 p h) (sat_cons (step837 p h) (sat_cons (step1106 p h) (sat_cons (step1115 p h) (sat_cons (step1122 p h) (sat_cons (step1126 p h) (sat_cons (step1118 p h) (sat_cons (step1103 p h) (sat_cons (step1108 p h) (sat_cons (step7 p h) (sat_cons (step63 p h) (sat_cons (step1921 p h) (sat_cons (step1943 p h) (sat_cons (step146 p h) (sat_cons (step2257 p h) (sat_cons (step1941 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))
def c2277 : List Lit := [(66, false), (58, true), (947, true), (68, false), (67, false), (938, false)]
theorem step2277 (p : Nat → Bool) (h : Constraints p) : clause p c2277 = true :=
  Snake9.LocalRup.prove_clause [c453, c457, c1276, c1292, c1284, c1302, c1311] c2277 (by decide) p (sat_cons (step453 p h) (sat_cons (step457 p h) (sat_cons (step1276 p h) (sat_cons (step1292 p h) (sat_cons (step1284 p h) (sat_cons (step1302 p h) (sat_cons (step1311 p h) (sat_nil p))))))))
def c2278 : List Lit := [(910, false), (955, true), (941, false), (171, true)]
theorem step2278 (p : Nat → Bool) (h : Constraints p) : clause p c2278 = true :=
  Snake9.LocalRup.prove_clause [c1305, c1339, c1261, c1333, c1310, c1262, c1282, c1249, c2239, c1246] c2278 (by decide) p (sat_cons (step1305 p h) (sat_cons (step1339 p h) (sat_cons (step1261 p h) (sat_cons (step1333 p h) (sat_cons (step1310 p h) (sat_cons (step1262 p h) (sat_cons (step1282 p h) (sat_cons (step1249 p h) (sat_cons (step2239 p h) (sat_cons (step1246 p h) (sat_nil p)))))))))))
def c2279 : List Lit := [(932, true), (36, false), (916, true), (68, false), (67, false), (339, true)]
theorem step2279 (p : Nat → Bool) (h : Constraints p) : clause p c2279 = true :=
  Snake9.LocalRup.prove_clause [c924, c920, c923, c922, c1282, c1284, c1279, c2239, c1276, c325, c1248, c453, c251, c350, c317] c2279 (by decide) p (sat_cons (step924 p h) (sat_cons (step920 p h) (sat_cons (step923 p h) (sat_cons (step922 p h) (sat_cons (step1282 p h) (sat_cons (step1284 p h) (sat_cons (step1279 p h) (sat_cons (step2239 p h) (sat_cons (step1276 p h) (sat_cons (step325 p h) (sat_cons (step1248 p h) (sat_cons (step453 p h) (sat_cons (step251 p h) (sat_cons (step350 p h) (sat_cons (step317 p h) (sat_nil p))))))))))))))))
def c2280 : List Lit := [(65, true), (403, false), (1003, true), (74, true)]
theorem step2280 (p : Nat → Bool) (h : Constraints p) : clause p c2280 = true :=
  Snake9.LocalRup.prove_clause [c999, c1026, c1090, c2072, c970, c965, c961, c956, c952, c951, c2060, c985, c982, c977, c1446, c1449, c1467, c1439, c1435, c1437, c1438, c2254, c1441, c1463, c1450, c1452, c1448, c1443, c2085, c1831, c471] c2280 (by decide) p (sat_cons (step999 p h) (sat_cons (step1026 p h) (sat_cons (step1090 p h) (sat_cons (step2072 p h) (sat_cons (step970 p h) (sat_cons (step965 p h) (sat_cons (step961 p h) (sat_cons (step956 p h) (sat_cons (step952 p h) (sat_cons (step951 p h) (sat_cons (step2060 p h) (sat_cons (step985 p h) (sat_cons (step982 p h) (sat_cons (step977 p h) (sat_cons (step1446 p h) (sat_cons (step1449 p h) (sat_cons (step1467 p h) (sat_cons (step1439 p h) (sat_cons (step1435 p h) (sat_cons (step1437 p h) (sat_cons (step1438 p h) (sat_cons (step2254 p h) (sat_cons (step1441 p h) (sat_cons (step1463 p h) (sat_cons (step1450 p h) (sat_cons (step1452 p h) (sat_cons (step1448 p h) (sat_cons (step1443 p h) (sat_cons (step2085 p h) (sat_cons (step1831 p h) (sat_cons (step471 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c2281 : List Lit := [(401, true), (1013, true), (88, false), (74, true), (78, false), (6, true)]
theorem step2281 (p : Nat → Bool) (h : Constraints p) : clause p c2281 = true :=
  Snake9.LocalRup.prove_clause [c992, c993, c991, c990, c514, c568, c571, c1479, c1996, c1485, c2259, c1477] c2281 (by decide) p (sat_cons (step992 p h) (sat_cons (step993 p h) (sat_cons (step991 p h) (sat_cons (step990 p h) (sat_cons (step514 p h) (sat_cons (step568 p h) (sat_cons (step571 p h) (sat_cons (step1479 p h) (sat_cons (step1996 p h) (sat_cons (step1485 p h) (sat_cons (step2259 p h) (sat_cons (step1477 p h) (sat_nil p)))))))))))))
def c2282 : List Lit := [(1026, true), (88, true), (1018, false)]
theorem step2282 (p : Nat → Bool) (h : Constraints p) : clause p c2282 = true :=
  Snake9.LocalRup.prove_clause [c1490, c1499, c1506, c1510, c1502, c1482, c1492, c1479, c2006] c2282 (by decide) p (sat_cons (step1490 p h) (sat_cons (step1499 p h) (sat_cons (step1506 p h) (sat_cons (step1510 p h) (sat_cons (step1502 p h) (sat_cons (step1482 p h) (sat_cons (step1492 p h) (sat_cons (step1479 p h) (sat_cons (step2006 p h) (sat_nil p))))))))))
def c2283 : List Lit := [(886, true), (64, true), (877, false), (155, true)]
theorem step2283 (p : Nat → Bool) (h : Constraints p) : clause p c2283 = true :=
  Snake9.LocalRup.prove_clause [c1168, c2275, c1162, c1156] c2283 (by decide) p (sat_cons (step1168 p h) (sat_cons (step2275 p h) (sat_cons (step1162 p h) (sat_cons (step1156 p h) (sat_nil p)))))
def c2284 : List Lit := [(21, false), (918, true), (865, true), (23, true), (132, true), (134, true), (148, true), (171, true), (185, true), (65, false), (10, true), (856, false), (6, true)]
theorem step2284 (p : Nat → Bool) (h : Constraints p) : clause p c2284 = true :=
  Snake9.LocalRup.prove_clause [c147, c146, c1922, c1941, c392, c378, c1943, c63, c1108, c2273, c1118, c1246, c1127, c1101, c1098, c1252, c2227] c2284 (by decide) p (sat_cons (step147 p h) (sat_cons (step146 p h) (sat_cons (step1922 p h) (sat_cons (step1941 p h) (sat_cons (step392 p h) (sat_cons (step378 p h) (sat_cons (step1943 p h) (sat_cons (step63 p h) (sat_cons (step1108 p h) (sat_cons (step2273 p h) (sat_cons (step1118 p h) (sat_cons (step1246 p h) (sat_cons (step1127 p h) (sat_cons (step1101 p h) (sat_cons (step1098 p h) (sat_cons (step1252 p h) (sat_cons (step2227 p h) (sat_nil p))))))))))))))))))
def c2285 : List Lit := [(1057, true), (107, false), (83, false)]
theorem step2285 (p : Nat → Bool) (h : Constraints p) : clause p c2285 = true :=
  Snake9.LocalRup.prove_clause [c1579, c1580, c665] c2285 (by decide) p (sat_cons (step1579 p h) (sat_cons (step1580 p h) (sat_cons (step665 p h) (sat_nil p))))
def c2286 : List Lit := [(16, false), (75, false), (90, false), (74, true), (78, false), (6, true)]
theorem step2286 (p : Nat → Bool) (h : Constraints p) : clause p c2286 = true :=
  Snake9.LocalRup.prove_clause [c2261, c586, c511] c2286 (by decide) p (sat_cons (step2261 p h) (sat_cons (step586 p h) (sat_cons (step511 p h) (sat_nil p))))
def c2287 : List Lit := [(205, true), (90, false), (78, false), (6, true)]
theorem step2287 (p : Nat → Bool) (h : Constraints p) : clause p c2287 = true :=
  Snake9.LocalRup.prove_clause [c514, c515, c1836] c2287 (by decide) p (sat_cons (step514 p h) (sat_cons (step515 p h) (sat_cons (step1836 p h) (sat_nil p))))
def c2288 : List Lit := [(910, true), (16, true), (160, true), (76, false), (203, true), (90, false)]
theorem step2288 (p : Nat → Bool) (h : Constraints p) : clause p c2288 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1240, c1236, c617, c506, c1997, c204, c220] c2288 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1240 p h) (sat_cons (step1236 p h) (sat_cons (step617 p h) (sat_cons (step506 p h) (sat_cons (step1997 p h) (sat_cons (step204 p h) (sat_cons (step220 p h) (sat_nil p)))))))))
def c2289 : List Lit := [(93, false), (99, true), (220, true), (90, false), (78, false)]
theorem step2289 (p : Nat → Bool) (h : Constraints p) : clause p c2289 = true :=
  Snake9.LocalRup.prove_clause [c520, c606] c2289 (by decide) p (sat_cons (step520 p h) (sat_cons (step606 p h) (sat_nil p)))
def c2290 : List Lit := [(886, true), (10, false), (65, false), (877, false), (155, true)]
theorem step2290 (p : Nat → Bool) (h : Constraints p) : clause p c2290 = true :=
  Snake9.LocalRup.prove_clause [c1168, c2283, c1162, c1156, c1157, c169, c1820, c183] c2290 (by decide) p (sat_cons (step1168 p h) (sat_cons (step2283 p h) (sat_cons (step1162 p h) (sat_cons (step1156 p h) (sat_cons (step1157 p h) (sat_cons (step169 p h) (sat_cons (step1820 p h) (sat_cons (step183 p h) (sat_nil p)))))))))
def c2291 : List Lit := [(28, false), (30, false), (10, false), (65, false), (155, true)]
theorem step2291 (p : Nat → Bool) (h : Constraints p) : clause p c2291 = true :=
  Snake9.LocalRup.prove_clause [c169, c183, c182, c1820] c2291 (by decide) p (sat_cons (step169 p h) (sat_cons (step183 p h) (sat_cons (step182 p h) (sat_cons (step1820 p h) (sat_nil p)))))
end B112E256
