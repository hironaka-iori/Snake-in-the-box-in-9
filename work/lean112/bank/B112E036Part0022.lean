import B112E036Part0021
namespace B112E036
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c3053 : List Lit := [(6, false), (73, false), (1550, true), (37, false)]
theorem step3053 (p : Nat → Bool) (h : Constraints p) : clause p c3053 = true :=
  Snake9.LocalRup.prove_clause [c22, c25, c1001] c3053 (by decide) p (sat_cons (step22 p h) (sat_cons (step25 p h) (sat_cons (step1001 p h) (sat_nil p))))
def c3054 : List Lit := [(1852, true), (1817, false), (105, true), (100, true), (95, true), (1771, false), (1759, false), (1725, false)]
theorem step3054 (p : Nat → Bool) (h : Constraints p) : clause p c3054 = true :=
  Snake9.LocalRup.prove_clause [c1400, c3003, c1506, c1408, c1390, c1395, c1556, c1563, c1513, c1368, c1425, c1429, c1411, c1409, c1396, c1398, c1402, c1403, c1404, c1391, c2286, c3038] c3054 (by decide) p (sat_cons (step1400 p h) (sat_cons (step3003 p h) (sat_cons (step1506 p h) (sat_cons (step1408 p h) (sat_cons (step1390 p h) (sat_cons (step1395 p h) (sat_cons (step1556 p h) (sat_cons (step1563 p h) (sat_cons (step1513 p h) (sat_cons (step1368 p h) (sat_cons (step1425 p h) (sat_cons (step1429 p h) (sat_cons (step1411 p h) (sat_cons (step1409 p h) (sat_cons (step1396 p h) (sat_cons (step1398 p h) (sat_cons (step1402 p h) (sat_cons (step1403 p h) (sat_cons (step1404 p h) (sat_cons (step1391 p h) (sat_cons (step2286 p h) (sat_cons (step3038 p h) (sat_nil p)))))))))))))))))))))))
def c3055 : List Lit := [(1628, true), (1623, false), (31, false), (37, false)]
theorem step3055 (p : Nat → Bool) (h : Constraints p) : clause p c3055 = true :=
  Snake9.LocalRup.prove_clause [c2718, c1137, c99, c1112, c1105] c3055 (by decide) p (sat_cons (step2718 p h) (sat_cons (step1137 p h) (sat_cons (step99 p h) (sat_cons (step1112 p h) (sat_cons (step1105 p h) (sat_nil p))))))
def c3056 : List Lit := [(1829, true), (1789, false), (95, true), (1773, false), (66, true)]
theorem step3056 (p : Nat → Bool) (h : Constraints p) : clause p c3056 = true :=
  Snake9.LocalRup.prove_clause [c2304, c1783, c1477, c1506, c1512, c2267, c2296] c3056 (by decide) p (sat_cons (step2304 p h) (sat_cons (step1783 p h) (sat_cons (step1477 p h) (sat_cons (step1506 p h) (sat_cons (step1512 p h) (sat_cons (step2267 p h) (sat_cons (step2296 p h) (sat_nil p))))))))
def c3057 : List Lit := [(1707, true), (1659, true), (46, false), (52, true), (37, false), (50, true)]
theorem step3057 (p : Nat → Bool) (h : Constraints p) : clause p c3057 = true :=
  Snake9.LocalRup.prove_clause [c1280, c1281, c211, c2414, c1154] c3057 (by decide) p (sat_cons (step1280 p h) (sat_cons (step1281 p h) (sat_cons (step211 p h) (sat_cons (step2414 p h) (sat_cons (step1154 p h) (sat_nil p))))))
def c3058 : List Lit := [(1725, true), (1707, false), (95, true), (6, true)]
theorem step3058 (p : Nat → Bool) (h : Constraints p) : clause p c3058 = true :=
  Snake9.LocalRup.prove_clause [c2004, c2300, c1289, c1891, c1890, c1283, c1613] c3058 (by decide) p (sat_cons (step2004 p h) (sat_cons (step2300 p h) (sat_cons (step1289 p h) (sat_cons (step1891 p h) (sat_cons (step1890 p h) (sat_cons (step1283 p h) (sat_cons (step1613 p h) (sat_nil p))))))))
def c3059 : List Lit := [(73, false), (74, false), (95, true), (6, true), (70, false)]
theorem step3059 (p : Nat → Bool) (h : Constraints p) : clause p c3059 = true :=
  Snake9.LocalRup.prove_clause [c1891, c1613] c3059 (by decide) p (sat_cons (step1891 p h) (sat_cons (step1613 p h) (sat_nil p)))
def c3060 : List Lit := [(64, false), (1659, true), (67, false), (46, false), (1637, false), (37, false), (50, true)]
theorem step3060 (p : Nat → Bool) (h : Constraints p) : clause p c3060 = true :=
  Snake9.LocalRup.prove_clause [c211, c1154, c1164, c1201, c2019, c2120, c2356, c312, c324, c1880] c3060 (by decide) p (sat_cons (step211 p h) (sat_cons (step1154 p h) (sat_cons (step1164 p h) (sat_cons (step1201 p h) (sat_cons (step2019 p h) (sat_cons (step2120 p h) (sat_cons (step2356 p h) (sat_cons (step312 p h) (sat_cons (step324 p h) (sat_cons (step1880 p h) (sat_nil p)))))))))))
def c3061 : List Lit := [(1630, true), (1635, true), (1619, false), (32, true)]
theorem step3061 (p : Nat → Bool) (h : Constraints p) : clause p c3061 = true :=
  Snake9.LocalRup.prove_clause [c2524, c2526, c1107, c2518] c3061 (by decide) p (sat_cons (step2524 p h) (sat_cons (step2526 p h) (sat_cons (step1107 p h) (sat_cons (step2518 p h) (sat_nil p)))))
def c3062 : List Lit := [(64, true), (1708, true), (193, true), (196, true), (66, true), (50, true), (58, true), (56, true)]
theorem step3062 (p : Nat → Bool) (h : Constraints p) : clause p c3062 = true :=
  Snake9.LocalRup.prove_clause [c1282, c317, c1872, c1880, c340] c3062 (by decide) p (sat_cons (step1282 p h) (sat_cons (step317 p h) (sat_cons (step1872 p h) (sat_cons (step1880 p h) (sat_cons (step340 p h) (sat_nil p))))))
def c3063 : List Lit := [(1799, true), (106, true), (97, false), (1791, true), (1773, false), (38, false), (37, false)]
theorem step3063 (p : Nat → Bool) (h : Constraints p) : clause p c3063 = true :=
  Snake9.LocalRup.prove_clause [c1444, c1783, c1441, c1442, c550, c553, c515, c1405, c1388, c1407, c1398, c1430] c3063 (by decide) p (sat_cons (step1444 p h) (sat_cons (step1783 p h) (sat_cons (step1441 p h) (sat_cons (step1442 p h) (sat_cons (step550 p h) (sat_cons (step553 p h) (sat_cons (step515 p h) (sat_cons (step1405 p h) (sat_cons (step1388 p h) (sat_cons (step1407 p h) (sat_cons (step1398 p h) (sat_cons (step1430 p h) (sat_nil p)))))))))))))
def c3064 : List Lit := [(1799, false), (95, false), (1810, false), (1781, false), (1829, true), (100, true), (37, false)]
theorem step3064 (p : Nat → Bool) (h : Constraints p) : clause p c3064 = true :=
  Snake9.LocalRup.prove_clause [c1406, c1390, c2339, c1395, c1424, c1506, c1477, c2301, c1512, c1425, c1409, c1401, c2033, c2032, c513, c515, c1388] c3064 (by decide) p (sat_cons (step1406 p h) (sat_cons (step1390 p h) (sat_cons (step2339 p h) (sat_cons (step1395 p h) (sat_cons (step1424 p h) (sat_cons (step1506 p h) (sat_cons (step1477 p h) (sat_cons (step2301 p h) (sat_cons (step1512 p h) (sat_cons (step1425 p h) (sat_cons (step1409 p h) (sat_cons (step1401 p h) (sat_cons (step2033 p h) (sat_cons (step2032 p h) (sat_cons (step513 p h) (sat_cons (step515 p h) (sat_cons (step1388 p h) (sat_nil p))))))))))))))))))
def c3065 : List Lit := [(95, false), (1810, false), (106, true), (1829, true), (100, true), (38, false), (37, false)]
theorem step3065 (p : Nat → Bool) (h : Constraints p) : clause p c3065 = true :=
  Snake9.LocalRup.prove_clause [c1404, c1406, c1473, c1517, c1434, c1390, c3064, c1444, c1446, c3063, c1441, c1442, c1438, c1439, c513, c515, c710, c1388, c1948, c1398, c1399, c730, c1429, c1391, c1512, c1784, c1474] c3065 (by decide) p (sat_cons (step1404 p h) (sat_cons (step1406 p h) (sat_cons (step1473 p h) (sat_cons (step1517 p h) (sat_cons (step1434 p h) (sat_cons (step1390 p h) (sat_cons (step3064 p h) (sat_cons (step1444 p h) (sat_cons (step1446 p h) (sat_cons (step3063 p h) (sat_cons (step1441 p h) (sat_cons (step1442 p h) (sat_cons (step1438 p h) (sat_cons (step1439 p h) (sat_cons (step513 p h) (sat_cons (step515 p h) (sat_cons (step710 p h) (sat_cons (step1388 p h) (sat_cons (step1948 p h) (sat_cons (step1398 p h) (sat_cons (step1399 p h) (sat_cons (step730 p h) (sat_cons (step1429 p h) (sat_cons (step1391 p h) (sat_cons (step1512 p h) (sat_cons (step1784 p h) (sat_cons (step1474 p h) (sat_nil p))))))))))))))))))))))))))))
def c3066 : List Lit := [(1776, false), (1790, true), (95, true), (1781, false), (1829, true)]
theorem step3066 (p : Nat → Bool) (h : Constraints p) : clause p c3066 = true :=
  Snake9.LocalRup.prove_clause [c1406, c1424, c1425, c1506, c1409, c2267, c1401, c2033] c3066 (by decide) p (sat_cons (step1406 p h) (sat_cons (step1424 p h) (sat_cons (step1425 p h) (sat_cons (step1506 p h) (sat_cons (step1409 p h) (sat_cons (step2267 p h) (sat_cons (step1401 p h) (sat_cons (step2033 p h) (sat_nil p)))))))))
def c3067 : List Lit := [(1660, true), (63, false), (52, true), (57, true), (56, true), (1635, false)]
theorem step3067 (p : Nat → Bool) (h : Constraints p) : clause p c3067 = true :=
  Snake9.LocalRup.prove_clause [c1873, c1156, c1161, c2382, c1199, c1202, c2500, c1162, c302, c1157] c3067 (by decide) p (sat_cons (step1873 p h) (sat_cons (step1156 p h) (sat_cons (step1161 p h) (sat_cons (step2382 p h) (sat_cons (step1199 p h) (sat_cons (step1202 p h) (sat_cons (step2500 p h) (sat_cons (step1162 p h) (sat_cons (step302 p h) (sat_cons (step1157 p h) (sat_nil p)))))))))))
def c3068 : List Lit := [(1636, false), (63, false), (1693, true), (1628, false)]
theorem step3068 (p : Nat → Bool) (h : Constraints p) : clause p c3068 = true :=
  Snake9.LocalRup.prove_clause [c2501, c1248, c1218, c2048, c2414, c1217, c2099, c1254] c3068 (by decide) p (sat_cons (step2501 p h) (sat_cons (step1248 p h) (sat_cons (step1218 p h) (sat_cons (step2048 p h) (sat_cons (step2414 p h) (sat_cons (step1217 p h) (sat_cons (step2099 p h) (sat_cons (step1254 p h) (sat_nil p)))))))))
def c3069 : List Lit := [(80, false), (109, false), (70, false), (101, false)]
theorem step3069 (p : Nat → Bool) (h : Constraints p) : clause p c3069 = true :=
  Snake9.LocalRup.prove_clause [c619, c1898, c382] c3069 (by decide) p (sat_cons (step619 p h) (sat_cons (step1898 p h) (sat_cons (step382 p h) (sat_nil p))))
def c3070 : List Lit := [(1789, true), (95, true), (1784, false), (1779, false)]
theorem step3070 (p : Nat → Bool) (h : Constraints p) : clause p c3070 = true :=
  Snake9.LocalRup.prove_clause [c3003, c1420, c1394, c1386, c1387, c1919, c571] c3070 (by decide) p (sat_cons (step3003 p h) (sat_cons (step1420 p h) (sat_cons (step1394 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step1919 p h) (sat_cons (step571 p h) (sat_nil p))))))))
def c3071 : List Lit := [(1628, true), (101, false)]
theorem step3071 (p : Nat → Bool) (h : Constraints p) : clause p c3071 = true :=
  Snake9.LocalRup.prove_clause [c2741, c3011, c1108] c3071 (by decide) p (sat_cons (step2741 p h) (sat_cons (step3011 p h) (sat_cons (step1108 p h) (sat_nil p))))
def c3072 : List Lit := [(1818, true), (1771, true), (95, true), (122, true), (1807, false)]
theorem step3072 (p : Nat → Bool) (h : Constraints p) : clause p c3072 = true :=
  Snake9.LocalRup.prove_clause [c1783, c1452, c1467, c1479, c1483, c1471, c1445, c2044, c1454, c3042, c1442, c1447, c1438, c1439, c2238, c2494, c1953] c3072 (by decide) p (sat_cons (step1783 p h) (sat_cons (step1452 p h) (sat_cons (step1467 p h) (sat_cons (step1479 p h) (sat_cons (step1483 p h) (sat_cons (step1471 p h) (sat_cons (step1445 p h) (sat_cons (step2044 p h) (sat_cons (step1454 p h) (sat_cons (step3042 p h) (sat_cons (step1442 p h) (sat_cons (step1447 p h) (sat_cons (step1438 p h) (sat_cons (step1439 p h) (sat_cons (step2238 p h) (sat_cons (step2494 p h) (sat_cons (step1953 p h) (sat_nil p))))))))))))))))))
def c3073 : List Lit := [(112, false), (116, true), (115, true), (78, true), (70, false), (88, true), (101, false)]
theorem step3073 (p : Nat → Bool) (h : Constraints p) : clause p c3073 = true :=
  Snake9.LocalRup.prove_clause [c440, c1881, c1882, c1941, c1613, c684, c343, c947, c903, c948, c906, c951, c908, c955, c918, c984, c932, c1984] c3073 (by decide) p (sat_cons (step440 p h) (sat_cons (step1881 p h) (sat_cons (step1882 p h) (sat_cons (step1941 p h) (sat_cons (step1613 p h) (sat_cons (step684 p h) (sat_cons (step343 p h) (sat_cons (step947 p h) (sat_cons (step903 p h) (sat_cons (step948 p h) (sat_cons (step906 p h) (sat_cons (step951 p h) (sat_cons (step908 p h) (sat_cons (step955 p h) (sat_cons (step918 p h) (sat_cons (step984 p h) (sat_cons (step932 p h) (sat_cons (step1984 p h) (sat_nil p)))))))))))))))))))
def c3074 : List Lit := [(1629, false), (1693, true), (1657, false), (1635, false), (1712, true)]
theorem step3074 (p : Nat → Bool) (h : Constraints p) : clause p c3074 = true :=
  Snake9.LocalRup.prove_clause [c2501, c1248, c1222, c1223, c1254, c2553, c2099] c3074 (by decide) p (sat_cons (step2501 p h) (sat_cons (step1248 p h) (sat_cons (step1222 p h) (sat_cons (step1223 p h) (sat_cons (step1254 p h) (sat_cons (step2553 p h) (sat_cons (step2099 p h) (sat_nil p))))))))
def c3075 : List Lit := [(1611, true), (52, false), (1658, true), (1635, false), (58, true)]
theorem step3075 (p : Nat → Bool) (h : Constraints p) : clause p c3075 = true :=
  Snake9.LocalRup.prove_clause [c1104, c2560, c2746, c1855] c3075 (by decide) p (sat_cons (step1104 p h) (sat_cons (step2560 p h) (sat_cons (step2746 p h) (sat_cons (step1855 p h) (sat_nil p)))))
def c3076 : List Lit := [(1611, false), (46, false), (1629, true), (47, false), (1621, false)]
theorem step3076 (p : Nat → Bool) (h : Constraints p) : clause p c3076 = true :=
  Snake9.LocalRup.prove_clause [c1124, c1142, c1112, c1113, c1138, c1108, c1127, c208, c1118] c3076 (by decide) p (sat_cons (step1124 p h) (sat_cons (step1142 p h) (sat_cons (step1112 p h) (sat_cons (step1113 p h) (sat_cons (step1138 p h) (sat_cons (step1108 p h) (sat_cons (step1127 p h) (sat_cons (step208 p h) (sat_cons (step1118 p h) (sat_nil p))))))))))
def c3077 : List Lit := [(89, true), (73, false), (78, true), (70, false)]
theorem step3077 (p : Nat → Bool) (h : Constraints p) : clause p c3077 = true :=
  Snake9.LocalRup.prove_clause [c1881, c1882, c1613] c3077 (by decide) p (sat_cons (step1881 p h) (sat_cons (step1882 p h) (sat_cons (step1613 p h) (sat_nil p))))
def c3078 : List Lit := [(1629, true), (47, false), (32, true), (73, false), (1621, false)]
theorem step3078 (p : Nat → Bool) (h : Constraints p) : clause p c3078 = true :=
  Snake9.LocalRup.prove_clause [c1105, c1112, c1124, c1142, c1115, c1106, c1113, c3076, c1138, c1108, c2442, c1127, c105, c1118] c3078 (by decide) p (sat_cons (step1105 p h) (sat_cons (step1112 p h) (sat_cons (step1124 p h) (sat_cons (step1142 p h) (sat_cons (step1115 p h) (sat_cons (step1106 p h) (sat_cons (step1113 p h) (sat_cons (step3076 p h) (sat_cons (step1138 p h) (sat_cons (step1108 p h) (sat_cons (step2442 p h) (sat_cons (step1127 p h) (sat_cons (step105 p h) (sat_cons (step1118 p h) (sat_nil p)))))))))))))))
def c3079 : List Lit := [(6, false), (52, false), (1603, true), (37, false), (73, false)]
theorem step3079 (p : Nat → Bool) (h : Constraints p) : clause p c3079 = true :=
  Snake9.LocalRup.prove_clause [c2097, c1092, c1808, c1780, c3053, c998, c2270, c2917] c3079 (by decide) p (sat_cons (step2097 p h) (sat_cons (step1092 p h) (sat_cons (step1808 p h) (sat_cons (step1780 p h) (sat_cons (step3053 p h) (sat_cons (step998 p h) (sat_cons (step2270 p h) (sat_cons (step2917 p h) (sat_nil p)))))))))
def c3080 : List Lit := [(1629, true), (32, true), (1621, false), (31, false), (37, false)]
theorem step3080 (p : Nat → Bool) (h : Constraints p) : clause p c3080 = true :=
  Snake9.LocalRup.prove_clause [c1105, c1112, c1124, c1142, c1138, c1115, c1127, c1106, c1118, c105] c3080 (by decide) p (sat_cons (step1105 p h) (sat_cons (step1112 p h) (sat_cons (step1124 p h) (sat_cons (step1142 p h) (sat_cons (step1138 p h) (sat_cons (step1115 p h) (sat_cons (step1127 p h) (sat_cons (step1106 p h) (sat_cons (step1118 p h) (sat_cons (step105 p h) (sat_nil p)))))))))))
def c3081 : List Lit := [(2, true), (1550, false), (1566, true)]
theorem step3081 (p : Nat → Bool) (h : Constraints p) : clause p c3081 = true :=
  Snake9.LocalRup.prove_clause [c1041, c1009, c997, c998, c1006, c2917, c1038] c3081 (by decide) p (sat_cons (step1041 p h) (sat_cons (step1009 p h) (sat_cons (step997 p h) (sat_cons (step998 p h) (sat_cons (step1006 p h) (sat_cons (step2917 p h) (sat_cons (step1038 p h) (sat_nil p))))))))
def c3082 : List Lit := [(1550, false), (1602, true)]
theorem step3082 (p : Nat → Bool) (h : Constraints p) : clause p c3082 = true :=
  Snake9.LocalRup.prove_clause [c1990, c1003, c3081, c1716, c1087, c1037, c1034, c1006, c2917, c996] c3082 (by decide) p (sat_cons (step1990 p h) (sat_cons (step1003 p h) (sat_cons (step3081 p h) (sat_cons (step1716 p h) (sat_cons (step1087 p h) (sat_cons (step1037 p h) (sat_cons (step1034 p h) (sat_cons (step1006 p h) (sat_cons (step2917 p h) (sat_cons (step996 p h) (sat_nil p)))))))))))
def c3083 : List Lit := [(1601, true), (1560, true), (33, false), (4, true), (6, true), (2, false)]
theorem step3083 (p : Nat → Bool) (h : Constraints p) : clause p c3083 = true :=
  Snake9.LocalRup.prove_clause [c996, c1004, c1028, c1716, c1079, c1083, c2037, c1033, c1016, c1005, c1013, c999, c2911, c1, c1793, c2334] c3083 (by decide) p (sat_cons (step996 p h) (sat_cons (step1004 p h) (sat_cons (step1028 p h) (sat_cons (step1716 p h) (sat_cons (step1079 p h) (sat_cons (step1083 p h) (sat_cons (step2037 p h) (sat_cons (step1033 p h) (sat_cons (step1016 p h) (sat_cons (step1005 p h) (sat_cons (step1013 p h) (sat_cons (step999 p h) (sat_cons (step2911 p h) (sat_cons (step1 p h) (sat_cons (step1793 p h) (sat_cons (step2334 p h) (sat_nil p)))))))))))))))))
def c3084 : List Lit := [(37, false), (1565, true), (1547, false), (6, false)]
theorem step3084 (p : Nat → Bool) (h : Constraints p) : clause p c3084 = true :=
  Snake9.LocalRup.prove_clause [c1037, c1006, c1779, c1005, c1034, c1018, c1011, c20, c23, c1001] c3084 (by decide) p (sat_cons (step1037 p h) (sat_cons (step1006 p h) (sat_cons (step1779 p h) (sat_cons (step1005 p h) (sat_cons (step1034 p h) (sat_cons (step1018 p h) (sat_cons (step1011 p h) (sat_cons (step20 p h) (sat_cons (step23 p h) (sat_cons (step1001 p h) (sat_nil p)))))))))))
def c3085 : List Lit := [(1807, false), (95, false), (1817, true), (1829, true), (1774, false), (102, false), (44, false), (1781, false)]
theorem step3085 (p : Nat → Bool) (h : Constraints p) : clause p c3085 = true :=
  Snake9.LocalRup.prove_clause [c1463, c2305, c2032, c1473, c1396, c1517, c1430, c2507, c1409, c1400] c3085 (by decide) p (sat_cons (step1463 p h) (sat_cons (step2305 p h) (sat_cons (step2032 p h) (sat_cons (step1473 p h) (sat_cons (step1396 p h) (sat_cons (step1517 p h) (sat_cons (step1430 p h) (sat_cons (step2507 p h) (sat_cons (step1409 p h) (sat_cons (step1400 p h) (sat_nil p)))))))))))
def c3086 : List Lit := [(1807, true), (1829, true), (1646, true), (57, false), (1776, false), (1781, false), (1652, true), (51, false)]
theorem step3086 (p : Nat → Bool) (h : Constraints p) : clause p c3086 = true :=
  Snake9.LocalRup.prove_clause [c1458, c1460, c2033, c2385, c1455, c1456, c767, c1401, c2271, c1171, c1409, c1867, c1425, c268, c1512, c2304, c1960, c2750, c738] c3086 (by decide) p (sat_cons (step1458 p h) (sat_cons (step1460 p h) (sat_cons (step2033 p h) (sat_cons (step2385 p h) (sat_cons (step1455 p h) (sat_cons (step1456 p h) (sat_cons (step767 p h) (sat_cons (step1401 p h) (sat_cons (step2271 p h) (sat_cons (step1171 p h) (sat_cons (step1409 p h) (sat_cons (step1867 p h) (sat_cons (step1425 p h) (sat_cons (step268 p h) (sat_cons (step1512 p h) (sat_cons (step2304 p h) (sat_cons (step1960 p h) (sat_cons (step2750 p h) (sat_cons (step738 p h) (sat_nil p))))))))))))))))))))
def c3087 : List Lit := [(1829, true), (1646, true), (57, false), (1774, false), (1789, false), (102, false), (44, false), (1781, false), (1652, true), (51, false)]
theorem step3087 (p : Nat → Bool) (h : Constraints p) : clause p c3087 = true :=
  Snake9.LocalRup.prove_clause [c1393, c1506, c3086, c2267, c3085] c3087 (by decide) p (sat_cons (step1393 p h) (sat_cons (step1506 p h) (sat_cons (step3086 p h) (sat_cons (step2267 p h) (sat_cons (step3085 p h) (sat_nil p))))))
def c3088 : List Lit := [(1601, true), (35, false), (50, false)]
theorem step3088 (p : Nat → Bool) (h : Constraints p) : clause p c3088 = true :=
  Snake9.LocalRup.prove_clause [c1989, c1768, c2530, c2917, c2916, c2461, c1034, c1083, c1005, c1716, c997] c3088 (by decide) p (sat_cons (step1989 p h) (sat_cons (step1768 p h) (sat_cons (step2530 p h) (sat_cons (step2917 p h) (sat_cons (step2916 p h) (sat_cons (step2461 p h) (sat_cons (step1034 p h) (sat_cons (step1083 p h) (sat_cons (step1005 p h) (sat_cons (step1716 p h) (sat_cons (step997 p h) (sat_nil p))))))))))))
def c3089 : List Lit := [(1612, false), (1621, false), (1618, true), (1631, true), (38, true), (46, false), (47, false)]
theorem step3089 (p : Nat → Bool) (h : Constraints p) : clause p c3089 = true :=
  Snake9.LocalRup.prove_clause [c1107, c1116, c1117, c1147, c1109, c1127, c208, c1118] c3089 (by decide) p (sat_cons (step1107 p h) (sat_cons (step1116 p h) (sat_cons (step1117 p h) (sat_cons (step1147 p h) (sat_cons (step1109 p h) (sat_cons (step1127 p h) (sat_cons (step208 p h) (sat_cons (step1118 p h) (sat_nil p)))))))))
def c3090 : List Lit := [(1760, true), (6, true), (7, false), (1712, false), (1741, false)]
theorem step3090 (p : Nat → Bool) (h : Constraints p) : clause p c3090 = true :=
  Snake9.LocalRup.prove_clause [c2903, c2004, c1337, c1346, c1373, c1368, c1315, c1347, c1719, c1744, c1340, c1892, c1890, c1333, c1615] c3090 (by decide) p (sat_cons (step2903 p h) (sat_cons (step2004 p h) (sat_cons (step1337 p h) (sat_cons (step1346 p h) (sat_cons (step1373 p h) (sat_cons (step1368 p h) (sat_cons (step1315 p h) (sat_cons (step1347 p h) (sat_cons (step1719 p h) (sat_cons (step1744 p h) (sat_cons (step1340 p h) (sat_cons (step1892 p h) (sat_cons (step1890 p h) (sat_cons (step1333 p h) (sat_cons (step1615 p h) (sat_nil p))))))))))))))))
def c3091 : List Lit := [(1720, false), (1749, false), (1783, false), (1708, false), (1712, false), (1773, false), (1651, true), (1852, true)]
theorem step3091 (p : Nat → Bool) (h : Constraints p) : clause p c3091 = true :=
  Snake9.LocalRup.prove_clause [c2027, c2385, c2399, c1572, c1380, c1315, c1374, c1318, c1568, c1292, c2309, c1284, c2925, c2356] c3091 (by decide) p (sat_cons (step2027 p h) (sat_cons (step2385 p h) (sat_cons (step2399 p h) (sat_cons (step1572 p h) (sat_cons (step1380 p h) (sat_cons (step1315 p h) (sat_cons (step1374 p h) (sat_cons (step1318 p h) (sat_cons (step1568 p h) (sat_cons (step1292 p h) (sat_cons (step2309 p h) (sat_cons (step1284 p h) (sat_cons (step2925 p h) (sat_cons (step2356 p h) (sat_nil p)))))))))))))))
def c3092 : List Lit := [(100, true), (1783, false), (1807, false), (73, false), (1829, true), (1725, false), (1852, true)]
theorem step3092 (p : Nat → Bool) (h : Constraints p) : clause p c3092 = true :=
  Snake9.LocalRup.prove_clause [c2903, c1463, c1390, c2470, c2325, c3003, c1424, c2309, c1401, c1395, c1568, c2289, c1369, c1348] c3092 (by decide) p (sat_cons (step2903 p h) (sat_cons (step1463 p h) (sat_cons (step1390 p h) (sat_cons (step2470 p h) (sat_cons (step2325 p h) (sat_cons (step3003 p h) (sat_cons (step1424 p h) (sat_cons (step2309 p h) (sat_cons (step1401 p h) (sat_cons (step1395 p h) (sat_cons (step1568 p h) (sat_cons (step2289 p h) (sat_cons (step1369 p h) (sat_cons (step1348 p h) (sat_nil p)))))))))))))))
def c3093 : List Lit := [(1773, false), (100, false), (1781, false), (1807, false), (73, false), (1829, true)]
theorem step3093 (p : Nat → Bool) (h : Constraints p) : clause p c3093 = true :=
  Snake9.LocalRup.prove_clause [c2316, c1406, c1463, c1473, c1517, c1395, c1424, c1506, c2267, c2032, c2077, c523, c525, c1438, c1388, c1398, c1429, c1430, c1512, c1409, c2506, c1400, c1943, c501] c3093 (by decide) p (sat_cons (step2316 p h) (sat_cons (step1406 p h) (sat_cons (step1463 p h) (sat_cons (step1473 p h) (sat_cons (step1517 p h) (sat_cons (step1395 p h) (sat_cons (step1424 p h) (sat_cons (step1506 p h) (sat_cons (step2267 p h) (sat_cons (step2032 p h) (sat_cons (step2077 p h) (sat_cons (step523 p h) (sat_cons (step525 p h) (sat_cons (step1438 p h) (sat_cons (step1388 p h) (sat_cons (step1398 p h) (sat_cons (step1429 p h) (sat_cons (step1430 p h) (sat_cons (step1512 p h) (sat_cons (step1409 p h) (sat_cons (step2506 p h) (sat_cons (step1400 p h) (sat_cons (step1943 p h) (sat_cons (step501 p h) (sat_nil p)))))))))))))))))))))))))
def c3094 : List Lit := [(109, false), (1745, true), (95, true), (1784, true), (1772, true), (1773, true), (100, false)]
theorem step3094 (p : Nat → Bool) (h : Constraints p) : clause p c3094 = true :=
  Snake9.LocalRup.prove_clause [c1389, c2030, c652, c3038, c661, c1388, c1921, c1919, c2071, c2281, c2965, c455, c1336, c1333, c1341] c3094 (by decide) p (sat_cons (step1389 p h) (sat_cons (step2030 p h) (sat_cons (step652 p h) (sat_cons (step3038 p h) (sat_cons (step661 p h) (sat_cons (step1388 p h) (sat_cons (step1921 p h) (sat_cons (step1919 p h) (sat_cons (step2071 p h) (sat_cons (step2281 p h) (sat_cons (step2965 p h) (sat_cons (step455 p h) (sat_cons (step1336 p h) (sat_cons (step1333 p h) (sat_cons (step1341 p h) (sat_nil p))))))))))))))))
def c3095 : List Lit := [(98, false), (103, false), (1745, true), (95, true), (100, false)]
theorem step3095 (p : Nat → Bool) (h : Constraints p) : clause p c3095 = true :=
  Snake9.LocalRup.prove_clause [c1921, c2071, c455, c458, c1333, c1336, c1341] c3095 (by decide) p (sat_cons (step1921 p h) (sat_cons (step2071 p h) (sat_cons (step455 p h) (sat_cons (step458 p h) (sat_cons (step1333 p h) (sat_cons (step1336 p h) (sat_cons (step1341 p h) (sat_nil p))))))))
def c3096 : List Lit := [(1739, false), (92, true), (103, false), (105, false), (1750, true), (101, false), (100, false)]
theorem step3096 (p : Nat → Bool) (h : Constraints p) : clause p c3096 = true :=
  Snake9.LocalRup.prove_clause [c2903, c1335, c1348, c1340, c1341, c1351, c1336, c2948, c498, c2991] c3096 (by decide) p (sat_cons (step2903 p h) (sat_cons (step1335 p h) (sat_cons (step1348 p h) (sat_cons (step1340 p h) (sat_cons (step1341 p h) (sat_cons (step1351 p h) (sat_cons (step1336 p h) (sat_cons (step2948 p h) (sat_cons (step498 p h) (sat_cons (step2991 p h) (sat_nil p)))))))))))
def c3097 : List Lit := [(80, false), (1779, true), (101, false), (100, false)]
theorem step3097 (p : Nat → Bool) (h : Constraints p) : clause p c3097 = true :=
  Snake9.LocalRup.prove_clause [c1401, c1400, c618, c2991, c3040, c1630] c3097 (by decide) p (sat_cons (step1401 p h) (sat_cons (step1400 p h) (sat_cons (step618 p h) (sat_cons (step2991 p h) (sat_cons (step3040 p h) (sat_cons (step1630 p h) (sat_nil p)))))))
def c3098 : List Lit := [(94, false), (1742, true), (105, false), (100, false)]
theorem step3098 (p : Nat → Bool) (h : Constraints p) : clause p c3098 = true :=
  Snake9.LocalRup.prove_clause [c495, c498, c1336] c3098 (by decide) p (sat_cons (step495 p h) (sat_cons (step498 p h) (sat_cons (step1336 p h) (sat_nil p))))
def c3099 : List Lit := [(1750, true), (95, true), (1784, true), (1772, true), (1818, true), (1773, true), (100, false), (1807, false)]
theorem step3099 (p : Nat → Bool) (h : Constraints p) : clause p c3099 = true :=
  Snake9.LocalRup.prove_clause [c2903, c1783, c1479, c1471, c1463, c1487, c1389, c1348, c3094, c1403, c1409, c1400, c1401, c636, c3097, c2948, c1351, c1338, c3098, c1929, c1726, c1452, c1454, c1467, c2605, c1483] c3099 (by decide) p (sat_cons (step2903 p h) (sat_cons (step1783 p h) (sat_cons (step1479 p h) (sat_cons (step1471 p h) (sat_cons (step1463 p h) (sat_cons (step1487 p h) (sat_cons (step1389 p h) (sat_cons (step1348 p h) (sat_cons (step3094 p h) (sat_cons (step1403 p h) (sat_cons (step1409 p h) (sat_cons (step1400 p h) (sat_cons (step1401 p h) (sat_cons (step636 p h) (sat_cons (step3097 p h) (sat_cons (step2948 p h) (sat_cons (step1351 p h) (sat_cons (step1338 p h) (sat_cons (step3098 p h) (sat_cons (step1929 p h) (sat_cons (step1726 p h) (sat_cons (step1452 p h) (sat_cons (step1454 p h) (sat_cons (step1467 p h) (sat_cons (step2605 p h) (sat_cons (step1483 p h) (sat_nil p)))))))))))))))))))))))))))
def c3100 : List Lit := [(122, true), (95, true), (1818, true), (100, false), (1807, false)]
theorem step3100 (p : Nat → Bool) (h : Constraints p) : clause p c3100 = true :=
  Snake9.LocalRup.prove_clause [c1783, c1479, c1471, c1452, c1454, c1467, c1483, c2044, c2557] c3100 (by decide) p (sat_cons (step1783 p h) (sat_cons (step1479 p h) (sat_cons (step1471 p h) (sat_cons (step1452 p h) (sat_cons (step1454 p h) (sat_cons (step1467 p h) (sat_cons (step1483 p h) (sat_cons (step2044 p h) (sat_cons (step2557 p h) (sat_nil p))))))))))
def c3101 : List Lit := [(105, false), (122, false), (95, true), (1818, true), (1773, true), (100, false)]
theorem step3101 (p : Nat → Bool) (h : Constraints p) : clause p c3101 = true :=
  Snake9.LocalRup.prove_clause [c1389, c1698, c2087, c2490] c3101 (by decide) p (sat_cons (step1389 p h) (sat_cons (step1698 p h) (sat_cons (step2087 p h) (sat_cons (step2490 p h) (sat_nil p)))))
def c3102 : List Lit := [(1816, true), (101, false), (100, false), (1810, false)]
theorem step3102 (p : Nat → Bool) (h : Constraints p) : clause p c3102 = true :=
  Snake9.LocalRup.prove_clause [c1474, c1477, c1784, c1444, c1728] c3102 (by decide) p (sat_cons (step1474 p h) (sat_cons (step1477 p h) (sat_cons (step1784 p h) (sat_cons (step1444 p h) (sat_cons (step1728 p h) (sat_nil p))))))
def c3103 : List Lit := [(1811, true), (1796, true), (1818, true), (1784, true), (95, false), (101, false), (100, false), (1807, false), (1720, true)]
theorem step3103 (p : Nat → Bool) (h : Constraints p) : clause p c3103 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1487, c2030, c1784, c1467, c1452, c1726, c1956, c733, c1439, c2079, c2498, c1440, c1448, c1400, c1943, c1409, c490, c1403, c2086, c2960] c3103 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1487 p h) (sat_cons (step2030 p h) (sat_cons (step1784 p h) (sat_cons (step1467 p h) (sat_cons (step1452 p h) (sat_cons (step1726 p h) (sat_cons (step1956 p h) (sat_cons (step733 p h) (sat_cons (step1439 p h) (sat_cons (step2079 p h) (sat_cons (step2498 p h) (sat_cons (step1440 p h) (sat_cons (step1448 p h) (sat_cons (step1400 p h) (sat_cons (step1943 p h) (sat_cons (step1409 p h) (sat_cons (step490 p h) (sat_cons (step1403 p h) (sat_cons (step2086 p h) (sat_cons (step2960 p h) (sat_nil p))))))))))))))))))))))
def c3104 : List Lit := [(1818, true), (115, true), (1784, true), (95, false), (101, false), (100, false), (1807, false), (1720, true)]
theorem step3104 (p : Nat → Bool) (h : Constraints p) : clause p c3104 = true :=
  Snake9.LocalRup.prove_clause [c1442, c1444, c1463, c1487, c1479, c1450, c1471, c3103, c1483, c1445, c1447, c1443, c1439, c2557, c1454, c1726, c1956, c733] c3104 (by decide) p (sat_cons (step1442 p h) (sat_cons (step1444 p h) (sat_cons (step1463 p h) (sat_cons (step1487 p h) (sat_cons (step1479 p h) (sat_cons (step1450 p h) (sat_cons (step1471 p h) (sat_cons (step3103 p h) (sat_cons (step1483 p h) (sat_cons (step1445 p h) (sat_cons (step1447 p h) (sat_cons (step1443 p h) (sat_cons (step1439 p h) (sat_cons (step2557 p h) (sat_cons (step1454 p h) (sat_cons (step1726 p h) (sat_cons (step1956 p h) (sat_cons (step733 p h) (sat_nil p)))))))))))))))))))
def c3105 : List Lit := [(102, true), (108, true), (107, true), (1742, true), (1784, true), (101, false), (100, false)]
theorem step3105 (p : Nat → Bool) (h : Constraints p) : clause p c3105 = true :=
  Snake9.LocalRup.prove_clause [c2943, c1403, c1409, c1400, c1401, c3098, c1929, c636] c3105 (by decide) p (sat_cons (step2943 p h) (sat_cons (step1403 p h) (sat_cons (step1409 p h) (sat_cons (step1400 p h) (sat_cons (step1401 p h) (sat_cons (step3098 p h) (sat_cons (step1929 p h) (sat_cons (step636 p h) (sat_nil p)))))))))
def c3106 : List Lit := [(1779, true), (104, true), (80, true), (89, true), (1750, true), (1739, false), (101, false), (100, false)]
theorem step3106 (p : Nat → Bool) (h : Constraints p) : clause p c3106 = true :=
  Snake9.LocalRup.prove_clause [c2903, c1348, c1341, c1400, c1401, c3096, c3098, c2948, c1908, c1351, c457, c1340, c1334] c3106 (by decide) p (sat_cons (step2903 p h) (sat_cons (step1348 p h) (sat_cons (step1341 p h) (sat_cons (step1400 p h) (sat_cons (step1401 p h) (sat_cons (step3096 p h) (sat_cons (step3098 p h) (sat_cons (step2948 p h) (sat_cons (step1908 p h) (sat_cons (step1351 p h) (sat_cons (step457 p h) (sat_cons (step1340 p h) (sat_cons (step1334 p h) (sat_nil p))))))))))))))
def c3107 : List Lit := [(109, false), (102, false), (1759, true), (1739, false), (1780, true), (101, false), (100, false)]
theorem step3107 (p : Nat → Bool) (h : Constraints p) : clause p c3107 = true :=
  Snake9.LocalRup.prove_clause [c2010, c1339, c624, c619, c1402, c2948, c1351, c1350, c1340, c1362, c1334, c1335, c2003, c457, c492, c633, c1286, c1908, c1283, c438] c3107 (by decide) p (sat_cons (step2010 p h) (sat_cons (step1339 p h) (sat_cons (step624 p h) (sat_cons (step619 p h) (sat_cons (step1402 p h) (sat_cons (step2948 p h) (sat_cons (step1351 p h) (sat_cons (step1350 p h) (sat_cons (step1340 p h) (sat_cons (step1362 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step2003 p h) (sat_cons (step457 p h) (sat_cons (step492 p h) (sat_cons (step633 p h) (sat_cons (step1286 p h) (sat_cons (step1908 p h) (sat_cons (step1283 p h) (sat_cons (step438 p h) (sat_nil p)))))))))))))))))))))
def c3108 : List Lit := [(1779, true), (1759, true), (1739, false), (101, false), (100, false)]
theorem step3108 (p : Nat → Bool) (h : Constraints p) : clause p c3108 = true :=
  Snake9.LocalRup.prove_clause [c2010, c1339, c1400, c1401, c3097, c636, c3096, c2948, c3106, c1350, c438, c1362, c1283, c2003, c1286] c3108 (by decide) p (sat_cons (step2010 p h) (sat_cons (step1339 p h) (sat_cons (step1400 p h) (sat_cons (step1401 p h) (sat_cons (step3097 p h) (sat_cons (step636 p h) (sat_cons (step3096 p h) (sat_cons (step2948 p h) (sat_cons (step3106 p h) (sat_cons (step1350 p h) (sat_cons (step438 p h) (sat_cons (step1362 p h) (sat_cons (step1283 p h) (sat_cons (step2003 p h) (sat_cons (step1286 p h) (sat_nil p))))))))))))))))
def c3109 : List Lit := [(1772, false), (95, false), (1790, true), (101, false), (100, false), (1807, false), (73, false), (1720, true), (1852, true)]
theorem step3109 (p : Nat → Bool) (h : Constraints p) : clause p c3109 = true :=
  Snake9.LocalRup.prove_clause [c2903, c1397, c2457, c1425, c1411, c2030, c526, c519, c1333, c1339, c3104, c1507, c1556, c2010, c1348, c1341, c3108, c1409, c1403, c652, c3107, c3105, c645, c1738, c2202, c1326, c2003, c1362, c1347, c1350, c1340, c1329, c1331, c1334, c1335, c1327, c1322, c2941, c1402, c457, c633, c391, c1925] c3109 (by decide) p (sat_cons (step2903 p h) (sat_cons (step1397 p h) (sat_cons (step2457 p h) (sat_cons (step1425 p h) (sat_cons (step1411 p h) (sat_cons (step2030 p h) (sat_cons (step526 p h) (sat_cons (step519 p h) (sat_cons (step1333 p h) (sat_cons (step1339 p h) (sat_cons (step3104 p h) (sat_cons (step1507 p h) (sat_cons (step1556 p h) (sat_cons (step2010 p h) (sat_cons (step1348 p h) (sat_cons (step1341 p h) (sat_cons (step3108 p h) (sat_cons (step1409 p h) (sat_cons (step1403 p h) (sat_cons (step652 p h) (sat_cons (step3107 p h) (sat_cons (step3105 p h) (sat_cons (step645 p h) (sat_cons (step1738 p h) (sat_cons (step2202 p h) (sat_cons (step1326 p h) (sat_cons (step2003 p h) (sat_cons (step1362 p h) (sat_cons (step1347 p h) (sat_cons (step1350 p h) (sat_cons (step1340 p h) (sat_cons (step1329 p h) (sat_cons (step1331 p h) (sat_cons (step1334 p h) (sat_cons (step1335 p h) (sat_cons (step1327 p h) (sat_cons (step1322 p h) (sat_cons (step2941 p h) (sat_cons (step1402 p h) (sat_cons (step457 p h) (sat_cons (step633 p h) (sat_cons (step391 p h) (sat_cons (step1925 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c3110 : List Lit := [(97, true), (100, false), (74, true), (1720, true)]
theorem step3110 (p : Nat → Bool) (h : Constraints p) : clause p c3110 = true :=
  Snake9.LocalRup.prove_clause [c1301, c1894, c2086, c1299, c378, c1896] c3110 (by decide) p (sat_cons (step1301 p h) (sat_cons (step1894 p h) (sat_cons (step2086 p h) (sat_cons (step1299 p h) (sat_cons (step378 p h) (sat_cons (step1896 p h) (sat_nil p)))))))
def c3111 : List Lit := [(75, true), (100, false), (74, true), (1720, true)]
theorem step3111 (p : Nat → Bool) (h : Constraints p) : clause p c3111 = true :=
  Snake9.LocalRup.prove_clause [c1301, c1298, c1299, c1303, c1896, c1295, c378] c3111 (by decide) p (sat_cons (step1301 p h) (sat_cons (step1298 p h) (sat_cons (step1299 p h) (sat_cons (step1303 p h) (sat_cons (step1896 p h) (sat_cons (step1295 p h) (sat_cons (step378 p h) (sat_nil p))))))))
def c3112 : List Lit := [(100, false), (74, true), (1720, true)]
theorem step3112 (p : Nat → Bool) (h : Constraints p) : clause p c3112 = true :=
  Snake9.LocalRup.prove_clause [c3110, c3111, c1619, c1895] c3112 (by decide) p (sat_cons (step3110 p h) (sat_cons (step3111 p h) (sat_cons (step1619 p h) (sat_cons (step1895 p h) (sat_nil p)))))
def c3113 : List Lit := [(77, true), (74, true), (1718, true)]
theorem step3113 (p : Nat → Bool) (h : Constraints p) : clause p c3113 = true :=
  Snake9.LocalRup.prove_clause [c1896, c1895, c1299] c3113 (by decide) p (sat_cons (step1896 p h) (sat_cons (step1895 p h) (sat_cons (step1299 p h) (sat_nil p))))
def c3114 : List Lit := [(122, true), (112, true), (94, true), (1818, true), (1807, false)]
theorem step3114 (p : Nat → Bool) (h : Constraints p) : clause p c3114 = true :=
  Snake9.LocalRup.prove_clause [c1439, c1446, c1479, c1471, c1452, c1454, c1467, c1483, c1449, c1447, c1440, c1441, c730, c1943] c3114 (by decide) p (sat_cons (step1439 p h) (sat_cons (step1446 p h) (sat_cons (step1479 p h) (sat_cons (step1471 p h) (sat_cons (step1452 p h) (sat_cons (step1454 p h) (sat_cons (step1467 p h) (sat_cons (step1483 p h) (sat_cons (step1449 p h) (sat_cons (step1447 p h) (sat_cons (step1440 p h) (sat_cons (step1441 p h) (sat_cons (step730 p h) (sat_cons (step1943 p h) (sat_nil p)))))))))))))))
def c3115 : List Lit := [(1724, false), (80, false), (1759, true), (92, false), (104, true), (1790, false), (103, false), (101, false), (1739, false), (72, false), (1807, false), (1852, true)]
theorem step3115 (p : Nat → Bool) (h : Constraints p) : clause p c3115 = true :=
  Snake9.LocalRup.prove_clause [c2903, c1339, c1346, c1361, c1362, c1550, c1347, c1514, c1340, c1334, c457, c482, c1908, c444, c3114, c620, c1898, c1956, c593] c3115 (by decide) p (sat_cons (step2903 p h) (sat_cons (step1339 p h) (sat_cons (step1346 p h) (sat_cons (step1361 p h) (sat_cons (step1362 p h) (sat_cons (step1550 p h) (sat_cons (step1347 p h) (sat_cons (step1514 p h) (sat_cons (step1340 p h) (sat_cons (step1334 p h) (sat_cons (step457 p h) (sat_cons (step482 p h) (sat_cons (step1908 p h) (sat_cons (step444 p h) (sat_cons (step3114 p h) (sat_cons (step620 p h) (sat_cons (step1898 p h) (sat_cons (step1956 p h) (sat_cons (step593 p h) (sat_nil p))))))))))))))))))))
def c3116 : List Lit := [(1830, true), (1779, false), (96, true), (109, true), (1807, false), (1773, false), (73, false)]
theorem step3116 (p : Nat → Bool) (h : Constraints p) : clause p c3116 = true :=
  Snake9.LocalRup.prove_clause [c1387, c1395, c1403, c1409, c1425, c1463, c1473, c1522, c1513, c2267, c2032, c525, c526, c1388, c1405, c1398, c1410, c1431] c3116 (by decide) p (sat_cons (step1387 p h) (sat_cons (step1395 p h) (sat_cons (step1403 p h) (sat_cons (step1409 p h) (sat_cons (step1425 p h) (sat_cons (step1463 p h) (sat_cons (step1473 p h) (sat_cons (step1522 p h) (sat_cons (step1513 p h) (sat_cons (step2267 p h) (sat_cons (step2032 p h) (sat_cons (step525 p h) (sat_cons (step526 p h) (sat_cons (step1388 p h) (sat_cons (step1405 p h) (sat_cons (step1398 p h) (sat_cons (step1410 p h) (sat_cons (step1431 p h) (sat_nil p)))))))))))))))))))
end B112E036
