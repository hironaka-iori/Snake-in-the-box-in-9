import B112E097Part0006
namespace B112E097
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2043 : List Lit := [(906, true), (86, false), (70, false)]
theorem step2043 (p : Nat → Bool) (h : Constraints p) : clause p c2043 = true :=
  Snake9.LocalRup.prove_clause [c1014, c2000, c1806, c995, c993, c1842, c498, c1862, c137, c138, c1001, c1004, c1009] c2043 (by decide) p (sat_cons (step1014 p h) (sat_cons (step2000 p h) (sat_cons (step1806 p h) (sat_cons (step995 p h) (sat_cons (step993 p h) (sat_cons (step1842 p h) (sat_cons (step498 p h) (sat_cons (step1862 p h) (sat_cons (step137 p h) (sat_cons (step138 p h) (sat_cons (step1001 p h) (sat_cons (step1004 p h) (sat_cons (step1009 p h) (sat_nil p))))))))))))))
def c2044 : List Lit := [(925, true), (57, true), (52, true), (50, false), (86, false)]
theorem step2044 (p : Nat → Bool) (h : Constraints p) : clause p c2044 = true :=
  Snake9.LocalRup.prove_clause [c1043, c1046, c1044, c1048, c1039, c1595, c163, c1891] c2044 (by decide) p (sat_cons (step1043 p h) (sat_cons (step1046 p h) (sat_cons (step1044 p h) (sat_cons (step1048 p h) (sat_cons (step1039 p h) (sat_cons (step1595 p h) (sat_cons (step163 p h) (sat_cons (step1891 p h) (sat_nil p)))))))))
def c2045 : List Lit := [(52, true), (50, false), (930, true), (914, false)]
theorem step2045 (p : Nat → Bool) (h : Constraints p) : clause p c2045 = true :=
  Snake9.LocalRup.prove_clause [c1673, c1709, c1062, c1025, c1034] c2045 (by decide) p (sat_cons (step1673 p h) (sat_cons (step1709 p h) (sat_cons (step1062 p h) (sat_cons (step1025 p h) (sat_cons (step1034 p h) (sat_nil p))))))
def c2046 : List Lit := [(52, false), (921, true), (70, false), (86, false)]
theorem step2046 (p : Nat → Bool) (h : Constraints p) : clause p c2046 = true :=
  Snake9.LocalRup.prove_clause [c206, c205, c1041] c2046 (by decide) p (sat_cons (step206 p h) (sat_cons (step205 p h) (sat_cons (step1041 p h) (sat_nil p))))
def c2047 : List Lit := [(34, false), (88, true), (52, true), (70, false), (86, false)]
theorem step2047 (p : Nat → Bool) (h : Constraints p) : clause p c2047 = true :=
  Snake9.LocalRup.prove_clause [c1842, c498, c1932] c2047 (by decide) p (sat_cons (step1842 p h) (sat_cons (step498 p h) (sat_cons (step1932 p h) (sat_nil p))))
def c2048 : List Lit := [(114, true), (1060, true), (72, false), (107, true), (88, true)]
theorem step2048 (p : Nat → Bool) (h : Constraints p) : clause p c2048 = true :=
  Snake9.LocalRup.prove_clause [c1314, c1310, c1312, c1316, c1307, c584, c1964] c2048 (by decide) p (sat_cons (step1314 p h) (sat_cons (step1310 p h) (sat_cons (step1312 p h) (sat_cons (step1316 p h) (sat_cons (step1307 p h) (sat_cons (step584 p h) (sat_cons (step1964 p h) (sat_nil p))))))))
def c2049 : List Lit := [(1060, false), (88, true), (1083, true), (1043, false)]
theorem step2049 (p : Nat → Bool) (h : Constraints p) : clause p c2049 = true :=
  Snake9.LocalRup.prove_clause [c1287, c1362, c2021, c1343, c1369, c1328, c1292, c1265, c1267, c1262, c1263, c1259, c435, c1951, c428, c1324, c1326, c1330, c1321, c1322, c627, c681, c1974] c2049 (by decide) p (sat_cons (step1287 p h) (sat_cons (step1362 p h) (sat_cons (step2021 p h) (sat_cons (step1343 p h) (sat_cons (step1369 p h) (sat_cons (step1328 p h) (sat_cons (step1292 p h) (sat_cons (step1265 p h) (sat_cons (step1267 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step1259 p h) (sat_cons (step435 p h) (sat_cons (step1951 p h) (sat_cons (step428 p h) (sat_cons (step1324 p h) (sat_cons (step1326 p h) (sat_cons (step1330 p h) (sat_cons (step1321 p h) (sat_cons (step1322 p h) (sat_cons (step627 p h) (sat_cons (step681 p h) (sat_cons (step1974 p h) (sat_nil p))))))))))))))))))))))))
def c2050 : List Lit := [(1063, true), (123, true), (114, false)]
theorem step2050 (p : Nat → Bool) (h : Constraints p) : clause p c2050 = true :=
  Snake9.LocalRup.prove_clause [c1321, c1322, c621, c1975] c2050 (by decide) p (sat_cons (step1321 p h) (sat_cons (step1322 p h) (sat_cons (step621 p h) (sat_cons (step1975 p h) (sat_nil p)))))
def c2051 : List Lit := [(102, false), (108, false), (1040, true), (114, false)]
theorem step2051 (p : Nat → Bool) (h : Constraints p) : clause p c2051 = true :=
  Snake9.LocalRup.prove_clause [c474, c475, c1275] c2051 (by decide) p (sat_cons (step474 p h) (sat_cons (step475 p h) (sat_cons (step1275 p h) (sat_nil p))))
def c2052 : List Lit := [(81, false), (72, false), (113, false), (123, true)]
theorem step2052 (p : Nat → Bool) (h : Constraints p) : clause p c2052 = true :=
  Snake9.LocalRup.prove_clause [c1923, c305] c2052 (by decide) p (sat_cons (step1923 p h) (sat_cons (step305 p h) (sat_nil p)))
def c2053 : List Lit := [(981, false), (1006, false), (1022, true), (69, false), (995, false)]
theorem step2053 (p : Nat → Bool) (h : Constraints p) : clause p c2053 = true :=
  Snake9.LocalRup.prove_clause [c1175, c1208, c1241, c1154, c1158, c1234, c1751, c1213, c1169, c1178] c2053 (by decide) p (sat_cons (step1175 p h) (sat_cons (step1208 p h) (sat_cons (step1241 p h) (sat_cons (step1154 p h) (sat_cons (step1158 p h) (sat_cons (step1234 p h) (sat_cons (step1751 p h) (sat_cons (step1213 p h) (sat_cons (step1169 p h) (sat_cons (step1178 p h) (sat_nil p)))))))))))
def c2054 : List Lit := [(106, false), (113, false), (72, false), (69, false)]
theorem step2054 (p : Nat → Bool) (h : Constraints p) : clause p c2054 = true :=
  Snake9.LocalRup.prove_clause [c303, c282, c581, c1910] c2054 (by decide) p (sat_cons (step303 p h) (sat_cons (step282 p h) (sat_cons (step581 p h) (sat_cons (step1910 p h) (sat_nil p)))))
def c2055 : List Lit := [(920, true), (56, false), (72, false)]
theorem step2055 (p : Nat → Bool) (h : Constraints p) : clause p c2055 = true :=
  Snake9.LocalRup.prove_clause [c1039, c1040, c224] c2055 (by decide) p (sat_cons (step1039 p h) (sat_cons (step1040 p h) (sat_cons (step224 p h) (sat_nil p))))
def c2056 : List Lit := [(53, false), (973, true), (70, false), (52, true), (57, false)]
theorem step2056 (p : Nat → Bool) (h : Constraints p) : clause p c2056 = true :=
  Snake9.LocalRup.prove_clause [c1884, c1885, c294, c262, c1135] c2056 (by decide) p (sat_cons (step1884 p h) (sat_cons (step1885 p h) (sat_cons (step294 p h) (sat_cons (step262 p h) (sat_cons (step1135 p h) (sat_nil p))))))
def c2057 : List Lit := [(92, true), (61, false), (62, true), (57, false)]
theorem step2057 (p : Nat → Bool) (h : Constraints p) : clause p c2057 = true :=
  Snake9.LocalRup.prove_clause [c1894, c1893, c1566] c2057 (by decide) p (sat_cons (step1894 p h) (sat_cons (step1893 p h) (sat_cons (step1566 p h) (sat_nil p))))
def c2058 : List Lit := [(88, false), (883, true), (855, false), (273, true), (52, true)]
theorem step2058 (p : Nat → Bool) (h : Constraints p) : clause p c2058 = true :=
  Snake9.LocalRup.prove_clause [c764, c747, c743, c742, c1816, c762, c759, c756, c755, c1845, c1846, c1830, c1823, c943, c33, c924, c948, c932, c1638, c986, c976, c974, c950, c957, c944, c955, c1691] c2058 (by decide) p (sat_cons (step764 p h) (sat_cons (step747 p h) (sat_cons (step743 p h) (sat_cons (step742 p h) (sat_cons (step1816 p h) (sat_cons (step762 p h) (sat_cons (step759 p h) (sat_cons (step756 p h) (sat_cons (step755 p h) (sat_cons (step1845 p h) (sat_cons (step1846 p h) (sat_cons (step1830 p h) (sat_cons (step1823 p h) (sat_cons (step943 p h) (sat_cons (step33 p h) (sat_cons (step924 p h) (sat_cons (step948 p h) (sat_cons (step932 p h) (sat_cons (step1638 p h) (sat_cons (step986 p h) (sat_cons (step976 p h) (sat_cons (step974 p h) (sat_cons (step950 p h) (sat_cons (step957 p h) (sat_cons (step944 p h) (sat_cons (step955 p h) (sat_cons (step1691 p h) (sat_nil p))))))))))))))))))))))))))))
def c2059 : List Lit := [(7, false), (34, false), (2, true), (52, true)]
theorem step2059 (p : Nat → Bool) (h : Constraints p) : clause p c2059 = true :=
  Snake9.LocalRup.prove_clause [c1835, c1823] c2059 (by decide) p (sat_cons (step1835 p h) (sat_cons (step1823 p h) (sat_nil p)))
def c2060 : List Lit := [(1057, false), (1035, false), (1082, true), (70, false), (34, false)]
theorem step2060 (p : Nat → Bool) (h : Constraints p) : clause p c2060 = true :=
  Snake9.LocalRup.prove_clause [c1291, c1361, c2021, c2025, c1293, c1284, c1313, c1316, c2020, c1307, c1308, c1368, c502, c1657, c1292, c1277, c1279] c2060 (by decide) p (sat_cons (step1291 p h) (sat_cons (step1361 p h) (sat_cons (step2021 p h) (sat_cons (step2025 p h) (sat_cons (step1293 p h) (sat_cons (step1284 p h) (sat_cons (step1313 p h) (sat_cons (step1316 p h) (sat_cons (step2020 p h) (sat_cons (step1307 p h) (sat_cons (step1308 p h) (sat_cons (step1368 p h) (sat_cons (step502 p h) (sat_cons (step1657 p h) (sat_cons (step1292 p h) (sat_cons (step1277 p h) (sat_cons (step1279 p h) (sat_nil p))))))))))))))))))
def c2061 : List Lit := [(109, false), (107, true), (111, false), (114, false), (1044, true)]
theorem step2061 (p : Nat → Bool) (h : Constraints p) : clause p c2061 = true :=
  Snake9.LocalRup.prove_clause [c1284, c1280, c1659, c1657, c2051, c1278] c2061 (by decide) p (sat_cons (step1284 p h) (sat_cons (step1280 p h) (sat_cons (step1659 p h) (sat_cons (step1657 p h) (sat_cons (step2051 p h) (sat_cons (step1278 p h) (sat_nil p)))))))
def c2062 : List Lit := [(1035, false), (1082, true), (70, false), (34, false)]
theorem step2062 (p : Nat → Bool) (h : Constraints p) : clause p c2062 = true :=
  Snake9.LocalRup.prove_clause [c2025, c1291, c1293, c1361, c2060, c1310, c1311, c1797, c1674, c502, c2061, c1308, c1315, c2020, c1339, c1368, c1330, c1292, c1324, c1325, c1279, c636, c686, c1276, c1979, c553] c2062 (by decide) p (sat_cons (step2025 p h) (sat_cons (step1291 p h) (sat_cons (step1293 p h) (sat_cons (step1361 p h) (sat_cons (step2060 p h) (sat_cons (step1310 p h) (sat_cons (step1311 p h) (sat_cons (step1797 p h) (sat_cons (step1674 p h) (sat_cons (step502 p h) (sat_cons (step2061 p h) (sat_cons (step1308 p h) (sat_cons (step1315 p h) (sat_cons (step2020 p h) (sat_cons (step1339 p h) (sat_cons (step1368 p h) (sat_cons (step1330 p h) (sat_cons (step1292 p h) (sat_cons (step1324 p h) (sat_cons (step1325 p h) (sat_cons (step1279 p h) (sat_cons (step636 p h) (sat_cons (step686 p h) (sat_cons (step1276 p h) (sat_cons (step1979 p h) (sat_cons (step553 p h) (sat_nil p)))))))))))))))))))))))))))
def c2063 : List Lit := [(1055, false), (1073, true), (1065, false)]
theorem step2063 (p : Nat → Bool) (h : Constraints p) : clause p c2063 = true :=
  Snake9.LocalRup.prove_clause [c2021, c1315, c1316, c1339, c1797, c1330] c2063 (by decide) p (sat_cons (step2021 p h) (sat_cons (step1315 p h) (sat_cons (step1316 p h) (sat_cons (step1339 p h) (sat_cons (step1797 p h) (sat_cons (step1330 p h) (sat_nil p)))))))
def c2064 : List Lit := [(111, false), (107, true), (114, false), (99, true), (97, false), (100, false), (1082, true)]
theorem step2064 (p : Nat → Bool) (h : Constraints p) : clause p c2064 = true :=
  Snake9.LocalRup.prove_clause [c1604, c1966, c1964, c1951, c1588, c428, c1277, c1324, c1279, c1287, c1361, c2063, c1308, c593, c2061, c1311, c1288, c1313, c1368, c2020] c2064 (by decide) p (sat_cons (step1604 p h) (sat_cons (step1966 p h) (sat_cons (step1964 p h) (sat_cons (step1951 p h) (sat_cons (step1588 p h) (sat_cons (step428 p h) (sat_cons (step1277 p h) (sat_cons (step1324 p h) (sat_cons (step1279 p h) (sat_cons (step1287 p h) (sat_cons (step1361 p h) (sat_cons (step2063 p h) (sat_cons (step1308 p h) (sat_cons (step593 p h) (sat_cons (step2061 p h) (sat_cons (step1311 p h) (sat_cons (step1288 p h) (sat_cons (step1313 p h) (sat_cons (step1368 p h) (sat_cons (step2020 p h) (sat_nil p)))))))))))))))))))))
def c2065 : List Lit := [(1065, true), (1035, true)]
theorem step2065 (p : Nat → Bool) (h : Constraints p) : clause p c2065 = true :=
  Snake9.LocalRup.prove_clause [c1265, c1262, c1263, c1267, c1259, c435, c1324, c1325, c428, c683, c1954] c2065 (by decide) p (sat_cons (step1265 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step1267 p h) (sat_cons (step1259 p h) (sat_cons (step435 p h) (sat_cons (step1324 p h) (sat_cons (step1325 p h) (sat_cons (step428 p h) (sat_cons (step683 p h) (sat_cons (step1954 p h) (sat_nil p))))))))))))
def c2066 : List Lit := [(111, true), (114, false), (1065, false), (1082, true), (70, false)]
theorem step2066 (p : Nat → Bool) (h : Constraints p) : clause p c2066 = true :=
  Snake9.LocalRup.prove_clause [c1356, c1307, c1315, c2020, c1368, c1288, c1284, c1753, c2063, c1330, c1361, c1343, c1287, c1318, c1279, c1281, c1276, c1277, c1273, c1274, c2051, c1692, c1309] c2066 (by decide) p (sat_cons (step1356 p h) (sat_cons (step1307 p h) (sat_cons (step1315 p h) (sat_cons (step2020 p h) (sat_cons (step1368 p h) (sat_cons (step1288 p h) (sat_cons (step1284 p h) (sat_cons (step1753 p h) (sat_cons (step2063 p h) (sat_cons (step1330 p h) (sat_cons (step1361 p h) (sat_cons (step1343 p h) (sat_cons (step1287 p h) (sat_cons (step1318 p h) (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step2051 p h) (sat_cons (step1692 p h) (sat_cons (step1309 p h) (sat_nil p))))))))))))))))))))))))
def c2067 : List Lit := [(114, false), (1082, true), (70, false), (34, false)]
theorem step2067 (p : Nat → Bool) (h : Constraints p) : clause p c2067 = true :=
  Snake9.LocalRup.prove_clause [c2062, c2065, c1265, c1262, c1263, c1267, c1259, c435, c2066, c502, c2064] c2067 (by decide) p (sat_cons (step2062 p h) (sat_cons (step2065 p h) (sat_cons (step1265 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step1267 p h) (sat_cons (step1259 p h) (sat_cons (step435 p h) (sat_cons (step2066 p h) (sat_cons (step502 p h) (sat_cons (step2064 p h) (sat_nil p))))))))))))
def c2068 : List Lit := [(111, false), (107, true), (1044, true), (97, false)]
theorem step2068 (p : Nat → Bool) (h : Constraints p) : clause p c2068 = true :=
  Snake9.LocalRup.prove_clause [c1604, c1966, c1964, c1588, c1277, c1282, c1273, c1274, c480] c2068 (by decide) p (sat_cons (step1604 p h) (sat_cons (step1966 p h) (sat_cons (step1964 p h) (sat_cons (step1588 p h) (sat_cons (step1277 p h) (sat_cons (step1282 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step480 p h) (sat_nil p))))))))))
def c2069 : List Lit := [(1055, false), (114, true), (1065, false), (100, false), (1082, true)]
theorem step2069 (p : Nat → Bool) (h : Constraints p) : clause p c2069 = true :=
  Snake9.LocalRup.prove_clause [c1310, c1356, c2022, c1317, c2063, c1316, c1312, c1361, c1343, c1287, c1328, c1330, c1279, c1812, c1321, c1322, c1277, c1974, c628] c2069 (by decide) p (sat_cons (step1310 p h) (sat_cons (step1356 p h) (sat_cons (step2022 p h) (sat_cons (step1317 p h) (sat_cons (step2063 p h) (sat_cons (step1316 p h) (sat_cons (step1312 p h) (sat_cons (step1361 p h) (sat_cons (step1343 p h) (sat_cons (step1287 p h) (sat_cons (step1328 p h) (sat_cons (step1330 p h) (sat_cons (step1279 p h) (sat_cons (step1812 p h) (sat_cons (step1321 p h) (sat_cons (step1322 p h) (sat_cons (step1277 p h) (sat_cons (step1974 p h) (sat_cons (step628 p h) (sat_nil p))))))))))))))))))))
def c2070 : List Lit := [(1082, true), (70, false), (34, false)]
theorem step2070 (p : Nat → Bool) (h : Constraints p) : clause p c2070 = true :=
  Snake9.LocalRup.prove_clause [c2062, c1265, c1262, c1263, c2065, c2067, c1310, c1313, c2020, c1368, c1288, c2069, c1307, c502, c2068] c2070 (by decide) p (sat_cons (step2062 p h) (sat_cons (step1265 p h) (sat_cons (step1262 p h) (sat_cons (step1263 p h) (sat_cons (step2065 p h) (sat_cons (step2067 p h) (sat_cons (step1310 p h) (sat_cons (step1313 p h) (sat_cons (step2020 p h) (sat_cons (step1368 p h) (sat_cons (step1288 p h) (sat_cons (step2069 p h) (sat_cons (step1307 p h) (sat_cons (step502 p h) (sat_cons (step2068 p h) (sat_nil p))))))))))))))))
def c2071 : List Lit := [(974, false), (1020, true), (994, false), (77, true), (1004, false), (72, true), (70, false)]
theorem step2071 (p : Nat → Bool) (h : Constraints p) : clause p c2071 = true :=
  Snake9.LocalRup.prove_clause [c1174, c1201, c1245, c1145, c1147, c1158, c1159, c1239, c1148, c1206, c1146, c1177, c1914, c1168, c319] c2071 (by decide) p (sat_cons (step1174 p h) (sat_cons (step1201 p h) (sat_cons (step1245 p h) (sat_cons (step1145 p h) (sat_cons (step1147 p h) (sat_cons (step1158 p h) (sat_cons (step1159 p h) (sat_cons (step1239 p h) (sat_cons (step1148 p h) (sat_cons (step1206 p h) (sat_cons (step1146 p h) (sat_cons (step1177 p h) (sat_cons (step1914 p h) (sat_cons (step1168 p h) (sat_cons (step319 p h) (sat_nil p))))))))))))))))
def c2072 : List Lit := [(87, true), (82, false), (1006, true), (89, true), (94, false), (97, false)]
theorem step2072 (p : Nat → Bool) (h : Constraints p) : clause p c2072 = true :=
  Snake9.LocalRup.prove_clause [c1182, c1813, c1192, c400, c1187] c2072 (by decide) p (sat_cons (step1182 p h) (sat_cons (step1813 p h) (sat_cons (step1192 p h) (sat_cons (step400 p h) (sat_cons (step1187 p h) (sat_nil p))))))
def c2073 : List Lit := [(86, false), (930, true), (88, true), (70, false), (34, false)]
theorem step2073 (p : Nat → Bool) (h : Constraints p) : clause p c2073 = true :=
  Snake9.LocalRup.prove_clause [c2047, c2046, c196, c1050, c1025, c1058, c1033] c2073 (by decide) p (sat_cons (step2047 p h) (sat_cons (step2046 p h) (sat_cons (step196 p h) (sat_cons (step1050 p h) (sat_cons (step1025 p h) (sat_cons (step1058 p h) (sat_cons (step1033 p h) (sat_nil p))))))))
def c2074 : List Lit := [(870, false), (922, false), (959, true), (906, false)]
theorem step2074 (p : Nat → Bool) (h : Constraints p) : clause p c2074 = true :=
  Snake9.LocalRup.prove_clause [c2008, c1120, c1643, c985, c1114, c1638, c1081, c932, c1807, c924] c2074 (by decide) p (sat_cons (step2008 p h) (sat_cons (step1120 p h) (sat_cons (step1643 p h) (sat_cons (step985 p h) (sat_cons (step1114 p h) (sat_cons (step1638 p h) (sat_cons (step1081 p h) (sat_cons (step932 p h) (sat_cons (step1807 p h) (sat_cons (step924 p h) (sat_nil p)))))))))))
def c2075 : List Lit := [(1039, true), (104, false), (111, false)]
theorem step2075 (p : Nat → Bool) (h : Constraints p) : clause p c2075 = true :=
  Snake9.LocalRup.prove_clause [c1273, c1274, c480] c2075 (by decide) p (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step480 p h) (sat_nil p))))
def c2076 : List Lit := [(907, true), (86, false), (36, true), (107, true)]
theorem step2076 (p : Nat → Bool) (h : Constraints p) : clause p c2076 = true :=
  Snake9.LocalRup.prove_clause [c992, c995, c2001, c1017, c996, c1806, c994, c1842, c1862, c137, c138, c1001, c1004, c1009] c2076 (by decide) p (sat_cons (step992 p h) (sat_cons (step995 p h) (sat_cons (step2001 p h) (sat_cons (step1017 p h) (sat_cons (step996 p h) (sat_cons (step1806 p h) (sat_cons (step994 p h) (sat_cons (step1842 p h) (sat_cons (step1862 p h) (sat_cons (step137 p h) (sat_cons (step138 p h) (sat_cons (step1001 p h) (sat_cons (step1004 p h) (sat_cons (step1009 p h) (sat_nil p)))))))))))))))
def c2077 : List Lit := [(1020, true), (1005, false), (979, false), (994, false)]
theorem step2077 (p : Nat → Bool) (h : Constraints p) : clause p c2077 = true :=
  Snake9.LocalRup.prove_clause [c1174, c1202, c1147, c1154, c1232, c1239, c1207, c1155, c1158, c1177, c1150, c1169, c1142, c1751] c2077 (by decide) p (sat_cons (step1174 p h) (sat_cons (step1202 p h) (sat_cons (step1147 p h) (sat_cons (step1154 p h) (sat_cons (step1232 p h) (sat_cons (step1239 p h) (sat_cons (step1207 p h) (sat_cons (step1155 p h) (sat_cons (step1158 p h) (sat_cons (step1177 p h) (sat_cons (step1150 p h) (sat_cons (step1169 p h) (sat_cons (step1142 p h) (sat_cons (step1751 p h) (sat_nil p)))))))))))))))
def c2078 : List Lit := [(929, true), (922, false)]
theorem step2078 (p : Nat → Bool) (h : Constraints p) : clause p c2078 = true :=
  Snake9.LocalRup.prove_clause [c1045, c1054, c1057, c1048, c1031, c1033, c1039, c1028, c1029, c1025, c188, c1709] c2078 (by decide) p (sat_cons (step1045 p h) (sat_cons (step1054 p h) (sat_cons (step1057 p h) (sat_cons (step1048 p h) (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1039 p h) (sat_cons (step1028 p h) (sat_cons (step1029 p h) (sat_cons (step1025 p h) (sat_cons (step188 p h) (sat_cons (step1709 p h) (sat_nil p)))))))))))))
def c2079 : List Lit := [(1063, true), (46, false), (114, false), (1066, true)]
theorem step2079 (p : Nat → Bool) (h : Constraints p) : clause p c2079 = true :=
  Snake9.LocalRup.prove_clause [c1321, c2050, c666, c665, c1326] c2079 (by decide) p (sat_cons (step1321 p h) (sat_cons (step2050 p h) (sat_cons (step666 p h) (sat_cons (step665 p h) (sat_cons (step1326 p h) (sat_nil p))))))
def c2080 : List Lit := [(916, true), (52, true)]
theorem step2080 (p : Nat → Bool) (h : Constraints p) : clause p c2080 = true :=
  Snake9.LocalRup.prove_clause [c1031, c1033, c1029, c1025, c1709] c2080 (by decide) p (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1029 p h) (sat_cons (step1025 p h) (sat_cons (step1709 p h) (sat_nil p))))))
def c2081 : List Lit := [(929, true), (52, true)]
theorem step2081 (p : Nat → Bool) (h : Constraints p) : clause p c2081 = true :=
  Snake9.LocalRup.prove_clause [c2080, c1061, c1057, c1706, c1673, c1025, c1029, c1034] c2081 (by decide) p (sat_cons (step2080 p h) (sat_cons (step1061 p h) (sat_cons (step1057 p h) (sat_cons (step1706 p h) (sat_cons (step1673 p h) (sat_cons (step1025 p h) (sat_cons (step1029 p h) (sat_cons (step1034 p h) (sat_nil p)))))))))
def c2082 : List Lit := [(91, false), (92, true), (1031, true)]
theorem step2082 (p : Nat → Bool) (h : Constraints p) : clause p c2082 = true :=
  Snake9.LocalRup.prove_clause [c1260, c1259, c404, c1942] c2082 (by decide) p (sat_cons (step1260 p h) (sat_cons (step1259 p h) (sat_cons (step404 p h) (sat_cons (step1942 p h) (sat_nil p)))))
def c2083 : List Lit := [(987, true), (982, false), (72, true), (992, true), (107, true), (52, true)]
theorem step2083 (p : Nat → Bool) (h : Constraints p) : clause p c2083 = true :=
  Snake9.LocalRup.prove_clause [c1145, c1169, c1168, c1156, c1159, c1153, c1751, c1142, c1143, c1151, c1907, c1146, c319] c2083 (by decide) p (sat_cons (step1145 p h) (sat_cons (step1169 p h) (sat_cons (step1168 p h) (sat_cons (step1156 p h) (sat_cons (step1159 p h) (sat_cons (step1153 p h) (sat_cons (step1751 p h) (sat_cons (step1142 p h) (sat_cons (step1143 p h) (sat_cons (step1151 p h) (sat_cons (step1907 p h) (sat_cons (step1146 p h) (sat_cons (step319 p h) (sat_nil p))))))))))))))
def c2084 : List Lit := [(959, true), (36, true), (107, true), (929, false)]
theorem step2084 (p : Nat → Bool) (h : Constraints p) : clause p c2084 = true :=
  Snake9.LocalRup.prove_clause [c992, c995, c2000, c1081, c2012, c1114, c1087, c1997, c2001, c1017, c1638, c996, c1806, c932, c994, c924, c1835, c1862, c137, c138, c1001, c1004, c1009] c2084 (by decide) p (sat_cons (step992 p h) (sat_cons (step995 p h) (sat_cons (step2000 p h) (sat_cons (step1081 p h) (sat_cons (step2012 p h) (sat_cons (step1114 p h) (sat_cons (step1087 p h) (sat_cons (step1997 p h) (sat_cons (step2001 p h) (sat_cons (step1017 p h) (sat_cons (step1638 p h) (sat_cons (step996 p h) (sat_cons (step1806 p h) (sat_cons (step932 p h) (sat_cons (step994 p h) (sat_cons (step924 p h) (sat_cons (step1835 p h) (sat_cons (step1862 p h) (sat_cons (step137 p h) (sat_cons (step138 p h) (sat_cons (step1001 p h) (sat_cons (step1004 p h) (sat_cons (step1009 p h) (sat_nil p))))))))))))))))))))))))
def c2085 : List Lit := [(72, true), (987, true), (992, true), (107, true), (52, true)]
theorem step2085 (p : Nat → Bool) (h : Constraints p) : clause p c2085 = true :=
  Snake9.LocalRup.prove_clause [c1168, c1145, c2083, c1148, c1150, c1146, c1141, c319, c1907] c2085 (by decide) p (sat_cons (step1168 p h) (sat_cons (step1145 p h) (sat_cons (step2083 p h) (sat_cons (step1148 p h) (sat_cons (step1150 p h) (sat_cons (step1146 p h) (sat_cons (step1141 p h) (sat_cons (step319 p h) (sat_cons (step1907 p h) (sat_nil p))))))))))
def c2086 : List Lit := [(1044, true), (106, true), (107, true), (111, false)]
theorem step2086 (p : Nat → Bool) (h : Constraints p) : clause p c2086 = true :=
  Snake9.LocalRup.prove_clause [c1277, c1280, c1282, c1278, c1273, c1274, c2075, c472, c1959] c2086 (by decide) p (sat_cons (step1277 p h) (sat_cons (step1280 p h) (sat_cons (step1282 p h) (sat_cons (step1278 p h) (sat_cons (step1273 p h) (sat_cons (step1274 p h) (sat_cons (step2075 p h) (sat_cons (step472 p h) (sat_cons (step1959 p h) (sat_nil p))))))))))
def c2087 : List Lit := [(929, true), (55, true)]
theorem step2087 (p : Nat → Bool) (h : Constraints p) : clause p c2087 = true :=
  Snake9.LocalRup.prove_clause [c1039, c1047, c1054, c2081, c1057, c1050, c1031, c1033, c1041, c1028, c1025, c187] c2087 (by decide) p (sat_cons (step1039 p h) (sat_cons (step1047 p h) (sat_cons (step1054 p h) (sat_cons (step2081 p h) (sat_cons (step1057 p h) (sat_cons (step1050 p h) (sat_cons (step1031 p h) (sat_cons (step1033 p h) (sat_cons (step1041 p h) (sat_cons (step1028 p h) (sat_cons (step1025 p h) (sat_cons (step187 p h) (sat_nil p)))))))))))))
def c2088 : List Lit := [(994, false), (1019, true), (1005, false)]
theorem step2088 (p : Nat → Bool) (h : Constraints p) : clause p c2088 = true :=
  Snake9.LocalRup.prove_clause [c1223, c1207, c1174, c1202, c1231, c1154, c1157, c1177, c1149, c1169, c1142, c1751] c2088 (by decide) p (sat_cons (step1223 p h) (sat_cons (step1207 p h) (sat_cons (step1174 p h) (sat_cons (step1202 p h) (sat_cons (step1231 p h) (sat_cons (step1154 p h) (sat_cons (step1157 p h) (sat_cons (step1177 p h) (sat_cons (step1149 p h) (sat_cons (step1169 p h) (sat_cons (step1142 p h) (sat_cons (step1751 p h) (sat_nil p)))))))))))))
def c2089 : List Lit := [(1020, true), (100, false), (82, true), (1069, true), (72, false), (1010, false), (1005, false), (974, false)]
theorem step2089 (p : Nat → Bool) (h : Constraints p) : clause p c2089 = true :=
  Snake9.LocalRup.prove_clause [c1157, c1239, c1232, c1158, c1207, c1149, c1175, c1142, c1173, c302, c1662, c1923] c2089 (by decide) p (sat_cons (step1157 p h) (sat_cons (step1239 p h) (sat_cons (step1232 p h) (sat_cons (step1158 p h) (sat_cons (step1207 p h) (sat_cons (step1149 p h) (sat_cons (step1175 p h) (sat_cons (step1142 p h) (sat_cons (step1173 p h) (sat_cons (step302 p h) (sat_cons (step1662 p h) (sat_cons (step1923 p h) (sat_nil p)))))))))))))
def c2090 : List Lit := [(114, true), (1058, true), (1061, true), (112, false), (72, false)]
theorem step2090 (p : Nat → Bool) (h : Constraints p) : clause p c2090 = true :=
  Snake9.LocalRup.prove_clause [c1310, c1312, c1319, c583, c584, c1309] c2090 (by decide) p (sat_cons (step1310 p h) (sat_cons (step1312 p h) (sat_cons (step1319 p h) (sat_cons (step583 p h) (sat_cons (step584 p h) (sat_cons (step1309 p h) (sat_nil p)))))))
def c2091 : List Lit := [(81, false), (1069, true), (113, false), (72, false)]
theorem step2091 (p : Nat → Bool) (h : Constraints p) : clause p c2091 = true :=
  Snake9.LocalRup.prove_clause [c2052, c1696] c2091 (by decide) p (sat_cons (step2052 p h) (sat_cons (step1696 p h) (sat_nil p)))
def c2092 : List Lit := [(92, false), (91, false), (82, false), (959, true), (906, false)]
theorem step2092 (p : Nat → Bool) (h : Constraints p) : clause p c2092 = true :=
  Snake9.LocalRup.prove_clause [c394, c388, c1043, c945, c2074, c1717] c2092 (by decide) p (sat_cons (step394 p h) (sat_cons (step388 p h) (sat_cons (step1043 p h) (sat_cons (step945 p h) (sat_cons (step2074 p h) (sat_cons (step1717 p h) (sat_nil p)))))))
def c2093 : List Lit := [(36, false), (46, false), (113, false), (72, false)]
theorem step2093 (p : Nat → Bool) (h : Constraints p) : clause p c2093 = true :=
  Snake9.LocalRup.prove_clause [c565, c118, c1865] c2093 (by decide) p (sat_cons (step565 p h) (sat_cons (step118 p h) (sat_cons (step1865 p h) (sat_nil p))))
def c2094 : List Lit := [(1004, false), (1018, true), (113, false), (46, false)]
theorem step2094 (p : Nat → Bool) (h : Constraints p) : clause p c2094 = true :=
  Snake9.LocalRup.prove_clause [c1196, c1743, c1237, c1172, c1155, c654, c2052, c1923, c1145, c304, c1150, c1142] c2094 (by decide) p (sat_cons (step1196 p h) (sat_cons (step1743 p h) (sat_cons (step1237 p h) (sat_cons (step1172 p h) (sat_cons (step1155 p h) (sat_cons (step654 p h) (sat_cons (step2052 p h) (sat_cons (step1923 p h) (sat_cons (step1145 p h) (sat_cons (step304 p h) (sat_cons (step1150 p h) (sat_cons (step1142 p h) (sat_nil p)))))))))))))
def c2095 : List Lit := [(123, true), (86, false), (113, false), (959, true), (906, false)]
theorem step2095 (p : Nat → Bool) (h : Constraints p) : clause p c2095 = true :=
  Snake9.LocalRup.prove_clause [c1798, c2012, c1805, c1878, c1997, c1801, c1638, c2001, c932, c1087, c924, c2081, c2087, c185] c2095 (by decide) p (sat_cons (step1798 p h) (sat_cons (step2012 p h) (sat_cons (step1805 p h) (sat_cons (step1878 p h) (sat_cons (step1997 p h) (sat_cons (step1801 p h) (sat_cons (step1638 p h) (sat_cons (step2001 p h) (sat_cons (step932 p h) (sat_cons (step1087 p h) (sat_cons (step924 p h) (sat_cons (step2081 p h) (sat_cons (step2087 p h) (sat_cons (step185 p h) (sat_nil p)))))))))))))))
def c2096 : List Lit := [(907, false), (86, false), (959, true)]
theorem step2096 (p : Nat → Bool) (h : Constraints p) : clause p c2096 = true :=
  Snake9.LocalRup.prove_clause [c2012, c2009, c1087, c1114, c2081, c2087, c1997, c185, c1638, c924, c932] c2096 (by decide) p (sat_cons (step2012 p h) (sat_cons (step2009 p h) (sat_cons (step1087 p h) (sat_cons (step1114 p h) (sat_cons (step2081 p h) (sat_cons (step2087 p h) (sat_cons (step1997 p h) (sat_cons (step185 p h) (sat_cons (step1638 p h) (sat_cons (step924 p h) (sat_cons (step932 p h) (sat_nil p))))))))))))
def c2097 : List Lit := [(1018, true), (36, true), (113, false), (959, true), (906, false)]
theorem step2097 (p : Nat → Bool) (h : Constraints p) : clause p c2097 = true :=
  Snake9.LocalRup.prove_clause [c2012, c1082, c1798, c2094, c1188, c1190, c1186, c1183, c1599, c2095, c654, c1172, c1174, c1200, c1237, c1155, c1152, c2096, c2001, c996, c994, c2073, c1141, c1143, c1149, c1154, c1158, c1230, c1751, c1205, c1169, c1177] c2097 (by decide) p (sat_cons (step2012 p h) (sat_cons (step1082 p h) (sat_cons (step1798 p h) (sat_cons (step2094 p h) (sat_cons (step1188 p h) (sat_cons (step1190 p h) (sat_cons (step1186 p h) (sat_cons (step1183 p h) (sat_cons (step1599 p h) (sat_cons (step2095 p h) (sat_cons (step654 p h) (sat_cons (step1172 p h) (sat_cons (step1174 p h) (sat_cons (step1200 p h) (sat_cons (step1237 p h) (sat_cons (step1155 p h) (sat_cons (step1152 p h) (sat_cons (step2096 p h) (sat_cons (step2001 p h) (sat_cons (step996 p h) (sat_cons (step994 p h) (sat_cons (step2073 p h) (sat_cons (step1141 p h) (sat_cons (step1143 p h) (sat_cons (step1149 p h) (sat_cons (step1154 p h) (sat_cons (step1158 p h) (sat_cons (step1230 p h) (sat_cons (step1751 p h) (sat_cons (step1205 p h) (sat_cons (step1169 p h) (sat_cons (step1177 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c2098 : List Lit := [(36, false), (89, false), (37, true), (113, false)]
theorem step2098 (p : Nat → Bool) (h : Constraints p) : clause p c2098 = true :=
  Snake9.LocalRup.prove_clause [c1865, c569] c2098 (by decide) p (sat_cons (step1865 p h) (sat_cons (step569 p h) (sat_nil p)))
def c2099 : List Lit := [(1019, true), (69, false), (982, false), (994, false)]
theorem step2099 (p : Nat → Bool) (h : Constraints p) : clause p c2099 = true :=
  Snake9.LocalRup.prove_clause [c1155, c1174, c1200, c1244, c1238, c1159, c1205, c1751, c1177, c1169] c2099 (by decide) p (sat_cons (step1155 p h) (sat_cons (step1174 p h) (sat_cons (step1200 p h) (sat_cons (step1244 p h) (sat_cons (step1238 p h) (sat_cons (step1159 p h) (sat_cons (step1205 p h) (sat_cons (step1751 p h) (sat_cons (step1177 p h) (sat_cons (step1169 p h) (sat_nil p)))))))))))
def c2100 : List Lit := [(1088, true), (1045, false), (1056, false), (91, false), (1069, false), (1033, false)]
theorem step2100 (p : Nat → Bool) (h : Constraints p) : clause p c2100 = true :=
  Snake9.LocalRup.prove_clause [c1265, c1294, c1318, c1344, c1387, c1394, c1348, c1299, c1319, c1268, c1310, c1260, c2082, c403] c2100 (by decide) p (sat_cons (step1265 p h) (sat_cons (step1294 p h) (sat_cons (step1318 p h) (sat_cons (step1344 p h) (sat_cons (step1387 p h) (sat_cons (step1394 p h) (sat_cons (step1348 p h) (sat_cons (step1299 p h) (sat_cons (step1319 p h) (sat_cons (step1268 p h) (sat_cons (step1310 p h) (sat_cons (step1260 p h) (sat_cons (step2082 p h) (sat_cons (step403 p h) (sat_nil p)))))))))))))))
def c2101 : List Lit := [(996, false), (979, false), (986, false), (69, true), (1088, false), (1019, true)]
theorem step2101 (p : Nat → Bool) (h : Constraints p) : clause p c2101 = true :=
  Snake9.LocalRup.prove_clause [c1238, c1200, c1201, c1244, c1237, c1190, c1156, c1421, c1183, c1153, c2030, c1143, c2011, c2043, c1081, c1054, c2081, c1050, c2046] c2101 (by decide) p (sat_cons (step1238 p h) (sat_cons (step1200 p h) (sat_cons (step1201 p h) (sat_cons (step1244 p h) (sat_cons (step1237 p h) (sat_cons (step1190 p h) (sat_cons (step1156 p h) (sat_cons (step1421 p h) (sat_cons (step1183 p h) (sat_cons (step1153 p h) (sat_cons (step2030 p h) (sat_cons (step1143 p h) (sat_cons (step2011 p h) (sat_cons (step2043 p h) (sat_cons (step1081 p h) (sat_cons (step1054 p h) (sat_cons (step2081 p h) (sat_cons (step1050 p h) (sat_cons (step2046 p h) (sat_nil p))))))))))))))))))))
def c2102 : List Lit := [(86, false), (939, true), (70, false)]
theorem step2102 (p : Nat → Bool) (h : Constraints p) : clause p c2102 = true :=
  Snake9.LocalRup.prove_clause [c2043, c1081, c1054, c2081, c1050, c2046] c2102 (by decide) p (sat_cons (step2043 p h) (sat_cons (step1081 p h) (sat_cons (step1054 p h) (sat_cons (step2081 p h) (sat_cons (step1050 p h) (sat_cons (step2046 p h) (sat_nil p)))))))
def c2103 : List Lit := [(922, true), (60, false), (61, false)]
theorem step2103 (p : Nat → Bool) (h : Constraints p) : clause p c2103 = true :=
  Snake9.LocalRup.prove_clause [c1042, c1043, c256] c2103 (by decide) p (sat_cons (step1042 p h) (sat_cons (step1043 p h) (sat_cons (step256 p h) (sat_nil p))))
def c2104 : List Lit := [(1008, false), (979, false), (982, false), (69, true), (1088, false), (1019, true)]
theorem step2104 (p : Nat → Bool) (h : Constraints p) : clause p c2104 = true :=
  Snake9.LocalRup.prove_clause [c1155, c2101, c1176, c1169, c1244, c1237, c1156, c1159, c1421, c1153, c1136, c1138, c2030, c1143, c1133, c1134, c2011, c247, c2004, c1898, c2103, c1045, c2078, c1062, c2003, c1032, c1113, c1997, c1638, c932, c1716, c924, c1030, c179, c1884, c294] c2104 (by decide) p (sat_cons (step1155 p h) (sat_cons (step2101 p h) (sat_cons (step1176 p h) (sat_cons (step1169 p h) (sat_cons (step1244 p h) (sat_cons (step1237 p h) (sat_cons (step1156 p h) (sat_cons (step1159 p h) (sat_cons (step1421 p h) (sat_cons (step1153 p h) (sat_cons (step1136 p h) (sat_cons (step1138 p h) (sat_cons (step2030 p h) (sat_cons (step1143 p h) (sat_cons (step1133 p h) (sat_cons (step1134 p h) (sat_cons (step2011 p h) (sat_cons (step247 p h) (sat_cons (step2004 p h) (sat_cons (step1898 p h) (sat_cons (step2103 p h) (sat_cons (step1045 p h) (sat_cons (step2078 p h) (sat_cons (step1062 p h) (sat_cons (step2003 p h) (sat_cons (step1032 p h) (sat_cons (step1113 p h) (sat_cons (step1997 p h) (sat_cons (step1638 p h) (sat_cons (step932 p h) (sat_cons (step1716 p h) (sat_cons (step924 p h) (sat_cons (step1030 p h) (sat_cons (step179 p h) (sat_cons (step1884 p h) (sat_cons (step294 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))
def c2105 : List Lit := [(92, true), (1037, true), (86, false), (100, true), (91, false)]
theorem step2105 (p : Nat → Bool) (h : Constraints p) : clause p c2105 = true :=
  Snake9.LocalRup.prove_clause [c2082, c1941, c1269, c418, c1264] c2105 (by decide) p (sat_cons (step2082 p h) (sat_cons (step1941 p h) (sat_cons (step1269 p h) (sat_cons (step418 p h) (sat_cons (step1264 p h) (sat_nil p))))))
def c2106 : List Lit := [(113, false), (72, false), (81, false), (46, false)]
theorem step2106 (p : Nat → Bool) (h : Constraints p) : clause p c2106 = true :=
  Snake9.LocalRup.prove_clause [c654, c2052] c2106 (by decide) p (sat_cons (step654 p h) (sat_cons (step2052 p h) (sat_nil p)))
end B112E097
