import B112E153Part0009
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c2187 : List Lit := [(945, false), (954, true)]
theorem step2187 (p : Nat → Bool) (h : Constraints p) : clause p c2187 = true :=
  Snake9.LocalRup.prove_clause [c2119, c1024] c2187 (by decide) p (sat_cons (step2119 p h) (sat_cons (step1024 p h) (sat_nil p)))
def c2188 : List Lit := [(892, false), (974, true)]
theorem step2188 (p : Nat → Bool) (h : Constraints p) : clause p c2188 = true :=
  Snake9.LocalRup.prove_clause [c2120, c1062] c2188 (by decide) p (sat_cons (step2120 p h) (sat_cons (step1062 p h) (sat_nil p)))
def c2189 : List Lit := [(1036, false), (1105, false)]
theorem step2189 (p : Nat → Bool) (h : Constraints p) : clause p c2189 = true :=
  Snake9.LocalRup.prove_clause [c2122, c1381] c2189 (by decide) p (sat_cons (step2122 p h) (sat_cons (step1381 p h) (sat_nil p)))
def c2190 : List Lit := [(15, true), (1513, true), (137, true)]
theorem step2190 (p : Nat → Bool) (h : Constraints p) : clause p c2190 = true :=
  Snake9.LocalRup.prove_clause [c1683, c1415, c22] c2190 (by decide) p (sat_cons (step1683 p h) (sat_cons (step1415 p h) (sat_cons (step22 p h) (sat_nil p))))
def c2191 : List Lit := [(107, true), (104, false), (106, true), (114, false), (102, true), (228, true)]
theorem step2191 (p : Nat → Bool) (h : Constraints p) : clause p c2191 = true :=
  Snake9.LocalRup.prove_clause [c444, c443, c1791, c519] c2191 (by decide) p (sat_cons (step444 p h) (sat_cons (step443 p h) (sat_cons (step1791 p h) (sat_cons (step519 p h) (sat_nil p)))))
def c2192 : List Lit := [(10, false), (54, false), (6, false)]
theorem step2192 (p : Nat → Bool) (h : Constraints p) : clause p c2192 = true :=
  Snake9.LocalRup.prove_clause [c8, c10, c17, c703, c707, c704, c709, c705, c715, c1811] c2192 (by decide) p (sat_cons (step8 p h) (sat_cons (step10 p h) (sat_cons (step17 p h) (sat_cons (step703 p h) (sat_cons (step707 p h) (sat_cons (step704 p h) (sat_cons (step709 p h) (sat_cons (step705 p h) (sat_cons (step715 p h) (sat_cons (step1811 p h) (sat_nil p)))))))))))
def c2193 : List Lit := [(1533, true), (16, false), (149, true), (150, true), (92, true), (23, true)]
theorem step2193 (p : Nat → Bool) (h : Constraints p) : clause p c2193 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1422, c68, c65, c1691, c59] c2193 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1422 p h) (sat_cons (step68 p h) (sat_cons (step65 p h) (sat_cons (step1691 p h) (sat_cons (step59 p h) (sat_nil p)))))))
def c2194 : List Lit := [(1751, true), (1736, false), (246, true)]
theorem step2194 (p : Nat → Bool) (h : Constraints p) : clause p c2194 = true :=
  Snake9.LocalRup.prove_clause [c1483, c1495, c1494, c1485, c1490, c2173] c2194 (by decide) p (sat_cons (step1483 p h) (sat_cons (step1495 p h) (sat_cons (step1494 p h) (sat_cons (step1485 p h) (sat_cons (step1490 p h) (sat_cons (step2173 p h) (sat_nil p)))))))
def c2195 : List Lit := [(124, false), (100, false), (46, false), (79, false), (203, true)]
theorem step2195 (p : Nat → Bool) (h : Constraints p) : clause p c2195 = true :=
  Snake9.LocalRup.prove_clause [c615, c623, c260] c2195 (by decide) p (sat_cons (step615 p h) (sat_cons (step623 p h) (sat_cons (step260 p h) (sat_nil p))))
def c2196 : List Lit := [(1103, true), (1055, false), (1084, false), (108, true), (1072, false), (1060, false), (90, true), (91, false), (99, true), (89, true), (94, true)]
theorem step2196 (p : Nat → Bool) (h : Constraints p) : clause p c2196 = true :=
  Snake9.LocalRup.prove_clause [c1259, c1286, c1199, c1202, c1207, c1237, c1332, c1326, c1242, c1238, c1290, c1208, c1210, c1222, c1260, c1203, c1200, c1217, c1252, c399, c1865] c2196 (by decide) p (sat_cons (step1259 p h) (sat_cons (step1286 p h) (sat_cons (step1199 p h) (sat_cons (step1202 p h) (sat_cons (step1207 p h) (sat_cons (step1237 p h) (sat_cons (step1332 p h) (sat_cons (step1326 p h) (sat_cons (step1242 p h) (sat_cons (step1238 p h) (sat_cons (step1290 p h) (sat_cons (step1208 p h) (sat_cons (step1210 p h) (sat_cons (step1222 p h) (sat_cons (step1260 p h) (sat_cons (step1203 p h) (sat_cons (step1200 p h) (sat_cons (step1217 p h) (sat_cons (step1252 p h) (sat_cons (step399 p h) (sat_cons (step1865 p h) (sat_nil p))))))))))))))))))))))
def c2197 : List Lit := [(920, false), (975, true), (68, false), (65, false), (82, false), (71, false)]
theorem step2197 (p : Nat → Bool) (h : Constraints p) : clause p c2197 = true :=
  Snake9.LocalRup.prove_clause [c1839, c1058, c1980, c1913, c1033, c907, c1861, c402, c985, c218, c1742, c1743, c1513] c2197 (by decide) p (sat_cons (step1839 p h) (sat_cons (step1058 p h) (sat_cons (step1980 p h) (sat_cons (step1913 p h) (sat_cons (step1033 p h) (sat_cons (step907 p h) (sat_cons (step1861 p h) (sat_cons (step402 p h) (sat_cons (step985 p h) (sat_cons (step218 p h) (sat_cons (step1742 p h) (sat_cons (step1743 p h) (sat_cons (step1513 p h) (sat_nil p))))))))))))))
def c2198 : List Lit := [(1077, false), (1065, false), (1082, false), (118, true), (35, true), (1035, false)]
theorem step2198 (p : Nat → Bool) (h : Constraints p) : clause p c2198 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1272, c938, c1605, c1837, c1291, c1319, c1370, c1854, c2108, c1057, c1264, c2013, c1275, c1050, c1292, c1853, c1320, c1371] c2198 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1272 p h) (sat_cons (step938 p h) (sat_cons (step1605 p h) (sat_cons (step1837 p h) (sat_cons (step1291 p h) (sat_cons (step1319 p h) (sat_cons (step1370 p h) (sat_cons (step1854 p h) (sat_cons (step2108 p h) (sat_cons (step1057 p h) (sat_cons (step1264 p h) (sat_cons (step2013 p h) (sat_cons (step1275 p h) (sat_cons (step1050 p h) (sat_cons (step1292 p h) (sat_cons (step1853 p h) (sat_cons (step1320 p h) (sat_cons (step1371 p h) (sat_nil p))))))))))))))))))))
def c2199 : List Lit := [(35, true), (920, true), (1024, false), (75, true), (990, false), (993, false), (65, false), (1008, true), (71, false), (1047, false), (86, false)]
theorem step2199 (p : Nat → Bool) (h : Constraints p) : clause p c2199 = true :=
  Snake9.LocalRup.prove_clause [c1657, c1077, c1083, c1094, c1178, c1107, c1106, c938, c1665, c940, c1619, c1609, c1216, c955, c1218, c96, c1718, c617, c618, c615, c616, c619, c1262, c1267, c1201, c1252, c1272, c1207, c1254, c1283, c1236, c2198, c1260, c1877, c1969, c1746, c1966, c1919, c1203, c254, c985, c1217, c1208, c1079, c1861, c1219, c1084, c2117, c1242, c1095, c1853, c1332, c1185, c1379] c2199 (by decide) p (sat_cons (step1657 p h) (sat_cons (step1077 p h) (sat_cons (step1083 p h) (sat_cons (step1094 p h) (sat_cons (step1178 p h) (sat_cons (step1107 p h) (sat_cons (step1106 p h) (sat_cons (step938 p h) (sat_cons (step1665 p h) (sat_cons (step940 p h) (sat_cons (step1619 p h) (sat_cons (step1609 p h) (sat_cons (step1216 p h) (sat_cons (step955 p h) (sat_cons (step1218 p h) (sat_cons (step96 p h) (sat_cons (step1718 p h) (sat_cons (step617 p h) (sat_cons (step618 p h) (sat_cons (step615 p h) (sat_cons (step616 p h) (sat_cons (step619 p h) (sat_cons (step1262 p h) (sat_cons (step1267 p h) (sat_cons (step1201 p h) (sat_cons (step1252 p h) (sat_cons (step1272 p h) (sat_cons (step1207 p h) (sat_cons (step1254 p h) (sat_cons (step1283 p h) (sat_cons (step1236 p h) (sat_cons (step2198 p h) (sat_cons (step1260 p h) (sat_cons (step1877 p h) (sat_cons (step1969 p h) (sat_cons (step1746 p h) (sat_cons (step1966 p h) (sat_cons (step1919 p h) (sat_cons (step1203 p h) (sat_cons (step254 p h) (sat_cons (step985 p h) (sat_cons (step1217 p h) (sat_cons (step1208 p h) (sat_cons (step1079 p h) (sat_cons (step1861 p h) (sat_cons (step1219 p h) (sat_cons (step1084 p h) (sat_cons (step2117 p h) (sat_cons (step1242 p h) (sat_cons (step1095 p h) (sat_cons (step1853 p h) (sat_cons (step1332 p h) (sat_cons (step1185 p h) (sat_cons (step1379 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c2200 : List Lit := [(46, false), (124, false), (1073, false), (1103, true), (108, true), (99, true), (109, true), (81, false), (1047, false)]
theorem step2200 (p : Nat → Bool) (h : Constraints p) : clause p c2200 = true :=
  Snake9.LocalRup.prove_clause [c1254, c1878, c617, c618, c615, c619, c1262, c1267, c1203, c1272, c1208, c1283, c1241, c1332, c1326, c1242, c1284, c1287, c1219, c1275, c1257, c1217, c1264, c1959] c2200 (by decide) p (sat_cons (step1254 p h) (sat_cons (step1878 p h) (sat_cons (step617 p h) (sat_cons (step618 p h) (sat_cons (step615 p h) (sat_cons (step619 p h) (sat_cons (step1262 p h) (sat_cons (step1267 p h) (sat_cons (step1203 p h) (sat_cons (step1272 p h) (sat_cons (step1208 p h) (sat_cons (step1283 p h) (sat_cons (step1241 p h) (sat_cons (step1332 p h) (sat_cons (step1326 p h) (sat_cons (step1242 p h) (sat_cons (step1284 p h) (sat_cons (step1287 p h) (sat_cons (step1219 p h) (sat_cons (step1275 p h) (sat_cons (step1257 p h) (sat_cons (step1217 p h) (sat_cons (step1264 p h) (sat_cons (step1959 p h) (sat_nil p)))))))))))))))))))))))))
def c2201 : List Lit := [(46, true), (42, false), (35, false), (920, true)]
theorem step2201 (p : Nat → Bool) (h : Constraints p) : clause p c2201 = true :=
  Snake9.LocalRup.prove_clause [c967, c1927, c1917, c970, c941, c944] c2201 (by decide) p (sat_cons (step967 p h) (sat_cons (step1927 p h) (sat_cons (step1917 p h) (sat_cons (step970 p h) (sat_cons (step941 p h) (sat_cons (step944 p h) (sat_nil p)))))))
def c2202 : List Lit := [(1060, true), (108, true), (109, true), (82, false)]
theorem step2202 (p : Nat → Bool) (h : Constraints p) : clause p c2202 = true :=
  Snake9.LocalRup.prove_clause [c1215, c1219, c1221, c1217, c1212, c1213, c1977, c426] c2202 (by decide) p (sat_cons (step1215 p h) (sat_cons (step1219 p h) (sat_cons (step1221 p h) (sat_cons (step1217 p h) (sat_cons (step1212 p h) (sat_cons (step1213 p h) (sat_cons (step1977 p h) (sat_cons (step426 p h) (sat_nil p)))))))))
def c2203 : List Lit := [(117, false), (92, true), (115, false), (1071, true), (1061, true), (108, true), (109, true), (82, false)]
theorem step2203 (p : Nat → Bool) (h : Constraints p) : clause p c2203 = true :=
  Snake9.LocalRup.prove_clause [c1959, c1631, c1217, c1212, c1222] c2203 (by decide) p (sat_cons (step1959 p h) (sat_cons (step1631 p h) (sat_cons (step1217 p h) (sat_cons (step1212 p h) (sat_cons (step1222 p h) (sat_nil p))))))
def c2204 : List Lit := [(113, false), (46, false), (68, false), (81, false)]
theorem step2204 (p : Nat → Bool) (h : Constraints p) : clause p c2204 = true :=
  Snake9.LocalRup.prove_clause [c616, c229, c1763] c2204 (by decide) p (sat_cons (step616 p h) (sat_cons (step229 p h) (sat_cons (step1763 p h) (sat_nil p))))
def c2205 : List Lit := [(1084, true), (1008, true)]
theorem step2205 (p : Nat → Bool) (h : Constraints p) : clause p c2205 = true :=
  Snake9.LocalRup.prove_clause [c1641, c1106, c1271, c2039] c2205 (by decide) p (sat_cons (step1641 p h) (sat_cons (step1106 p h) (sat_cons (step1271 p h) (sat_cons (step2039 p h) (sat_nil p)))))
def c2206 : List Lit := [(1079, true), (113, false), (81, false)]
theorem step2206 (p : Nat → Bool) (h : Constraints p) : clause p c2206 = true :=
  Snake9.LocalRup.prove_clause [c1262, c1998, c634] c2206 (by decide) p (sat_cons (step1262 p h) (sat_cons (step1998 p h) (sat_cons (step634 p h) (sat_nil p))))
def c2207 : List Lit := [(109, false), (1101, true), (1084, false), (71, false), (1051, false), (86, false)]
theorem step2207 (p : Nat → Bool) (h : Constraints p) : clause p c2207 = true :=
  Snake9.LocalRup.prove_clause [c1661, c1877, c1232, c1259, c1317, c1286] c2207 (by decide) p (sat_cons (step1661 p h) (sat_cons (step1877 p h) (sat_cons (step1232 p h) (sat_cons (step1259 p h) (sat_cons (step1317 p h) (sat_cons (step1286 p h) (sat_nil p)))))))
def c2208 : List Lit := [(113, false), (124, true), (1101, false), (109, true), (75, true), (1024, false), (63, true), (993, false), (65, false), (1008, true), (71, false), (1047, false), (86, false)]
theorem step2208 (p : Nat → Bool) (h : Constraints p) : clause p c2208 = true :=
  Snake9.LocalRup.prove_clause [c1106, c1763, c1966, c985, c1861, c2183, c1107, c1746, c254, c1079, c1084, c1071, c229, c1066, c1072, c1100, c1191, c1385, c1854, c1846, c1057, c1033, c2013, c2199, c1051, c1703, c1027, c2201, c1605, c1718, c98, c939] c2208 (by decide) p (sat_cons (step1106 p h) (sat_cons (step1763 p h) (sat_cons (step1966 p h) (sat_cons (step985 p h) (sat_cons (step1861 p h) (sat_cons (step2183 p h) (sat_cons (step1107 p h) (sat_cons (step1746 p h) (sat_cons (step254 p h) (sat_cons (step1079 p h) (sat_cons (step1084 p h) (sat_cons (step1071 p h) (sat_cons (step229 p h) (sat_cons (step1066 p h) (sat_cons (step1072 p h) (sat_cons (step1100 p h) (sat_cons (step1191 p h) (sat_cons (step1385 p h) (sat_cons (step1854 p h) (sat_cons (step1846 p h) (sat_cons (step1057 p h) (sat_cons (step1033 p h) (sat_cons (step2013 p h) (sat_cons (step2199 p h) (sat_cons (step1051 p h) (sat_cons (step1703 p h) (sat_cons (step1027 p h) (sat_cons (step2201 p h) (sat_cons (step1605 p h) (sat_cons (step1718 p h) (sat_cons (step98 p h) (sat_cons (step939 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c2209 : List Lit := [(1123, true), (1036, false), (1004, false), (1101, false), (1072, false), (1060, false), (1079, false), (1084, false), (1047, false)]
theorem step2209 (p : Nat → Bool) (h : Constraints p) : clause p c2209 = true :=
  Snake9.LocalRup.prove_clause [c1259, c1286, c1206, c1232, c1378, c1385, c1318, c1325, c1186, c1290, c1287, c1237, c1135, c1260, c1272, c1207, c1131, c1252, c1201, c1975, c1864] c2209 (by decide) p (sat_cons (step1259 p h) (sat_cons (step1286 p h) (sat_cons (step1206 p h) (sat_cons (step1232 p h) (sat_cons (step1378 p h) (sat_cons (step1385 p h) (sat_cons (step1318 p h) (sat_cons (step1325 p h) (sat_cons (step1186 p h) (sat_cons (step1290 p h) (sat_cons (step1287 p h) (sat_cons (step1237 p h) (sat_cons (step1135 p h) (sat_cons (step1260 p h) (sat_cons (step1272 p h) (sat_cons (step1207 p h) (sat_cons (step1131 p h) (sat_cons (step1252 p h) (sat_cons (step1201 p h) (sat_cons (step1975 p h) (sat_cons (step1864 p h) (sat_nil p))))))))))))))))))))))
def c2210 : List Lit := [(1004, false), (1123, true), (1101, false), (1072, false), (1060, false), (1079, false), (1024, false), (1084, false), (1047, false)]
theorem step2210 (p : Nat → Bool) (h : Constraints p) : clause p c2210 = true :=
  Snake9.LocalRup.prove_clause [c1185, c2209] c2210 (by decide) p (sat_cons (step1185 p h) (sat_cons (step2209 p h) (sat_nil p)))
def c2211 : List Lit := [(105, false), (988, true), (75, false), (65, false), (82, false)]
theorem step2211 (p : Nat → Bool) (h : Constraints p) : clause p c2211 = true :=
  Snake9.LocalRup.prove_clause [c417, c2168] c2211 (by decide) p (sat_cons (step417 p h) (sat_cons (step2168 p h) (sat_nil p)))
def c2212 : List Lit := [(1103, true), (1017, true), (1061, false), (1072, false), (1079, false), (1084, false), (1047, false)]
theorem step2212 (p : Nat → Bool) (h : Constraints p) : clause p c2212 = true :=
  Snake9.LocalRup.prove_clause [c1206, c1233, c1259, c1286, c1332, c1326, c1238, c1290, c1287, c1207, c1260, c1272, c1201, c1252, c1864, c1975] c2212 (by decide) p (sat_cons (step1206 p h) (sat_cons (step1233 p h) (sat_cons (step1259 p h) (sat_cons (step1286 p h) (sat_cons (step1332 p h) (sat_cons (step1326 p h) (sat_cons (step1238 p h) (sat_cons (step1290 p h) (sat_cons (step1287 p h) (sat_cons (step1207 p h) (sat_cons (step1260 p h) (sat_cons (step1272 p h) (sat_cons (step1201 p h) (sat_cons (step1252 p h) (sat_cons (step1864 p h) (sat_cons (step1975 p h) (sat_nil p)))))))))))))))))
def c2213 : List Lit := [(1056, false), (1103, true), (1035, false), (944, false), (1090, false), (1076, false), (108, true), (35, true), (1079, false), (1051, false)]
theorem step2213 (p : Nat → Bool) (h : Constraints p) : clause p c2213 = true :=
  Snake9.LocalRup.prove_clause [c938, c1605, c1027, c1215, c1224, c2144, c1233, c1033, c1325, c1980, c1369, c1855] c2213 (by decide) p (sat_cons (step938 p h) (sat_cons (step1605 p h) (sat_cons (step1027 p h) (sat_cons (step1215 p h) (sat_cons (step1224 p h) (sat_cons (step2144 p h) (sat_cons (step1233 p h) (sat_cons (step1033 p h) (sat_cons (step1325 p h) (sat_cons (step1980 p h) (sat_cons (step1369 p h) (sat_cons (step1855 p h) (sat_nil p)))))))))))))
def c2214 : List Lit := [(974, true), (944, false), (109, true)]
theorem step2214 (p : Nat → Bool) (h : Constraints p) : clause p c2214 = true :=
  Snake9.LocalRup.prove_clause [c2183, c1057, c1913, c2013, c907, c1051, c1027, c966, c1605, c1632, c963, c938, c939, c956, c1703, c1906, c119, c954] c2214 (by decide) p (sat_cons (step2183 p h) (sat_cons (step1057 p h) (sat_cons (step1913 p h) (sat_cons (step2013 p h) (sat_cons (step907 p h) (sat_cons (step1051 p h) (sat_cons (step1027 p h) (sat_cons (step966 p h) (sat_cons (step1605 p h) (sat_cons (step1632 p h) (sat_cons (step963 p h) (sat_cons (step938 p h) (sat_cons (step939 p h) (sat_cons (step956 p h) (sat_cons (step1703 p h) (sat_cons (step1906 p h) (sat_cons (step119 p h) (sat_cons (step954 p h) (sat_nil p)))))))))))))))))))
def c2215 : List Lit := [(1072, false), (1103, true), (1123, true), (998, false), (1060, false), (99, true), (1024, false), (63, true), (1008, true), (1047, false)]
theorem step2215 (p : Nat → Bool) (h : Constraints p) : clause p c2215 = true :=
  Snake9.LocalRup.prove_clause [c2205, c1202, c1207, c1237, c1326, c1290, c1106, c1259, c1286, c1325, c1378, c1332, c1185, c1242, c1287, c1099, c1208, c1260, c1072, c1203, c1252, c1066, c1947, c229, c1763] c2215 (by decide) p (sat_cons (step2205 p h) (sat_cons (step1202 p h) (sat_cons (step1207 p h) (sat_cons (step1237 p h) (sat_cons (step1326 p h) (sat_cons (step1290 p h) (sat_cons (step1106 p h) (sat_cons (step1259 p h) (sat_cons (step1286 p h) (sat_cons (step1325 p h) (sat_cons (step1378 p h) (sat_cons (step1332 p h) (sat_cons (step1185 p h) (sat_cons (step1242 p h) (sat_cons (step1287 p h) (sat_cons (step1099 p h) (sat_cons (step1208 p h) (sat_cons (step1260 p h) (sat_cons (step1072 p h) (sat_cons (step1203 p h) (sat_cons (step1252 p h) (sat_cons (step1066 p h) (sat_cons (step1947 p h) (sat_cons (step229 p h) (sat_cons (step1763 p h) (sat_nil p))))))))))))))))))))))))))
def c2216 : List Lit := [(1061, true), (102, true), (105, true), (108, true), (109, true)]
theorem step2216 (p : Nat → Bool) (h : Constraints p) : clause p c2216 = true :=
  Snake9.LocalRup.prove_clause [c1212, c1215, c1224, c1222, c1214, c1217, c1791, c1792, c1538] c2216 (by decide) p (sat_cons (step1212 p h) (sat_cons (step1215 p h) (sat_cons (step1224 p h) (sat_cons (step1222 p h) (sat_cons (step1214 p h) (sat_cons (step1217 p h) (sat_cons (step1791 p h) (sat_cons (step1792 p h) (sat_cons (step1538 p h) (sat_nil p))))))))))
def c2217 : List Lit := [(1061, false), (1102, true), (68, false), (99, true), (1008, true), (1047, false)]
theorem step2217 (p : Nat → Bool) (h : Constraints p) : clause p c2217 = true :=
  Snake9.LocalRup.prove_clause [c1873, c1336, c1202, c1207, c2205, c1106, c1243, c1238, c1208, c1331, c1203, c1278, c1282, c1947, c1254, c1763, c1252, c229] c2217 (by decide) p (sat_cons (step1873 p h) (sat_cons (step1336 p h) (sat_cons (step1202 p h) (sat_cons (step1207 p h) (sat_cons (step2205 p h) (sat_cons (step1106 p h) (sat_cons (step1243 p h) (sat_cons (step1238 p h) (sat_cons (step1208 p h) (sat_cons (step1331 p h) (sat_cons (step1203 p h) (sat_cons (step1278 p h) (sat_cons (step1282 p h) (sat_cons (step1947 p h) (sat_cons (step1254 p h) (sat_cons (step1763 p h) (sat_cons (step1252 p h) (sat_cons (step229 p h) (sat_nil p)))))))))))))))))))
def c2218 : List Lit := [(1061, true), (105, true), (108, true), (109, true), (65, false), (82, false)]
theorem step2218 (p : Nat → Bool) (h : Constraints p) : clause p c2218 = true :=
  Snake9.LocalRup.prove_clause [c1215, c1224, c2216, c1214, c416] c2218 (by decide) p (sat_cons (step1215 p h) (sat_cons (step1224 p h) (sat_cons (step2216 p h) (sat_cons (step1214 p h) (sat_cons (step416 p h) (sat_nil p))))))
def c2219 : List Lit := [(112, false), (1021, true), (89, false), (86, false)]
theorem step2219 (p : Nat → Bool) (h : Constraints p) : clause p c2219 = true :=
  Snake9.LocalRup.prove_clause [c323, c325, c1120, c1124, c1129] c2219 (by decide) p (sat_cons (step323 p h) (sat_cons (step325 p h) (sat_cons (step1120 p h) (sat_cons (step1124 p h) (sat_cons (step1129 p h) (sat_nil p))))))
def c2220 : List Lit := [(891, true), (88, false), (93, false), (89, true), (82, false)]
theorem step2220 (p : Nat → Bool) (h : Constraints p) : clause p c2220 = true :=
  Snake9.LocalRup.prove_clause [c1829, c2019, c2021, c354, c1691, c57, c55, c905, c893, c912, c2025, c923, c932, c901, c1888, c896, c1602, c1687, c869, c44, c1573, c874, c887, c880] c2220 (by decide) p (sat_cons (step1829 p h) (sat_cons (step2019 p h) (sat_cons (step2021 p h) (sat_cons (step354 p h) (sat_cons (step1691 p h) (sat_cons (step57 p h) (sat_cons (step55 p h) (sat_cons (step905 p h) (sat_cons (step893 p h) (sat_cons (step912 p h) (sat_cons (step2025 p h) (sat_cons (step923 p h) (sat_cons (step932 p h) (sat_cons (step901 p h) (sat_cons (step1888 p h) (sat_cons (step896 p h) (sat_cons (step1602 p h) (sat_cons (step1687 p h) (sat_cons (step869 p h) (sat_cons (step44 p h) (sat_cons (step1573 p h) (sat_cons (step874 p h) (sat_cons (step887 p h) (sat_cons (step880 p h) (sat_nil p)))))))))))))))))))))))))
def c2221 : List Lit := [(858, true), (852, false), (20, false)]
theorem step2221 (p : Nat → Bool) (h : Constraints p) : clause p c2221 = true :=
  Snake9.LocalRup.prove_clause [c1888, c887, c1602, c1573, c869] c2221 (by decide) p (sat_cons (step1888 p h) (sat_cons (step887 p h) (sat_cons (step1602 p h) (sat_cons (step1573 p h) (sat_cons (step869 p h) (sat_nil p))))))
def c2222 : List Lit := [(275, false), (105, true), (102, true), (29, false), (14, true), (108, true), (35, true)]
theorem step2222 (p : Nat → Bool) (h : Constraints p) : clause p c2222 = true :=
  Snake9.LocalRup.prove_clause [c735, c1812, c1814, c732, c764, c730, c752, c729, c744, c728, c740, c738, c91, c1699, c1698, c81, c1503] c2222 (by decide) p (sat_cons (step735 p h) (sat_cons (step1812 p h) (sat_cons (step1814 p h) (sat_cons (step732 p h) (sat_cons (step764 p h) (sat_cons (step730 p h) (sat_cons (step752 p h) (sat_cons (step729 p h) (sat_cons (step744 p h) (sat_cons (step728 p h) (sat_cons (step740 p h) (sat_cons (step738 p h) (sat_cons (step91 p h) (sat_cons (step1699 p h) (sat_cons (step1698 p h) (sat_cons (step81 p h) (sat_cons (step1503 p h) (sat_nil p))))))))))))))))))
def c2223 : List Lit := [(873, true), (18, false), (5, true), (14, true), (20, false), (26, false), (92, true), (88, false), (108, true), (35, true), (65, false), (82, false)]
theorem step2223 (p : Nat → Bool) (h : Constraints p) : clause p c2223 = true :=
  Snake9.LocalRup.prove_clause [c907, c908, c402, c1870, c2165, c2222, c717, c714, c715, c713, c709, c710, c1612, c22, c1602] c2223 (by decide) p (sat_cons (step907 p h) (sat_cons (step908 p h) (sat_cons (step402 p h) (sat_cons (step1870 p h) (sat_cons (step2165 p h) (sat_cons (step2222 p h) (sat_cons (step717 p h) (sat_cons (step714 p h) (sat_cons (step715 p h) (sat_cons (step713 p h) (sat_cons (step709 p h) (sat_cons (step710 p h) (sat_cons (step1612 p h) (sat_cons (step22 p h) (sat_cons (step1602 p h) (sat_nil p))))))))))))))))
def c2224 : List Lit := [(871, true), (22, false), (21, false)]
theorem step2224 (p : Nat → Bool) (h : Constraints p) : clause p c2224 = true :=
  Snake9.LocalRup.prove_clause [c904, c905, c57] c2224 (by decide) p (sat_cons (step904 p h) (sat_cons (step905 p h) (sat_cons (step57 p h) (sat_nil p))))
def c2225 : List Lit := [(20, false), (864, true), (873, true), (26, false), (92, true), (88, false), (108, true), (35, true), (89, true), (65, false), (82, false)]
theorem step2225 (p : Nat → Bool) (h : Constraints p) : clause p c2225 = true :=
  Snake9.LocalRup.prove_clause [c1687, c45, c44, c2223, c894] c2225 (by decide) p (sat_cons (step1687 p h) (sat_cons (step45 p h) (sat_cons (step44 p h) (sat_cons (step2223 p h) (sat_cons (step894 p h) (sat_nil p))))))
def c2226 : List Lit := [(881, true), (21, false), (92, true), (88, false), (108, true), (35, true), (89, true), (65, false), (82, false)]
theorem step2226 (p : Nat → Bool) (h : Constraints p) : clause p c2226 = true :=
  Snake9.LocalRup.prove_clause [c1691, c2224, c912, c1690, c1615, c920, c913, c923, c907, c903, c402, c2225, c1765, c896, c278, c901, c893] c2226 (by decide) p (sat_cons (step1691 p h) (sat_cons (step2224 p h) (sat_cons (step912 p h) (sat_cons (step1690 p h) (sat_cons (step1615 p h) (sat_cons (step920 p h) (sat_cons (step913 p h) (sat_cons (step923 p h) (sat_cons (step907 p h) (sat_cons (step903 p h) (sat_cons (step402 p h) (sat_cons (step2225 p h) (sat_cons (step1765 p h) (sat_cons (step896 p h) (sat_cons (step278 p h) (sat_cons (step901 p h) (sat_cons (step893 p h) (sat_nil p))))))))))))))))))
def c2227 : List Lit := [(52, false), (54, true), (65, false), (71, false)]
theorem step2227 (p : Nat → Bool) (h : Constraints p) : clause p c2227 = true :=
  Snake9.LocalRup.prove_clause [c218, c1723] c2227 (by decide) p (sat_cons (step218 p h) (sat_cons (step1723 p h) (sat_nil p)))
def c2228 : List Lit := [(920, true), (43, true), (29, false), (35, true)]
theorem step2228 (p : Nat → Bool) (h : Constraints p) : clause p c2228 = true :=
  Snake9.LocalRup.prove_clause [c938, c946, c1657, c970, c940, c963, c1906, c954] c2228 (by decide) p (sat_cons (step938 p h) (sat_cons (step946 p h) (sat_cons (step1657 p h) (sat_cons (step970 p h) (sat_cons (step940 p h) (sat_cons (step963 p h) (sat_cons (step1906 p h) (sat_cons (step954 p h) (sat_nil p)))))))))
def c2229 : List Lit := [(20, false), (261, true), (854, true), (88, false), (89, true)]
theorem step2229 (p : Nat → Bool) (h : Constraints p) : clause p c2229 = true :=
  Snake9.LocalRup.prove_clause [c1687, c1950, c44] c2229 (by decide) p (sat_cons (step1687 p h) (sat_cons (step1950 p h) (sat_cons (step44 p h) (sat_nil p))))
def c2230 : List Lit := [(920, true), (1068, true), (99, true), (1055, false), (108, true), (35, true), (81, false), (1047, false)]
theorem step2230 (p : Nat → Bool) (h : Constraints p) : clause p c2230 = true :=
  Snake9.LocalRup.prove_clause [c938, c1657, c1665, c1619, c1609, c940, c1217, c955, c1222, c96, c1243, c1718, c1208, c615, c1203] c2230 (by decide) p (sat_cons (step938 p h) (sat_cons (step1657 p h) (sat_cons (step1665 p h) (sat_cons (step1619 p h) (sat_cons (step1609 p h) (sat_cons (step940 p h) (sat_cons (step1217 p h) (sat_cons (step955 p h) (sat_cons (step1222 p h) (sat_cons (step96 p h) (sat_cons (step1243 p h) (sat_cons (step1718 p h) (sat_cons (step1208 p h) (sat_cons (step615 p h) (sat_cons (step1203 p h) (sat_nil p))))))))))))))))
def c2231 : List Lit := [(944, true), (88, false), (63, false), (65, false), (71, false)]
theorem step2231 (p : Nat → Bool) (h : Constraints p) : clause p c2231 = true :=
  Snake9.LocalRup.prove_clause [c1833, c1861, c1003, c985, c218, c2227, c1722, c155, c191, c994] c2231 (by decide) p (sat_cons (step1833 p h) (sat_cons (step1861 p h) (sat_cons (step1003 p h) (sat_cons (step985 p h) (sat_cons (step218 p h) (sat_cons (step2227 p h) (sat_cons (step1722 p h) (sat_cons (step155 p h) (sat_cons (step191 p h) (sat_cons (step994 p h) (sat_nil p)))))))))))
def c2232 : List Lit := [(1105, false), (954, false), (89, true), (88, false), (1001, false), (82, false)]
theorem step2232 (p : Nat → Bool) (h : Constraints p) : clause p c2232 = true :=
  Snake9.LocalRup.prove_clause [c1162, c1351, c1855, c1058, c2013, c2220, c1051, c1123, c1854, c1126, c1357, c1134, c1163] c2232 (by decide) p (sat_cons (step1162 p h) (sat_cons (step1351 p h) (sat_cons (step1855 p h) (sat_cons (step1058 p h) (sat_cons (step2013 p h) (sat_cons (step2220 p h) (sat_cons (step1051 p h) (sat_cons (step1123 p h) (sat_cons (step1854 p h) (sat_cons (step1126 p h) (sat_cons (step1357 p h) (sat_cons (step1134 p h) (sat_cons (step1163 p h) (sat_nil p))))))))))))))
def c2233 : List Lit := [(1052, true), (99, false), (89, true), (88, false), (94, true)]
theorem step2233 (p : Nat → Bool) (h : Constraints p) : clause p c2233 = true :=
  Snake9.LocalRup.prove_clause [c1199, c1209, c1207, c1200, c1201, c401, c382, c1784] c2233 (by decide) p (sat_cons (step1199 p h) (sat_cons (step1209 p h) (sat_cons (step1207 p h) (sat_cons (step1200 p h) (sat_cons (step1201 p h) (sat_cons (step401 p h) (sat_cons (step382 p h) (sat_cons (step1784 p h) (sat_nil p)))))))))
def c2234 : List Lit := [(108, false), (65, false), (71, false), (86, false)]
theorem step2234 (p : Nat → Bool) (h : Constraints p) : clause p c2234 = true :=
  Snake9.LocalRup.prove_clause [c488, c1919] c2234 (by decide) p (sat_cons (step488 p h) (sat_cons (step1919 p h) (sat_nil p)))
def c2235 : List Lit := [(939, true), (55, true), (63, false)]
theorem step2235 (p : Nat → Bool) (h : Constraints p) : clause p c2235 = true :=
  Snake9.LocalRup.prove_clause [c993, c1003, c1001, c994, c995, c996, c173, c1737, c182] c2235 (by decide) p (sat_cons (step993 p h) (sat_cons (step1003 p h) (sat_cons (step1001 p h) (sat_cons (step994 p h) (sat_cons (step995 p h) (sat_cons (step996 p h) (sat_cons (step173 p h) (sat_cons (step1737 p h) (sat_cons (step182 p h) (sat_nil p))))))))))
def c2236 : List Lit := [(919, true), (113, false), (81, false)]
theorem step2236 (p : Nat → Bool) (h : Constraints p) : clause p c2236 = true :=
  Snake9.LocalRup.prove_clause [c1605, c1632, c939, c955, c98, c616, c1718] c2236 (by decide) p (sat_cons (step1605 p h) (sat_cons (step1632 p h) (sat_cons (step939 p h) (sat_cons (step955 p h) (sat_cons (step98 p h) (sat_cons (step616 p h) (sat_cons (step1718 p h) (sat_nil p))))))))
def c2237 : List Lit := [(945, false), (975, true), (919, false)]
theorem step2237 (p : Nat → Bool) (h : Constraints p) : clause p c2237 = true :=
  Snake9.LocalRup.prove_clause [c2187, c1028, c1980] c2237 (by decide) p (sat_cons (step2187 p h) (sat_cons (step1028 p h) (sat_cons (step1980 p h) (sat_nil p))))
def c2238 : List Lit := [(890, true), (865, false)]
theorem step2238 (p : Nat → Bool) (h : Constraints p) : clause p c2238 = true :=
  Snake9.LocalRup.prove_clause [c898, c918, c1828, c931, c1618, c1888] c2238 (by decide) p (sat_cons (step898 p h) (sat_cons (step918 p h) (sat_cons (step1828 p h) (sat_cons (step931 p h) (sat_cons (step1618 p h) (sat_cons (step1888 p h) (sat_nil p)))))))
def c2239 : List Lit := [(14, false), (22, false), (21, false), (84, false), (867, false), (892, true)]
theorem step2239 (p : Nat → Bool) (h : Constraints p) : clause p c2239 = true :=
  Snake9.LocalRup.prove_clause [c55, c54, c25, c906, c1683, c914, c1888, c920, c933] c2239 (by decide) p (sat_cons (step55 p h) (sat_cons (step54 p h) (sat_cons (step25 p h) (sat_cons (step906 p h) (sat_cons (step1683 p h) (sat_cons (step914 p h) (sat_cons (step1888 p h) (sat_cons (step920 p h) (sat_cons (step933 p h) (sat_nil p))))))))))
def c2240 : List Lit := [(938, true), (63, false)]
theorem step2240 (p : Nat → Bool) (h : Constraints p) : clause p c2240 = true :=
  Snake9.LocalRup.prove_clause [c998, c1000, c995, c996, c992, c173, c1737, c182] c2240 (by decide) p (sat_cons (step998 p h) (sat_cons (step1000 p h) (sat_cons (step995 p h) (sat_cons (step996 p h) (sat_cons (step992 p h) (sat_cons (step173 p h) (sat_cons (step1737 p h) (sat_cons (step182 p h) (sat_nil p)))))))))
def c2241 : List Lit := [(92, true), (21, false), (881, true), (865, false), (892, true), (102, true), (82, false)]
theorem step2241 (p : Nat → Bool) (h : Constraints p) : clause p c2241 = true :=
  Snake9.LocalRup.prove_clause [c898, c1765, c1691, c2224, c2239, c912, c893, c923, c901] c2241 (by decide) p (sat_cons (step898 p h) (sat_cons (step1765 p h) (sat_cons (step1691 p h) (sat_cons (step2224 p h) (sat_cons (step2239 p h) (sat_cons (step912 p h) (sat_cons (step893 p h) (sat_cons (step923 p h) (sat_cons (step901 p h) (sat_nil p))))))))))
def c2242 : List Lit := [(92, false), (931, false), (975, true), (919, false), (115, false), (82, false)]
theorem step2242 (p : Nat → Bool) (h : Constraints p) : clause p c2242 = true :=
  Snake9.LocalRup.prove_clause [c356, c362, c2021, c992, c1058, c1000, c1027, c1012] c2242 (by decide) p (sat_cons (step356 p h) (sat_cons (step362 p h) (sat_cons (step2021 p h) (sat_cons (step992 p h) (sat_cons (step1058 p h) (sat_cons (step1000 p h) (sat_cons (step1027 p h) (sat_cons (step1012 p h) (sat_nil p)))))))))
def c2243 : List Lit := [(1101, true), (1052, false), (123, true), (120, false), (89, false), (1072, true), (1079, false), (115, false), (1089, false), (1075, false), (1010, true)]
theorem step2243 (p : Nat → Bool) (h : Constraints p) : clause p c2243 = true :=
  Snake9.LocalRup.prove_clause [c1110, c1109, c1324, c1237, c1660, c286, c1878, c2202, c1236, c599, c1317, c1267, c1283, c1272] c2243 (by decide) p (sat_cons (step1110 p h) (sat_cons (step1109 p h) (sat_cons (step1324 p h) (sat_cons (step1237 p h) (sat_cons (step1660 p h) (sat_cons (step286 p h) (sat_cons (step1878 p h) (sat_cons (step2202 p h) (sat_cons (step1236 p h) (sat_cons (step599 p h) (sat_cons (step1317 p h) (sat_cons (step1267 p h) (sat_cons (step1283 p h) (sat_cons (step1272 p h) (sat_nil p)))))))))))))))
def c2244 : List Lit := [(55, true), (1004, true), (944, true), (1072, true), (80, false), (86, false)]
theorem step2244 (p : Nat → Bool) (h : Constraints p) : clause p c2244 = true :=
  Snake9.LocalRup.prove_clause [c1861, c985, c1833, c1003, c993, c2235, c994, c1001, c1071, c995, c996, c1095, c182, c1737, c1734, c174, c248, c1079, c1635, c1084, c1075, c1877, c1747] c2244 (by decide) p (sat_cons (step1861 p h) (sat_cons (step985 p h) (sat_cons (step1833 p h) (sat_cons (step1003 p h) (sat_cons (step993 p h) (sat_cons (step2235 p h) (sat_cons (step994 p h) (sat_cons (step1001 p h) (sat_cons (step1071 p h) (sat_cons (step995 p h) (sat_cons (step996 p h) (sat_cons (step1095 p h) (sat_cons (step182 p h) (sat_cons (step1737 p h) (sat_cons (step1734 p h) (sat_cons (step174 p h) (sat_cons (step248 p h) (sat_cons (step1079 p h) (sat_cons (step1635 p h) (sat_cons (step1084 p h) (sat_cons (step1075 p h) (sat_cons (step1877 p h) (sat_cons (step1747 p h) (sat_nil p))))))))))))))))))))))))
def c2245 : List Lit := [(76, true), (74, false), (80, false)]
theorem step2245 (p : Nat → Bool) (h : Constraints p) : clause p c2245 = true :=
  Snake9.LocalRup.prove_clause [c1755, c1754, c1519] c2245 (by decide) p (sat_cons (step1755 p h) (sat_cons (step1754 p h) (sat_cons (step1519 p h) (sat_nil p))))
def c2246 : List Lit := [(393, false), (55, false), (63, true), (53, false), (89, false)]
theorem step2246 (p : Nat → Bool) (h : Constraints p) : clause p c2246 = true :=
  Snake9.LocalRup.prove_clause [c792, c1817, c816, c782, c861, c772, c1827, c771, c766, c198, c763, c1725, c1726, c762, c157, c755, c1720, c754, c2169, c753] c2246 (by decide) p (sat_cons (step792 p h) (sat_cons (step1817 p h) (sat_cons (step816 p h) (sat_cons (step782 p h) (sat_cons (step861 p h) (sat_cons (step772 p h) (sat_cons (step1827 p h) (sat_cons (step771 p h) (sat_cons (step766 p h) (sat_cons (step198 p h) (sat_cons (step763 p h) (sat_cons (step1725 p h) (sat_cons (step1726 p h) (sat_cons (step762 p h) (sat_cons (step157 p h) (sat_cons (step755 p h) (sat_cons (step1720 p h) (sat_cons (step754 p h) (sat_cons (step2169 p h) (sat_cons (step753 p h) (sat_nil p)))))))))))))))))))))
def c2247 : List Lit := [(996, false), (1004, true), (63, true), (52, false), (1072, true), (86, false)]
theorem step2247 (p : Nat → Bool) (h : Constraints p) : clause p c2247 = true :=
  Snake9.LocalRup.prove_clause [c1071, c1095, c1635, c1084, c1075, c1877, c1747] c2247 (by decide) p (sat_cons (step1071 p h) (sat_cons (step1095 p h) (sat_cons (step1635 p h) (sat_cons (step1084 p h) (sat_cons (step1075 p h) (sat_cons (step1877 p h) (sat_cons (step1747 p h) (sat_nil p))))))))
def c2248 : List Lit := [(1003, true), (995, false), (63, true), (52, false), (1072, true), (86, false)]
theorem step2248 (p : Nat → Bool) (h : Constraints p) : clause p c2248 = true :=
  Snake9.LocalRup.prove_clause [c1080, c1071, c1098, c1094, c1072, c1083, c1067, c1075, c1966, c1877] c2248 (by decide) p (sat_cons (step1080 p h) (sat_cons (step1071 p h) (sat_cons (step1098 p h) (sat_cons (step1094 p h) (sat_cons (step1072 p h) (sat_cons (step1083 p h) (sat_cons (step1067 p h) (sat_cons (step1075 p h) (sat_cons (step1966 p h) (sat_cons (step1877 p h) (sat_nil p)))))))))))
def c2249 : List Lit := [(1037, true), (76, true), (75, true), (1021, false), (63, true), (1025, false), (52, false), (1072, true), (86, false)]
theorem step2249 (p : Nat → Bool) (h : Constraints p) : clause p c2249 = true :=
  Snake9.LocalRup.prove_clause [c1077, c2248, c1186, c1180, c2247, c1140, c1079, c1114, c2245, c1107] c2249 (by decide) p (sat_cons (step1077 p h) (sat_cons (step2248 p h) (sat_cons (step1186 p h) (sat_cons (step1180 p h) (sat_cons (step2247 p h) (sat_cons (step1140 p h) (sat_cons (step1079 p h) (sat_cons (step1114 p h) (sat_cons (step2245 p h) (sat_cons (step1107 p h) (sat_nil p)))))))))))
def c2250 : List Lit := [(1047, false), (1102, true), (1060, false), (73, false), (1008, true), (1071, false), (99, true)]
theorem step2250 (p : Nat → Bool) (h : Constraints p) : clause p c2250 = true :=
  Snake9.LocalRup.prove_clause [c1256, c2205, c1282, c1331, c1242, c1106, c1202, c1207, c1208, c1237, c1203, c1325, c1286, c1283, c1257, c1947, c1252, c1763, c230] c2250 (by decide) p (sat_cons (step1256 p h) (sat_cons (step2205 p h) (sat_cons (step1282 p h) (sat_cons (step1331 p h) (sat_cons (step1242 p h) (sat_cons (step1106 p h) (sat_cons (step1202 p h) (sat_cons (step1207 p h) (sat_cons (step1208 p h) (sat_cons (step1237 p h) (sat_cons (step1203 p h) (sat_cons (step1325 p h) (sat_cons (step1286 p h) (sat_cons (step1283 p h) (sat_cons (step1257 p h) (sat_cons (step1947 p h) (sat_cons (step1252 p h) (sat_cons (step1763 p h) (sat_cons (step230 p h) (sat_nil p))))))))))))))))))))
end B112E153
