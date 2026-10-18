import B112E260Part0015
namespace B112E260
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c3127 : List Lit := [(899, true), (881, false), (855, false), (11, false), (872, false), (1, false)]
theorem step3127 (p : Nat → Bool) (h : Constraints p) : clause p c3127 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1222, c2651, c1261, c1266, c1227, c1169, c1194, c1165, c1185, c2911] c3127 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1222 p h) (sat_cons (step2651 p h) (sat_cons (step1261 p h) (sat_cons (step1266 p h) (sat_cons (step1227 p h) (sat_cons (step1169 p h) (sat_cons (step1194 p h) (sat_cons (step1165 p h) (sat_cons (step1185 p h) (sat_cons (step2911 p h) (sat_nil p))))))))))))
def c3128 : List Lit := [(1120, true), (881, false), (918, false), (855, false), (62, false), (78, true), (37, true), (11, false), (51, true), (1011, false), (92, true), (872, false), (81, true), (1, false)]
theorem step3128 (p : Nat → Bool) (h : Constraints p) : clause p c3128 = true :=
  Snake9.LocalRup.prove_clause [c1505, c3097, c3125, c1136, c1534, c3117, c2488, c2669, c81, c88, c91, c85, c1000, c3042, c1157, c2347, c2379, c1185, c353, c997, c2496, c1165, c2984, c1194, c972, c1169, c1354, c1227, c954, c1267, c948, c1453, c947, c1393, c234, c1306, c1279, c1281] c3128 (by decide) p (sat_cons (step1505 p h) (sat_cons (step3097 p h) (sat_cons (step3125 p h) (sat_cons (step1136 p h) (sat_cons (step1534 p h) (sat_cons (step3117 p h) (sat_cons (step2488 p h) (sat_cons (step2669 p h) (sat_cons (step81 p h) (sat_cons (step88 p h) (sat_cons (step91 p h) (sat_cons (step85 p h) (sat_cons (step1000 p h) (sat_cons (step3042 p h) (sat_cons (step1157 p h) (sat_cons (step2347 p h) (sat_cons (step2379 p h) (sat_cons (step1185 p h) (sat_cons (step353 p h) (sat_cons (step997 p h) (sat_cons (step2496 p h) (sat_cons (step1165 p h) (sat_cons (step2984 p h) (sat_cons (step1194 p h) (sat_cons (step972 p h) (sat_cons (step1169 p h) (sat_cons (step1354 p h) (sat_cons (step1227 p h) (sat_cons (step954 p h) (sat_cons (step1267 p h) (sat_cons (step948 p h) (sat_cons (step1453 p h) (sat_cons (step947 p h) (sat_cons (step1393 p h) (sat_cons (step234 p h) (sat_cons (step1306 p h) (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c3129 : List Lit := [(881, false), (918, false), (855, false), (62, false), (78, true), (37, true), (11, false), (51, true), (1011, false), (92, true), (872, false), (81, true), (1, false)]
theorem step3129 (p : Nat → Bool) (h : Constraints p) : clause p c3129 = true :=
  Snake9.LocalRup.prove_clause [c1320, c1323, c1349, c1301, c1384, c3127, c3128, c2494, c1451, c1446, c3126, c1385, c353, c1354, c2994] c3129 (by decide) p (sat_cons (step1320 p h) (sat_cons (step1323 p h) (sat_cons (step1349 p h) (sat_cons (step1301 p h) (sat_cons (step1384 p h) (sat_cons (step3127 p h) (sat_cons (step3128 p h) (sat_cons (step2494 p h) (sat_cons (step1451 p h) (sat_cons (step1446 p h) (sat_cons (step3126 p h) (sat_cons (step1385 p h) (sat_cons (step353 p h) (sat_cons (step1354 p h) (sat_cons (step2994 p h) (sat_nil p))))))))))))))))
def c3130 : List Lit := [(918, false), (855, false), (62, false), (78, true), (37, true), (11, false), (51, true), (1011, false), (92, true), (872, false), (81, true), (1, false)]
theorem step3130 (p : Nat → Bool) (h : Constraints p) : clause p c3130 = true :=
  Snake9.LocalRup.prove_clause [c1301, c3129, c1204, c1202, c79, c83, c90, c89, c86, c1157, c3117, c353, c1185, c1165, c3125, c2994, c1194, c1169, c2494, c1354, c1226, c1266, c1446, c1385] c3130 (by decide) p (sat_cons (step1301 p h) (sat_cons (step3129 p h) (sat_cons (step1204 p h) (sat_cons (step1202 p h) (sat_cons (step79 p h) (sat_cons (step83 p h) (sat_cons (step90 p h) (sat_cons (step89 p h) (sat_cons (step86 p h) (sat_cons (step1157 p h) (sat_cons (step3117 p h) (sat_cons (step353 p h) (sat_cons (step1185 p h) (sat_cons (step1165 p h) (sat_cons (step3125 p h) (sat_cons (step2994 p h) (sat_cons (step1194 p h) (sat_cons (step1169 p h) (sat_cons (step2494 p h) (sat_cons (step1354 p h) (sat_cons (step1226 p h) (sat_cons (step1266 p h) (sat_cons (step1446 p h) (sat_cons (step1385 p h) (sat_nil p)))))))))))))))))))))))))
def c3131 : List Lit := [(5, false), (4, false), (3, false), (2, false), (1, false)]
theorem step3131 (p : Nat → Bool) (h : Constraints p) : clause p c3131 = true :=
  Snake9.TreeRup.prove_clause [c18, c16, c17, c26, c27, c30, c29, c32, c33, c1287, c1189, c2422, c1503, c378, c1294, c1191, c1505, c1320, c1221, c3005, c1153, c3112, c2, c3, c3122, c3124, c1154, c2651, c1259, c3130, c1297, c1295, c1288, c1289, c1290, c305, c340, c331, c962, c326, c963, c1334, c966, c2460, c970, c959, c997, c958, c1000, c299, c2488, c257, c253, c256, c1136, c1332, c1278, c1317, c3097, c1340, c1281, c1326, c2494, c1356, c1305, c1434, c1387] c3131 (by decide) p (sat_cons (step18 p h) (sat_cons (step16 p h) (sat_cons (step17 p h) (sat_cons (step26 p h) (sat_cons (step27 p h) (sat_cons (step30 p h) (sat_cons (step29 p h) (sat_cons (step32 p h) (sat_cons (step33 p h) (sat_cons (step1287 p h) (sat_cons (step1189 p h) (sat_cons (step2422 p h) (sat_cons (step1503 p h) (sat_cons (step378 p h) (sat_cons (step1294 p h) (sat_cons (step1191 p h) (sat_cons (step1505 p h) (sat_cons (step1320 p h) (sat_cons (step1221 p h) (sat_cons (step3005 p h) (sat_cons (step1153 p h) (sat_cons (step3112 p h) (sat_cons (step2 p h) (sat_cons (step3 p h) (sat_cons (step3122 p h) (sat_cons (step3124 p h) (sat_cons (step1154 p h) (sat_cons (step2651 p h) (sat_cons (step1259 p h) (sat_cons (step3130 p h) (sat_cons (step1297 p h) (sat_cons (step1295 p h) (sat_cons (step1288 p h) (sat_cons (step1289 p h) (sat_cons (step1290 p h) (sat_cons (step305 p h) (sat_cons (step340 p h) (sat_cons (step331 p h) (sat_cons (step962 p h) (sat_cons (step326 p h) (sat_cons (step963 p h) (sat_cons (step1334 p h) (sat_cons (step966 p h) (sat_cons (step2460 p h) (sat_cons (step970 p h) (sat_cons (step959 p h) (sat_cons (step997 p h) (sat_cons (step958 p h) (sat_cons (step1000 p h) (sat_cons (step299 p h) (sat_cons (step2488 p h) (sat_cons (step257 p h) (sat_cons (step253 p h) (sat_cons (step256 p h) (sat_cons (step1136 p h) (sat_cons (step1332 p h) (sat_cons (step1278 p h) (sat_cons (step1317 p h) (sat_cons (step3097 p h) (sat_cons (step1340 p h) (sat_cons (step1281 p h) (sat_cons (step1326 p h) (sat_cons (step2494 p h) (sat_cons (step1356 p h) (sat_cons (step1305 p h) (sat_cons (step1434 p h) (sat_cons (step1387 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c3132 : List Lit := [(12, true), (857, true), (898, true), (47, true), (50, false), (874, false), (11, true), (851, false)]
theorem step3132 (p : Nat → Bool) (h : Constraints p) : clause p c3132 = true :=
  Snake9.LocalRup.prove_clause [c1155, c1157, c1158, c2628, c1171, c1205, c1253, c1223] c3132 (by decide) p (sat_cons (step1155 p h) (sat_cons (step1157 p h) (sat_cons (step1158 p h) (sat_cons (step2628 p h) (sat_cons (step1171 p h) (sat_cons (step1205 p h) (sat_cons (step1253 p h) (sat_cons (step1223 p h) (sat_nil p)))))))))
def c3133 : List Lit := [(928, true), (50, false), (37, true), (175, true), (11, true)]
theorem step3133 (p : Nat → Bool) (h : Constraints p) : clause p c3133 = true :=
  Snake9.LocalRup.prove_clause [c1317, c1318, c350, c365] c3133 (by decide) p (sat_cons (step1317 p h) (sat_cons (step1318 p h) (sat_cons (step350 p h) (sat_cons (step365 p h) (sat_nil p)))))
def c3134 : List Lit := [(918, false), (13, false), (47, false), (10, false), (923, true), (957, true), (940, false)]
theorem step3134 (p : Nat → Bool) (h : Constraints p) : clause p c3134 = true :=
  Snake9.LocalRup.prove_clause [c2071, c1321, c1301, c1306, c1387, c1281, c1360, c1278, c1329, c342, c3007, c1319] c3134 (by decide) p (sat_cons (step2071 p h) (sat_cons (step1321 p h) (sat_cons (step1301 p h) (sat_cons (step1306 p h) (sat_cons (step1387 p h) (sat_cons (step1281 p h) (sat_cons (step1360 p h) (sat_cons (step1278 p h) (sat_cons (step1329 p h) (sat_cons (step342 p h) (sat_cons (step3007 p h) (sat_cons (step1319 p h) (sat_nil p)))))))))))))
def c3135 : List Lit := [(930, false), (956, true), (918, false), (933, true), (37, false), (940, false), (1, false)]
theorem step3135 (p : Nat → Bool) (h : Constraints p) : clause p c3135 = true :=
  Snake9.LocalRup.prove_clause [c1323, c1326, c1350, c1318, c1393, c244, c1306, c1278, c1281] c3135 (by decide) p (sat_cons (step1323 p h) (sat_cons (step1326 p h) (sat_cons (step1350 p h) (sat_cons (step1318 p h) (sat_cons (step1393 p h) (sat_cons (step244 p h) (sat_cons (step1306 p h) (sat_cons (step1278 p h) (sat_cons (step1281 p h) (sat_nil p))))))))))
def c3136 : List Lit := [(933, false), (956, true), (910, false), (173, true), (913, false), (41, true), (9, true)]
theorem step3136 (p : Nat → Bool) (h : Constraints p) : clause p c3136 = true :=
  Snake9.LocalRup.prove_clause [c1294, c1305, c1386, c1354, c1355, c1393, c1337, c1306, c1334, c1295, c2924] c3136 (by decide) p (sat_cons (step1294 p h) (sat_cons (step1305 p h) (sat_cons (step1386 p h) (sat_cons (step1354 p h) (sat_cons (step1355 p h) (sat_cons (step1393 p h) (sat_cons (step1337 p h) (sat_cons (step1306 p h) (sat_cons (step1334 p h) (sat_cons (step1295 p h) (sat_cons (step2924 p h) (sat_nil p))))))))))))
def c3137 : List Lit := [(349, true), (933, true), (37, true), (41, true), (11, true)]
theorem step3137 (p : Nat → Bool) (h : Constraints p) : clause p c3137 = true :=
  Snake9.LocalRup.prove_clause [c979, c980, c977, c976, c380, c3006] c3137 (by decide) p (sat_cons (step979 p h) (sat_cons (step980 p h) (sat_cons (step977 p h) (sat_cons (step976 p h) (sat_cons (step380 p h) (sat_cons (step3006 p h) (sat_nil p)))))))
def c3138 : List Lit := [(941, true), (6, false), (24, false), (151, true), (62, true)]
theorem step3138 (p : Nat → Bool) (h : Constraints p) : clause p c3138 = true :=
  Snake9.LocalRup.prove_clause [c2654, c2882, c190, c2324] c3138 (by decide) p (sat_cons (step2654 p h) (sat_cons (step2882 p h) (sat_cons (step190 p h) (sat_cons (step2324 p h) (sat_nil p)))))
def c3139 : List Lit := [(917, true), (43, false), (7, false)]
theorem step3139 (p : Nat → Bool) (h : Constraints p) : clause p c3139 = true :=
  Snake9.LocalRup.prove_clause [c1292, c1294, c1289, c1286, c300] c3139 (by decide) p (sat_cons (step1292 p h) (sat_cons (step1294 p h) (sat_cons (step1289 p h) (sat_cons (step1286 p h) (sat_cons (step300 p h) (sat_nil p))))))
def c3140 : List Lit := [(44, true), (918, true), (43, false), (7, false)]
theorem step3140 (p : Nat → Bool) (h : Constraints p) : clause p c3140 = true :=
  Snake9.LocalRup.prove_clause [c1293, c1290, c1291, c1295, c300, c1286] c3140 (by decide) p (sat_cons (step1293 p h) (sat_cons (step1290 p h) (sat_cons (step1291 p h) (sat_cons (step1295 p h) (sat_cons (step300 p h) (sat_cons (step1286 p h) (sat_nil p)))))))
def c3141 : List Lit := [(917, true), (173, true), (7, false), (40, false), (9, true)]
theorem step3141 (p : Nat → Bool) (h : Constraints p) : clause p c3141 = true :=
  Snake9.LocalRup.prove_clause [c1292, c3139, c1289, c2656] c3141 (by decide) p (sat_cons (step1292 p h) (sat_cons (step3139 p h) (sat_cons (step1289 p h) (sat_cons (step2656 p h) (sat_nil p)))))
def c3142 : List Lit := [(44, true), (918, true), (173, true), (7, false), (40, false), (9, true)]
theorem step3142 (p : Nat → Bool) (h : Constraints p) : clause p c3142 = true :=
  Snake9.LocalRup.prove_clause [c1293, c3140, c1291, c2656] c3142 (by decide) p (sat_cons (step1293 p h) (sat_cons (step3140 p h) (sat_cons (step1291 p h) (sat_cons (step2656 p h) (sat_nil p)))))
def c3143 : List Lit := [(23, false), (32, false), (878, true), (6, false)]
theorem step3143 (p : Nat → Bool) (h : Constraints p) : clause p c3143 = true :=
  Snake9.LocalRup.prove_clause [c173, c175, c1200] c3143 (by decide) p (sat_cons (step173 p h) (sat_cons (step175 p h) (sat_cons (step1200 p h) (sat_nil p))))
def c3144 : List Lit := [(917, true), (173, true), (41, true), (9, true)]
theorem step3144 (p : Nat → Bool) (h : Constraints p) : clause p c3144 = true :=
  Snake9.LocalRup.prove_clause [c1292, c1289, c2636, c339] c3144 (by decide) p (sat_cons (step1292 p h) (sat_cons (step1289 p h) (sat_cons (step2636 p h) (sat_cons (step339 p h) (sat_nil p)))))
def c3145 : List Lit := [(6, false), (878, true), (32, false), (133, true), (151, true), (44, false), (25, true)]
theorem step3145 (p : Nat → Bool) (h : Constraints p) : clause p c3145 = true :=
  Snake9.LocalRup.prove_clause [c3143, c191, c2630, c1200] c3145 (by decide) p (sat_cons (step3143 p h) (sat_cons (step191 p h) (sat_cons (step2630 p h) (sat_cons (step1200 p h) (sat_nil p)))))
def c3146 : List Lit := [(908, true), (933, true), (347, false), (37, true), (11, true)]
theorem step3146 (p : Nat → Bool) (h : Constraints p) : clause p c3146 = true :=
  Snake9.LocalRup.prove_clause [c979, c982, c993, c995, c2464, c943, c908, c904, c901, c900, c2463, c972, c954, c948, c947, c2462, c976, c1278, c1279, c234, c2347, c138, c2378, c365, c347, c348, c1317, c1321, c1326] c3146 (by decide) p (sat_cons (step979 p h) (sat_cons (step982 p h) (sat_cons (step993 p h) (sat_cons (step995 p h) (sat_cons (step2464 p h) (sat_cons (step943 p h) (sat_cons (step908 p h) (sat_cons (step904 p h) (sat_cons (step901 p h) (sat_cons (step900 p h) (sat_cons (step2463 p h) (sat_cons (step972 p h) (sat_cons (step954 p h) (sat_cons (step948 p h) (sat_cons (step947 p h) (sat_cons (step2462 p h) (sat_cons (step976 p h) (sat_cons (step1278 p h) (sat_cons (step1279 p h) (sat_cons (step234 p h) (sat_cons (step2347 p h) (sat_cons (step138 p h) (sat_cons (step2378 p h) (sat_cons (step365 p h) (sat_cons (step347 p h) (sat_cons (step348 p h) (sat_cons (step1317 p h) (sat_cons (step1321 p h) (sat_cons (step1326 p h) (sat_nil p))))))))))))))))))))))))))))))
def c3147 : List Lit := [(48, false), (36, false), (933, true), (175, true), (37, true), (11, true)]
theorem step3147 (p : Nat → Bool) (h : Constraints p) : clause p c3147 = true :=
  Snake9.LocalRup.prove_clause [c365, c347, c348, c1317, c1321, c1326] c3147 (by decide) p (sat_cons (step365 p h) (sat_cons (step347 p h) (sat_cons (step348 p h) (sat_cons (step1317 p h) (sat_cons (step1321 p h) (sat_cons (step1326 p h) (sat_nil p)))))))
def c3148 : List Lit := [(48, true), (870, true), (53, false), (42, false), (929, true), (142, true), (11, true)]
theorem step3148 (p : Nat → Bool) (h : Constraints p) : clause p c3148 = true :=
  Snake9.LocalRup.prove_clause [c2378, c1319, c138, c384, c1186] c3148 (by decide) p (sat_cons (step2378 p h) (sat_cons (step1319 p h) (sat_cons (step138 p h) (sat_cons (step384 p h) (sat_cons (step1186 p h) (sat_nil p))))))
def c3149 : List Lit := [(877, true), (6, false), (151, true), (62, false)]
theorem step3149 (p : Nat → Bool) (h : Constraints p) : clause p c3149 = true :=
  Snake9.LocalRup.prove_clause [c1198, c1199, c172, c2940] c3149 (by decide) p (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step172 p h) (sat_cons (step2940 p h) (sat_nil p)))))
def c3150 : List Lit := [(51, true), (857, true), (137, true), (139, true), (933, true), (11, true), (5, true)]
theorem step3150 (p : Nat → Bool) (h : Constraints p) : clause p c3150 = true :=
  Snake9.LocalRup.prove_clause [c1320, c2341, c1326, c123, c2635, c1157] c3150 (by decide) p (sat_cons (step1320 p h) (sat_cons (step2341 p h) (sat_cons (step1326 p h) (sat_cons (step123 p h) (sat_cons (step2635 p h) (sat_cons (step1157 p h) (sat_nil p)))))))
def c3151 : List Lit := [(6, false), (1017, true)]
theorem step3151 (p : Nat → Bool) (h : Constraints p) : clause p c3151 = true :=
  Snake9.LocalRup.prove_clause [c2408, c2409, c1513] c3151 (by decide) p (sat_cons (step2408 p h) (sat_cons (step2409 p h) (sat_cons (step1513 p h) (sat_nil p))))
def c3152 : List Lit := [(877, true), (32, false), (151, true), (62, false)]
theorem step3152 (p : Nat → Bool) (h : Constraints p) : clause p c3152 = true :=
  Snake9.LocalRup.prove_clause [c1198, c1199, c178, c2940] c3152 (by decide) p (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step178 p h) (sat_cons (step2940 p h) (sat_nil p)))))
def c3153 : List Lit := [(908, true), (161, true), (175, true), (142, true), (933, true), (37, true), (11, true)]
theorem step3153 (p : Nat → Bool) (h : Constraints p) : clause p c3153 = true :=
  Snake9.LocalRup.prove_clause [c1278, c1279, c3147, c234, c2378, c2347, c138] c3153 (by decide) p (sat_cons (step1278 p h) (sat_cons (step1279 p h) (sat_cons (step3147 p h) (sat_cons (step234 p h) (sat_cons (step2378 p h) (sat_cons (step2347 p h) (sat_cons (step138 p h) (sat_nil p))))))))
def c3154 : List Lit := [(932, true), (175, true), (37, true), (11, true)]
theorem step3154 (p : Nat → Bool) (h : Constraints p) : clause p c3154 = true :=
  Snake9.LocalRup.prove_clause [c1323, c1325, c1321, c3133] c3154 (by decide) p (sat_cons (step1323 p h) (sat_cons (step1325 p h) (sat_cons (step1321 p h) (sat_cons (step3133 p h) (sat_nil p)))))
def c3155 : List Lit := [(10, false), (47, false), (137, true), (933, true), (11, true)]
theorem step3155 (p : Nat → Bool) (h : Constraints p) : clause p c3155 = true :=
  Snake9.LocalRup.prove_clause [c2635, c76, c2071, c1326, c1321] c3155 (by decide) p (sat_cons (step2635 p h) (sat_cons (step76 p h) (sat_cons (step2071 p h) (sat_cons (step1326 p h) (sat_cons (step1321 p h) (sat_nil p))))))
def c3156 : List Lit := [(941, true), (32, false), (24, false), (151, true), (62, true)]
theorem step3156 (p : Nat → Bool) (h : Constraints p) : clause p c3156 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1340, c2654, c1331, c190, c180] c3156 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1340 p h) (sat_cons (step2654 p h) (sat_cons (step1331 p h) (sat_cons (step190 p h) (sat_cons (step180 p h) (sat_nil p)))))))
def c3157 : List Lit := [(918, false), (24, false), (908, false), (910, false), (932, false), (957, true), (151, true), (62, true)]
theorem step3157 (p : Nat → Bool) (h : Constraints p) : clause p c3157 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1337, c1350, c1400, c1311, c1306, c1284, c1394, c3156, c1351] c3157 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1337 p h) (sat_cons (step1350 p h) (sat_cons (step1400 p h) (sat_cons (step1311 p h) (sat_cons (step1306 p h) (sat_cons (step1284 p h) (sat_cons (step1394 p h) (sat_cons (step3156 p h) (sat_cons (step1351 p h) (sat_nil p)))))))))))
def c3158 : List Lit := [(922, false), (863, false), (32, false), (879, false), (933, false), (977, true), (151, true), (62, true), (874, false)]
theorem step3158 (p : Nat → Bool) (h : Constraints p) : clause p c3158 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1222, c1252, c1434, c1335, c1337, c1355, c1386, c1387, c1440, c1356, c1253, c3156, c1223, c1199, c1207] c3158 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1222 p h) (sat_cons (step1252 p h) (sat_cons (step1434 p h) (sat_cons (step1335 p h) (sat_cons (step1337 p h) (sat_cons (step1355 p h) (sat_cons (step1386 p h) (sat_cons (step1387 p h) (sat_cons (step1440 p h) (sat_cons (step1356 p h) (sat_cons (step1253 p h) (sat_cons (step3156 p h) (sat_cons (step1223 p h) (sat_cons (step1199 p h) (sat_cons (step1207 p h) (sat_nil p)))))))))))))))))
def c3159 : List Lit := [(923, false), (6, false), (879, false), (933, false), (977, true), (151, true), (62, true), (874, false), (862, false)]
theorem step3159 (p : Nat → Bool) (h : Constraints p) : clause p c3159 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1222, c1244, c1427, c1335, c1337, c1355, c1394, c1395, c1434, c1356, c1245, c3138, c1223, c1199, c1207] c3159 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1222 p h) (sat_cons (step1244 p h) (sat_cons (step1427 p h) (sat_cons (step1335 p h) (sat_cons (step1337 p h) (sat_cons (step1355 p h) (sat_cons (step1394 p h) (sat_cons (step1395 p h) (sat_cons (step1434 p h) (sat_cons (step1356 p h) (sat_cons (step1245 p h) (sat_cons (step3138 p h) (sat_cons (step1223 p h) (sat_cons (step1199 p h) (sat_cons (step1207 p h) (sat_nil p)))))))))))))))))
def c3160 : List Lit := [(10, false), (933, true), (137, true), (11, true)]
theorem step3160 (p : Nat → Bool) (h : Constraints p) : clause p c3160 = true :=
  Snake9.LocalRup.prove_clause [c75, c3155] c3160 (by decide) p (sat_cons (step75 p h) (sat_cons (step3155 p h) (sat_nil p)))
def c3161 : List Lit := [(908, true), (47, false), (10, false), (161, true), (142, true), (11, true)]
theorem step3161 (p : Nat → Bool) (h : Constraints p) : clause p c3161 = true :=
  Snake9.LocalRup.prove_clause [c1278, c1279, c341, c234, c2378, c2347, c138] c3161 (by decide) p (sat_cons (step1278 p h) (sat_cons (step1279 p h) (sat_cons (step341 p h) (sat_cons (step234 p h) (sat_cons (step2378 p h) (sat_cons (step2347 p h) (sat_cons (step138 p h) (sat_nil p))))))))
def c3162 : List Lit := [(142, true), (870, true), (42, false), (143, true), (48, true), (929, true), (11, true)]
theorem step3162 (p : Nat → Bool) (h : Constraints p) : clause p c3162 = true :=
  Snake9.LocalRup.prove_clause [c2378, c138, c3148, c1186, c2344] c3162 (by decide) p (sat_cons (step2378 p h) (sat_cons (step138 p h) (sat_cons (step3148 p h) (sat_cons (step1186 p h) (sat_cons (step2344 p h) (sat_nil p))))))
def c3163 : List Lit := [(311, false), (908, true), (175, true), (933, true), (37, true), (11, true)]
theorem step3163 (p : Nat → Bool) (h : Constraints p) : clause p c3163 = true :=
  Snake9.LocalRup.prove_clause [c941, c2456, c2464, c908, c997, c904, c972, c901, c954, c900, c948, c3153, c947] c3163 (by decide) p (sat_cons (step941 p h) (sat_cons (step2456 p h) (sat_cons (step2464 p h) (sat_cons (step908 p h) (sat_cons (step997 p h) (sat_cons (step904 p h) (sat_cons (step972 p h) (sat_cons (step901 p h) (sat_cons (step954 p h) (sat_cons (step900 p h) (sat_cons (step948 p h) (sat_cons (step3153 p h) (sat_cons (step947 p h) (sat_nil p))))))))))))))
def c3164 : List Lit := [(882, true), (47, false), (44, false), (28, true), (171, true), (10, true), (157, true), (39, true), (45, true)]
theorem step3164 (p : Nat → Bool) (h : Constraints p) : clause p c3164 = true :=
  Snake9.LocalRup.prove_clause [c1202, c1205, c1207, c1203, c1198, c219, c2338, c374, c320, c317, c2070] c3164 (by decide) p (sat_cons (step1202 p h) (sat_cons (step1205 p h) (sat_cons (step1207 p h) (sat_cons (step1203 p h) (sat_cons (step1198 p h) (sat_cons (step219 p h) (sat_cons (step2338 p h) (sat_cons (step374 p h) (sat_cons (step320 p h) (sat_cons (step317 p h) (sat_cons (step2070 p h) (sat_nil p))))))))))))
def c3165 : List Lit := [(923, false), (879, false), (155, true), (977, true), (933, false), (151, true), (62, true), (874, false), (851, false)]
theorem step3165 (p : Nat → Bool) (h : Constraints p) : clause p c3165 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1337, c1355, c1170, c3159, c1394, c1153, c1434, c2518] c3165 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1337 p h) (sat_cons (step1355 p h) (sat_cons (step1170 p h) (sat_cons (step3159 p h) (sat_cons (step1394 p h) (sat_cons (step1153 p h) (sat_cons (step1434 p h) (sat_cons (step2518 p h) (sat_nil p))))))))))
def c3166 : List Lit := [(48, false), (10, false), (36, false), (175, true), (37, true), (11, true)]
theorem step3166 (p : Nat → Bool) (h : Constraints p) : clause p c3166 = true :=
  Snake9.LocalRup.prove_clause [c365, c341] c3166 (by decide) p (sat_cons (step365 p h) (sat_cons (step341 p h) (sat_nil p)))
def c3167 : List Lit := [(28, false), (34, false), (51, false), (62, true), (11, true)]
theorem step3167 (p : Nat → Bool) (h : Constraints p) : clause p c3167 = true :=
  Snake9.LocalRup.prove_clause [c210, c207, c926, c929, c931, c936, c941, c1002, c2464, c2488, c995, c997, c1136, c993, c972, c1065, c982, c954, c1036, c979, c948, c1033, c977, c947, c1026, c2631, c233, c1024, c211, c2363, c518, c2397] c3167 (by decide) p (sat_cons (step210 p h) (sat_cons (step207 p h) (sat_cons (step926 p h) (sat_cons (step929 p h) (sat_cons (step931 p h) (sat_cons (step936 p h) (sat_cons (step941 p h) (sat_cons (step1002 p h) (sat_cons (step2464 p h) (sat_cons (step2488 p h) (sat_cons (step995 p h) (sat_cons (step997 p h) (sat_cons (step1136 p h) (sat_cons (step993 p h) (sat_cons (step972 p h) (sat_cons (step1065 p h) (sat_cons (step982 p h) (sat_cons (step954 p h) (sat_cons (step1036 p h) (sat_cons (step979 p h) (sat_cons (step948 p h) (sat_cons (step1033 p h) (sat_cons (step977 p h) (sat_cons (step947 p h) (sat_cons (step1026 p h) (sat_cons (step2631 p h) (sat_cons (step233 p h) (sat_cons (step1024 p h) (sat_cons (step211 p h) (sat_cons (step2363 p h) (sat_cons (step518 p h) (sat_cons (step2397 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c3168 : List Lit := [(1002, true), (70, false), (32, false), (26, false), (937, true), (44, false), (988, false)]
theorem step3168 (p : Nat → Bool) (h : Constraints p) : clause p c3168 = true :=
  Snake9.LocalRup.prove_clause [c1463, c1490, c1486, c1464, c1466, c1476, c451, c1468, c1469, c2535, c502, c1333] c3168 (by decide) p (sat_cons (step1463 p h) (sat_cons (step1490 p h) (sat_cons (step1486 p h) (sat_cons (step1464 p h) (sat_cons (step1466 p h) (sat_cons (step1476 p h) (sat_cons (step451 p h) (sat_cons (step1468 p h) (sat_cons (step1469 p h) (sat_cons (step2535 p h) (sat_cons (step502 p h) (sat_cons (step1333 p h) (sat_nil p)))))))))))))
def c3169 : List Lit := [(936, true), (39, true), (47, true), (36, false), (163, true), (37, true), (2, false)]
theorem step3169 (p : Nat → Bool) (h : Constraints p) : clause p c3169 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1332, c391, c255, c242] c3169 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1332 p h) (sat_cons (step391 p h) (sat_cons (step255 p h) (sat_cons (step242 p h) (sat_nil p))))))
def c3170 : List Lit := [(877, true), (32, false), (151, true), (25, true)]
theorem step3170 (p : Nat → Bool) (h : Constraints p) : clause p c3170 = true :=
  Snake9.LocalRup.prove_clause [c1198, c1199, c178, c191] c3170 (by decide) p (sat_cons (step1198 p h) (sat_cons (step1199 p h) (sat_cons (step178 p h) (sat_cons (step191 p h) (sat_nil p)))))
def c3171 : List Lit := [(13, false), (50, false), (63, true), (45, true), (47, false), (44, false), (171, true)]
theorem step3171 (p : Nat → Bool) (h : Constraints p) : clause p c3171 = true :=
  Snake9.LocalRup.prove_clause [c374, c371, c317] c3171 (by decide) p (sat_cons (step374 p h) (sat_cons (step371 p h) (sat_cons (step317 p h) (sat_nil p))))
def c3172 : List Lit := [(908, true), (13, false), (161, true), (175, true), (142, true), (37, true), (11, true)]
theorem step3172 (p : Nat → Bool) (h : Constraints p) : clause p c3172 = true :=
  Snake9.LocalRup.prove_clause [c1278, c1279, c234, c2347, c138, c2378, c365, c3007] c3172 (by decide) p (sat_cons (step1278 p h) (sat_cons (step1279 p h) (sat_cons (step234 p h) (sat_cons (step2347 p h) (sat_cons (step138 p h) (sat_cons (step2378 p h) (sat_cons (step365 p h) (sat_cons (step3007 p h) (sat_nil p)))))))))
def c3173 : List Lit := [(888, true), (879, false), (143, true), (151, true), (62, false), (872, false)]
theorem step3173 (p : Nat → Bool) (h : Constraints p) : clause p c3173 = true :=
  Snake9.LocalRup.prove_clause [c1204, c1191, c1223, c1227, c1207, c1194, c3152, c1184, c2361, c2345] c3173 (by decide) p (sat_cons (step1204 p h) (sat_cons (step1191 p h) (sat_cons (step1223 p h) (sat_cons (step1227 p h) (sat_cons (step1207 p h) (sat_cons (step1194 p h) (sat_cons (step3152 p h) (sat_cons (step1184 p h) (sat_cons (step2361 p h) (sat_cons (step2345 p h) (sat_nil p)))))))))))
def c3174 : List Lit := [(51, true), (43, true), (173, true), (41, false), (9, true), (5, true)]
theorem step3174 (p : Nat → Bool) (h : Constraints p) : clause p c3174 = true :=
  Snake9.LocalRup.prove_clause [c2370, c2369, c2656] c3174 (by decide) p (sat_cons (step2370 p h) (sat_cons (step2369 p h) (sat_cons (step2656 p h) (sat_nil p))))
def c3175 : List Lit := [(51, false), (922, true), (200, true), (161, true), (178, true), (28, true), (139, true), (62, false), (11, true)]
theorem step3175 (p : Nat → Bool) (h : Constraints p) : clause p c3175 = true :=
  Snake9.LocalRup.prove_clause [c2631, c122, c2356, c2509, c2363, c233, c1279, c1281, c1305, c1292, c1294, c2632] c3175 (by decide) p (sat_cons (step2631 p h) (sat_cons (step122 p h) (sat_cons (step2356 p h) (sat_cons (step2509 p h) (sat_cons (step2363 p h) (sat_cons (step233 p h) (sat_cons (step1279 p h) (sat_cons (step1281 p h) (sat_cons (step1305 p h) (sat_cons (step1292 p h) (sat_cons (step1294 p h) (sat_cons (step2632 p h) (sat_nil p)))))))))))))
def c3176 : List Lit := [(917, true), (51, false), (62, false)]
theorem step3176 (p : Nat → Bool) (h : Constraints p) : clause p c3176 = true :=
  Snake9.LocalRup.prove_clause [c1292, c1294, c2632] c3176 (by decide) p (sat_cons (step1292 p h) (sat_cons (step1294 p h) (sat_cons (step2632 p h) (sat_nil p))))
def c3177 : List Lit := [(42, true), (51, false), (918, true), (41, false)]
theorem step3177 (p : Nat → Bool) (h : Constraints p) : clause p c3177 = true :=
  Snake9.LocalRup.prove_clause [c1297, c1286, c1288, c1295, c287, c1289] c3177 (by decide) p (sat_cons (step1297 p h) (sat_cons (step1286 p h) (sat_cons (step1288 p h) (sat_cons (step1295 p h) (sat_cons (step287 p h) (sat_cons (step1289 p h) (sat_nil p)))))))
def c3178 : List Lit := [(24, false), (25, true), (32, false), (941, true), (151, true), (62, false)]
theorem step3178 (p : Nat → Bool) (h : Constraints p) : clause p c3178 = true :=
  Snake9.LocalRup.prove_clause [c2940, c189, c180, c439, c1331, c1334, c1340] c3178 (by decide) p (sat_cons (step2940 p h) (sat_cons (step189 p h) (sat_cons (step180 p h) (sat_cons (step439 p h) (sat_cons (step1331 p h) (sat_cons (step1334 p h) (sat_cons (step1340 p h) (sat_nil p))))))))
def c3179 : List Lit := [(48, false), (44, true), (934, true), (923, true), (10, false), (175, true), (37, true), (41, false), (11, true)]
theorem step3179 (p : Nat → Bool) (h : Constraints p) : clause p c3179 = true :=
  Snake9.LocalRup.prove_clause [c1290, c365, c345, c344, c3166, c1317, c1278, c1327, c1281, c1322, c1306, c1293, c1295, c1291, c1287, c287] c3179 (by decide) p (sat_cons (step1290 p h) (sat_cons (step365 p h) (sat_cons (step345 p h) (sat_cons (step344 p h) (sat_cons (step3166 p h) (sat_cons (step1317 p h) (sat_cons (step1278 p h) (sat_cons (step1327 p h) (sat_cons (step1281 p h) (sat_cons (step1322 p h) (sat_cons (step1306 p h) (sat_cons (step1293 p h) (sat_cons (step1295 p h) (sat_cons (step1291 p h) (sat_cons (step1287 p h) (sat_cons (step287 p h) (sat_nil p)))))))))))))))))
def c3180 : List Lit := [(887, true), (143, true), (151, true), (62, false), (872, false)]
theorem step3180 (p : Nat → Bool) (h : Constraints p) : clause p c3180 = true :=
  Snake9.LocalRup.prove_clause [c1191, c1226, c1222, c1194, c1206, c1184, c3152, c2345, c2361] c3180 (by decide) p (sat_cons (step1191 p h) (sat_cons (step1226 p h) (sat_cons (step1222 p h) (sat_cons (step1194 p h) (sat_cons (step1206 p h) (sat_cons (step1184 p h) (sat_cons (step3152 p h) (sat_cons (step2345 p h) (sat_cons (step2361 p h) (sat_nil p))))))))))
def c3181 : List Lit := [(918, true), (169, true), (38, true), (7, false), (51, false), (40, true), (41, false)]
theorem step3181 (p : Nat → Bool) (h : Constraints p) : clause p c3181 = true :=
  Snake9.LocalRup.prove_clause [c3177, c2834, c299] c3181 (by decide) p (sat_cons (step3177 p h) (sat_cons (step2834 p h) (sat_cons (step299 p h) (sat_nil p))))
def c3182 : List Lit := [(879, false), (863, false), (143, true), (933, false), (977, true), (922, false), (151, true), (62, true), (872, false)]
theorem step3182 (p : Nat → Bool) (h : Constraints p) : clause p c3182 = true :=
  Snake9.LocalRup.prove_clause [c1335, c1337, c1355, c1386, c1440, c1253, c1191, c1204, c3158, c1227, c2361, c1194, c2345, c1184] c3182 (by decide) p (sat_cons (step1335 p h) (sat_cons (step1337 p h) (sat_cons (step1355 p h) (sat_cons (step1386 p h) (sat_cons (step1440 p h) (sat_cons (step1253 p h) (sat_cons (step1191 p h) (sat_cons (step1204 p h) (sat_cons (step3158 p h) (sat_cons (step1227 p h) (sat_cons (step2361 p h) (sat_cons (step1194 p h) (sat_cons (step2345 p h) (sat_cons (step1184 p h) (sat_nil p)))))))))))))))
def c3183 : List Lit := [(955, true), (918, false), (922, false), (940, false), (37, false), (1, false)]
theorem step3183 (p : Nat → Bool) (h : Constraints p) : clause p c3183 = true :=
  Snake9.LocalRup.prove_clause [c1345, c1392, c1385, c1306, c1350, c1281, c1325, c1278, c1318, c244] c3183 (by decide) p (sat_cons (step1345 p h) (sat_cons (step1392 p h) (sat_cons (step1385 p h) (sat_cons (step1306 p h) (sat_cons (step1350 p h) (sat_cons (step1281 p h) (sat_cons (step1325 p h) (sat_cons (step1278 p h) (sat_cons (step1318 p h) (sat_cons (step244 p h) (sat_nil p)))))))))))
def c3184 : List Lit := [(377, true), (908, true), (933, true), (37, true), (11, true)]
theorem step3184 (p : Nat → Bool) (h : Constraints p) : clause p c3184 = true :=
  Snake9.LocalRup.prove_clause [c1000, c1002, c995, c997, c943, c993, c972, c908, c982, c954, c904, c980, c948, c901, c976, c947, c900, c3153] c3184 (by decide) p (sat_cons (step1000 p h) (sat_cons (step1002 p h) (sat_cons (step995 p h) (sat_cons (step997 p h) (sat_cons (step943 p h) (sat_cons (step993 p h) (sat_cons (step972 p h) (sat_cons (step908 p h) (sat_cons (step982 p h) (sat_cons (step954 p h) (sat_cons (step904 p h) (sat_cons (step980 p h) (sat_cons (step948 p h) (sat_cons (step901 p h) (sat_cons (step976 p h) (sat_cons (step947 p h) (sat_cons (step900 p h) (sat_cons (step3153 p h) (sat_nil p)))))))))))))))))))
def c3185 : List Lit := [(76, true), (1023, false), (405, true), (1040, true), (81, true), (1011, false)]
theorem step3185 (p : Nat → Bool) (h : Constraints p) : clause p c3185 = true :=
  Snake9.LocalRup.prove_clause [c1038, c1017, c1014, c1009, c495, c1460, c1463, c1036, c1033, c1026, c1023, c1499, c2398, c1508, c524, c1539, c1471, c1559, c1474, c1486] c3185 (by decide) p (sat_cons (step1038 p h) (sat_cons (step1017 p h) (sat_cons (step1014 p h) (sat_cons (step1009 p h) (sat_cons (step495 p h) (sat_cons (step1460 p h) (sat_cons (step1463 p h) (sat_cons (step1036 p h) (sat_cons (step1033 p h) (sat_cons (step1026 p h) (sat_cons (step1023 p h) (sat_cons (step1499 p h) (sat_cons (step2398 p h) (sat_cons (step1508 p h) (sat_cons (step524 p h) (sat_cons (step1539 p h) (sat_cons (step1471 p h) (sat_cons (step1559 p h) (sat_cons (step1474 p h) (sat_cons (step1486 p h) (sat_nil p)))))))))))))))))))))
def c3186 : List Lit := [(932, true), (880, true), (10, false), (11, true)]
theorem step3186 (p : Nat → Bool) (h : Constraints p) : clause p c3186 = true :=
  Snake9.LocalRup.prove_clause [c1323, c1325, c1321, c1317, c1318, c2628, c350] c3186 (by decide) p (sat_cons (step1323 p h) (sat_cons (step1325 p h) (sat_cons (step1321 p h) (sat_cons (step1317 p h) (sat_cons (step1318 p h) (sat_cons (step2628 p h) (sat_cons (step350 p h) (sat_nil p))))))))
def c3187 : List Lit := [(8, true), (23, true), (31, false), (26, false), (153, true), (4, false)]
theorem step3187 (p : Nat → Bool) (h : Constraints p) : clause p c3187 = true :=
  Snake9.LocalRup.prove_clause [c202, c3009, c158] c3187 (by decide) p (sat_cons (step202 p h) (sat_cons (step3009 p h) (sat_cons (step158 p h) (sat_nil p))))
def c3188 : List Lit := [(942, true), (56, true), (877, true), (32, false), (151, true), (938, false)]
theorem step3188 (p : Nat → Bool) (h : Constraints p) : clause p c3188 = true :=
  Snake9.LocalRup.prove_clause [c1332, c1343, c1341, c1333, c2530] c3188 (by decide) p (sat_cons (step1332 p h) (sat_cons (step1343 p h) (sat_cons (step1341 p h) (sat_cons (step1333 p h) (sat_cons (step2530 p h) (sat_nil p))))))
def c3189 : List Lit := [(10, false), (934, true), (137, true), (51, true), (11, true)]
theorem step3189 (p : Nat → Bool) (h : Constraints p) : clause p c3189 = true :=
  Snake9.LocalRup.prove_clause [c2635, c75, c76, c2071, c1327, c1322] c3189 (by decide) p (sat_cons (step2635 p h) (sat_cons (step75 p h) (sat_cons (step76 p h) (sat_cons (step2071 p h) (sat_cons (step1327 p h) (sat_cons (step1322 p h) (sat_nil p)))))))
def c3190 : List Lit := [(935, false), (957, true), (24, false), (151, true), (62, true)]
theorem step3190 (p : Nat → Bool) (h : Constraints p) : clause p c3190 = true :=
  Snake9.LocalRup.prove_clause [c1373, c1335, c1337, c1365, c1366, c1380, c3156, c1304, c1283] c3190 (by decide) p (sat_cons (step1373 p h) (sat_cons (step1335 p h) (sat_cons (step1337 p h) (sat_cons (step1365 p h) (sat_cons (step1366 p h) (sat_cons (step1380 p h) (sat_cons (step3156 p h) (sat_cons (step1304 p h) (sat_cons (step1283 p h) (sat_nil p))))))))))
end B112E260
