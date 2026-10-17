import B112E115Inputs
namespace B112E115
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1239 : List Lit := [(110, false)]
theorem step1239 (p : Nat → Bool) (h : Constraints p) : clause p c1239 = true :=
  Snake9.LocalRup.prove_clause [c571, c518] c1239 (by decide) p (sat_cons (step571 p h) (sat_cons (step518 p h) (sat_nil p)))
def c1240 : List Lit := [(115, false)]
theorem step1240 (p : Nat → Bool) (h : Constraints p) : clause p c1240 = true :=
  Snake9.LocalRup.prove_clause [c574, c527] c1240 (by decide) p (sat_cons (step574 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1241 : List Lit := [(117, false)]
theorem step1241 (p : Nat → Bool) (h : Constraints p) : clause p c1241 = true :=
  Snake9.LocalRup.prove_clause [c575, c529] c1241 (by decide) p (sat_cons (step575 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1242 : List Lit := [(462, false)]
theorem step1242 (p : Nat → Bool) (h : Constraints p) : clause p c1242 = true :=
  Snake9.LocalRup.prove_clause [c728, c725] c1242 (by decide) p (sat_cons (step728 p h) (sat_cons (step725 p h) (sat_nil p)))
def c1243 : List Lit := [(348, false)]
theorem step1243 (p : Nat → Bool) (h : Constraints p) : clause p c1243 = true :=
  Snake9.LocalRup.prove_clause [c728, c727] c1243 (by decide) p (sat_cons (step728 p h) (sat_cons (step727 p h) (sat_nil p)))
def c1244 : List Lit := [(460, false)]
theorem step1244 (p : Nat → Bool) (h : Constraints p) : clause p c1244 = true :=
  Snake9.LocalRup.prove_clause [c1242, c721] c1244 (by decide) p (sat_cons (step1242 p h) (sat_cons (step721 p h) (sat_nil p)))
def c1245 : List Lit := [(404, false)]
theorem step1245 (p : Nat → Bool) (h : Constraints p) : clause p c1245 = true :=
  Snake9.LocalRup.prove_clause [c1242, c724] c1245 (by decide) p (sat_cons (step1242 p h) (sat_cons (step724 p h) (sat_nil p)))
def c1246 : List Lit := [(346, false)]
theorem step1246 (p : Nat → Bool) (h : Constraints p) : clause p c1246 = true :=
  Snake9.LocalRup.prove_clause [c1243, c651] c1246 (by decide) p (sat_cons (step1243 p h) (sat_cons (step651 p h) (sat_nil p)))
def c1247 : List Lit := [(290, false)]
theorem step1247 (p : Nat → Bool) (h : Constraints p) : clause p c1247 = true :=
  Snake9.LocalRup.prove_clause [c1243, c654] c1247 (by decide) p (sat_cons (step1243 p h) (sat_cons (step654 p h) (sat_nil p)))
def c1248 : List Lit := [(458, false)]
theorem step1248 (p : Nat → Bool) (h : Constraints p) : clause p c1248 = true :=
  Snake9.LocalRup.prove_clause [c1244, c717] c1248 (by decide) p (sat_cons (step1244 p h) (sat_cons (step717 p h) (sat_nil p)))
def c1249 : List Lit := [(430, false)]
theorem step1249 (p : Nat → Bool) (h : Constraints p) : clause p c1249 = true :=
  Snake9.LocalRup.prove_clause [c1244, c719] c1249 (by decide) p (sat_cons (step1244 p h) (sat_cons (step719 p h) (sat_nil p)))
def c1250 : List Lit := [(402, false)]
theorem step1250 (p : Nat → Bool) (h : Constraints p) : clause p c1250 = true :=
  Snake9.LocalRup.prove_clause [c1245, c685] c1250 (by decide) p (sat_cons (step1245 p h) (sat_cons (step685 p h) (sat_nil p)))
def c1251 : List Lit := [(374, false)]
theorem step1251 (p : Nat → Bool) (h : Constraints p) : clause p c1251 = true :=
  Snake9.LocalRup.prove_clause [c1245, c687] c1251 (by decide) p (sat_cons (step1245 p h) (sat_cons (step687 p h) (sat_nil p)))
def c1252 : List Lit := [(316, false)]
theorem step1252 (p : Nat → Bool) (h : Constraints p) : clause p c1252 = true :=
  Snake9.LocalRup.prove_clause [c1246, c649] c1252 (by decide) p (sat_cons (step1246 p h) (sat_cons (step649 p h) (sat_nil p)))
def c1253 : List Lit := [(288, false)]
theorem step1253 (p : Nat → Bool) (h : Constraints p) : clause p c1253 = true :=
  Snake9.LocalRup.prove_clause [c1247, c604] c1253 (by decide) p (sat_cons (step1247 p h) (sat_cons (step604 p h) (sat_nil p)))
def c1254 : List Lit := [(260, false)]
theorem step1254 (p : Nat → Bool) (h : Constraints p) : clause p c1254 = true :=
  Snake9.LocalRup.prove_clause [c1247, c606] c1254 (by decide) p (sat_cons (step1247 p h) (sat_cons (step606 p h) (sat_nil p)))
def c1255 : List Lit := [(456, false)]
theorem step1255 (p : Nat → Bool) (h : Constraints p) : clause p c1255 = true :=
  Snake9.LocalRup.prove_clause [c1248, c713] c1255 (by decide) p (sat_cons (step1248 p h) (sat_cons (step713 p h) (sat_nil p)))
def c1256 : List Lit := [(416, false)]
theorem step1256 (p : Nat → Bool) (h : Constraints p) : clause p c1256 = true :=
  Snake9.LocalRup.prove_clause [c1249, c696] c1256 (by decide) p (sat_cons (step1249 p h) (sat_cons (step696 p h) (sat_nil p)))
def c1257 : List Lit := [(372, false)]
theorem step1257 (p : Nat → Bool) (h : Constraints p) : clause p c1257 = true :=
  Snake9.LocalRup.prove_clause [c1251, c669] c1257 (by decide) p (sat_cons (step1251 p h) (sat_cons (step669 p h) (sat_nil p)))
def c1258 : List Lit := [(360, false)]
theorem step1258 (p : Nat → Bool) (h : Constraints p) : clause p c1258 = true :=
  Snake9.LocalRup.prove_clause [c1251, c672] c1258 (by decide) p (sat_cons (step1251 p h) (sat_cons (step672 p h) (sat_nil p)))
def c1259 : List Lit := [(314, false)]
theorem step1259 (p : Nat → Bool) (h : Constraints p) : clause p c1259 = true :=
  Snake9.LocalRup.prove_clause [c1252, c626] c1259 (by decide) p (sat_cons (step1252 p h) (sat_cons (step626 p h) (sat_nil p)))
def c1260 : List Lit := [(302, false)]
theorem step1260 (p : Nat → Bool) (h : Constraints p) : clause p c1260 = true :=
  Snake9.LocalRup.prove_clause [c1252, c629] c1260 (by decide) p (sat_cons (step1252 p h) (sat_cons (step629 p h) (sat_nil p)))
def c1261 : List Lit := [(286, false)]
theorem step1261 (p : Nat → Bool) (h : Constraints p) : clause p c1261 = true :=
  Snake9.LocalRup.prove_clause [c1253, c601] c1261 (by decide) p (sat_cons (step1253 p h) (sat_cons (step601 p h) (sat_nil p)))
def c1262 : List Lit := [(448, false)]
theorem step1262 (p : Nat → Bool) (h : Constraints p) : clause p c1262 = true :=
  Snake9.LocalRup.prove_clause [c1255, c711] c1262 (by decide) p (sat_cons (step1255 p h) (sat_cons (step711 p h) (sat_nil p)))
def c1263 : List Lit := [(408, false)]
theorem step1263 (p : Nat → Bool) (h : Constraints p) : clause p c1263 = true :=
  Snake9.LocalRup.prove_clause [c1256, c694] c1263 (by decide) p (sat_cons (step1256 p h) (sat_cons (step694 p h) (sat_nil p)))
def c1264 : List Lit := [(284, false)]
theorem step1264 (p : Nat → Bool) (h : Constraints p) : clause p c1264 = true :=
  Snake9.LocalRup.prove_clause [c1261, c599] c1264 (by decide) p (sat_cons (step1261 p h) (sat_cons (step599 p h) (sat_nil p)))
def c1265 : List Lit := [(406, false)]
theorem step1265 (p : Nat → Bool) (h : Constraints p) : clause p c1265 = true :=
  Snake9.LocalRup.prove_clause [c1263, c692] c1265 (by decide) p (sat_cons (step1263 p h) (sat_cons (step692 p h) (sat_nil p)))
def c1266 : List Lit := [(1010, true)]
theorem step1266 (p : Nat → Bool) (h : Constraints p) : clause p c1266 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1132] c1266 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1132 p h) (sat_nil p)))
def c1267 : List Lit := [(107, true), (1011, true)]
theorem step1267 (p : Nat → Bool) (h : Constraints p) : clause p c1267 = true :=
  Snake9.LocalRup.prove_clause [c1239, c1133] c1267 (by decide) p (sat_cons (step1239 p h) (sat_cons (step1133 p h) (sat_nil p)))
def c1268 : List Lit := [(1012, true)]
theorem step1268 (p : Nat → Bool) (h : Constraints p) : clause p c1268 = true :=
  Snake9.LocalRup.prove_clause [c1266, c1134] c1268 (by decide) p (sat_cons (step1266 p h) (sat_cons (step1134 p h) (sat_nil p)))
def c1269 : List Lit := [(1008, false), (1013, true)]
theorem step1269 (p : Nat → Bool) (h : Constraints p) : clause p c1269 = true :=
  Snake9.LocalRup.prove_clause [c1266, c1136] c1269 (by decide) p (sat_cons (step1266 p h) (sat_cons (step1136 p h) (sat_nil p)))
def c1270 : List Lit := [(1019, true)]
theorem step1270 (p : Nat → Bool) (h : Constraints p) : clause p c1270 = true :=
  Snake9.LocalRup.prove_clause [c1240, c1241, c1141] c1270 (by decide) p (sat_cons (step1240 p h) (sat_cons (step1241 p h) (sat_cons (step1141 p h) (sat_nil p))))
def c1271 : List Lit := [(1021, true)]
theorem step1271 (p : Nat → Bool) (h : Constraints p) : clause p c1271 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1142] c1271 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1142 p h) (sat_nil p)))
def c1272 : List Lit := [(1016, false), (1022, true)]
theorem step1272 (p : Nat → Bool) (h : Constraints p) : clause p c1272 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1143] c1272 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1143 p h) (sat_nil p)))
def c1273 : List Lit := [(1017, false), (1023, true)]
theorem step1273 (p : Nat → Bool) (h : Constraints p) : clause p c1273 = true :=
  Snake9.LocalRup.prove_clause [c1270, c1144] c1273 (by decide) p (sat_cons (step1270 p h) (sat_cons (step1144 p h) (sat_nil p)))
def c1274 : List Lit := [(1026, true)]
theorem step1274 (p : Nat → Bool) (h : Constraints p) : clause p c1274 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1271, c1145] c1274 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1271 p h) (sat_cons (step1145 p h) (sat_nil p))))
def c1275 : List Lit := [(1022, false), (1027, true)]
theorem step1275 (p : Nat → Bool) (h : Constraints p) : clause p c1275 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1146] c1275 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1146 p h) (sat_nil p)))
def c1276 : List Lit := [(1023, false), (1028, true)]
theorem step1276 (p : Nat → Bool) (h : Constraints p) : clause p c1276 = true :=
  Snake9.LocalRup.prove_clause [c1268, c1147] c1276 (by decide) p (sat_cons (step1268 p h) (sat_cons (step1147 p h) (sat_nil p)))
def c1277 : List Lit := [(1013, false), (1027, true)]
theorem step1277 (p : Nat → Bool) (h : Constraints p) : clause p c1277 = true :=
  Snake9.LocalRup.prove_clause [c1271, c1148] c1277 (by decide) p (sat_cons (step1271 p h) (sat_cons (step1148 p h) (sat_nil p)))
def c1278 : List Lit := [(1014, false), (1028, true)]
theorem step1278 (p : Nat → Bool) (h : Constraints p) : clause p c1278 = true :=
  Snake9.LocalRup.prove_clause [c1271, c1151] c1278 (by decide) p (sat_cons (step1271 p h) (sat_cons (step1151 p h) (sat_nil p)))
def c1279 : List Lit := [(1034, true)]
theorem step1279 (p : Nat → Bool) (h : Constraints p) : clause p c1279 = true :=
  Snake9.LocalRup.prove_clause [c1274, c1154] c1279 (by decide) p (sat_cons (step1274 p h) (sat_cons (step1154 p h) (sat_nil p)))
def c1280 : List Lit := [(1001, false), (1035, true)]
theorem step1280 (p : Nat → Bool) (h : Constraints p) : clause p c1280 = true :=
  Snake9.LocalRup.prove_clause [c1274, c1159] c1280 (by decide) p (sat_cons (step1274 p h) (sat_cons (step1159 p h) (sat_nil p)))
def c1281 : List Lit := [(974, false), (1051, true)]
theorem step1281 (p : Nat → Bool) (h : Constraints p) : clause p c1281 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1167] c1281 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1167 p h) (sat_nil p)))
def c1282 : List Lit := [(975, false), (1052, true)]
theorem step1282 (p : Nat → Bool) (h : Constraints p) : clause p c1282 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1171] c1282 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1171 p h) (sat_nil p)))
def c1283 : List Lit := [(976, false), (1053, true)]
theorem step1283 (p : Nat → Bool) (h : Constraints p) : clause p c1283 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1176] c1283 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1176 p h) (sat_nil p)))
def c1284 : List Lit := [(977, false), (1054, true)]
theorem step1284 (p : Nat → Bool) (h : Constraints p) : clause p c1284 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1180] c1284 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1180 p h) (sat_nil p)))
def c1285 : List Lit := [(978, false), (1055, true)]
theorem step1285 (p : Nat → Bool) (h : Constraints p) : clause p c1285 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1185] c1285 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1185 p h) (sat_nil p)))
def c1286 : List Lit := [(979, false), (1056, true)]
theorem step1286 (p : Nat → Bool) (h : Constraints p) : clause p c1286 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1190] c1286 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1190 p h) (sat_nil p)))
def c1287 : List Lit := [(980, false), (1057, true)]
theorem step1287 (p : Nat → Bool) (h : Constraints p) : clause p c1287 = true :=
  Snake9.LocalRup.prove_clause [c1279, c1194] c1287 (by decide) p (sat_cons (step1279 p h) (sat_cons (step1194 p h) (sat_nil p)))
def c1288 : List Lit := [(799, true), (2, false), (39, false)]
theorem step1288 (p : Nat → Bool) (h : Constraints p) : clause p c1288 = true :=
  Snake9.LocalRup.prove_clause [c732, c734, c730, c8] c1288 (by decide) p (sat_cons (step732 p h) (sat_cons (step734 p h) (sat_cons (step730 p h) (sat_cons (step8 p h) (sat_nil p)))))
def c1289 : List Lit := [(797, true), (2, false), (39, false)]
theorem step1289 (p : Nat → Bool) (h : Constraints p) : clause p c1289 = true :=
  Snake9.LocalRup.prove_clause [c729, c730, c22] c1289 (by decide) p (sat_cons (step729 p h) (sat_cons (step730 p h) (sat_cons (step22 p h) (sat_nil p))))
def c1290 : List Lit := [(61, false), (882, true), (39, false), (57, false)]
theorem step1290 (p : Nat → Bool) (h : Constraints p) : clause p c1290 = true :=
  Snake9.LocalRup.prove_clause [c356, c359, c901] c1290 (by decide) p (sat_cons (step356 p h) (sat_cons (step359 p h) (sat_cons (step901 p h) (sat_nil p))))
def c1291 : List Lit := [(812, true), (802, false), (2, false), (39, false)]
theorem step1291 (p : Nat → Bool) (h : Constraints p) : clause p c1291 = true :=
  Snake9.LocalRup.prove_clause [c745, c1289, c1288, c761, c757, c735, c746, c15, c741] c1291 (by decide) p (sat_cons (step745 p h) (sat_cons (step1289 p h) (sat_cons (step1288 p h) (sat_cons (step761 p h) (sat_cons (step757 p h) (sat_cons (step735 p h) (sat_cons (step746 p h) (sat_cons (step15 p h) (sat_cons (step741 p h) (sat_nil p))))))))))
def c1292 : List Lit := [(966, true), (949, false)]
theorem step1292 (p : Nat → Bool) (h : Constraints p) : clause p c1292 = true :=
  Snake9.LocalRup.prove_clause [c563, c1060, c1088, c1084, c1061, c1071, c1073, c1055, c1068, c1066, c482, c481] c1292 (by decide) p (sat_cons (step563 p h) (sat_cons (step1060 p h) (sat_cons (step1088 p h) (sat_cons (step1084 p h) (sat_cons (step1061 p h) (sat_cons (step1071 p h) (sat_cons (step1073 p h) (sat_cons (step1055 p h) (sat_cons (step1068 p h) (sat_cons (step1066 p h) (sat_cons (step482 p h) (sat_cons (step481 p h) (sat_nil p)))))))))))))
def c1293 : List Lit := [(86, false), (78, false), (75, false), (16, false)]
theorem step1293 (p : Nat → Bool) (h : Constraints p) : clause p c1293 = true :=
  Snake9.LocalRup.prove_clause [c561, c489, c468, c463] c1293 (by decide) p (sat_cons (step561 p h) (sat_cons (step489 p h) (sat_cons (step468 p h) (sat_cons (step463 p h) (sat_nil p)))))
def c1294 : List Lit := [(965, true)]
theorem step1294 (p : Nat → Bool) (h : Constraints p) : clause p c1294 = true :=
  Snake9.LocalRup.prove_clause [c563, c1079, c1083, c1071, c1073, c1058, c1068, c1066, c1055, c482, c481] c1294 (by decide) p (sat_cons (step563 p h) (sat_cons (step1079 p h) (sat_cons (step1083 p h) (sat_cons (step1071 p h) (sat_cons (step1073 p h) (sat_cons (step1058 p h) (sat_cons (step1068 p h) (sat_cons (step1066 p h) (sat_cons (step1055 p h) (sat_cons (step482 p h) (sat_cons (step481 p h) (sat_nil p))))))))))))
def c1295 : List Lit := [(973, true)]
theorem step1295 (p : Nat → Bool) (h : Constraints p) : clause p c1295 = true :=
  Snake9.LocalRup.prove_clause [c1294, c1095] c1295 (by decide) p (sat_cons (step1294 p h) (sat_cons (step1095 p h) (sat_nil p)))
def c1296 : List Lit := [(82, false), (79, false), (88, false)]
theorem step1296 (p : Nat → Bool) (h : Constraints p) : clause p c1296 = true :=
  Snake9.LocalRup.prove_clause [c563, c482, c481] c1296 (by decide) p (sat_cons (step563 p h) (sat_cons (step482 p h) (sat_cons (step481 p h) (sat_nil p))))
def c1297 : List Lit := [(942, true), (106, false)]
theorem step1297 (p : Nat → Bool) (h : Constraints p) : clause p c1297 = true :=
  Snake9.LocalRup.prove_clause [c557, c1036, c1039, c1028, c1030, c1019, c1026, c1022, c1023, c424, c429, c374] c1297 (by decide) p (sat_cons (step557 p h) (sat_cons (step1036 p h) (sat_cons (step1039 p h) (sat_cons (step1028 p h) (sat_cons (step1030 p h) (sat_cons (step1019 p h) (sat_cons (step1026 p h) (sat_cons (step1022 p h) (sat_cons (step1023 p h) (sat_cons (step424 p h) (sat_cons (step429 p h) (sat_cons (step374 p h) (sat_nil p)))))))))))))
def c1298 : List Lit := [(865, true), (858, false), (21, false)]
theorem step1298 (p : Nat → Bool) (h : Constraints p) : clause p c1298 = true :=
  Snake9.LocalRup.prove_clause [c542, c860, c869, c873, c863, c849, c854, c855, c846, c265, c257, c254] c1298 (by decide) p (sat_cons (step542 p h) (sat_cons (step860 p h) (sat_cons (step869 p h) (sat_cons (step873 p h) (sat_cons (step863 p h) (sat_cons (step849 p h) (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step846 p h) (sat_cons (step265 p h) (sat_cons (step257 p h) (sat_cons (step254 p h) (sat_nil p)))))))))))))
def c1299 : List Lit := [(864, true), (21, false)]
theorem step1299 (p : Nat → Bool) (h : Constraints p) : clause p c1299 = true :=
  Snake9.LocalRup.prove_clause [c542, c868, c872, c862, c849, c854, c855, c846, c265, c257, c254] c1299 (by decide) p (sat_cons (step542 p h) (sat_cons (step868 p h) (sat_cons (step872 p h) (sat_cons (step862 p h) (sat_cons (step849 p h) (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step846 p h) (sat_cons (step265 p h) (sat_cons (step257 p h) (sat_cons (step254 p h) (sat_nil p))))))))))))
def c1300 : List Lit := [(879, true), (23, true), (19, false)]
theorem step1300 (p : Nat → Bool) (h : Constraints p) : clause p c1300 = true :=
  Snake9.LocalRup.prove_clause [c551, c896, c897, c335, c321] c1300 (by decide) p (sat_cons (step551 p h) (sat_cons (step896 p h) (sat_cons (step897 p h) (sat_cons (step335 p h) (sat_cons (step321 p h) (sat_nil p))))))
def c1301 : List Lit := [(879, false), (817, false), (888, true), (30, false), (858, true), (896, false), (21, false), (90, false), (1035, false)]
theorem step1301 (p : Nat → Bool) (h : Constraints p) : clause p c1301 = true :=
  Snake9.TreeRup.prove_clause [c552, c544, c549, c532, c536, c547, c1207, c1294, c911, c907, c858, c857, c904, c905, c915, c899, c900, c889, c891, c355, c886, c883, c884, c339, c281, c375, c275, c313, c277, c314, c1022, c293, c189, c328, c185, c188, c308, c311, c898, c90, c191, c776, c295, c738, c778, c297, c1291, c786, c399, c400, c401, c801, c1016, c1027, c825, c1021, c1032, c984, c1051, c1200, c1120, c1191] c1301 (by decide) p (sat_cons (step552 p h) (sat_cons (step544 p h) (sat_cons (step549 p h) (sat_cons (step532 p h) (sat_cons (step536 p h) (sat_cons (step547 p h) (sat_cons (step1207 p h) (sat_cons (step1294 p h) (sat_cons (step911 p h) (sat_cons (step907 p h) (sat_cons (step858 p h) (sat_cons (step857 p h) (sat_cons (step904 p h) (sat_cons (step905 p h) (sat_cons (step915 p h) (sat_cons (step899 p h) (sat_cons (step900 p h) (sat_cons (step889 p h) (sat_cons (step891 p h) (sat_cons (step355 p h) (sat_cons (step886 p h) (sat_cons (step883 p h) (sat_cons (step884 p h) (sat_cons (step339 p h) (sat_cons (step281 p h) (sat_cons (step375 p h) (sat_cons (step275 p h) (sat_cons (step313 p h) (sat_cons (step277 p h) (sat_cons (step314 p h) (sat_cons (step1022 p h) (sat_cons (step293 p h) (sat_cons (step189 p h) (sat_cons (step328 p h) (sat_cons (step185 p h) (sat_cons (step188 p h) (sat_cons (step308 p h) (sat_cons (step311 p h) (sat_cons (step898 p h) (sat_cons (step90 p h) (sat_cons (step191 p h) (sat_cons (step776 p h) (sat_cons (step295 p h) (sat_cons (step738 p h) (sat_cons (step778 p h) (sat_cons (step297 p h) (sat_cons (step1291 p h) (sat_cons (step786 p h) (sat_cons (step399 p h) (sat_cons (step400 p h) (sat_cons (step401 p h) (sat_cons (step801 p h) (sat_cons (step1016 p h) (sat_cons (step1027 p h) (sat_cons (step825 p h) (sat_cons (step1021 p h) (sat_cons (step1032 p h) (sat_cons (step984 p h) (sat_cons (step1051 p h) (sat_cons (step1200 p h) (sat_cons (step1120 p h) (sat_cons (step1191 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1302 : List Lit := [(6, true), (45, true), (43, false), (28, false), (152, true), (52, false)]
theorem step1302 (p : Nat → Bool) (h : Constraints p) : clause p c1302 = true :=
  Snake9.LocalRup.prove_clause [c539, c546, c241, c287, c261, c315] c1302 (by decide) p (sat_cons (step539 p h) (sat_cons (step546 p h) (sat_cons (step241 p h) (sat_cons (step287 p h) (sat_cons (step261 p h) (sat_cons (step315 p h) (sat_nil p)))))))
end B112E115
