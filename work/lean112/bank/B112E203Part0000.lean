import B112E203Inputs
namespace B112E203
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1273 : List Lit := [(105, true)]
theorem step1273 (p : Nat → Bool) (h : Constraints p) : clause p c1273 = true :=
  Snake9.LocalRup.prove_clause [c495, c494] c1273 (by decide) p (sat_cons (step495 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1274 : List Lit := [(222, true), (110, true)]
theorem step1274 (p : Nat → Bool) (h : Constraints p) : clause p c1274 = true :=
  Snake9.LocalRup.prove_clause [c1273, c496] c1274 (by decide) p (sat_cons (step1273 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1275 : List Lit := [(36, false)]
theorem step1275 (p : Nat → Bool) (h : Constraints p) : clause p c1275 = true :=
  Snake9.LocalRup.prove_clause [c535, c130] c1275 (by decide) p (sat_cons (step535 p h) (sat_cons (step130 p h) (sat_nil p)))
def c1276 : List Lit := [(42, false)]
theorem step1276 (p : Nat → Bool) (h : Constraints p) : clause p c1276 = true :=
  Snake9.LocalRup.prove_clause [c537, c141] c1276 (by decide) p (sat_cons (step537 p h) (sat_cons (step141 p h) (sat_nil p)))
def c1277 : List Lit := [(44, false)]
theorem step1277 (p : Nat → Bool) (h : Constraints p) : clause p c1277 = true :=
  Snake9.LocalRup.prove_clause [c538, c143] c1277 (by decide) p (sat_cons (step538 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1278 : List Lit := [(462, false)]
theorem step1278 (p : Nat → Bool) (h : Constraints p) : clause p c1278 = true :=
  Snake9.LocalRup.prove_clause [c731, c728] c1278 (by decide) p (sat_cons (step731 p h) (sat_cons (step728 p h) (sat_nil p)))
def c1279 : List Lit := [(348, false)]
theorem step1279 (p : Nat → Bool) (h : Constraints p) : clause p c1279 = true :=
  Snake9.LocalRup.prove_clause [c731, c730] c1279 (by decide) p (sat_cons (step731 p h) (sat_cons (step730 p h) (sat_nil p)))
def c1280 : List Lit := [(404, false)]
theorem step1280 (p : Nat → Bool) (h : Constraints p) : clause p c1280 = true :=
  Snake9.LocalRup.prove_clause [c1278, c727] c1280 (by decide) p (sat_cons (step1278 p h) (sat_cons (step727 p h) (sat_nil p)))
def c1281 : List Lit := [(346, false)]
theorem step1281 (p : Nat → Bool) (h : Constraints p) : clause p c1281 = true :=
  Snake9.LocalRup.prove_clause [c1279, c645] c1281 (by decide) p (sat_cons (step1279 p h) (sat_cons (step645 p h) (sat_nil p)))
def c1282 : List Lit := [(290, false)]
theorem step1282 (p : Nat → Bool) (h : Constraints p) : clause p c1282 = true :=
  Snake9.LocalRup.prove_clause [c1279, c648] c1282 (by decide) p (sat_cons (step1279 p h) (sat_cons (step648 p h) (sat_nil p)))
def c1283 : List Lit := [(402, false)]
theorem step1283 (p : Nat → Bool) (h : Constraints p) : clause p c1283 = true :=
  Snake9.LocalRup.prove_clause [c1280, c690] c1283 (by decide) p (sat_cons (step1280 p h) (sat_cons (step690 p h) (sat_nil p)))
def c1284 : List Lit := [(374, false)]
theorem step1284 (p : Nat → Bool) (h : Constraints p) : clause p c1284 = true :=
  Snake9.LocalRup.prove_clause [c1280, c693] c1284 (by decide) p (sat_cons (step1280 p h) (sat_cons (step693 p h) (sat_nil p)))
def c1285 : List Lit := [(344, false)]
theorem step1285 (p : Nat → Bool) (h : Constraints p) : clause p c1285 = true :=
  Snake9.LocalRup.prove_clause [c1281, c641] c1285 (by decide) p (sat_cons (step1281 p h) (sat_cons (step641 p h) (sat_nil p)))
def c1286 : List Lit := [(316, false)]
theorem step1286 (p : Nat → Bool) (h : Constraints p) : clause p c1286 = true :=
  Snake9.LocalRup.prove_clause [c1281, c643] c1286 (by decide) p (sat_cons (step1281 p h) (sat_cons (step643 p h) (sat_nil p)))
def c1287 : List Lit := [(288, false)]
theorem step1287 (p : Nat → Bool) (h : Constraints p) : clause p c1287 = true :=
  Snake9.LocalRup.prove_clause [c1282, c608] c1287 (by decide) p (sat_cons (step1282 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1288 : List Lit := [(260, false)]
theorem step1288 (p : Nat → Bool) (h : Constraints p) : clause p c1288 = true :=
  Snake9.LocalRup.prove_clause [c1282, c611] c1288 (by decide) p (sat_cons (step1282 p h) (sat_cons (step611 p h) (sat_nil p)))
def c1289 : List Lit := [(386, false)]
theorem step1289 (p : Nat → Bool) (h : Constraints p) : clause p c1289 = true :=
  Snake9.LocalRup.prove_clause [c1283, c688] c1289 (by decide) p (sat_cons (step1283 p h) (sat_cons (step688 p h) (sat_nil p)))
def c1290 : List Lit := [(372, false)]
theorem step1290 (p : Nat → Bool) (h : Constraints p) : clause p c1290 = true :=
  Snake9.LocalRup.prove_clause [c1284, c669] c1290 (by decide) p (sat_cons (step1284 p h) (sat_cons (step669 p h) (sat_nil p)))
def c1291 : List Lit := [(360, false)]
theorem step1291 (p : Nat → Bool) (h : Constraints p) : clause p c1291 = true :=
  Snake9.LocalRup.prove_clause [c1284, c672] c1291 (by decide) p (sat_cons (step1284 p h) (sat_cons (step672 p h) (sat_nil p)))
def c1292 : List Lit := [(286, false)]
theorem step1292 (p : Nat → Bool) (h : Constraints p) : clause p c1292 = true :=
  Snake9.LocalRup.prove_clause [c1287, c606] c1292 (by decide) p (sat_cons (step1287 p h) (sat_cons (step606 p h) (sat_nil p)))
def c1293 : List Lit := [(246, false)]
theorem step1293 (p : Nat → Bool) (h : Constraints p) : clause p c1293 = true :=
  Snake9.LocalRup.prove_clause [c1288, c594] c1293 (by decide) p (sat_cons (step1288 p h) (sat_cons (step594 p h) (sat_nil p)))
def c1294 : List Lit := [(378, false)]
theorem step1294 (p : Nat → Bool) (h : Constraints p) : clause p c1294 = true :=
  Snake9.LocalRup.prove_clause [c1289, c681] c1294 (by decide) p (sat_cons (step1289 p h) (sat_cons (step681 p h) (sat_nil p)))
def c1295 : List Lit := [(370, false)]
theorem step1295 (p : Nat → Bool) (h : Constraints p) : clause p c1295 = true :=
  Snake9.LocalRup.prove_clause [c1290, c666] c1295 (by decide) p (sat_cons (step1290 p h) (sat_cons (step666 p h) (sat_nil p)))
def c1296 : List Lit := [(278, false)]
theorem step1296 (p : Nat → Bool) (h : Constraints p) : clause p c1296 = true :=
  Snake9.LocalRup.prove_clause [c1292, c604] c1296 (by decide) p (sat_cons (step1292 p h) (sat_cons (step604 p h) (sat_nil p)))
def c1297 : List Lit := [(244, false)]
theorem step1297 (p : Nat → Bool) (h : Constraints p) : clause p c1297 = true :=
  Snake9.LocalRup.prove_clause [c1293, c581] c1297 (by decide) p (sat_cons (step1293 p h) (sat_cons (step581 p h) (sat_nil p)))
def c1298 : List Lit := [(376, false)]
theorem step1298 (p : Nat → Bool) (h : Constraints p) : clause p c1298 = true :=
  Snake9.LocalRup.prove_clause [c1294, c676] c1298 (by decide) p (sat_cons (step1294 p h) (sat_cons (step676 p h) (sat_nil p)))
def c1299 : List Lit := [(368, false)]
theorem step1299 (p : Nat → Bool) (h : Constraints p) : clause p c1299 = true :=
  Snake9.LocalRup.prove_clause [c1295, c663] c1299 (by decide) p (sat_cons (step1295 p h) (sat_cons (step663 p h) (sat_nil p)))
def c1300 : List Lit := [(240, false)]
theorem step1300 (p : Nat → Bool) (h : Constraints p) : clause p c1300 = true :=
  Snake9.LocalRup.prove_clause [c1297, c579] c1300 (by decide) p (sat_cons (step1297 p h) (sat_cons (step579 p h) (sat_nil p)))
def c1301 : List Lit := [(856, true)]
theorem step1301 (p : Nat → Bool) (h : Constraints p) : clause p c1301 = true :=
  Snake9.LocalRup.prove_clause [c1275, c835] c1301 (by decide) p (sat_cons (step1275 p h) (sat_cons (step835 p h) (sat_nil p)))
def c1302 : List Lit := [(34, true), (857, true)]
theorem step1302 (p : Nat → Bool) (h : Constraints p) : clause p c1302 = true :=
  Snake9.LocalRup.prove_clause [c1275, c836] c1302 (by decide) p (sat_cons (step1275 p h) (sat_cons (step836 p h) (sat_nil p)))
def c1303 : List Lit := [(860, true)]
theorem step1303 (p : Nat → Bool) (h : Constraints p) : clause p c1303 = true :=
  Snake9.LocalRup.prove_clause [c1301, c839] c1303 (by decide) p (sat_cons (step1301 p h) (sat_cons (step839 p h) (sat_nil p)))
def c1304 : List Lit := [(858, false), (861, true)]
theorem step1304 (p : Nat → Bool) (h : Constraints p) : clause p c1304 = true :=
  Snake9.LocalRup.prove_clause [c1301, c840] c1304 (by decide) p (sat_cons (step1301 p h) (sat_cons (step840 p h) (sat_nil p)))
def c1305 : List Lit := [(864, true)]
theorem step1305 (p : Nat → Bool) (h : Constraints p) : clause p c1305 = true :=
  Snake9.LocalRup.prove_clause [c1303, c843] c1305 (by decide) p (sat_cons (step1303 p h) (sat_cons (step843 p h) (sat_nil p)))
def c1306 : List Lit := [(853, false), (865, true)]
theorem step1306 (p : Nat → Bool) (h : Constraints p) : clause p c1306 = true :=
  Snake9.LocalRup.prove_clause [c1303, c845] c1306 (by decide) p (sat_cons (step1303 p h) (sat_cons (step845 p h) (sat_nil p)))
def c1307 : List Lit := [(854, false), (866, true)]
theorem step1307 (p : Nat → Bool) (h : Constraints p) : clause p c1307 = true :=
  Snake9.LocalRup.prove_clause [c1303, c847] c1307 (by decide) p (sat_cons (step1303 p h) (sat_cons (step847 p h) (sat_nil p)))
def c1308 : List Lit := [(872, true)]
theorem step1308 (p : Nat → Bool) (h : Constraints p) : clause p c1308 = true :=
  Snake9.LocalRup.prove_clause [c1276, c1277, c851] c1308 (by decide) p (sat_cons (step1276 p h) (sat_cons (step1277 p h) (sat_cons (step851 p h) (sat_nil p))))
def c1309 : List Lit := [(876, true)]
theorem step1309 (p : Nat → Bool) (h : Constraints p) : clause p c1309 = true :=
  Snake9.LocalRup.prove_clause [c1308, c855] c1309 (by decide) p (sat_cons (step1308 p h) (sat_cons (step855 p h) (sat_nil p)))
def c1310 : List Lit := [(873, false), (877, true)]
theorem step1310 (p : Nat → Bool) (h : Constraints p) : clause p c1310 = true :=
  Snake9.LocalRup.prove_clause [c1308, c856] c1310 (by decide) p (sat_cons (step1308 p h) (sat_cons (step856 p h) (sat_nil p)))
def c1311 : List Lit := [(874, false), (878, true)]
theorem step1311 (p : Nat → Bool) (h : Constraints p) : clause p c1311 = true :=
  Snake9.LocalRup.prove_clause [c1308, c857] c1311 (by decide) p (sat_cons (step1308 p h) (sat_cons (step857 p h) (sat_nil p)))
def c1312 : List Lit := [(883, false), (889, true)]
theorem step1312 (p : Nat → Bool) (h : Constraints p) : clause p c1312 = true :=
  Snake9.LocalRup.prove_clause [c1309, c872] c1312 (by decide) p (sat_cons (step1309 p h) (sat_cons (step872 p h) (sat_nil p)))
def c1313 : List Lit := [(884, false), (890, true)]
theorem step1313 (p : Nat → Bool) (h : Constraints p) : clause p c1313 = true :=
  Snake9.LocalRup.prove_clause [c1309, c873] c1313 (by decide) p (sat_cons (step1309 p h) (sat_cons (step873 p h) (sat_nil p)))
def c1314 : List Lit := [(885, false), (891, true)]
theorem step1314 (p : Nat → Bool) (h : Constraints p) : clause p c1314 = true :=
  Snake9.LocalRup.prove_clause [c1309, c874] c1314 (by decide) p (sat_cons (step1309 p h) (sat_cons (step874 p h) (sat_nil p)))
def c1315 : List Lit := [(886, false), (892, true)]
theorem step1315 (p : Nat → Bool) (h : Constraints p) : clause p c1315 = true :=
  Snake9.LocalRup.prove_clause [c1309, c875] c1315 (by decide) p (sat_cons (step1309 p h) (sat_cons (step875 p h) (sat_nil p)))
def c1316 : List Lit := [(889, false), (898, true)]
theorem step1316 (p : Nat → Bool) (h : Constraints p) : clause p c1316 = true :=
  Snake9.LocalRup.prove_clause [c1305, c888] c1316 (by decide) p (sat_cons (step1305 p h) (sat_cons (step888 p h) (sat_nil p)))
def c1317 : List Lit := [(890, false), (899, true)]
theorem step1317 (p : Nat → Bool) (h : Constraints p) : clause p c1317 = true :=
  Snake9.LocalRup.prove_clause [c1305, c889] c1317 (by decide) p (sat_cons (step1305 p h) (sat_cons (step889 p h) (sat_nil p)))
def c1318 : List Lit := [(891, false), (900, true)]
theorem step1318 (p : Nat → Bool) (h : Constraints p) : clause p c1318 = true :=
  Snake9.LocalRup.prove_clause [c1305, c890] c1318 (by decide) p (sat_cons (step1305 p h) (sat_cons (step890 p h) (sat_nil p)))
def c1319 : List Lit := [(892, false), (901, true)]
theorem step1319 (p : Nat → Bool) (h : Constraints p) : clause p c1319 = true :=
  Snake9.LocalRup.prove_clause [c1305, c891] c1319 (by decide) p (sat_cons (step1305 p h) (sat_cons (step891 p h) (sat_nil p)))
def c1320 : List Lit := [(893, false), (902, true)]
theorem step1320 (p : Nat → Bool) (h : Constraints p) : clause p c1320 = true :=
  Snake9.LocalRup.prove_clause [c1305, c892] c1320 (by decide) p (sat_cons (step1305 p h) (sat_cons (step892 p h) (sat_nil p)))
def c1321 : List Lit := [(894, false), (903, true)]
theorem step1321 (p : Nat → Bool) (h : Constraints p) : clause p c1321 = true :=
  Snake9.LocalRup.prove_clause [c1305, c893] c1321 (by decide) p (sat_cons (step1305 p h) (sat_cons (step893 p h) (sat_nil p)))
def c1322 : List Lit := [(75, false), (1551, true)]
theorem step1322 (p : Nat → Bool) (h : Constraints p) : clause p c1322 = true :=
  Snake9.LocalRup.prove_clause [c1298, c1194, c1192, c1193, c1195, c1191, c412, c1190, c423, c420, c417, c674] c1322 (by decide) p (sat_cons (step1298 p h) (sat_cons (step1194 p h) (sat_cons (step1192 p h) (sat_cons (step1193 p h) (sat_cons (step1195 p h) (sat_cons (step1191 p h) (sat_cons (step412 p h) (sat_cons (step1190 p h) (sat_cons (step423 p h) (sat_cons (step420 p h) (sat_cons (step417 p h) (sat_cons (step674 p h) (sat_nil p)))))))))))))
def c1323 : List Lit := [(1555, true), (1576, true)]
theorem step1323 (p : Nat → Bool) (h : Constraints p) : clause p c1323 = true :=
  Snake9.LocalRup.prove_clause [c1210, c1196, c1197, c1189, c1187, c1188, c1322, c1202, c1203, c1209, c1199, c1200, c1206, c1204, c1205, c379, c448, c431, c441] c1323 (by decide) p (sat_cons (step1210 p h) (sat_cons (step1196 p h) (sat_cons (step1197 p h) (sat_cons (step1189 p h) (sat_cons (step1187 p h) (sat_cons (step1188 p h) (sat_cons (step1322 p h) (sat_cons (step1202 p h) (sat_cons (step1203 p h) (sat_cons (step1209 p h) (sat_cons (step1199 p h) (sat_cons (step1200 p h) (sat_cons (step1206 p h) (sat_cons (step1204 p h) (sat_cons (step1205 p h) (sat_cons (step379 p h) (sat_cons (step448 p h) (sat_cons (step431 p h) (sat_cons (step441 p h) (sat_nil p))))))))))))))))))))
def c1324 : List Lit := [(1583, true)]
theorem step1324 (p : Nat → Bool) (h : Constraints p) : clause p c1324 = true :=
  Snake9.LocalRup.prove_clause [c1211, c1213, c1323, c1212, c1207, c1208, c1206, c1201, c1202, c1204, c1205, c1199, c1200, c1322, c448, c431, c1198, c441, c1189, c1187, c1188, c379] c1324 (by decide) p (sat_cons (step1211 p h) (sat_cons (step1213 p h) (sat_cons (step1323 p h) (sat_cons (step1212 p h) (sat_cons (step1207 p h) (sat_cons (step1208 p h) (sat_cons (step1206 p h) (sat_cons (step1201 p h) (sat_cons (step1202 p h) (sat_cons (step1204 p h) (sat_cons (step1205 p h) (sat_cons (step1199 p h) (sat_cons (step1200 p h) (sat_cons (step1322 p h) (sat_cons (step448 p h) (sat_cons (step431 p h) (sat_cons (step1198 p h) (sat_cons (step441 p h) (sat_cons (step1189 p h) (sat_cons (step1187 p h) (sat_cons (step1188 p h) (sat_cons (step379 p h) (sat_nil p)))))))))))))))))))))))
def c1325 : List Lit := [(1495, false), (1502, true)]
theorem step1325 (p : Nat → Bool) (h : Constraints p) : clause p c1325 = true :=
  Snake9.LocalRup.prove_clause [c1182, c1179, c1181, c1183, c1175, c1176, c1171, c1172, c1169, c1170, c1166, c1167, c288, c195, c259, c282] c1325 (by decide) p (sat_cons (step1182 p h) (sat_cons (step1179 p h) (sat_cons (step1181 p h) (sat_cons (step1183 p h) (sat_cons (step1175 p h) (sat_cons (step1176 p h) (sat_cons (step1171 p h) (sat_cons (step1172 p h) (sat_cons (step1169 p h) (sat_cons (step1170 p h) (sat_cons (step1166 p h) (sat_cons (step1167 p h) (sat_cons (step288 p h) (sat_cons (step195 p h) (sat_cons (step259 p h) (sat_cons (step282 p h) (sat_nil p)))))))))))))))))
def c1326 : List Lit := [(1485, false), (172, true), (1502, true)]
theorem step1326 (p : Nat → Bool) (h : Constraints p) : clause p c1326 = true :=
  Snake9.LocalRup.prove_clause [c1325, c1177, c1184, c1172, c1173, c1183, c1169, c1170, c1180, c1175, c1176, c287, c196, c284] c1326 (by decide) p (sat_cons (step1325 p h) (sat_cons (step1177 p h) (sat_cons (step1184 p h) (sat_cons (step1172 p h) (sat_cons (step1173 p h) (sat_cons (step1183 p h) (sat_cons (step1169 p h) (sat_cons (step1170 p h) (sat_cons (step1180 p h) (sat_cons (step1175 p h) (sat_cons (step1176 p h) (sat_cons (step287 p h) (sat_cons (step196 p h) (sat_cons (step284 p h) (sat_nil p)))))))))))))))
def c1327 : List Lit := [(1485, true), (1495, true)]
theorem step1327 (p : Nat → Bool) (h : Constraints p) : clause p c1327 = true :=
  Snake9.LocalRup.prove_clause [c731, c1178, c1177, c1166, c1167, c364, c186, c192, c363, c206, c649, c628, c650, c629, c655, c630, c670, c638, c691, c640, c725, c644, c729] c1327 (by decide) p (sat_cons (step731 p h) (sat_cons (step1178 p h) (sat_cons (step1177 p h) (sat_cons (step1166 p h) (sat_cons (step1167 p h) (sat_cons (step364 p h) (sat_cons (step186 p h) (sat_cons (step192 p h) (sat_cons (step363 p h) (sat_cons (step206 p h) (sat_cons (step649 p h) (sat_cons (step628 p h) (sat_cons (step650 p h) (sat_cons (step629 p h) (sat_cons (step655 p h) (sat_cons (step630 p h) (sat_cons (step670 p h) (sat_cons (step638 p h) (sat_cons (step691 p h) (sat_cons (step640 p h) (sat_cons (step725 p h) (sat_cons (step644 p h) (sat_cons (step729 p h) (sat_nil p))))))))))))))))))))))))
def c1328 : List Lit := [(1502, true)]
theorem step1328 (p : Nat → Bool) (h : Constraints p) : clause p c1328 = true :=
  Snake9.LocalRup.prove_clause [c1285, c1184, c1325, c1174, c1177, c1178, c1327, c1172, c1173, c1326, c1183, c1169, c1170, c281, c633, c1180, c196, c286, c282, c634, c1175, c259, c635, c1168, c639, c364, c242, c630, c205, c629, c628] c1328 (by decide) p (sat_cons (step1285 p h) (sat_cons (step1184 p h) (sat_cons (step1325 p h) (sat_cons (step1174 p h) (sat_cons (step1177 p h) (sat_cons (step1178 p h) (sat_cons (step1327 p h) (sat_cons (step1172 p h) (sat_cons (step1173 p h) (sat_cons (step1326 p h) (sat_cons (step1183 p h) (sat_cons (step1169 p h) (sat_cons (step1170 p h) (sat_cons (step281 p h) (sat_cons (step633 p h) (sat_cons (step1180 p h) (sat_cons (step196 p h) (sat_cons (step286 p h) (sat_cons (step282 p h) (sat_cons (step634 p h) (sat_cons (step1175 p h) (sat_cons (step259 p h) (sat_cons (step635 p h) (sat_cons (step1168 p h) (sat_cons (step639 p h) (sat_cons (step364 p h) (sat_cons (step242 p h) (sat_cons (step630 p h) (sat_cons (step205 p h) (sat_cons (step629 p h) (sat_cons (step628 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c1329 : List Lit := [(1002, true), (88, true), (89, true), (57, true)]
theorem step1329 (p : Nat → Bool) (h : Constraints p) : clause p c1329 = true :=
  Snake9.LocalRup.prove_clause [c559, c1056, c1058, c1079, c1077, c1059, c1069, c1071, c1057, c1066, c1064, c470, c472] c1329 (by decide) p (sat_cons (step559 p h) (sat_cons (step1056 p h) (sat_cons (step1058 p h) (sat_cons (step1079 p h) (sat_cons (step1077 p h) (sat_cons (step1059 p h) (sat_cons (step1069 p h) (sat_cons (step1071 p h) (sat_cons (step1057 p h) (sat_cons (step1066 p h) (sat_cons (step1064 p h) (sat_cons (step470 p h) (sat_cons (step472 p h) (sat_nil p))))))))))))))
def c1330 : List Lit := [(961, true)]
theorem step1330 (p : Nat → Bool) (h : Constraints p) : clause p c1330 = true :=
  Snake9.LocalRup.prove_clause [c554, c1008, c1010, c1005, c1006, c1002, c446, c444] c1330 (by decide) p (sat_cons (step554 p h) (sat_cons (step1008 p h) (sat_cons (step1010 p h) (sat_cons (step1005 p h) (sat_cons (step1006 p h) (sat_cons (step1002 p h) (sat_cons (step446 p h) (sat_cons (step444 p h) (sat_nil p)))))))))
def c1331 : List Lit := [(965, true)]
theorem step1331 (p : Nat → Bool) (h : Constraints p) : clause p c1331 = true :=
  Snake9.LocalRup.prove_clause [c1330, c1015] c1331 (by decide) p (sat_cons (step1330 p h) (sat_cons (step1015 p h) (sat_nil p)))
def c1332 : List Lit := [(973, true)]
theorem step1332 (p : Nat → Bool) (h : Constraints p) : clause p c1332 = true :=
  Snake9.LocalRup.prove_clause [c1331, c1025] c1332 (by decide) p (sat_cons (step1331 p h) (sat_cons (step1025 p h) (sat_nil p)))
def c1333 : List Lit := [(934, true), (881, true)]
theorem step1333 (p : Nat → Bool) (h : Constraints p) : clause p c1333 = true :=
  Snake9.LocalRup.prove_clause [c544, c862, c861, c955, c956, c385, c374, c376] c1333 (by decide) p (sat_cons (step544 p h) (sat_cons (step862 p h) (sat_cons (step861 p h) (sat_cons (step955 p h) (sat_cons (step956 p h) (sat_cons (step385 p h) (sat_cons (step374 p h) (sat_cons (step376 p h) (sat_nil p)))))))))
def c1334 : List Lit := [(830, true)]
theorem step1334 (p : Nat → Bool) (h : Constraints p) : clause p c1334 = true :=
  Snake9.LocalRup.prove_clause [c527, c787, c791, c781, c768, c770, c773, c774, c766, c92, c54, c57] c1334 (by decide) p (sat_cons (step527 p h) (sat_cons (step787 p h) (sat_cons (step791 p h) (sat_cons (step781 p h) (sat_cons (step768 p h) (sat_cons (step770 p h) (sat_cons (step773 p h) (sat_cons (step774 p h) (sat_cons (step766 p h) (sat_cons (step92 p h) (sat_cons (step54 p h) (sat_cons (step57 p h) (sat_nil p)))))))))))))
def c1335 : List Lit := [(17, false), (822, true), (820, true)]
theorem step1335 (p : Nat → Bool) (h : Constraints p) : clause p c1335 = true :=
  Snake9.LocalRup.prove_clause [c529, c774, c773, c96, c98, c77, c82, c771, c765] c1335 (by decide) p (sat_cons (step529 p h) (sat_cons (step774 p h) (sat_cons (step773 p h) (sat_cons (step96 p h) (sat_cons (step98 p h) (sat_cons (step77 p h) (sat_cons (step82 p h) (sat_cons (step771 p h) (sat_cons (step765 p h) (sat_nil p))))))))))
def c1336 : List Lit := [(822, true), (1, false), (820, true)]
theorem step1336 (p : Nat → Bool) (h : Constraints p) : clause p c1336 = true :=
  Snake9.LocalRup.prove_clause [c527, c769, c773, c774, c1335, c766, c767, c771, c79, c50, c58] c1336 (by decide) p (sat_cons (step527 p h) (sat_cons (step769 p h) (sat_cons (step773 p h) (sat_cons (step774 p h) (sat_cons (step1335 p h) (sat_cons (step766 p h) (sat_cons (step767 p h) (sat_cons (step771 p h) (sat_cons (step79 p h) (sat_cons (step50 p h) (sat_cons (step58 p h) (sat_nil p))))))))))))
end B112E203
