import B112E187Part0003
namespace B112E187
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1273 : List Lit := [(28, false), (32, true), (80, true)]
theorem step1273 (p : Nat → Bool) (h : Constraints p) : clause p c1273 = true :=
  Snake9.LocalRup.prove_clause [c403, c30] c1273 (by decide) p (sat_cons (step403 p h) (sat_cons (step30 p h) (sat_nil p)))
def c1274 : List Lit := [(29, true), (28, false), (80, true)]
theorem step1274 (p : Nat → Bool) (h : Constraints p) : clause p c1274 = true :=
  Snake9.LocalRup.prove_clause [c403, c31] c1274 (by decide) p (sat_cons (step403 p h) (sat_cons (step31 p h) (sat_nil p)))
def c1275 : List Lit := [(39, true), (37, false), (93, true)]
theorem step1275 (p : Nat → Bool) (h : Constraints p) : clause p c1275 = true :=
  Snake9.LocalRup.prove_clause [c404, c64] c1275 (by decide) p (sat_cons (step404 p h) (sat_cons (step64 p h) (sat_nil p)))
def c1276 : List Lit := [(37, false), (29, true), (93, true)]
theorem step1276 (p : Nat → Bool) (h : Constraints p) : clause p c1276 = true :=
  Snake9.LocalRup.prove_clause [c404, c65] c1276 (by decide) p (sat_cons (step404 p h) (sat_cons (step65 p h) (sat_nil p)))
def c1277 : List Lit := [(38, false), (41, true), (39, true)]
theorem step1277 (p : Nat → Bool) (h : Constraints p) : clause p c1277 = true :=
  Snake9.LocalRup.prove_clause [c405, c67] c1277 (by decide) p (sat_cons (step405 p h) (sat_cons (step67 p h) (sat_nil p)))
def c1278 : List Lit := [(38, false), (40, true), (39, true)]
theorem step1278 (p : Nat → Bool) (h : Constraints p) : clause p c1278 = true :=
  Snake9.LocalRup.prove_clause [c405, c68] c1278 (by decide) p (sat_cons (step405 p h) (sat_cons (step68 p h) (sat_nil p)))
def c1279 : List Lit := [(43, false), (42, true)]
theorem step1279 (p : Nat → Bool) (h : Constraints p) : clause p c1279 = true :=
  Snake9.LocalRup.prove_clause [c406, c76] c1279 (by decide) p (sat_cons (step406 p h) (sat_cons (step76 p h) (sat_nil p)))
def c1280 : List Lit := [(43, false), (35, true)]
theorem step1280 (p : Nat → Bool) (h : Constraints p) : clause p c1280 = true :=
  Snake9.LocalRup.prove_clause [c406, c77] c1280 (by decide) p (sat_cons (step406 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1281 : List Lit := [(45, false), (49, true), (80, true)]
theorem step1281 (p : Nat → Bool) (h : Constraints p) : clause p c1281 = true :=
  Snake9.LocalRup.prove_clause [c407, c80] c1281 (by decide) p (sat_cons (step407 p h) (sat_cons (step80 p h) (sat_nil p)))
def c1282 : List Lit := [(45, false), (46, true), (80, true)]
theorem step1282 (p : Nat → Bool) (h : Constraints p) : clause p c1282 = true :=
  Snake9.LocalRup.prove_clause [c407, c81] c1282 (by decide) p (sat_cons (step407 p h) (sat_cons (step81 p h) (sat_nil p)))
def c1283 : List Lit := [(50, false), (52, true), (46, true), (51, true), (68, true)]
theorem step1283 (p : Nat → Bool) (h : Constraints p) : clause p c1283 = true :=
  Snake9.LocalRup.prove_clause [c408, c105] c1283 (by decide) p (sat_cons (step408 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1284 : List Lit := [(52, true), (50, false), (49, true), (46, true), (51, true)]
theorem step1284 (p : Nat → Bool) (h : Constraints p) : clause p c1284 = true :=
  Snake9.LocalRup.prove_clause [c408, c106] c1284 (by decide) p (sat_cons (step408 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1285 : List Lit := [(53, false), (51, true), (48, true), (92, true)]
theorem step1285 (p : Nat → Bool) (h : Constraints p) : clause p c1285 = true :=
  Snake9.LocalRup.prove_clause [c409, c121] c1285 (by decide) p (sat_cons (step409 p h) (sat_cons (step121 p h) (sat_nil p)))
def c1286 : List Lit := [(54, false), (56, true), (93, true)]
theorem step1286 (p : Nat → Bool) (h : Constraints p) : clause p c1286 = true :=
  Snake9.LocalRup.prove_clause [c410, c123] c1286 (by decide) p (sat_cons (step410 p h) (sat_cons (step123 p h) (sat_nil p)))
def c1287 : List Lit := [(54, false), (46, true), (93, true)]
theorem step1287 (p : Nat → Bool) (h : Constraints p) : clause p c1287 = true :=
  Snake9.LocalRup.prove_clause [c410, c124] c1287 (by decide) p (sat_cons (step410 p h) (sat_cons (step124 p h) (sat_nil p)))
def c1288 : List Lit := [(61, false), (60, true)]
theorem step1288 (p : Nat → Bool) (h : Constraints p) : clause p c1288 = true :=
  Snake9.LocalRup.prove_clause [c411, c142] c1288 (by decide) p (sat_cons (step411 p h) (sat_cons (step142 p h) (sat_nil p)))
def c1289 : List Lit := [(61, false), (52, true)]
theorem step1289 (p : Nat → Bool) (h : Constraints p) : clause p c1289 = true :=
  Snake9.LocalRup.prove_clause [c411, c143] c1289 (by decide) p (sat_cons (step411 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1290 : List Lit := [(62, false), (58, true), (59, true)]
theorem step1290 (p : Nat → Bool) (h : Constraints p) : clause p c1290 = true :=
  Snake9.LocalRup.prove_clause [c412, c145] c1290 (by decide) p (sat_cons (step412 p h) (sat_cons (step145 p h) (sat_nil p)))
def c1291 : List Lit := [(63, false), (66, true)]
theorem step1291 (p : Nat → Bool) (h : Constraints p) : clause p c1291 = true :=
  Snake9.LocalRup.prove_clause [c413, c146] c1291 (by decide) p (sat_cons (step413 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1292 : List Lit := [(71, false), (70, true), (66, true)]
theorem step1292 (p : Nat → Bool) (h : Constraints p) : clause p c1292 = true :=
  Snake9.LocalRup.prove_clause [c414, c160] c1292 (by decide) p (sat_cons (step414 p h) (sat_cons (step160 p h) (sat_nil p)))
def c1293 : List Lit := [(76, false), (77, false), (75, false)]
theorem step1293 (p : Nat → Bool) (h : Constraints p) : clause p c1293 = true :=
  Snake9.LocalRup.prove_clause [c390, c167] c1293 (by decide) p (sat_cons (step390 p h) (sat_cons (step167 p h) (sat_nil p)))
def c1294 : List Lit := [(78, true), (76, false), (75, true)]
theorem step1294 (p : Nat → Bool) (h : Constraints p) : clause p c1294 = true :=
  Snake9.LocalRup.prove_clause [c415, c170] c1294 (by decide) p (sat_cons (step415 p h) (sat_cons (step170 p h) (sat_nil p)))
def c1295 : List Lit := [(32, true), (87, false), (90, true), (107, true), (80, true), (98, true), (88, true)]
theorem step1295 (p : Nat → Bool) (h : Constraints p) : clause p c1295 = true :=
  Snake9.LocalRup.prove_clause [c417, c252] c1295 (by decide) p (sat_cons (step417 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1296 : List Lit := [(34, true), (88, true), (51, true), (89, false), (92, true), (101, true)]
theorem step1296 (p : Nat → Bool) (h : Constraints p) : clause p c1296 = true :=
  Snake9.LocalRup.prove_clause [c418, c274] c1296 (by decide) p (sat_cons (step418 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1297 : List Lit := [(91, false), (88, true), (85, true), (92, true)]
theorem step1297 (p : Nat → Bool) (h : Constraints p) : clause p c1297 = true :=
  Snake9.LocalRup.prove_clause [c419, c284] c1297 (by decide) p (sat_cons (step419 p h) (sat_cons (step284 p h) (sat_nil p)))
def c1298 : List Lit := [(39, true), (94, false), (114, true), (93, true), (101, true), (97, true)]
theorem step1298 (p : Nat → Bool) (h : Constraints p) : clause p c1298 = true :=
  Snake9.LocalRup.prove_clause [c420, c309] c1298 (by decide) p (sat_cons (step420 p h) (sat_cons (step309 p h) (sat_nil p)))
def c1299 : List Lit := [(99, false), (87, false), (98, false)]
theorem step1299 (p : Nat → Bool) (h : Constraints p) : clause p c1299 = true :=
  Snake9.LocalRup.prove_clause [c390, c325] c1299 (by decide) p (sat_cons (step390 p h) (sat_cons (step325 p h) (sat_nil p)))
def c1300 : List Lit := [(100, false), (87, false), (98, false)]
theorem step1300 (p : Nat → Bool) (h : Constraints p) : clause p c1300 = true :=
  Snake9.LocalRup.prove_clause [c390, c326] c1300 (by decide) p (sat_cons (step390 p h) (sat_cons (step326 p h) (sat_nil p)))
def c1301 : List Lit := [(99, false), (101, true), (93, true)]
theorem step1301 (p : Nat → Bool) (h : Constraints p) : clause p c1301 = true :=
  Snake9.LocalRup.prove_clause [c421, c329] c1301 (by decide) p (sat_cons (step421 p h) (sat_cons (step329 p h) (sat_nil p)))
def c1302 : List Lit := [(99, false), (93, true), (98, true)]
theorem step1302 (p : Nat → Bool) (h : Constraints p) : clause p c1302 = true :=
  Snake9.LocalRup.prove_clause [c421, c330] c1302 (by decide) p (sat_cons (step421 p h) (sat_cons (step330 p h) (sat_nil p)))
def c1303 : List Lit := [(102, false), (101, true), (92, true)]
theorem step1303 (p : Nat → Bool) (h : Constraints p) : clause p c1303 = true :=
  Snake9.LocalRup.prove_clause [c422, c341] c1303 (by decide) p (sat_cons (step422 p h) (sat_cons (step341 p h) (sat_nil p)))
def c1304 : List Lit := [(103, false), (80, true), (111, true), (107, true)]
theorem step1304 (p : Nat → Bool) (h : Constraints p) : clause p c1304 = true :=
  Snake9.LocalRup.prove_clause [c423, c343] c1304 (by decide) p (sat_cons (step423 p h) (sat_cons (step343 p h) (sat_nil p)))
def c1305 : List Lit := [(103, false), (87, false), (107, false)]
theorem step1305 (p : Nat → Bool) (h : Constraints p) : clause p c1305 = true :=
  Snake9.LocalRup.prove_clause [c390, c355] c1305 (by decide) p (sat_cons (step390 p h) (sat_cons (step355 p h) (sat_nil p)))
def c1306 : List Lit := [(110, false), (109, true), (92, true)]
theorem step1306 (p : Nat → Bool) (h : Constraints p) : clause p c1306 = true :=
  Snake9.LocalRup.prove_clause [c425, c365] c1306 (by decide) p (sat_cons (step425 p h) (sat_cons (step365 p h) (sat_nil p)))
def c1307 : List Lit := [(110, false), (108, true), (92, true)]
theorem step1307 (p : Nat → Bool) (h : Constraints p) : clause p c1307 = true :=
  Snake9.LocalRup.prove_clause [c425, c366] c1307 (by decide) p (sat_cons (step425 p h) (sat_cons (step366 p h) (sat_nil p)))
def c1308 : List Lit := [(112, false), (114, true), (93, true), (111, true)]
theorem step1308 (p : Nat → Bool) (h : Constraints p) : clause p c1308 = true :=
  Snake9.LocalRup.prove_clause [c426, c370] c1308 (by decide) p (sat_cons (step426 p h) (sat_cons (step370 p h) (sat_nil p)))
def c1309 : List Lit := [(93, true), (112, false), (104, true), (111, true)]
theorem step1309 (p : Nat → Bool) (h : Constraints p) : clause p c1309 = true :=
  Snake9.LocalRup.prove_clause [c426, c371] c1309 (by decide) p (sat_cons (step426 p h) (sat_cons (step371 p h) (sat_nil p)))
def c1310 : List Lit := [(113, false), (115, true), (111, true)]
theorem step1310 (p : Nat → Bool) (h : Constraints p) : clause p c1310 = true :=
  Snake9.LocalRup.prove_clause [c427, c373] c1310 (by decide) p (sat_cons (step427 p h) (sat_cons (step373 p h) (sat_nil p)))
def c1311 : List Lit := [(113, false), (114, true), (111, true)]
theorem step1311 (p : Nat → Bool) (h : Constraints p) : clause p c1311 = true :=
  Snake9.LocalRup.prove_clause [c427, c374] c1311 (by decide) p (sat_cons (step427 p h) (sat_cons (step374 p h) (sat_nil p)))
def c1312 : List Lit := [(75, false), (98, false)]
theorem step1312 (p : Nat → Bool) (h : Constraints p) : clause p c1312 = true :=
  Snake9.LocalRup.prove_clause [c391, c380] c1312 (by decide) p (sat_cons (step391 p h) (sat_cons (step380 p h) (sat_nil p)))
def c1313 : List Lit := [(75, false), (107, false)]
theorem step1313 (p : Nat → Bool) (h : Constraints p) : clause p c1313 = true :=
  Snake9.LocalRup.prove_clause [c391, c381] c1313 (by decide) p (sat_cons (step391 p h) (sat_cons (step381 p h) (sat_nil p)))
def c1314 : List Lit := [(75, false), (111, false)]
theorem step1314 (p : Nat → Bool) (h : Constraints p) : clause p c1314 = true :=
  Snake9.LocalRup.prove_clause [c391, c382] c1314 (by decide) p (sat_cons (step391 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1315 : List Lit := [(75, false), (117, false)]
theorem step1315 (p : Nat → Bool) (h : Constraints p) : clause p c1315 = true :=
  Snake9.LocalRup.prove_clause [c391, c383] c1315 (by decide) p (sat_cons (step391 p h) (sat_cons (step383 p h) (sat_nil p)))
def c1316 : List Lit := [(98, false), (107, false)]
theorem step1316 (p : Nat → Bool) (h : Constraints p) : clause p c1316 = true :=
  Snake9.LocalRup.prove_clause [c391, c384] c1316 (by decide) p (sat_cons (step391 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1317 : List Lit := [(98, false), (111, false)]
theorem step1317 (p : Nat → Bool) (h : Constraints p) : clause p c1317 = true :=
  Snake9.LocalRup.prove_clause [c391, c385] c1317 (by decide) p (sat_cons (step391 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1318 : List Lit := [(98, false), (117, false)]
theorem step1318 (p : Nat → Bool) (h : Constraints p) : clause p c1318 = true :=
  Snake9.LocalRup.prove_clause [c391, c386] c1318 (by decide) p (sat_cons (step391 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1319 : List Lit := [(107, false), (111, false)]
theorem step1319 (p : Nat → Bool) (h : Constraints p) : clause p c1319 = true :=
  Snake9.LocalRup.prove_clause [c391, c387] c1319 (by decide) p (sat_cons (step391 p h) (sat_cons (step387 p h) (sat_nil p)))
def c1320 : List Lit := [(107, false), (117, false)]
theorem step1320 (p : Nat → Bool) (h : Constraints p) : clause p c1320 = true :=
  Snake9.LocalRup.prove_clause [c391, c388] c1320 (by decide) p (sat_cons (step391 p h) (sat_cons (step388 p h) (sat_nil p)))
def c1321 : List Lit := [(111, false), (117, false)]
theorem step1321 (p : Nat → Bool) (h : Constraints p) : clause p c1321 = true :=
  Snake9.LocalRup.prove_clause [c391, c389] c1321 (by decide) p (sat_cons (step391 p h) (sat_cons (step389 p h) (sat_nil p)))
def c1322 : List Lit := [(118, false), (117, true)]
theorem step1322 (p : Nat → Bool) (h : Constraints p) : clause p c1322 = true :=
  Snake9.LocalRup.prove_clause [c428, c393] c1322 (by decide) p (sat_cons (step428 p h) (sat_cons (step393 p h) (sat_nil p)))
def c1323 : List Lit := [(119, false), (117, true)]
theorem step1323 (p : Nat → Bool) (h : Constraints p) : clause p c1323 = true :=
  Snake9.LocalRup.prove_clause [c429, c394] c1323 (by decide) p (sat_cons (step429 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1324 : List Lit := [(263, false), (291, false)]
theorem step1324 (p : Nat → Bool) (h : Constraints p) : clause p c1324 = true :=
  Snake9.LocalRup.prove_clause [c1027, c468] c1324 (by decide) p (sat_cons (step1027 p h) (sat_cons (step468 p h) (sat_nil p)))
def c1325 : List Lit := [(150, false), (151, false)]
theorem step1325 (p : Nat → Bool) (h : Constraints p) : clause p c1325 = true :=
  Snake9.LocalRup.prove_clause [c1055, c471] c1325 (by decide) p (sat_cons (step1055 p h) (sat_cons (step471 p h) (sat_nil p)))
def c1326 : List Lit := [(299, false), (301, false)]
theorem step1326 (p : Nat → Bool) (h : Constraints p) : clause p c1326 = true :=
  Snake9.LocalRup.prove_clause [c1050, c478] c1326 (by decide) p (sat_cons (step1050 p h) (sat_cons (step478 p h) (sat_nil p)))
def c1327 : List Lit := [(297, false), (303, false)]
theorem step1327 (p : Nat → Bool) (h : Constraints p) : clause p c1327 = true :=
  Snake9.LocalRup.prove_clause [c1043, c482] c1327 (by decide) p (sat_cons (step1043 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1328 : List Lit := [(160, false), (161, false)]
theorem step1328 (p : Nat → Bool) (h : Constraints p) : clause p c1328 = true :=
  Snake9.LocalRup.prove_clause [c1054, c489] c1328 (by decide) p (sat_cons (step1054 p h) (sat_cons (step489 p h) (sat_nil p)))
def c1329 : List Lit := [(305, false), (319, false)]
theorem step1329 (p : Nat → Bool) (h : Constraints p) : clause p c1329 = true :=
  Snake9.LocalRup.prove_clause [c1033, c498] c1329 (by decide) p (sat_cons (step1033 p h) (sat_cons (step498 p h) (sat_nil p)))
def c1330 : List Lit := [(327, false), (329, false)]
theorem step1330 (p : Nat → Bool) (h : Constraints p) : clause p c1330 = true :=
  Snake9.LocalRup.prove_clause [c1048, c506] c1330 (by decide) p (sat_cons (step1048 p h) (sat_cons (step506 p h) (sat_nil p)))
def c1331 : List Lit := [(325, false), (331, false)]
theorem step1331 (p : Nat → Bool) (h : Constraints p) : clause p c1331 = true :=
  Snake9.LocalRup.prove_clause [c1041, c510] c1331 (by decide) p (sat_cons (step1041 p h) (sat_cons (step510 p h) (sat_nil p)))
def c1332 : List Lit := [(341, false), (343, false)]
theorem step1332 (p : Nat → Bool) (h : Constraints p) : clause p c1332 = true :=
  Snake9.LocalRup.prove_clause [c1047, c518] c1332 (by decide) p (sat_cons (step1047 p h) (sat_cons (step518 p h) (sat_nil p)))
def c1333 : List Lit := [(339, false), (345, false)]
theorem step1333 (p : Nat → Bool) (h : Constraints p) : clause p c1333 = true :=
  Snake9.LocalRup.prove_clause [c1040, c522] c1333 (by decide) p (sat_cons (step1040 p h) (sat_cons (step522 p h) (sat_nil p)))
def c1334 : List Lit := [(333, false), (347, false)]
theorem step1334 (p : Nat → Bool) (h : Constraints p) : clause p c1334 = true :=
  Snake9.LocalRup.prove_clause [c1032, c526] c1334 (by decide) p (sat_cons (step1032 p h) (sat_cons (step526 p h) (sat_nil p)))
def c1335 : List Lit := [(321, false), (349, false)]
theorem step1335 (p : Nat → Bool) (h : Constraints p) : clause p c1335 = true :=
  Snake9.LocalRup.prove_clause [c1026, c531] c1335 (by decide) p (sat_cons (step1026 p h) (sat_cons (step531 p h) (sat_nil p)))
def c1336 : List Lit := [(293, false), (351, false)]
theorem step1336 (p : Nat → Bool) (h : Constraints p) : clause p c1336 = true :=
  Snake9.LocalRup.prove_clause [c1023, c536] c1336 (by decide) p (sat_cons (step1023 p h) (sat_cons (step536 p h) (sat_nil p)))
end B112E187
