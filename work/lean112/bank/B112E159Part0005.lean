import B112E159Part0004
namespace B112E159
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1325 : List Lit := [(16, true), (48, true), (40, true), (37, false)]
theorem step1325 (p : Nat → Bool) (h : Constraints p) : clause p c1325 = true :=
  Snake9.LocalRup.prove_clause [c405, c168] c1325 (by decide) p (sat_cons (step405 p h) (sat_cons (step168 p h) (sat_nil p)))
def c1326 : List Lit := [(16, true), (38, true), (40, true), (37, false)]
theorem step1326 (p : Nat → Bool) (h : Constraints p) : clause p c1326 = true :=
  Snake9.LocalRup.prove_clause [c405, c169] c1326 (by decide) p (sat_cons (step405 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1327 : List Lit := [(17, true), (42, true), (33, true), (38, true), (39, false)]
theorem step1327 (p : Nat → Bool) (h : Constraints p) : clause p c1327 = true :=
  Snake9.LocalRup.prove_clause [c406, c182] c1327 (by decide) p (sat_cons (step406 p h) (sat_cons (step182 p h) (sat_nil p)))
def c1328 : List Lit := [(47, true), (44, true), (34, true), (45, false)]
theorem step1328 (p : Nat → Bool) (h : Constraints p) : clause p c1328 = true :=
  Snake9.LocalRup.prove_clause [c407, c212] c1328 (by decide) p (sat_cons (step407 p h) (sat_cons (step212 p h) (sat_nil p)))
def c1329 : List Lit := [(47, true), (44, true), (26, true), (45, false)]
theorem step1329 (p : Nat → Bool) (h : Constraints p) : clause p c1329 = true :=
  Snake9.LocalRup.prove_clause [c407, c213] c1329 (by decide) p (sat_cons (step407 p h) (sat_cons (step213 p h) (sat_nil p)))
def c1330 : List Lit := [(47, true), (34, true), (45, false), (26, true)]
theorem step1330 (p : Nat → Bool) (h : Constraints p) : clause p c1330 = true :=
  Snake9.LocalRup.prove_clause [c407, c214] c1330 (by decide) p (sat_cons (step407 p h) (sat_cons (step214 p h) (sat_nil p)))
def c1331 : List Lit := [(44, true), (34, true), (26, true), (45, false)]
theorem step1331 (p : Nat → Bool) (h : Constraints p) : clause p c1331 = true :=
  Snake9.LocalRup.prove_clause [c407, c215] c1331 (by decide) p (sat_cons (step407 p h) (sat_cons (step215 p h) (sat_nil p)))
def c1332 : List Lit := [(114, true), (49, false), (48, true)]
theorem step1332 (p : Nat → Bool) (h : Constraints p) : clause p c1332 = true :=
  Snake9.LocalRup.prove_clause [c408, c230] c1332 (by decide) p (sat_cons (step408 p h) (sat_cons (step230 p h) (sat_nil p)))
def c1333 : List Lit := [(114, true), (38, true), (49, false)]
theorem step1333 (p : Nat → Bool) (h : Constraints p) : clause p c1333 = true :=
  Snake9.LocalRup.prove_clause [c408, c231] c1333 (by decide) p (sat_cons (step408 p h) (sat_cons (step231 p h) (sat_nil p)))
def c1334 : List Lit := [(48, true), (52, true), (50, false)]
theorem step1334 (p : Nat → Bool) (h : Constraints p) : clause p c1334 = true :=
  Snake9.LocalRup.prove_clause [c409, c233] c1334 (by decide) p (sat_cons (step409 p h) (sat_cons (step233 p h) (sat_nil p)))
def c1335 : List Lit := [(43, true), (52, true), (50, false)]
theorem step1335 (p : Nat → Bool) (h : Constraints p) : clause p c1335 = true :=
  Snake9.LocalRup.prove_clause [c409, c234] c1335 (by decide) p (sat_cons (step409 p h) (sat_cons (step234 p h) (sat_nil p)))
def c1336 : List Lit := [(43, true), (48, true), (50, false)]
theorem step1336 (p : Nat → Bool) (h : Constraints p) : clause p c1336 = true :=
  Snake9.LocalRup.prove_clause [c409, c235] c1336 (by decide) p (sat_cons (step409 p h) (sat_cons (step235 p h) (sat_nil p)))
def c1337 : List Lit := [(55, false), (64, true)]
theorem step1337 (p : Nat → Bool) (h : Constraints p) : clause p c1337 = true :=
  Snake9.LocalRup.prove_clause [c411, c262] c1337 (by decide) p (sat_cons (step411 p h) (sat_cons (step262 p h) (sat_nil p)))
def c1338 : List Lit := [(55, false), (53, true)]
theorem step1338 (p : Nat → Bool) (h : Constraints p) : clause p c1338 = true :=
  Snake9.LocalRup.prove_clause [c411, c263] c1338 (by decide) p (sat_cons (step411 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1339 : List Lit := [(56, true), (57, true), (58, false)]
theorem step1339 (p : Nat → Bool) (h : Constraints p) : clause p c1339 = true :=
  Snake9.LocalRup.prove_clause [c412, c267] c1339 (by decide) p (sat_cons (step412 p h) (sat_cons (step267 p h) (sat_nil p)))
def c1340 : List Lit := [(61, true), (59, false), (177, true)]
theorem step1340 (p : Nat → Bool) (h : Constraints p) : clause p c1340 = true :=
  Snake9.LocalRup.prove_clause [c1012, c269] c1340 (by decide) p (sat_cons (step1012 p h) (sat_cons (step269 p h) (sat_nil p)))
def c1341 : List Lit := [(59, false), (60, true), (177, true)]
theorem step1341 (p : Nat → Bool) (h : Constraints p) : clause p c1341 = true :=
  Snake9.LocalRup.prove_clause [c1012, c270] c1341 (by decide) p (sat_cons (step1012 p h) (sat_cons (step270 p h) (sat_nil p)))
def c1342 : List Lit := [(60, false), (62, true)]
theorem step1342 (p : Nat → Bool) (h : Constraints p) : clause p c1342 = true :=
  Snake9.LocalRup.prove_clause [c413, c271] c1342 (by decide) p (sat_cons (step413 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1343 : List Lit := [(60, false), (59, true)]
theorem step1343 (p : Nat → Bool) (h : Constraints p) : clause p c1343 = true :=
  Snake9.LocalRup.prove_clause [c413, c272] c1343 (by decide) p (sat_cons (step413 p h) (sat_cons (step272 p h) (sat_nil p)))
def c1344 : List Lit := [(61, false), (59, true)]
theorem step1344 (p : Nat → Bool) (h : Constraints p) : clause p c1344 = true :=
  Snake9.LocalRup.prove_clause [c414, c273] c1344 (by decide) p (sat_cons (step414 p h) (sat_cons (step273 p h) (sat_nil p)))
def c1345 : List Lit := [(61, false), (56, true)]
theorem step1345 (p : Nat → Bool) (h : Constraints p) : clause p c1345 = true :=
  Snake9.LocalRup.prove_clause [c414, c274] c1345 (by decide) p (sat_cons (step414 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1346 : List Lit := [(67, false), (65, true)]
theorem step1346 (p : Nat → Bool) (h : Constraints p) : clause p c1346 = true :=
  Snake9.LocalRup.prove_clause [c415, c285] c1346 (by decide) p (sat_cons (step415 p h) (sat_cons (step285 p h) (sat_nil p)))
def c1347 : List Lit := [(67, false), (64, true)]
theorem step1347 (p : Nat → Bool) (h : Constraints p) : clause p c1347 = true :=
  Snake9.LocalRup.prove_clause [c415, c286] c1347 (by decide) p (sat_cons (step415 p h) (sat_cons (step286 p h) (sat_nil p)))
def c1348 : List Lit := [(68, false), (73, true)]
theorem step1348 (p : Nat → Bool) (h : Constraints p) : clause p c1348 = true :=
  Snake9.LocalRup.prove_clause [c416, c287] c1348 (by decide) p (sat_cons (step416 p h) (sat_cons (step287 p h) (sat_nil p)))
def c1349 : List Lit := [(72, false), (80, true)]
theorem step1349 (p : Nat → Bool) (h : Constraints p) : clause p c1349 = true :=
  Snake9.LocalRup.prove_clause [c417, c289] c1349 (by decide) p (sat_cons (step417 p h) (sat_cons (step289 p h) (sat_nil p)))
def c1350 : List Lit := [(72, false), (73, true)]
theorem step1350 (p : Nat → Bool) (h : Constraints p) : clause p c1350 = true :=
  Snake9.LocalRup.prove_clause [c417, c290] c1350 (by decide) p (sat_cons (step417 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1351 : List Lit := [(78, false), (83, true)]
theorem step1351 (p : Nat → Bool) (h : Constraints p) : clause p c1351 = true :=
  Snake9.LocalRup.prove_clause [c418, c292] c1351 (by decide) p (sat_cons (step418 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1352 : List Lit := [(82, false), (80, true)]
theorem step1352 (p : Nat → Bool) (h : Constraints p) : clause p c1352 = true :=
  Snake9.LocalRup.prove_clause [c420, c297] c1352 (by decide) p (sat_cons (step420 p h) (sat_cons (step297 p h) (sat_nil p)))
def c1353 : List Lit := [(84, false), (89, true)]
theorem step1353 (p : Nat → Bool) (h : Constraints p) : clause p c1353 = true :=
  Snake9.LocalRup.prove_clause [c421, c300] c1353 (by decide) p (sat_cons (step421 p h) (sat_cons (step300 p h) (sat_nil p)))
def c1354 : List Lit := [(84, false), (85, true)]
theorem step1354 (p : Nat → Bool) (h : Constraints p) : clause p c1354 = true :=
  Snake9.LocalRup.prove_clause [c421, c301] c1354 (by decide) p (sat_cons (step421 p h) (sat_cons (step301 p h) (sat_nil p)))
def c1355 : List Lit := [(96, true), (91, true), (87, false), (86, true)]
theorem step1355 (p : Nat → Bool) (h : Constraints p) : clause p c1355 = true :=
  Snake9.LocalRup.prove_clause [c422, c312] c1355 (by decide) p (sat_cons (step422 p h) (sat_cons (step312 p h) (sat_nil p)))
def c1356 : List Lit := [(97, true), (16, true), (88, false)]
theorem step1356 (p : Nat → Bool) (h : Constraints p) : clause p c1356 = true :=
  Snake9.LocalRup.prove_clause [c423, c315] c1356 (by decide) p (sat_cons (step423 p h) (sat_cons (step315 p h) (sat_nil p)))
def c1357 : List Lit := [(89, true), (16, true), (88, false)]
theorem step1357 (p : Nat → Bool) (h : Constraints p) : clause p c1357 = true :=
  Snake9.LocalRup.prove_clause [c423, c316] c1357 (by decide) p (sat_cons (step423 p h) (sat_cons (step316 p h) (sat_nil p)))
def c1358 : List Lit := [(86, true), (91, true), (90, false), (20, true)]
theorem step1358 (p : Nat → Bool) (h : Constraints p) : clause p c1358 = true :=
  Snake9.LocalRup.prove_clause [c424, c321] c1358 (by decide) p (sat_cons (step424 p h) (sat_cons (step321 p h) (sat_nil p)))
def c1359 : List Lit := [(89, true), (100, true), (98, false), (114, true)]
theorem step1359 (p : Nat → Bool) (h : Constraints p) : clause p c1359 = true :=
  Snake9.LocalRup.prove_clause [c426, c338] c1359 (by decide) p (sat_cons (step426 p h) (sat_cons (step338 p h) (sat_nil p)))
def c1360 : List Lit := [(99, false), (97, true)]
theorem step1360 (p : Nat → Bool) (h : Constraints p) : clause p c1360 = true :=
  Snake9.LocalRup.prove_clause [c427, c339] c1360 (by decide) p (sat_cons (step427 p h) (sat_cons (step339 p h) (sat_nil p)))
def c1361 : List Lit := [(99, false), (92, true)]
theorem step1361 (p : Nat → Bool) (h : Constraints p) : clause p c1361 = true :=
  Snake9.LocalRup.prove_clause [c427, c340] c1361 (by decide) p (sat_cons (step427 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1362 : List Lit := [(103, true), (109, true), (104, false)]
theorem step1362 (p : Nat → Bool) (h : Constraints p) : clause p c1362 = true :=
  Snake9.LocalRup.prove_clause [c429, c352] c1362 (by decide) p (sat_cons (step429 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1363 : List Lit := [(109, true), (34, true), (104, false)]
theorem step1363 (p : Nat → Bool) (h : Constraints p) : clause p c1363 = true :=
  Snake9.LocalRup.prove_clause [c429, c353] c1363 (by decide) p (sat_cons (step429 p h) (sat_cons (step353 p h) (sat_nil p)))
def c1364 : List Lit := [(103, true), (34, true), (104, false)]
theorem step1364 (p : Nat → Bool) (h : Constraints p) : clause p c1364 = true :=
  Snake9.LocalRup.prove_clause [c429, c354] c1364 (by decide) p (sat_cons (step429 p h) (sat_cons (step354 p h) (sat_nil p)))
def c1365 : List Lit := [(106, false), (107, true)]
theorem step1365 (p : Nat → Bool) (h : Constraints p) : clause p c1365 = true :=
  Snake9.LocalRup.prove_clause [c430, c355] c1365 (by decide) p (sat_cons (step430 p h) (sat_cons (step355 p h) (sat_nil p)))
def c1366 : List Lit := [(106, false), (102, true)]
theorem step1366 (p : Nat → Bool) (h : Constraints p) : clause p c1366 = true :=
  Snake9.LocalRup.prove_clause [c430, c356] c1366 (by decide) p (sat_cons (step430 p h) (sat_cons (step356 p h) (sat_nil p)))
def c1367 : List Lit := [(112, true), (114, true), (111, false)]
theorem step1367 (p : Nat → Bool) (h : Constraints p) : clause p c1367 = true :=
  Snake9.LocalRup.prove_clause [c431, c363] c1367 (by decide) p (sat_cons (step431 p h) (sat_cons (step363 p h) (sat_nil p)))
def c1368 : List Lit := [(118, true), (96, true), (113, false), (112, true)]
theorem step1368 (p : Nat → Bool) (h : Constraints p) : clause p c1368 = true :=
  Snake9.LocalRup.prove_clause [c432, c366] c1368 (by decide) p (sat_cons (step432 p h) (sat_cons (step366 p h) (sat_nil p)))
def c1369 : List Lit := [(118, true), (47, true), (113, false), (112, true)]
theorem step1369 (p : Nat → Bool) (h : Constraints p) : clause p c1369 = true :=
  Snake9.LocalRup.prove_clause [c432, c367] c1369 (by decide) p (sat_cons (step432 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1370 : List Lit := [(107, true), (118, true), (115, false), (112, true)]
theorem step1370 (p : Nat → Bool) (h : Constraints p) : clause p c1370 = true :=
  Snake9.LocalRup.prove_clause [c433, c382] c1370 (by decide) p (sat_cons (step433 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1371 : List Lit := [(118, true), (116, true), (117, false)]
theorem step1371 (p : Nat → Bool) (h : Constraints p) : clause p c1371 = true :=
  Snake9.LocalRup.prove_clause [c434, c385] c1371 (by decide) p (sat_cons (step434 p h) (sat_cons (step385 p h) (sat_nil p)))
def c1372 : List Lit := [(118, true), (52, true), (117, false)]
theorem step1372 (p : Nat → Bool) (h : Constraints p) : clause p c1372 = true :=
  Snake9.LocalRup.prove_clause [c434, c386] c1372 (by decide) p (sat_cons (step434 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1373 : List Lit := [(116, true), (52, true), (117, false)]
theorem step1373 (p : Nat → Bool) (h : Constraints p) : clause p c1373 = true :=
  Snake9.LocalRup.prove_clause [c434, c387] c1373 (by decide) p (sat_cons (step434 p h) (sat_cons (step387 p h) (sat_nil p)))
def c1374 : List Lit := [(239, false), (245, false)]
theorem step1374 (p : Nat → Bool) (h : Constraints p) : clause p c1374 = true :=
  Snake9.LocalRup.prove_clause [c1026, c440] c1374 (by decide) p (sat_cons (step1026 p h) (sat_cons (step440 p h) (sat_nil p)))
def c1375 : List Lit := [(247, false), (259, false)]
theorem step1375 (p : Nat → Bool) (h : Constraints p) : clause p c1375 = true :=
  Snake9.LocalRup.prove_clause [c1022, c448] c1375 (by decide) p (sat_cons (step1022 p h) (sat_cons (step448 p h) (sat_nil p)))
def c1376 : List Lit := [(261, false), (289, false)]
theorem step1376 (p : Nat → Bool) (h : Constraints p) : clause p c1376 = true :=
  Snake9.LocalRup.prove_clause [c1017, c465] c1376 (by decide) p (sat_cons (step1017 p h) (sat_cons (step465 p h) (sat_nil p)))
def c1377 : List Lit := [(161, false), (162, false)]
theorem step1377 (p : Nat → Bool) (h : Constraints p) : clause p c1377 = true :=
  Snake9.LocalRup.prove_clause [c1029, c472] c1377 (by decide) p (sat_cons (step1029 p h) (sat_cons (step472 p h) (sat_nil p)))
def c1378 : List Lit := [(291, false), (347, false)]
theorem step1378 (p : Nat → Bool) (h : Constraints p) : clause p c1378 = true :=
  Snake9.LocalRup.prove_clause [c1014, c507] c1378 (by decide) p (sat_cons (step1014 p h) (sat_cons (step507 p h) (sat_nil p)))
def c1379 : List Lit := [(349, false), (465, false)]
theorem step1379 (p : Nat → Bool) (h : Constraints p) : clause p c1379 = true :=
  Snake9.LocalRup.prove_clause [c566, c564] c1379 (by decide) p (sat_cons (step566 p h) (sat_cons (step564 p h) (sat_nil p)))
def c1380 : List Lit := [(806, false), (811, true)]
theorem step1380 (p : Nat → Bool) (h : Constraints p) : clause p c1380 = true :=
  Snake9.LocalRup.prove_clause [c1048, c579] c1380 (by decide) p (sat_cons (step1048 p h) (sat_cons (step579 p h) (sat_nil p)))
def c1381 : List Lit := [(816, true), (804, false)]
theorem step1381 (p : Nat → Bool) (h : Constraints p) : clause p c1381 = true :=
  Snake9.LocalRup.prove_clause [c1049, c583] c1381 (by decide) p (sat_cons (step1049 p h) (sat_cons (step583 p h) (sat_nil p)))
def c1382 : List Lit := [(805, false), (817, true)]
theorem step1382 (p : Nat → Bool) (h : Constraints p) : clause p c1382 = true :=
  Snake9.LocalRup.prove_clause [c1049, c585] c1382 (by decide) p (sat_cons (step1049 p h) (sat_cons (step585 p h) (sat_nil p)))
def c1383 : List Lit := [(843, true), (834, false)]
theorem step1383 (p : Nat → Bool) (h : Constraints p) : clause p c1383 = true :=
  Snake9.LocalRup.prove_clause [c1050, c626] c1383 (by decide) p (sat_cons (step1050 p h) (sat_cons (step626 p h) (sat_nil p)))
def c1384 : List Lit := [(844, true), (835, false)]
theorem step1384 (p : Nat → Bool) (h : Constraints p) : clause p c1384 = true :=
  Snake9.LocalRup.prove_clause [c1050, c627] c1384 (by decide) p (sat_cons (step1050 p h) (sat_cons (step627 p h) (sat_nil p)))
def c1385 : List Lit := [(845, true), (836, false)]
theorem step1385 (p : Nat → Bool) (h : Constraints p) : clause p c1385 = true :=
  Snake9.LocalRup.prove_clause [c1050, c628] c1385 (by decide) p (sat_cons (step1050 p h) (sat_cons (step628 p h) (sat_nil p)))
def c1386 : List Lit := [(846, true), (837, false)]
theorem step1386 (p : Nat → Bool) (h : Constraints p) : clause p c1386 = true :=
  Snake9.LocalRup.prove_clause [c1050, c629] c1386 (by decide) p (sat_cons (step1050 p h) (sat_cons (step629 p h) (sat_nil p)))
def c1387 : List Lit := [(838, false), (847, true)]
theorem step1387 (p : Nat → Bool) (h : Constraints p) : clause p c1387 = true :=
  Snake9.LocalRup.prove_clause [c1050, c630] c1387 (by decide) p (sat_cons (step1050 p h) (sat_cons (step630 p h) (sat_nil p)))
def c1388 : List Lit := [(869, true), (857, false)]
theorem step1388 (p : Nat → Bool) (h : Constraints p) : clause p c1388 = true :=
  Snake9.LocalRup.prove_clause [c1162, c671] c1388 (by decide) p (sat_cons (step1162 p h) (sat_cons (step671 p h) (sat_nil p)))
end B112E159
