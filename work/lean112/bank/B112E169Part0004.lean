import B112E169Part0003
namespace B112E169
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1390 : List Lit := [(46, true), (9, true), (103, true), (17, true), (31, true), (37, false), (40, true)]
theorem step1390 (p : Nat → Bool) (h : Constraints p) : clause p c1390 = true :=
  Snake9.LocalRup.prove_clause [c447, c206] c1390 (by decide) p (sat_cons (step447 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1391 : List Lit := [(38, true), (9, true), (103, true), (46, true), (31, true), (37, false), (17, true)]
theorem step1391 (p : Nat → Bool) (h : Constraints p) : clause p c1391 = true :=
  Snake9.LocalRup.prove_clause [c447, c207] c1391 (by decide) p (sat_cons (step447 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1392 : List Lit := [(41, false), (38, true), (40, true)]
theorem step1392 (p : Nat → Bool) (h : Constraints p) : clause p c1392 = true :=
  Snake9.LocalRup.prove_clause [c449, c223] c1392 (by decide) p (sat_cons (step449 p h) (sat_cons (step223 p h) (sat_nil p)))
def c1393 : List Lit := [(41, false), (36, true), (40, true)]
theorem step1393 (p : Nat → Bool) (h : Constraints p) : clause p c1393 = true :=
  Snake9.LocalRup.prove_clause [c449, c224] c1393 (by decide) p (sat_cons (step449 p h) (sat_cons (step224 p h) (sat_nil p)))
def c1394 : List Lit := [(43, true), (45, true), (44, false), (42, true)]
theorem step1394 (p : Nat → Bool) (h : Constraints p) : clause p c1394 = true :=
  Snake9.LocalRup.prove_clause [c450, c240] c1394 (by decide) p (sat_cons (step450 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1395 : List Lit := [(44, false), (45, true), (35, true), (42, true)]
theorem step1395 (p : Nat → Bool) (h : Constraints p) : clause p c1395 = true :=
  Snake9.LocalRup.prove_clause [c450, c241] c1395 (by decide) p (sat_cons (step450 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1396 : List Lit := [(35, true), (43, true), (44, false), (42, true)]
theorem step1396 (p : Nat → Bool) (h : Constraints p) : clause p c1396 = true :=
  Snake9.LocalRup.prove_clause [c450, c242] c1396 (by decide) p (sat_cons (step450 p h) (sat_cons (step242 p h) (sat_nil p)))
def c1397 : List Lit := [(47, false), (49, true), (42, true)]
theorem step1397 (p : Nat → Bool) (h : Constraints p) : clause p c1397 = true :=
  Snake9.LocalRup.prove_clause [c451, c258] c1397 (by decide) p (sat_cons (step451 p h) (sat_cons (step258 p h) (sat_nil p)))
def c1398 : List Lit := [(47, false), (46, true), (42, true)]
theorem step1398 (p : Nat → Bool) (h : Constraints p) : clause p c1398 = true :=
  Snake9.LocalRup.prove_clause [c451, c259] c1398 (by decide) p (sat_cons (step451 p h) (sat_cons (step259 p h) (sat_nil p)))
def c1399 : List Lit := [(50, false), (49, true), (30, true)]
theorem step1399 (p : Nat → Bool) (h : Constraints p) : clause p c1399 = true :=
  Snake9.LocalRup.prove_clause [c453, c271] c1399 (by decide) p (sat_cons (step453 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1400 : List Lit := [(50, false), (45, true), (30, true)]
theorem step1400 (p : Nat → Bool) (h : Constraints p) : clause p c1400 = true :=
  Snake9.LocalRup.prove_clause [c453, c272] c1400 (by decide) p (sat_cons (step453 p h) (sat_cons (step272 p h) (sat_nil p)))
def c1401 : List Lit := [(51, true), (59, true), (53, false)]
theorem step1401 (p : Nat → Bool) (h : Constraints p) : clause p c1401 = true :=
  Snake9.LocalRup.prove_clause [c454, c278] c1401 (by decide) p (sat_cons (step454 p h) (sat_cons (step278 p h) (sat_nil p)))
def c1402 : List Lit := [(4, true), (53, false), (59, true)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true :=
  Snake9.LocalRup.prove_clause [c454, c279] c1402 (by decide) p (sat_cons (step454 p h) (sat_cons (step279 p h) (sat_nil p)))
def c1403 : List Lit := [(54, false), (63, true)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true :=
  Snake9.LocalRup.prove_clause [c455, c280] c1403 (by decide) p (sat_cons (step455 p h) (sat_cons (step280 p h) (sat_nil p)))
def c1404 : List Lit := [(54, false), (55, true)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c455, c281] c1404 (by decide) p (sat_cons (step455 p h) (sat_cons (step281 p h) (sat_nil p)))
def c1405 : List Lit := [(55, true), (57, true), (56, false)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.LocalRup.prove_clause [c456, c285] c1405 (by decide) p (sat_cons (step456 p h) (sat_cons (step285 p h) (sat_nil p)))
def c1406 : List Lit := [(55, true), (52, true), (56, false)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c456, c287] c1406 (by decide) p (sat_cons (step456 p h) (sat_cons (step287 p h) (sat_nil p)))
def c1407 : List Lit := [(53, true), (59, false), (60, true)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.LocalRup.prove_clause [c1140, c293] c1407 (by decide) p (sat_cons (step1140 p h) (sat_cons (step293 p h) (sat_nil p)))
def c1408 : List Lit := [(59, false), (60, true), (175, true)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c1140, c295] c1408 (by decide) p (sat_cons (step1140 p h) (sat_cons (step295 p h) (sat_nil p)))
def c1409 : List Lit := [(60, false), (59, true)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c458, c296] c1409 (by decide) p (sat_cons (step458 p h) (sat_cons (step296 p h) (sat_nil p)))
def c1410 : List Lit := [(60, false), (57, true)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c458, c297] c1410 (by decide) p (sat_cons (step458 p h) (sat_cons (step297 p h) (sat_nil p)))
def c1411 : List Lit := [(64, true), (90, true), (63, false), (179, true), (54, true)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c1141, c303] c1411 (by decide) p (sat_cons (step1141 p h) (sat_cons (step303 p h) (sat_nil p)))
def c1412 : List Lit := [(64, false), (65, true)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c460, c304] c1412 (by decide) p (sat_cons (step460 p h) (sat_cons (step304 p h) (sat_nil p)))
def c1413 : List Lit := [(83, true), (82, false), (13, true)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c462, c319] c1413 (by decide) p (sat_cons (step462 p h) (sat_cons (step319 p h) (sat_nil p)))
def c1414 : List Lit := [(89, false), (88, true)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c464, c343] c1414 (by decide) p (sat_cons (step464 p h) (sat_cons (step343 p h) (sat_nil p)))
def c1415 : List Lit := [(89, false), (86, true)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c464, c344] c1415 (by decide) p (sat_cons (step464 p h) (sat_cons (step344 p h) (sat_nil p)))
def c1416 : List Lit := [(91, true), (92, false), (85, true)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c465, c352] c1416 (by decide) p (sat_cons (step465 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1417 : List Lit := [(95, false), (97, true)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c466, c361] c1417 (by decide) p (sat_cons (step466 p h) (sat_cons (step361 p h) (sat_nil p)))
def c1418 : List Lit := [(95, false), (94, true)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c466, c362] c1418 (by decide) p (sat_cons (step466 p h) (sat_cons (step362 p h) (sat_nil p)))
def c1419 : List Lit := [(98, false), (93, true), (30, true)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c468, c375] c1419 (by decide) p (sat_cons (step468 p h) (sat_cons (step375 p h) (sat_nil p)))
def c1420 : List Lit := [(99, false), (31, true), (103, true)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c469, c377] c1420 (by decide) p (sat_cons (step469 p h) (sat_cons (step377 p h) (sat_nil p)))
def c1421 : List Lit := [(99, false), (100, true), (31, true)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c469, c378] c1421 (by decide) p (sat_cons (step469 p h) (sat_cons (step378 p h) (sat_nil p)))
def c1422 : List Lit := [(107, false), (106, true), (105, true)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c471, c403] c1422 (by decide) p (sat_cons (step471 p h) (sat_cons (step403 p h) (sat_nil p)))
def c1423 : List Lit := [(108, false), (110, true), (42, true)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c472, c406] c1423 (by decide) p (sat_cons (step472 p h) (sat_cons (step406 p h) (sat_nil p)))
def c1424 : List Lit := [(100, true), (108, false), (42, true)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c472, c407] c1424 (by decide) p (sat_cons (step472 p h) (sat_cons (step407 p h) (sat_nil p)))
def c1425 : List Lit := [(112, true), (109, false), (113, true)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c473, c409] c1425 (by decide) p (sat_cons (step473 p h) (sat_cons (step409 p h) (sat_nil p)))
def c1426 : List Lit := [(115, false), (114, true)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c474, c429] c1426 (by decide) p (sat_cons (step474 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1427 : List Lit := [(115, false), (106, true)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c474, c430] c1427 (by decide) p (sat_cons (step474 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1428 : List Lit := [(116, false), (114, true), (113, true)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c475, c432] c1428 (by decide) p (sat_cons (step475 p h) (sat_cons (step432 p h) (sat_nil p)))
def c1429 : List Lit := [(112, true), (116, false), (113, true)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c475, c433] c1429 (by decide) p (sat_cons (step475 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1430 : List Lit := [(120, false), (121, false)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c1179, c480] c1430 (by decide) p (sat_cons (step1179 p h) (sat_cons (step480 p h) (sat_nil p)))
def c1431 : List Lit := [(235, false), (241, false)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c1164, c486] c1431 (by decide) p (sat_cons (step1164 p h) (sat_cons (step486 p h) (sat_nil p)))
def c1432 : List Lit := [(124, false), (245, false)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c1173, c490] c1432 (by decide) p (sat_cons (step1173 p h) (sat_cons (step490 p h) (sat_nil p)))
def c1433 : List Lit := [(247, false), (253, false)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c1163, c495] c1433 (by decide) p (sat_cons (step1163 p h) (sat_cons (step495 p h) (sat_nil p)))
def c1434 : List Lit := [(243, false), (255, false)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c1154, c500] c1434 (by decide) p (sat_cons (step1154 p h) (sat_cons (step500 p h) (sat_nil p)))
def c1435 : List Lit := [(133, false), (134, false)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c1178, c504] c1435 (by decide) p (sat_cons (step1178 p h) (sat_cons (step504 p h) (sat_nil p)))
def c1436 : List Lit := [(261, false), (267, false)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c1162, c513] c1436 (by decide) p (sat_cons (step1162 p h) (sat_cons (step513 p h) (sat_nil p)))
def c1437 : List Lit := [(140, false), (141, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c1177, c517] c1437 (by decide) p (sat_cons (step1177 p h) (sat_cons (step517 p h) (sat_nil p)))
def c1438 : List Lit := [(269, false), (281, false)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c1153, c529] c1438 (by decide) p (sat_cons (step1153 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1439 : List Lit := [(257, false), (283, false)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c1147, c534] c1439 (by decide) p (sat_cons (step1147 p h) (sat_cons (step534 p h) (sat_nil p)))
def c1440 : List Lit := [(303, false), (305, false)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c1170, c546] c1440 (by decide) p (sat_cons (step1170 p h) (sat_cons (step546 p h) (sat_nil p)))
def c1441 : List Lit := [(297, false), (309, false)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c1152, c553] c1441 (by decide) p (sat_cons (step1152 p h) (sat_cons (step553 p h) (sat_nil p)))
def c1442 : List Lit := [(161, false), (162, false)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c1176, c556] c1442 (by decide) p (sat_cons (step1176 p h) (sat_cons (step556 p h) (sat_nil p)))
def c1443 : List Lit := [(315, false), (321, false)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c1159, c563] c1443 (by decide) p (sat_cons (step1159 p h) (sat_cons (step563 p h) (sat_nil p)))
def c1444 : List Lit := [(329, false), (335, false)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c1158, c576] c1444 (by decide) p (sat_cons (step1158 p h) (sat_cons (step576 p h) (sat_nil p)))
def c1445 : List Lit := [(323, false), (337, false)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c1151, c580] c1445 (by decide) p (sat_cons (step1151 p h) (sat_cons (step580 p h) (sat_nil p)))
def c1446 : List Lit := [(311, false), (339, false)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c1146, c585] c1446 (by decide) p (sat_cons (step1146 p h) (sat_cons (step585 p h) (sat_nil p)))
def c1447 : List Lit := [(285, false), (341, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c1143, c590] c1447 (by decide) p (sat_cons (step1143 p h) (sat_cons (step590 p h) (sat_nil p)))
def c1448 : List Lit := [(355, false), (367, false)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c1150, c607] c1448 (by decide) p (sat_cons (step1150 p h) (sat_cons (step607 p h) (sat_nil p)))
def c1449 : List Lit := [(369, false), (397, false)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c1145, c625] c1449 (by decide) p (sat_cons (step1145 p h) (sat_cons (step625 p h) (sat_nil p)))
def c1450 : List Lit := [(209, false), (210, false)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c1175, c631] c1450 (by decide) p (sat_cons (step1175 p h) (sat_cons (step631 p h) (sat_nil p)))
def c1451 : List Lit := [(403, false), (409, false)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c1157, c638] c1451 (by decide) p (sat_cons (step1157 p h) (sat_cons (step638 p h) (sat_nil p)))
def c1452 : List Lit := [(411, false), (423, false)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c1149, c647] c1452 (by decide) p (sat_cons (step1149 p h) (sat_cons (step647 p h) (sat_nil p)))
def c1453 : List Lit := [(218, false), (427, false)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c1166, c652] c1453 (by decide) p (sat_cons (step1166 p h) (sat_cons (step652 p h) (sat_nil p)))
end B112E169
