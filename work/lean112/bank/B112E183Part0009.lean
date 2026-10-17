import B112E183Part0008
namespace B112E183
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1404 : List Lit := [(20, true), (4, true), (25, true), (34, true), (24, false), (21, false)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true :=
  Snake9.LocalRup.prove_clause [c67, c57, c339, c338, c342, c1076] c1404 (by decide) p (sat_cons (step67 p h) (sat_cons (step57 p h) (sat_cons (step339 p h) (sat_cons (step338 p h) (sat_cons (step342 p h) (sat_cons (step1076 p h) (sat_nil p)))))))
def c1405 : List Lit := [(179, true), (87, false), (90, true), (92, false), (183, true), (189, true), (191, true), (202, true), (186, true), (21, false), (1371, true), (1383, false)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true :=
  Snake9.TreeRup.prove_clause [c1283, c1385, c1392, c1382, c1255, c1290, c1394, c1289, c1294, c1063, c174, c1217, c964, c719, c703, c686, c701, c1401, c608, c909, c1095, c556, c934, c866, c1264, c698, c1055, c527, c689, c1000, c1001, c530, c533, c1058, c191, c552, c553, c200, c1094, c567, c540, c234, c639, c523, c538, c228, c227, c629, c1054, c595, c1047, c590, c69, c1403, c1404, c53, c504, c506, c509, c521, c514, c511, c512, c869, c31, c37] c1405 (by decide) p (sat_cons (step1283 p h) (sat_cons (step1385 p h) (sat_cons (step1392 p h) (sat_cons (step1382 p h) (sat_cons (step1255 p h) (sat_cons (step1290 p h) (sat_cons (step1394 p h) (sat_cons (step1289 p h) (sat_cons (step1294 p h) (sat_cons (step1063 p h) (sat_cons (step174 p h) (sat_cons (step1217 p h) (sat_cons (step964 p h) (sat_cons (step719 p h) (sat_cons (step703 p h) (sat_cons (step686 p h) (sat_cons (step701 p h) (sat_cons (step1401 p h) (sat_cons (step608 p h) (sat_cons (step909 p h) (sat_cons (step1095 p h) (sat_cons (step556 p h) (sat_cons (step934 p h) (sat_cons (step866 p h) (sat_cons (step1264 p h) (sat_cons (step698 p h) (sat_cons (step1055 p h) (sat_cons (step527 p h) (sat_cons (step689 p h) (sat_cons (step1000 p h) (sat_cons (step1001 p h) (sat_cons (step530 p h) (sat_cons (step533 p h) (sat_cons (step1058 p h) (sat_cons (step191 p h) (sat_cons (step552 p h) (sat_cons (step553 p h) (sat_cons (step200 p h) (sat_cons (step1094 p h) (sat_cons (step567 p h) (sat_cons (step540 p h) (sat_cons (step234 p h) (sat_cons (step639 p h) (sat_cons (step523 p h) (sat_cons (step538 p h) (sat_cons (step228 p h) (sat_cons (step227 p h) (sat_cons (step629 p h) (sat_cons (step1054 p h) (sat_cons (step595 p h) (sat_cons (step1047 p h) (sat_cons (step590 p h) (sat_cons (step69 p h) (sat_cons (step1403 p h) (sat_cons (step1404 p h) (sat_cons (step53 p h) (sat_cons (step504 p h) (sat_cons (step506 p h) (sat_cons (step509 p h) (sat_cons (step521 p h) (sat_cons (step514 p h) (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step869 p h) (sat_cons (step31 p h) (sat_cons (step37 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1406 : List Lit := [(89, false), (29, true)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true :=
  Snake9.LocalRup.prove_clause [c1251, c1383, c1256, c582, c1400, c1402, c1356, c1093, c494, c496, c491, c444, c468, c470, c439, c441, c466, c453, c435, c437, c425, c459, c452, c432, c433, c429, c424, c456, c451, c431, c430, c423, c874, c733, c219, c726, c213, c1405, c426, c421] c1406 (by decide) p (sat_cons (step1251 p h) (sat_cons (step1383 p h) (sat_cons (step1256 p h) (sat_cons (step582 p h) (sat_cons (step1400 p h) (sat_cons (step1402 p h) (sat_cons (step1356 p h) (sat_cons (step1093 p h) (sat_cons (step494 p h) (sat_cons (step496 p h) (sat_cons (step491 p h) (sat_cons (step444 p h) (sat_cons (step468 p h) (sat_cons (step470 p h) (sat_cons (step439 p h) (sat_cons (step441 p h) (sat_cons (step466 p h) (sat_cons (step453 p h) (sat_cons (step435 p h) (sat_cons (step437 p h) (sat_cons (step425 p h) (sat_cons (step459 p h) (sat_cons (step452 p h) (sat_cons (step432 p h) (sat_cons (step433 p h) (sat_cons (step429 p h) (sat_cons (step424 p h) (sat_cons (step456 p h) (sat_cons (step451 p h) (sat_cons (step431 p h) (sat_cons (step430 p h) (sat_cons (step423 p h) (sat_cons (step874 p h) (sat_cons (step733 p h) (sat_cons (step219 p h) (sat_cons (step726 p h) (sat_cons (step213 p h) (sat_cons (step1405 p h) (sat_cons (step426 p h) (sat_cons (step421 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))
def c1407 : List Lit := [(29, true)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true :=
  Snake9.LocalRup.prove_clause [c1383, c1248, c1253, c1283, c1294, c582, c594, c1406, c168, c1362, c419, c781, c420, c990, c426, c441, c444, c496, c1092, c1093, c490, c1356, c488, c1003, c1402, c486, c986, c826, c643, c484, c1099, c626, c483, c595, c909, c273, c588, c608, c609, c1071, c585, c586, c1396] c1407 (by decide) p (sat_cons (step1383 p h) (sat_cons (step1248 p h) (sat_cons (step1253 p h) (sat_cons (step1283 p h) (sat_cons (step1294 p h) (sat_cons (step582 p h) (sat_cons (step594 p h) (sat_cons (step1406 p h) (sat_cons (step168 p h) (sat_cons (step1362 p h) (sat_cons (step419 p h) (sat_cons (step781 p h) (sat_cons (step420 p h) (sat_cons (step990 p h) (sat_cons (step426 p h) (sat_cons (step441 p h) (sat_cons (step444 p h) (sat_cons (step496 p h) (sat_cons (step1092 p h) (sat_cons (step1093 p h) (sat_cons (step490 p h) (sat_cons (step1356 p h) (sat_cons (step488 p h) (sat_cons (step1003 p h) (sat_cons (step1402 p h) (sat_cons (step486 p h) (sat_cons (step986 p h) (sat_cons (step826 p h) (sat_cons (step643 p h) (sat_cons (step484 p h) (sat_cons (step1099 p h) (sat_cons (step626 p h) (sat_cons (step483 p h) (sat_cons (step595 p h) (sat_cons (step909 p h) (sat_cons (step273 p h) (sat_cons (step588 p h) (sat_cons (step608 p h) (sat_cons (step609 p h) (sat_cons (step1071 p h) (sat_cons (step585 p h) (sat_cons (step586 p h) (sat_cons (step1396 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))
def c1408 : List Lit := [(89, false)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true :=
  Snake9.LocalRup.prove_clause [c1407, c1388] c1408 (by decide) p (sat_cons (step1407 p h) (sat_cons (step1388 p h) (sat_nil p)))
def c1409 : List Lit := [(181, true)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1383, c168] c1409 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1383 p h) (sat_cons (step168 p h) (sat_nil p))))
def c1410 : List Lit := [(1499, true)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true :=
  Snake9.LocalRup.prove_clause [c1408, c1362] c1410 (by decide) p (sat_cons (step1408 p h) (sat_cons (step1362 p h) (sat_nil p)))
def c1411 : List Lit := [(351, true)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true :=
  Snake9.LocalRup.prove_clause [c1409, c419] c1411 (by decide) p (sat_cons (step1409 p h) (sat_cons (step419 p h) (sat_nil p)))
def c1412 : List Lit := [(1519, false)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true :=
  Snake9.LocalRup.prove_clause [c1410, c1248, c781] c1412 (by decide) p (sat_cons (step1410 p h) (sat_cons (step1248 p h) (sat_cons (step781 p h) (sat_nil p))))
def c1413 : List Lit := [(353, true)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true :=
  Snake9.LocalRup.prove_clause [c1411, c420] c1413 (by decide) p (sat_cons (step1411 p h) (sat_cons (step420 p h) (sat_nil p)))
def c1414 : List Lit := [(99, true)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true :=
  Snake9.LocalRup.prove_clause [c1412, c990] c1414 (by decide) p (sat_cons (step1412 p h) (sat_cons (step990 p h) (sat_nil p)))
def c1415 : List Lit := [(361, true)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true :=
  Snake9.LocalRup.prove_clause [c1413, c426] c1415 (by decide) p (sat_cons (step1413 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1416 : List Lit := [(375, true)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true :=
  Snake9.LocalRup.prove_clause [c1415, c441] c1416 (by decide) p (sat_cons (step1415 p h) (sat_cons (step441 p h) (sat_nil p)))
def c1417 : List Lit := [(377, true)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true :=
  Snake9.LocalRup.prove_clause [c1416, c444] c1417 (by decide) p (sat_cons (step1416 p h) (sat_cons (step444 p h) (sat_nil p)))
def c1418 : List Lit := [(433, true)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true :=
  Snake9.LocalRup.prove_clause [c1417, c496] c1418 (by decide) p (sat_cons (step1417 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1419 : List Lit := [(431, false)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true :=
  Snake9.LocalRup.prove_clause [c1417, c1092] c1419 (by decide) p (sat_cons (step1417 p h) (sat_cons (step1092 p h) (sat_nil p)))
def c1420 : List Lit := [(325, false)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true :=
  Snake9.LocalRup.prove_clause [c1418, c1093] c1420 (by decide) p (sat_cons (step1418 p h) (sat_cons (step1093 p h) (sat_nil p)))
def c1421 : List Lit := [(429, false)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true :=
  Snake9.LocalRup.prove_clause [c1419, c490] c1421 (by decide) p (sat_cons (step1419 p h) (sat_cons (step490 p h) (sat_nil p)))
def c1422 : List Lit := [(323, false)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true :=
  Snake9.LocalRup.prove_clause [c1420, c391] c1422 (by decide) p (sat_cons (step1420 p h) (sat_cons (step391 p h) (sat_nil p)))
def c1423 : List Lit := [(271, false)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true :=
  Snake9.LocalRup.prove_clause [c1420, c393] c1423 (by decide) p (sat_cons (step1420 p h) (sat_cons (step393 p h) (sat_nil p)))
def c1424 : List Lit := [(427, false)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true :=
  Snake9.LocalRup.prove_clause [c1421, c488] c1424 (by decide) p (sat_cons (step1421 p h) (sat_cons (step488 p h) (sat_nil p)))
def c1425 : List Lit := [(415, false)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true :=
  Snake9.LocalRup.prove_clause [c1421, c489] c1425 (by decide) p (sat_cons (step1421 p h) (sat_cons (step489 p h) (sat_nil p)))
def c1426 : List Lit := [(95, true)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true :=
  Snake9.LocalRup.prove_clause [c1421, c1412, c1003] c1426 (by decide) p (sat_cons (step1421 p h) (sat_cons (step1412 p h) (sat_cons (step1003 p h) (sat_nil p))))
def c1427 : List Lit := [(295, false)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true :=
  Snake9.LocalRup.prove_clause [c1422, c389] c1427 (by decide) p (sat_cons (step1422 p h) (sat_cons (step389 p h) (sat_nil p)))
def c1428 : List Lit := [(269, false)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true :=
  Snake9.LocalRup.prove_clause [c1423, c353] c1428 (by decide) p (sat_cons (step1423 p h) (sat_cons (step353 p h) (sat_nil p)))
def c1429 : List Lit := [(243, false)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true :=
  Snake9.LocalRup.prove_clause [c1423, c355] c1429 (by decide) p (sat_cons (step1423 p h) (sat_cons (step355 p h) (sat_nil p)))
def c1430 : List Lit := [(425, false)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true :=
  Snake9.LocalRup.prove_clause [c1424, c486] c1430 (by decide) p (sat_cons (step1424 p h) (sat_cons (step486 p h) (sat_nil p)))
def c1431 : List Lit := [(419, false)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true :=
  Snake9.LocalRup.prove_clause [c1424, c487] c1431 (by decide) p (sat_cons (step1424 p h) (sat_cons (step487 p h) (sat_nil p)))
def c1432 : List Lit := [(109, true)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true :=
  Snake9.LocalRup.prove_clause [c1424, c1253, c986] c1432 (by decide) p (sat_cons (step1424 p h) (sat_cons (step1253 p h) (sat_cons (step986 p h) (sat_nil p))))
def c1433 : List Lit := [(413, false)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true :=
  Snake9.LocalRup.prove_clause [c1425, c478] c1433 (by decide) p (sat_cons (step1425 p h) (sat_cons (step478 p h) (sat_nil p)))
def c1434 : List Lit := [(407, false)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true :=
  Snake9.LocalRup.prove_clause [c1425, c479] c1434 (by decide) p (sat_cons (step1425 p h) (sat_cons (step479 p h) (sat_nil p)))
def c1435 : List Lit := [(100, false)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true :=
  Snake9.LocalRup.prove_clause [c1426, c1283, c1414, c826] c1435 (by decide) p (sat_cons (step1426 p h) (sat_cons (step1283 p h) (sat_cons (step1414 p h) (sat_cons (step826 p h) (sat_nil p)))))
def c1436 : List Lit := [(281, false)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true :=
  Snake9.LocalRup.prove_clause [c1427, c375] c1436 (by decide) p (sat_cons (step1427 p h) (sat_cons (step375 p h) (sat_nil p)))
def c1437 : List Lit := [(267, false)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true :=
  Snake9.LocalRup.prove_clause [c1428, c348] c1437 (by decide) p (sat_cons (step1428 p h) (sat_cons (step348 p h) (sat_nil p)))
def c1438 : List Lit := [(255, false)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true :=
  Snake9.LocalRup.prove_clause [c1428, c350] c1438 (by decide) p (sat_cons (step1428 p h) (sat_cons (step350 p h) (sat_nil p)))
def c1439 : List Lit := [(241, false)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true :=
  Snake9.LocalRup.prove_clause [c1429, c325] c1439 (by decide) p (sat_cons (step1429 p h) (sat_cons (step325 p h) (sat_nil p)))
def c1440 : List Lit := [(423, false)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true :=
  Snake9.LocalRup.prove_clause [c1430, c484] c1440 (by decide) p (sat_cons (step1430 p h) (sat_cons (step484 p h) (sat_nil p)))
def c1441 : List Lit := [(421, false)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true :=
  Snake9.LocalRup.prove_clause [c1430, c485] c1441 (by decide) p (sat_cons (step1430 p h) (sat_cons (step485 p h) (sat_nil p)))
def c1442 : List Lit := [(417, false)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true :=
  Snake9.LocalRup.prove_clause [c1431, c481] c1442 (by decide) p (sat_cons (step1431 p h) (sat_cons (step481 p h) (sat_nil p)))
def c1443 : List Lit := [(409, false)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true :=
  Snake9.LocalRup.prove_clause [c1433, c477] c1443 (by decide) p (sat_cons (step1433 p h) (sat_cons (step477 p h) (sat_nil p)))
def c1444 : List Lit := [(405, false)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true :=
  Snake9.LocalRup.prove_clause [c1434, c475] c1444 (by decide) p (sat_cons (step1434 p h) (sat_cons (step475 p h) (sat_nil p)))
def c1445 : List Lit := [(279, false)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true :=
  Snake9.LocalRup.prove_clause [c1436, c363] c1445 (by decide) p (sat_cons (step1436 p h) (sat_cons (step363 p h) (sat_nil p)))
def c1446 : List Lit := [(275, false)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true :=
  Snake9.LocalRup.prove_clause [c1436, c365] c1446 (by decide) p (sat_cons (step1436 p h) (sat_cons (step365 p h) (sat_nil p)))
def c1447 : List Lit := [(265, false)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true :=
  Snake9.LocalRup.prove_clause [c1437, c344] c1447 (by decide) p (sat_cons (step1437 p h) (sat_cons (step344 p h) (sat_nil p)))
def c1448 : List Lit := [(247, false)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true :=
  Snake9.LocalRup.prove_clause [c1438, c333] c1448 (by decide) p (sat_cons (step1438 p h) (sat_cons (step333 p h) (sat_nil p)))
def c1449 : List Lit := [(239, false)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true :=
  Snake9.LocalRup.prove_clause [c1439, c323] c1449 (by decide) p (sat_cons (step1439 p h) (sat_cons (step323 p h) (sat_nil p)))
def c1450 : List Lit := [(219, false)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true :=
  Snake9.LocalRup.prove_clause [c1440, c483] c1450 (by decide) p (sat_cons (step1440 p h) (sat_cons (step483 p h) (sat_nil p)))
def c1451 : List Lit := [(217, false)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true :=
  Snake9.LocalRup.prove_clause [c1441, c482] c1451 (by decide) p (sat_cons (step1441 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1452 : List Lit := [(216, false)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true :=
  Snake9.LocalRup.prove_clause [c1442, c480] c1452 (by decide) p (sat_cons (step1442 p h) (sat_cons (step480 p h) (sat_nil p)))
def c1453 : List Lit := [(211, false)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true :=
  Snake9.LocalRup.prove_clause [c1443, c476] c1453 (by decide) p (sat_cons (step1443 p h) (sat_cons (step476 p h) (sat_nil p)))
def c1454 : List Lit := [(209, false)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true :=
  Snake9.LocalRup.prove_clause [c1444, c473] c1454 (by decide) p (sat_cons (step1444 p h) (sat_cons (step473 p h) (sat_nil p)))
def c1455 : List Lit := [(277, false)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true :=
  Snake9.LocalRup.prove_clause [c1445, c360] c1455 (by decide) p (sat_cons (step1445 p h) (sat_cons (step360 p h) (sat_nil p)))
def c1456 : List Lit := [(141, false)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true :=
  Snake9.LocalRup.prove_clause [c1445, c361] c1456 (by decide) p (sat_cons (step1445 p h) (sat_cons (step361 p h) (sat_nil p)))
def c1457 : List Lit := [(273, false)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true :=
  Snake9.LocalRup.prove_clause [c1446, c358] c1457 (by decide) p (sat_cons (step1446 p h) (sat_cons (step358 p h) (sat_nil p)))
def c1458 : List Lit := [(263, false)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c1447, c341] c1458 (by decide) p (sat_cons (step1447 p h) (sat_cons (step341 p h) (sat_nil p)))
def c1459 : List Lit := [(261, false)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c1447, c342] c1459 (by decide) p (sat_cons (step1447 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1460 : List Lit := [(124, false)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c1448, c329] c1460 (by decide) p (sat_cons (step1448 p h) (sat_cons (step329 p h) (sat_nil p)))
def c1461 : List Lit := [(237, false)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c1449, c322] c1461 (by decide) p (sat_cons (step1449 p h) (sat_cons (step322 p h) (sat_nil p)))
def c1462 : List Lit := [(110, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c1450, c1435, c1432, c272] c1462 (by decide) p (sat_cons (step1450 p h) (sat_cons (step1435 p h) (sat_cons (step1432 p h) (sat_cons (step272 p h) (sat_nil p)))))
def c1463 : List Lit := [(108, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c1450, c1435, c1432, c273] c1463 (by decide) p (sat_cons (step1450 p h) (sat_cons (step1435 p h) (sat_cons (step1432 p h) (sat_cons (step273 p h) (sat_nil p)))))
def c1464 : List Lit := [(102, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c1454, c1414, c1435, c250] c1464 (by decide) p (sat_cons (step1454 p h) (sat_cons (step1414 p h) (sat_cons (step1435 p h) (sat_cons (step250 p h) (sat_nil p)))))
def c1465 : List Lit := [(142, false)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c1455, c359] c1465 (by decide) p (sat_cons (step1455 p h) (sat_cons (step359 p h) (sat_nil p)))
def c1466 : List Lit := [(139, false)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c1457, c357] c1466 (by decide) p (sat_cons (step1457 p h) (sat_cons (step357 p h) (sat_nil p)))
def c1467 : List Lit := [(136, false)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c1458, c340] c1467 (by decide) p (sat_cons (step1458 p h) (sat_cons (step340 p h) (sat_nil p)))
end B112E183
