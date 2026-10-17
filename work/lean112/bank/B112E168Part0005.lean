import B112E168Part0004
namespace B112E168
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1458 : List Lit := [(46, true), (53, true), (47, false), (45, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true :=
  Snake9.LocalRup.prove_clause [c470, c203] c1458 (by decide) p (sat_cons (step470 p h) (sat_cons (step203 p h) (sat_nil p)))
def c1459 : List Lit := [(46, true), (53, true), (47, false), (27, true)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true :=
  Snake9.LocalRup.prove_clause [c470, c204] c1459 (by decide) p (sat_cons (step470 p h) (sat_cons (step204 p h) (sat_nil p)))
def c1460 : List Lit := [(27, true), (53, true), (47, false), (45, true)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true :=
  Snake9.LocalRup.prove_clause [c470, c205] c1460 (by decide) p (sat_cons (step470 p h) (sat_cons (step205 p h) (sat_nil p)))
def c1461 : List Lit := [(27, true), (46, true), (47, false), (45, true)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true :=
  Snake9.LocalRup.prove_clause [c470, c206] c1461 (by decide) p (sat_cons (step470 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1462 : List Lit := [(46, true), (63, true), (51, false), (53, true), (50, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true :=
  Snake9.LocalRup.prove_clause [c471, c260] c1462 (by decide) p (sat_cons (step471 p h) (sat_cons (step260 p h) (sat_nil p)))
def c1463 : List Lit := [(48, true), (63, true), (51, false), (46, true), (50, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true :=
  Snake9.LocalRup.prove_clause [c471, c261] c1463 (by decide) p (sat_cons (step471 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1464 : List Lit := [(46, true), (48, true), (51, false), (50, true), (53, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true :=
  Snake9.LocalRup.prove_clause [c471, c262] c1464 (by decide) p (sat_cons (step471 p h) (sat_cons (step262 p h) (sat_nil p)))
def c1465 : List Lit := [(33, true), (56, true), (14, true), (42, true), (54, false), (55, true), (59, true)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true :=
  Snake9.LocalRup.prove_clause [c473, c271] c1465 (by decide) p (sat_cons (step473 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1466 : List Lit := [(55, true), (56, true), (57, false)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true :=
  Snake9.LocalRup.prove_clause [c474, c288] c1466 (by decide) p (sat_cons (step474 p h) (sat_cons (step288 p h) (sat_nil p)))
def c1467 : List Lit := [(56, true), (57, false), (45, true)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true :=
  Snake9.LocalRup.prove_clause [c474, c289] c1467 (by decide) p (sat_cons (step474 p h) (sat_cons (step289 p h) (sat_nil p)))
def c1468 : List Lit := [(55, true), (57, false), (45, true)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true :=
  Snake9.LocalRup.prove_clause [c474, c290] c1468 (by decide) p (sat_cons (step474 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1469 : List Lit := [(56, true), (109, true), (58, false)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true :=
  Snake9.LocalRup.prove_clause [c475, c291] c1469 (by decide) p (sat_cons (step475 p h) (sat_cons (step291 p h) (sat_nil p)))
def c1470 : List Lit := [(56, true), (64, true), (58, false)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true :=
  Snake9.LocalRup.prove_clause [c475, c292] c1470 (by decide) p (sat_cons (step475 p h) (sat_cons (step292 p h) (sat_nil p)))
def c1471 : List Lit := [(56, true), (64, true), (49, true), (61, false), (20, true), (59, true)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true :=
  Snake9.LocalRup.prove_clause [c477, c316] c1471 (by decide) p (sat_cons (step477 p h) (sat_cons (step316 p h) (sat_nil p)))
def c1472 : List Lit := [(38, true), (64, true), (61, false), (49, true), (20, true), (59, true)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true :=
  Snake9.LocalRup.prove_clause [c477, c317] c1472 (by decide) p (sat_cons (step477 p h) (sat_cons (step317 p h) (sat_nil p)))
def c1473 : List Lit := [(38, true), (56, true), (61, false), (49, true), (20, true), (59, true)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true :=
  Snake9.LocalRup.prove_clause [c477, c318] c1473 (by decide) p (sat_cons (step477 p h) (sat_cons (step318 p h) (sat_nil p)))
def c1474 : List Lit := [(64, true), (63, true), (62, false), (59, true)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true :=
  Snake9.LocalRup.prove_clause [c478, c319] c1474 (by decide) p (sat_cons (step478 p h) (sat_cons (step319 p h) (sat_nil p)))
def c1475 : List Lit := [(64, true), (62, false), (50, true), (59, true)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true :=
  Snake9.LocalRup.prove_clause [c478, c321] c1475 (by decide) p (sat_cons (step478 p h) (sat_cons (step321 p h) (sat_nil p)))
def c1476 : List Lit := [(63, true), (62, false), (59, true), (50, true)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c478, c322] c1476 (by decide) p (sat_cons (step478 p h) (sat_cons (step322 p h) (sat_nil p)))
def c1477 : List Lit := [(65, false), (85, true), (179, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c1142, c335] c1477 (by decide) p (sat_cons (step1142 p h) (sat_cons (step335 p h) (sat_nil p)))
def c1478 : List Lit := [(74, true), (68, false), (71, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c480, c340] c1478 (by decide) p (sat_cons (step480 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1479 : List Lit := [(67, true), (68, false), (71, true)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c480, c341] c1479 (by decide) p (sat_cons (step480 p h) (sat_cons (step341 p h) (sat_nil p)))
def c1480 : List Lit := [(67, true), (71, true), (70, false)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c481, c344] c1480 (by decide) p (sat_cons (step481 p h) (sat_cons (step344 p h) (sat_nil p)))
def c1481 : List Lit := [(65, true), (71, true), (70, false)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c481, c345] c1481 (by decide) p (sat_cons (step481 p h) (sat_cons (step345 p h) (sat_nil p)))
def c1482 : List Lit := [(71, true), (79, true), (72, false)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c482, c352] c1482 (by decide) p (sat_cons (step482 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1483 : List Lit := [(76, false), (75, true)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c483, c360] c1483 (by decide) p (sat_cons (step483 p h) (sat_cons (step360 p h) (sat_nil p)))
def c1484 : List Lit := [(76, false), (74, true)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c483, c361] c1484 (by decide) p (sat_cons (step483 p h) (sat_cons (step361 p h) (sat_nil p)))
def c1485 : List Lit := [(77, false), (20, true), (80, true)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c484, c363] c1485 (by decide) p (sat_cons (step484 p h) (sat_cons (step363 p h) (sat_nil p)))
def c1486 : List Lit := [(75, true), (20, true), (77, false)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c484, c364] c1486 (by decide) p (sat_cons (step484 p h) (sat_cons (step364 p h) (sat_nil p)))
def c1487 : List Lit := [(78, false), (80, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c485, c365] c1487 (by decide) p (sat_cons (step485 p h) (sat_cons (step365 p h) (sat_nil p)))
def c1488 : List Lit := [(78, false), (79, true)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c485, c366] c1488 (by decide) p (sat_cons (step485 p h) (sat_cons (step366 p h) (sat_nil p)))
def c1489 : List Lit := [(89, true), (83, true), (82, false), (86, true)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c486, c375] c1489 (by decide) p (sat_cons (step486 p h) (sat_cons (step375 p h) (sat_nil p)))
def c1490 : List Lit := [(81, true), (83, true), (82, false), (86, true)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c486, c376] c1490 (by decide) p (sat_cons (step486 p h) (sat_cons (step376 p h) (sat_nil p)))
def c1491 : List Lit := [(83, true), (88, true), (84, false)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c487, c382] c1491 (by decide) p (sat_cons (step487 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1492 : List Lit := [(88, true), (84, false), (27, true)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c487, c383] c1492 (by decide) p (sat_cons (step487 p h) (sat_cons (step383 p h) (sat_nil p)))
def c1493 : List Lit := [(83, true), (84, false), (27, true)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c487, c384] c1493 (by decide) p (sat_cons (step487 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1494 : List Lit := [(28, true), (86, true), (85, false), (81, true)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c488, c386] c1494 (by decide) p (sat_cons (step488 p h) (sat_cons (step386 p h) (sat_nil p)))
def c1495 : List Lit := [(83, true), (95, true), (87, false), (86, true)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c489, c393] c1495 (by decide) p (sat_cons (step489 p h) (sat_cons (step393 p h) (sat_nil p)))
def c1496 : List Lit := [(83, true), (88, true), (87, false), (86, true)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c489, c394] c1496 (by decide) p (sat_cons (step489 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1497 : List Lit := [(91, false), (90, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c490, c401] c1497 (by decide) p (sat_cons (step490 p h) (sat_cons (step401 p h) (sat_nil p)))
def c1498 : List Lit := [(91, false), (89, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c490, c402] c1498 (by decide) p (sat_cons (step490 p h) (sat_cons (step402 p h) (sat_nil p)))
def c1499 : List Lit := [(94, false), (96, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c493, c405] c1499 (by decide) p (sat_cons (step493 p h) (sat_cons (step405 p h) (sat_nil p)))
def c1500 : List Lit := [(94, false), (95, true)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c493, c406] c1500 (by decide) p (sat_cons (step493 p h) (sat_cons (step406 p h) (sat_nil p)))
def c1501 : List Lit := [(103, true), (97, true), (98, false)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c494, c414] c1501 (by decide) p (sat_cons (step494 p h) (sat_cons (step414 p h) (sat_nil p)))
def c1502 : List Lit := [(103, true), (45, true), (98, false)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c494, c415] c1502 (by decide) p (sat_cons (step494 p h) (sat_cons (step415 p h) (sat_nil p)))
def c1503 : List Lit := [(97, true), (45, true), (98, false)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c494, c416] c1503 (by decide) p (sat_cons (step494 p h) (sat_cons (step416 p h) (sat_nil p)))
def c1504 : List Lit := [(99, true), (108, true), (100, false), (83, true)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c495, c419] c1504 (by decide) p (sat_cons (step495 p h) (sat_cons (step419 p h) (sat_nil p)))
def c1505 : List Lit := [(99, true), (108, true), (100, false), (46, true)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c495, c420] c1505 (by decide) p (sat_cons (step495 p h) (sat_cons (step420 p h) (sat_nil p)))
def c1506 : List Lit := [(108, true), (83, true), (100, false), (46, true)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c495, c421] c1506 (by decide) p (sat_cons (step495 p h) (sat_cons (step421 p h) (sat_nil p)))
def c1507 : List Lit := [(99, true), (83, true), (100, false), (46, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c495, c422] c1507 (by decide) p (sat_cons (step495 p h) (sat_cons (step422 p h) (sat_nil p)))
def c1508 : List Lit := [(103, true), (112, true), (71, true), (86, true), (101, false)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c496, c423] c1508 (by decide) p (sat_cons (step496 p h) (sat_cons (step423 p h) (sat_nil p)))
def c1509 : List Lit := [(101, false), (103, true), (71, true), (48, true), (112, true)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c496, c424] c1509 (by decide) p (sat_cons (step496 p h) (sat_cons (step424 p h) (sat_nil p)))
def c1510 : List Lit := [(101, false), (112, true), (71, true), (86, true), (48, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c496, c425] c1510 (by decide) p (sat_cons (step496 p h) (sat_cons (step425 p h) (sat_nil p)))
def c1511 : List Lit := [(101, false), (103, true), (71, true), (86, true), (48, true)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c496, c426] c1511 (by decide) p (sat_cons (step496 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1512 : List Lit := [(103, true), (102, false), (49, true), (105, true)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c497, c427] c1512 (by decide) p (sat_cons (step497 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1513 : List Lit := [(102, false), (105, true), (49, true), (97, true)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c497, c428] c1513 (by decide) p (sat_cons (step497 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1514 : List Lit := [(105, true), (104, false), (50, true)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c498, c433] c1514 (by decide) p (sat_cons (step498 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1515 : List Lit := [(99, true), (104, false), (50, true)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c498, c434] c1515 (by decide) p (sat_cons (step498 p h) (sat_cons (step434 p h) (sat_nil p)))
def c1516 : List Lit := [(108, true), (110, false), (109, true)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c500, c441] c1516 (by decide) p (sat_cons (step500 p h) (sat_cons (step441 p h) (sat_nil p)))
def c1517 : List Lit := [(112, true), (111, false), (59, true)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c501, c442] c1517 (by decide) p (sat_cons (step501 p h) (sat_cons (step442 p h) (sat_nil p)))
def c1518 : List Lit := [(103, true), (112, true), (113, false)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c502, c447] c1518 (by decide) p (sat_cons (step502 p h) (sat_cons (step447 p h) (sat_nil p)))
def c1519 : List Lit := [(120, false), (121, false)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c1155, c507] c1519 (by decide) p (sat_cons (step1155 p h) (sat_cons (step507 p h) (sat_nil p)))
def c1520 : List Lit := [(231, false), (237, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c1152, c515] c1520 (by decide) p (sat_cons (step1152 p h) (sat_cons (step515 p h) (sat_nil p)))
def c1521 : List Lit := [(239, false), (251, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c1150, c524] c1521 (by decide) p (sat_cons (step1150 p h) (sat_cons (step524 p h) (sat_nil p)))
end B112E168
