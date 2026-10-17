import B112E104Part0004
namespace B112E104
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1476 : List Lit := [(156, false), (39, false)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true :=
  Snake9.LocalRup.prove_clause [c164, c152] c1476 (by decide) p (sat_cons (step164 p h) (sat_cons (step152 p h) (sat_nil p)))
def c1477 : List Lit := [(30, true), (39, false), (38, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true :=
  Snake9.LocalRup.prove_clause [c524, c153] c1477 (by decide) p (sat_cons (step524 p h) (sat_cons (step153 p h) (sat_nil p)))
def c1478 : List Lit := [(22, true), (39, false), (38, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true :=
  Snake9.LocalRup.prove_clause [c524, c154] c1478 (by decide) p (sat_cons (step524 p h) (sat_cons (step154 p h) (sat_nil p)))
def c1479 : List Lit := [(30, true), (22, true), (39, false)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true :=
  Snake9.LocalRup.prove_clause [c524, c155] c1479 (by decide) p (sat_cons (step524 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1480 : List Lit := [(40, false), (42, true)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true :=
  Snake9.LocalRup.prove_clause [c525, c156] c1480 (by decide) p (sat_cons (step525 p h) (sat_cons (step156 p h) (sat_nil p)))
def c1481 : List Lit := [(40, false), (38, true)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true :=
  Snake9.LocalRup.prove_clause [c525, c157] c1481 (by decide) p (sat_cons (step525 p h) (sat_cons (step157 p h) (sat_nil p)))
def c1482 : List Lit := [(32, false), (38, false)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true :=
  Snake9.LocalRup.prove_clause [c165, c158] c1482 (by decide) p (sat_cons (step165 p h) (sat_cons (step158 p h) (sat_nil p)))
def c1483 : List Lit := [(32, false), (43, false)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true :=
  Snake9.LocalRup.prove_clause [c165, c159] c1483 (by decide) p (sat_cons (step165 p h) (sat_cons (step159 p h) (sat_nil p)))
def c1484 : List Lit := [(32, false), (110, false)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true :=
  Snake9.LocalRup.prove_clause [c165, c160] c1484 (by decide) p (sat_cons (step165 p h) (sat_cons (step160 p h) (sat_nil p)))
def c1485 : List Lit := [(38, false), (43, false)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true :=
  Snake9.LocalRup.prove_clause [c165, c161] c1485 (by decide) p (sat_cons (step165 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1486 : List Lit := [(38, false), (110, false)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true :=
  Snake9.LocalRup.prove_clause [c165, c162] c1486 (by decide) p (sat_cons (step165 p h) (sat_cons (step162 p h) (sat_nil p)))
def c1487 : List Lit := [(43, false), (110, false)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true :=
  Snake9.LocalRup.prove_clause [c165, c163] c1487 (by decide) p (sat_cons (step165 p h) (sat_cons (step163 p h) (sat_nil p)))
def c1488 : List Lit := [(46, true), (44, false), (43, true), (117, true)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true :=
  Snake9.LocalRup.prove_clause [c526, c175] c1488 (by decide) p (sat_cons (step526 p h) (sat_cons (step175 p h) (sat_nil p)))
def c1489 : List Lit := [(44, false), (43, true), (37, true), (117, true)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true :=
  Snake9.LocalRup.prove_clause [c526, c176] c1489 (by decide) p (sat_cons (step526 p h) (sat_cons (step176 p h) (sat_nil p)))
def c1490 : List Lit := [(46, true), (43, true), (45, false)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true :=
  Snake9.LocalRup.prove_clause [c527, c177] c1490 (by decide) p (sat_cons (step527 p h) (sat_cons (step177 p h) (sat_nil p)))
def c1491 : List Lit := [(42, true), (43, true), (45, false)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true :=
  Snake9.LocalRup.prove_clause [c527, c178] c1491 (by decide) p (sat_cons (step527 p h) (sat_cons (step178 p h) (sat_nil p)))
def c1492 : List Lit := [(68, true), (98, true), (63, false), (62, true)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true :=
  Snake9.LocalRup.prove_clause [c536, c187] c1492 (by decide) p (sat_cons (step536 p h) (sat_cons (step187 p h) (sat_nil p)))
def c1493 : List Lit := [(66, true), (98, true), (63, false), (62, true)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true :=
  Snake9.LocalRup.prove_clause [c536, c188] c1493 (by decide) p (sat_cons (step536 p h) (sat_cons (step188 p h) (sat_nil p)))
def c1494 : List Lit := [(66, true), (68, true), (63, false), (62, true)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true :=
  Snake9.LocalRup.prove_clause [c536, c189] c1494 (by decide) p (sat_cons (step536 p h) (sat_cons (step189 p h) (sat_nil p)))
def c1495 : List Lit := [(64, true), (66, true), (65, false), (70, true), (62, true)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c537, c197] c1495 (by decide) p (sat_cons (step537 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1496 : List Lit := [(75, true), (68, true), (67, false), (104, true)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c538, c200] c1496 (by decide) p (sat_cons (step538 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1497 : List Lit := [(75, true), (68, true), (67, false), (18, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c538, c201] c1497 (by decide) p (sat_cons (step538 p h) (sat_cons (step201 p h) (sat_nil p)))
def c1498 : List Lit := [(64, true), (69, false), (106, true), (70, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c539, c206] c1498 (by decide) p (sat_cons (step539 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1499 : List Lit := [(20, true), (69, false), (106, true), (70, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c539, c207] c1499 (by decide) p (sat_cons (step539 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1500 : List Lit := [(20, true), (64, true), (106, true), (69, false)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c539, c208] c1500 (by decide) p (sat_cons (step539 p h) (sat_cons (step208 p h) (sat_nil p)))
def c1501 : List Lit := [(71, true), (62, true), (72, false)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c540, c214] c1501 (by decide) p (sat_cons (step540 p h) (sat_cons (step214 p h) (sat_nil p)))
def c1502 : List Lit := [(22, true), (71, true), (72, false)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c540, c215] c1502 (by decide) p (sat_cons (step540 p h) (sat_cons (step215 p h) (sat_nil p)))
def c1503 : List Lit := [(22, true), (62, true), (72, false)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c540, c216] c1503 (by decide) p (sat_cons (step540 p h) (sat_cons (step216 p h) (sat_nil p)))
def c1504 : List Lit := [(78, true), (117, true), (76, false)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c542, c222] c1504 (by decide) p (sat_cons (step542 p h) (sat_cons (step222 p h) (sat_nil p)))
def c1505 : List Lit := [(70, true), (117, true), (76, false)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c542, c223] c1505 (by decide) p (sat_cons (step542 p h) (sat_cons (step223 p h) (sat_nil p)))
def c1506 : List Lit := [(78, true), (70, true), (76, false)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c542, c224] c1506 (by decide) p (sat_cons (step542 p h) (sat_cons (step224 p h) (sat_nil p)))
def c1507 : List Lit := [(75, true), (78, true), (77, false)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c543, c225] c1507 (by decide) p (sat_cons (step543 p h) (sat_cons (step225 p h) (sat_nil p)))
def c1508 : List Lit := [(78, true), (74, true), (77, false)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c543, c226] c1508 (by decide) p (sat_cons (step543 p h) (sat_cons (step226 p h) (sat_nil p)))
def c1509 : List Lit := [(85, true), (83, true), (80, false), (98, true)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c544, c232] c1509 (by decide) p (sat_cons (step544 p h) (sat_cons (step232 p h) (sat_nil p)))
def c1510 : List Lit := [(92, true), (84, false), (104, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c546, c234] c1510 (by decide) p (sat_cons (step546 p h) (sat_cons (step234 p h) (sat_nil p)))
def c1511 : List Lit := [(84, false), (85, true), (104, true)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c546, c235] c1511 (by decide) p (sat_cons (step546 p h) (sat_cons (step235 p h) (sat_nil p)))
def c1512 : List Lit := [(92, true), (85, true), (84, false)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c546, c236] c1512 (by decide) p (sat_cons (step546 p h) (sat_cons (step236 p h) (sat_nil p)))
def c1513 : List Lit := [(86, false), (87, true), (106, true)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c547, c240] c1513 (by decide) p (sat_cons (step547 p h) (sat_cons (step240 p h) (sat_nil p)))
def c1514 : List Lit := [(81, true), (86, false), (106, true)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c547, c241] c1514 (by decide) p (sat_cons (step547 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1515 : List Lit := [(89, false), (88, true)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c548, c248] c1515 (by decide) p (sat_cons (step548 p h) (sat_cons (step248 p h) (sat_nil p)))
def c1516 : List Lit := [(89, false), (79, true)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c548, c249] c1516 (by decide) p (sat_cons (step548 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1517 : List Lit := [(92, true), (91, true), (90, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c549, c250] c1517 (by decide) p (sat_cons (step549 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1518 : List Lit := [(95, true), (93, false), (117, true)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c550, c254] c1518 (by decide) p (sat_cons (step550 p h) (sat_cons (step254 p h) (sat_nil p)))
def c1519 : List Lit := [(87, true), (93, false), (117, true)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c550, c255] c1519 (by decide) p (sat_cons (step550 p h) (sat_cons (step255 p h) (sat_nil p)))
def c1520 : List Lit := [(95, true), (92, true), (94, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c551, c256] c1520 (by decide) p (sat_cons (step551 p h) (sat_cons (step256 p h) (sat_nil p)))
def c1521 : List Lit := [(95, true), (91, true), (94, false)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c551, c257] c1521 (by decide) p (sat_cons (step551 p h) (sat_cons (step257 p h) (sat_nil p)))
def c1522 : List Lit := [(100, true), (104, true), (97, false), (98, true)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c552, c263] c1522 (by decide) p (sat_cons (step552 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1523 : List Lit := [(104, true), (96, true), (97, false), (100, true)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c552, c264] c1523 (by decide) p (sat_cons (step552 p h) (sat_cons (step264 p h) (sat_nil p)))
def c1524 : List Lit := [(96, true), (104, true), (97, false), (98, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c552, c265] c1524 (by decide) p (sat_cons (step552 p h) (sat_cons (step265 p h) (sat_nil p)))
def c1525 : List Lit := [(96, true), (98, true), (97, false), (100, true)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c552, c266] c1525 (by decide) p (sat_cons (step552 p h) (sat_cons (step266 p h) (sat_nil p)))
def c1526 : List Lit := [(104, true), (96, true), (102, false), (106, true), (114, true)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c555, c318] c1526 (by decide) p (sat_cons (step555 p h) (sat_cons (step318 p h) (sat_nil p)))
def c1527 : List Lit := [(104, true), (96, true), (106, true), (102, false), (103, true)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c555, c319] c1527 (by decide) p (sat_cons (step555 p h) (sat_cons (step319 p h) (sat_nil p)))
def c1528 : List Lit := [(68, true), (116, true), (105, false), (98, true), (103, true), (104, true)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c556, c375] c1528 (by decide) p (sat_cons (step556 p h) (sat_cons (step375 p h) (sat_nil p)))
def c1529 : List Lit := [(104, true), (106, true), (108, false)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c558, c427] c1529 (by decide) p (sat_cons (step558 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1530 : List Lit := [(100, true), (106, true), (108, false)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c558, c428] c1530 (by decide) p (sat_cons (step558 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1531 : List Lit := [(100, true), (104, true), (108, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c558, c429] c1531 (by decide) p (sat_cons (step558 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1532 : List Lit := [(116, true), (109, false), (113, true)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c559, c430] c1532 (by decide) p (sat_cons (step559 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1533 : List Lit := [(98, true), (116, true), (109, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c559, c431] c1533 (by decide) p (sat_cons (step559 p h) (sat_cons (step431 p h) (sat_nil p)))
def c1534 : List Lit := [(98, true), (109, false), (113, true)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c559, c432] c1534 (by decide) p (sat_cons (step559 p h) (sat_cons (step432 p h) (sat_nil p)))
def c1535 : List Lit := [(113, true), (111, false), (117, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c560, c437] c1535 (by decide) p (sat_cons (step560 p h) (sat_cons (step437 p h) (sat_nil p)))
def c1536 : List Lit := [(110, true), (111, false), (117, true)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c560, c438] c1536 (by decide) p (sat_cons (step560 p h) (sat_cons (step438 p h) (sat_nil p)))
def c1537 : List Lit := [(113, true), (111, false), (110, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c560, c439] c1537 (by decide) p (sat_cons (step560 p h) (sat_cons (step439 p h) (sat_nil p)))
def c1538 : List Lit := [(91, true), (110, true), (100, true), (112, false), (113, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c561, c440] c1538 (by decide) p (sat_cons (step561 p h) (sat_cons (step440 p h) (sat_nil p)))
def c1539 : List Lit := [(116, true), (115, false), (103, true), (117, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c562, c457] c1539 (by decide) p (sat_cons (step562 p h) (sat_cons (step457 p h) (sat_nil p)))
end B112E104
