import B112E115Part0003
namespace B112E115
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1495 : List Lit := [(10, true), (9, false), (6, true)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true :=
  Snake9.LocalRup.prove_clause [c532, c92] c1495 (by decide) p (sat_cons (step532 p h) (sat_cons (step92 p h) (sat_nil p)))
def c1496 : List Lit := [(23, true), (10, true), (11, false), (8, true)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true :=
  Snake9.LocalRup.prove_clause [c533, c102] c1496 (by decide) p (sat_cons (step533 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1497 : List Lit := [(5, true), (23, true), (11, false), (10, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true :=
  Snake9.LocalRup.prove_clause [c533, c103] c1497 (by decide) p (sat_cons (step533 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1498 : List Lit := [(5, true), (23, true), (8, true), (11, false)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true :=
  Snake9.LocalRup.prove_clause [c533, c104] c1498 (by decide) p (sat_cons (step533 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1499 : List Lit := [(5, true), (10, true), (8, true), (11, false)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true :=
  Snake9.LocalRup.prove_clause [c533, c105] c1499 (by decide) p (sat_cons (step533 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1500 : List Lit := [(15, true), (12, true), (13, false)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true :=
  Snake9.LocalRup.prove_clause [c534, c117] c1500 (by decide) p (sat_cons (step534 p h) (sat_cons (step117 p h) (sat_nil p)))
def c1501 : List Lit := [(15, true), (13, false), (2, true)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true :=
  Snake9.LocalRup.prove_clause [c534, c118] c1501 (by decide) p (sat_cons (step534 p h) (sat_cons (step118 p h) (sat_nil p)))
def c1502 : List Lit := [(12, true), (13, false), (2, true)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true :=
  Snake9.LocalRup.prove_clause [c534, c119] c1502 (by decide) p (sat_cons (step534 p h) (sat_cons (step119 p h) (sat_nil p)))
def c1503 : List Lit := [(85, true), (49, true), (12, true), (17, true), (16, false)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true :=
  Snake9.LocalRup.prove_clause [c535, c161] c1503 (by decide) p (sat_cons (step535 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1504 : List Lit := [(20, true), (17, true), (12, true), (16, false), (49, true)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true :=
  Snake9.LocalRup.prove_clause [c535, c162] c1504 (by decide) p (sat_cons (step535 p h) (sat_cons (step162 p h) (sat_nil p)))
def c1505 : List Lit := [(20, true), (22, false), (23, true)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true :=
  Snake9.LocalRup.prove_clause [c536, c191] c1505 (by decide) p (sat_cons (step536 p h) (sat_cons (step191 p h) (sat_nil p)))
def c1506 : List Lit := [(22, false), (23, true), (17, true)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true :=
  Snake9.LocalRup.prove_clause [c536, c192] c1506 (by decide) p (sat_cons (step536 p h) (sat_cons (step192 p h) (sat_nil p)))
def c1507 : List Lit := [(20, true), (22, false), (17, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true :=
  Snake9.LocalRup.prove_clause [c536, c193] c1507 (by decide) p (sat_cons (step536 p h) (sat_cons (step193 p h) (sat_nil p)))
def c1508 : List Lit := [(26, true), (24, false), (57, true)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true :=
  Snake9.LocalRup.prove_clause [c537, c230] c1508 (by decide) p (sat_cons (step537 p h) (sat_cons (step230 p h) (sat_nil p)))
def c1509 : List Lit := [(57, true), (24, false), (2, true)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true :=
  Snake9.LocalRup.prove_clause [c537, c231] c1509 (by decide) p (sat_cons (step537 p h) (sat_cons (step231 p h) (sat_nil p)))
def c1510 : List Lit := [(26, true), (24, false), (2, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true :=
  Snake9.LocalRup.prove_clause [c537, c232] c1510 (by decide) p (sat_cons (step537 p h) (sat_cons (step232 p h) (sat_nil p)))
def c1511 : List Lit := [(25, false), (27, true)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true :=
  Snake9.LocalRup.prove_clause [c538, c233] c1511 (by decide) p (sat_cons (step538 p h) (sat_cons (step233 p h) (sat_nil p)))
def c1512 : List Lit := [(25, false), (26, true)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true :=
  Snake9.LocalRup.prove_clause [c538, c234] c1512 (by decide) p (sat_cons (step538 p h) (sat_cons (step234 p h) (sat_nil p)))
def c1513 : List Lit := [(35, true), (28, false), (6, true)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true :=
  Snake9.LocalRup.prove_clause [c539, c241] c1513 (by decide) p (sat_cons (step539 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1514 : List Lit := [(29, true), (28, false), (6, true)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c539, c242] c1514 (by decide) p (sat_cons (step539 p h) (sat_cons (step242 p h) (sat_nil p)))
def c1515 : List Lit := [(29, true), (64, true), (30, false)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c540, c246] c1515 (by decide) p (sat_cons (step540 p h) (sat_cons (step246 p h) (sat_nil p)))
def c1516 : List Lit := [(27, true), (30, false), (64, true)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c540, c247] c1516 (by decide) p (sat_cons (step540 p h) (sat_cons (step247 p h) (sat_nil p)))
def c1517 : List Lit := [(36, true), (15, true), (34, true), (32, false), (69, true)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c541, c251] c1517 (by decide) p (sat_cons (step541 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1518 : List Lit := [(31, true), (36, true), (15, true), (32, false), (69, true)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c541, c252] c1518 (by decide) p (sat_cons (step541 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1519 : List Lit := [(31, true), (15, true), (34, true), (32, false), (69, true)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c541, c253] c1519 (by decide) p (sat_cons (step541 p h) (sat_cons (step253 p h) (sat_nil p)))
def c1520 : List Lit := [(34, true), (37, true), (33, false)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c542, c254] c1520 (by decide) p (sat_cons (step542 p h) (sat_cons (step254 p h) (sat_nil p)))
def c1521 : List Lit := [(33, false), (26, true), (37, true)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c542, c255] c1521 (by decide) p (sat_cons (step542 p h) (sat_cons (step255 p h) (sat_nil p)))
def c1522 : List Lit := [(37, true), (36, true), (23, true), (38, false)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c543, c269] c1522 (by decide) p (sat_cons (step543 p h) (sat_cons (step269 p h) (sat_nil p)))
def c1523 : List Lit := [(34, true), (37, true), (23, true), (38, false)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c543, c270] c1523 (by decide) p (sat_cons (step543 p h) (sat_cons (step270 p h) (sat_nil p)))
def c1524 : List Lit := [(36, true), (34, true), (38, false), (23, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c543, c271] c1524 (by decide) p (sat_cons (step543 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1525 : List Lit := [(41, true), (44, true), (57, true), (39, false)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c544, c275] c1525 (by decide) p (sat_cons (step544 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1526 : List Lit := [(44, true), (39, false), (2, true), (57, true)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c544, c276] c1526 (by decide) p (sat_cons (step544 p h) (sat_cons (step276 p h) (sat_nil p)))
def c1527 : List Lit := [(41, true), (39, false), (57, true), (2, true)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c544, c277] c1527 (by decide) p (sat_cons (step544 p h) (sat_cons (step277 p h) (sat_nil p)))
def c1528 : List Lit := [(41, true), (44, true), (39, false), (2, true)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c544, c278] c1528 (by decide) p (sat_cons (step544 p h) (sat_cons (step278 p h) (sat_nil p)))
def c1529 : List Lit := [(41, true), (49, true), (40, false)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c545, c279] c1529 (by decide) p (sat_cons (step545 p h) (sat_cons (step279 p h) (sat_nil p)))
def c1530 : List Lit := [(42, true), (41, true), (40, false)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c545, c280] c1530 (by decide) p (sat_cons (step545 p h) (sat_cons (step280 p h) (sat_nil p)))
def c1531 : List Lit := [(45, true), (44, true), (51, true), (43, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c546, c286] c1531 (by decide) p (sat_cons (step546 p h) (sat_cons (step286 p h) (sat_nil p)))
def c1532 : List Lit := [(45, true), (51, true), (6, true), (43, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c546, c287] c1532 (by decide) p (sat_cons (step546 p h) (sat_cons (step287 p h) (sat_nil p)))
def c1533 : List Lit := [(45, true), (44, true), (6, true), (43, false)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c546, c289] c1533 (by decide) p (sat_cons (step546 p h) (sat_cons (step289 p h) (sat_nil p)))
def c1534 : List Lit := [(45, true), (46, false), (64, true)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c547, c297] c1534 (by decide) p (sat_cons (step547 p h) (sat_cons (step297 p h) (sat_nil p)))
def c1535 : List Lit := [(42, true), (46, false), (64, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c547, c298] c1535 (by decide) p (sat_cons (step547 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1536 : List Lit := [(47, true), (69, true), (53, true), (48, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c548, c304] c1536 (by decide) p (sat_cons (step548 p h) (sat_cons (step304 p h) (sat_nil p)))
def c1537 : List Lit := [(69, true), (15, true), (53, true), (48, false)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c548, c305] c1537 (by decide) p (sat_cons (step548 p h) (sat_cons (step305 p h) (sat_nil p)))
def c1538 : List Lit := [(47, true), (69, true), (15, true), (48, false)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c548, c306] c1538 (by decide) p (sat_cons (step548 p h) (sat_cons (step306 p h) (sat_nil p)))
def c1539 : List Lit := [(47, true), (15, true), (48, false), (53, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c548, c307] c1539 (by decide) p (sat_cons (step548 p h) (sat_cons (step307 p h) (sat_nil p)))
def c1540 : List Lit := [(49, true), (54, true), (50, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c549, c312] c1540 (by decide) p (sat_cons (step549 p h) (sat_cons (step312 p h) (sat_nil p)))
def c1541 : List Lit := [(41, true), (54, true), (50, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c549, c313] c1541 (by decide) p (sat_cons (step549 p h) (sat_cons (step313 p h) (sat_nil p)))
def c1542 : List Lit := [(41, true), (49, true), (50, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c549, c314] c1542 (by decide) p (sat_cons (step549 p h) (sat_cons (step314 p h) (sat_nil p)))
def c1543 : List Lit := [(47, true), (53, true), (52, false), (45, true), (51, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c550, c318] c1543 (by decide) p (sat_cons (step550 p h) (sat_cons (step318 p h) (sat_nil p)))
def c1544 : List Lit := [(53, true), (54, true), (55, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c551, c333] c1544 (by decide) p (sat_cons (step551 p h) (sat_cons (step333 p h) (sat_nil p)))
def c1545 : List Lit := [(23, true), (54, true), (55, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c551, c334] c1545 (by decide) p (sat_cons (step551 p h) (sat_cons (step334 p h) (sat_nil p)))
def c1546 : List Lit := [(53, true), (23, true), (55, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c551, c335] c1546 (by decide) p (sat_cons (step551 p h) (sat_cons (step335 p h) (sat_nil p)))
def c1547 : List Lit := [(58, true), (66, true), (56, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c552, c337] c1547 (by decide) p (sat_cons (step552 p h) (sat_cons (step337 p h) (sat_nil p)))
def c1548 : List Lit := [(66, true), (56, false), (57, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c552, c338] c1548 (by decide) p (sat_cons (step552 p h) (sat_cons (step338 p h) (sat_nil p)))
def c1549 : List Lit := [(58, true), (56, false), (57, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c552, c339] c1549 (by decide) p (sat_cons (step552 p h) (sat_cons (step339 p h) (sat_nil p)))
def c1550 : List Lit := [(60, true), (69, true), (59, false), (57, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c553, c382] c1550 (by decide) p (sat_cons (step553 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1551 : List Lit := [(58, true), (69, true), (57, true), (59, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c553, c383] c1551 (by decide) p (sat_cons (step553 p h) (sat_cons (step383 p h) (sat_nil p)))
def c1552 : List Lit := [(58, true), (60, true), (57, true), (59, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c553, c384] c1552 (by decide) p (sat_cons (step553 p h) (sat_cons (step384 p h) (sat_nil p)))
def c1553 : List Lit := [(63, true), (61, false), (57, true)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c554, c389] c1553 (by decide) p (sat_cons (step554 p h) (sat_cons (step389 p h) (sat_nil p)))
def c1554 : List Lit := [(61, false), (44, true), (57, true)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c554, c391] c1554 (by decide) p (sat_cons (step554 p h) (sat_cons (step391 p h) (sat_nil p)))
def c1555 : List Lit := [(72, true), (62, false), (64, true)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c555, c392] c1555 (by decide) p (sat_cons (step555 p h) (sat_cons (step392 p h) (sat_nil p)))
def c1556 : List Lit := [(63, true), (62, false), (64, true)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c555, c394] c1556 (by decide) p (sat_cons (step555 p h) (sat_cons (step394 p h) (sat_nil p)))
def c1557 : List Lit := [(63, true), (65, false), (64, true)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c556, c419] c1557 (by decide) p (sat_cons (step556 p h) (sat_cons (step419 p h) (sat_nil p)))
def c1558 : List Lit := [(65, false), (64, true), (60, true)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c556, c420] c1558 (by decide) p (sat_cons (step556 p h) (sat_cons (step420 p h) (sat_nil p)))
end B112E115
