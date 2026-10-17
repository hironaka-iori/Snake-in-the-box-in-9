import B112E161Part0004
namespace B112E161
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1514 : List Lit := [(74, true), (71, false), (72, true)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true :=
  Snake9.LocalRup.prove_clause [c457, c302] c1514 (by decide) p (sat_cons (step457 p h) (sat_cons (step302 p h) (sat_nil p)))
def c1515 : List Lit := [(71, false), (70, true), (72, true)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true :=
  Snake9.LocalRup.prove_clause [c457, c304] c1515 (by decide) p (sat_cons (step457 p h) (sat_cons (step304 p h) (sat_nil p)))
def c1516 : List Lit := [(73, false), (57, true), (78, true)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true :=
  Snake9.LocalRup.prove_clause [c458, c308] c1516 (by decide) p (sat_cons (step458 p h) (sat_cons (step308 p h) (sat_nil p)))
def c1517 : List Lit := [(57, true), (72, true), (73, false)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true :=
  Snake9.LocalRup.prove_clause [c458, c309] c1517 (by decide) p (sat_cons (step458 p h) (sat_cons (step309 p h) (sat_nil p)))
def c1518 : List Lit := [(77, false), (78, true)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true :=
  Snake9.LocalRup.prove_clause [c460, c320] c1518 (by decide) p (sat_cons (step460 p h) (sat_cons (step320 p h) (sat_nil p)))
def c1519 : List Lit := [(77, false), (76, true)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true :=
  Snake9.LocalRup.prove_clause [c460, c321] c1519 (by decide) p (sat_cons (step460 p h) (sat_cons (step321 p h) (sat_nil p)))
def c1520 : List Lit := [(79, false), (88, true), (81, true)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true :=
  Snake9.LocalRup.prove_clause [c461, c326] c1520 (by decide) p (sat_cons (step461 p h) (sat_cons (step326 p h) (sat_nil p)))
def c1521 : List Lit := [(79, false), (88, true), (80, true)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true :=
  Snake9.LocalRup.prove_clause [c461, c327] c1521 (by decide) p (sat_cons (step461 p h) (sat_cons (step327 p h) (sat_nil p)))
def c1522 : List Lit := [(79, false), (80, true), (81, true)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true :=
  Snake9.LocalRup.prove_clause [c461, c328] c1522 (by decide) p (sat_cons (step461 p h) (sat_cons (step328 p h) (sat_nil p)))
def c1523 : List Lit := [(82, false), (46, true), (14, true), (81, true)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true :=
  Snake9.LocalRup.prove_clause [c462, c340] c1523 (by decide) p (sat_cons (step462 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1524 : List Lit := [(83, false), (47, true), (81, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true :=
  Snake9.LocalRup.prove_clause [c463, c342] c1524 (by decide) p (sat_cons (step463 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1525 : List Lit := [(93, true), (86, false), (81, true)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true :=
  Snake9.LocalRup.prove_clause [c465, c355] c1525 (by decide) p (sat_cons (step465 p h) (sat_cons (step355 p h) (sat_nil p)))
def c1526 : List Lit := [(86, false), (87, true), (81, true)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true :=
  Snake9.LocalRup.prove_clause [c465, c356] c1526 (by decide) p (sat_cons (step465 p h) (sat_cons (step356 p h) (sat_nil p)))
def c1527 : List Lit := [(89, false), (90, true)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true :=
  Snake9.LocalRup.prove_clause [c466, c366] c1527 (by decide) p (sat_cons (step466 p h) (sat_cons (step366 p h) (sat_nil p)))
def c1528 : List Lit := [(89, false), (88, true)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true :=
  Snake9.LocalRup.prove_clause [c466, c367] c1528 (by decide) p (sat_cons (step466 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1529 : List Lit := [(94, false), (95, true)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true :=
  Snake9.LocalRup.prove_clause [c469, c382] c1529 (by decide) p (sat_cons (step469 p h) (sat_cons (step382 p h) (sat_nil p)))
def c1530 : List Lit := [(94, false), (93, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c469, c383] c1530 (by decide) p (sat_cons (step469 p h) (sat_cons (step383 p h) (sat_nil p)))
def c1531 : List Lit := [(103, true), (99, false), (98, true)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c471, c395] c1531 (by decide) p (sat_cons (step471 p h) (sat_cons (step395 p h) (sat_nil p)))
def c1532 : List Lit := [(100, false), (101, true)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c472, c396] c1532 (by decide) p (sat_cons (step472 p h) (sat_cons (step396 p h) (sat_nil p)))
def c1533 : List Lit := [(100, false), (97, true)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c472, c397] c1533 (by decide) p (sat_cons (step472 p h) (sat_cons (step397 p h) (sat_nil p)))
def c1534 : List Lit := [(110, false), (109, true)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c477, c419] c1534 (by decide) p (sat_cons (step477 p h) (sat_cons (step419 p h) (sat_nil p)))
def c1535 : List Lit := [(225, false), (229, false)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c1221, c484] c1535 (by decide) p (sat_cons (step1221 p h) (sat_cons (step484 p h) (sat_nil p)))
def c1536 : List Lit := [(231, false), (243, false)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c1210, c496] c1536 (by decide) p (sat_cons (step1210 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1537 : List Lit := [(127, false), (128, false)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c1236, c500] c1537 (by decide) p (sat_cons (step1236 p h) (sat_cons (step500 p h) (sat_nil p)))
def c1538 : List Lit := [(251, false), (253, false)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c1230, c507] c1538 (by decide) p (sat_cons (step1230 p h) (sat_cons (step507 p h) (sat_nil p)))
def c1539 : List Lit := [(249, false), (255, false)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c1220, c511] c1539 (by decide) p (sat_cons (step1220 p h) (sat_cons (step511 p h) (sat_nil p)))
def c1540 : List Lit := [(261, false), (267, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c1219, c520] c1540 (by decide) p (sat_cons (step1219 p h) (sat_cons (step520 p h) (sat_nil p)))
def c1541 : List Lit := [(257, false), (269, false)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c1209, c524] c1541 (by decide) p (sat_cons (step1209 p h) (sat_cons (step524 p h) (sat_nil p)))
def c1542 : List Lit := [(245, false), (271, false)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c1202, c529] c1542 (by decide) p (sat_cons (step1202 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1543 : List Lit := [(140, false), (275, false)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c1229, c534] c1543 (by decide) p (sat_cons (step1229 p h) (sat_cons (step534 p h) (sat_nil p)))
def c1544 : List Lit := [(143, false), (144, false)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c1235, c537] c1544 (by decide) p (sat_cons (step1235 p h) (sat_cons (step537 p h) (sat_nil p)))
def c1545 : List Lit := [(277, false), (283, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c1218, c545] c1545 (by decide) p (sat_cons (step1218 p h) (sat_cons (step545 p h) (sat_nil p)))
def c1546 : List Lit := [(291, false), (293, false)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c1227, c552] c1546 (by decide) p (sat_cons (step1227 p h) (sat_cons (step552 p h) (sat_nil p)))
def c1547 : List Lit := [(285, false), (297, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c1208, c558] c1547 (by decide) p (sat_cons (step1208 p h) (sat_cons (step558 p h) (sat_nil p)))
def c1548 : List Lit := [(303, false), (309, false)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c1216, c567] c1548 (by decide) p (sat_cons (step1216 p h) (sat_cons (step567 p h) (sat_nil p)))
def c1549 : List Lit := [(164, false), (165, false)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c1234, c573] c1549 (by decide) p (sat_cons (step1234 p h) (sat_cons (step573 p h) (sat_nil p)))
def c1550 : List Lit := [(317, false), (319, false)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c1226, c577] c1550 (by decide) p (sat_cons (step1226 p h) (sat_cons (step577 p h) (sat_nil p)))
def c1551 : List Lit := [(311, false), (323, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c1207, c586] c1551 (by decide) p (sat_cons (step1207 p h) (sat_cons (step586 p h) (sat_nil p)))
def c1552 : List Lit := [(299, false), (325, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c1201, c591] c1552 (by decide) p (sat_cons (step1201 p h) (sat_cons (step591 p h) (sat_nil p)))
def c1553 : List Lit := [(273, false), (327, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c1198, c596] c1553 (by decide) p (sat_cons (step1198 p h) (sat_cons (step596 p h) (sat_nil p)))
def c1554 : List Lit := [(345, false), (347, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c1225, c610] c1554 (by decide) p (sat_cons (step1225 p h) (sat_cons (step610 p h) (sat_nil p)))
def c1555 : List Lit := [(343, false), (349, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c1214, c614] c1555 (by decide) p (sat_cons (step1214 p h) (sat_cons (step614 p h) (sat_nil p)))
def c1556 : List Lit := [(339, false), (351, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c1206, c618] c1556 (by decide) p (sat_cons (step1206 p h) (sat_cons (step618 p h) (sat_nil p)))
def c1557 : List Lit := [(181, false), (355, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c1224, c622] c1557 (by decide) p (sat_cons (step1224 p h) (sat_cons (step622 p h) (sat_nil p)))
def c1558 : List Lit := [(353, false), (379, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c1200, c643] c1558 (by decide) p (sat_cons (step1200 p h) (sat_cons (step643 p h) (sat_nil p)))
def c1559 : List Lit := [(198, false), (199, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c1233, c649] c1559 (by decide) p (sat_cons (step1233 p h) (sat_cons (step649 p h) (sat_nil p)))
def c1560 : List Lit := [(387, false), (389, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c1223, c653] c1560 (by decide) p (sat_cons (step1223 p h) (sat_cons (step653 p h) (sat_nil p)))
def c1561 : List Lit := [(393, false), (405, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c1204, c668] c1561 (by decide) p (sat_cons (step1204 p h) (sat_cons (step668 p h) (sat_nil p)))
def c1562 : List Lit := [(214, false), (215, false)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c1232, c674] c1562 (by decide) p (sat_cons (step1232 p h) (sat_cons (step674 p h) (sat_nil p)))
def c1563 : List Lit := [(411, false), (417, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c1211, c681] c1563 (by decide) p (sat_cons (step1211 p h) (sat_cons (step681 p h) (sat_nil p)))
def c1564 : List Lit := [(419, false), (431, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c1203, c692] c1564 (by decide) p (sat_cons (step1203 p h) (sat_cons (step692 p h) (sat_nil p)))
def c1565 : List Lit := [(407, false), (433, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c1199, c697] c1565 (by decide) p (sat_cons (step1199 p h) (sat_cons (step697 p h) (sat_nil p)))
def c1566 : List Lit := [(381, false), (435, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c1197, c702] c1566 (by decide) p (sat_cons (step1197 p h) (sat_cons (step702 p h) (sat_nil p)))
def c1567 : List Lit := [(329, false), (437, false)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c707, c705] c1567 (by decide) p (sat_cons (step707 p h) (sat_cons (step705 p h) (sat_nil p)))
def c1568 : List Lit := [(1332, false), (1361, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c1254, c812] c1568 (by decide) p (sat_cons (step1254 p h) (sat_cons (step812 p h) (sat_nil p)))
def c1569 : List Lit := [(1333, false), (1361, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c1242, c818] c1569 (by decide) p (sat_cons (step1242 p h) (sat_cons (step818 p h) (sat_nil p)))
def c1570 : List Lit := [(1333, false), (1362, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c1254, c819] c1570 (by decide) p (sat_cons (step1254 p h) (sat_cons (step819 p h) (sat_nil p)))
def c1571 : List Lit := [(1363, true), (1334, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c1254, c825] c1571 (by decide) p (sat_cons (step1254 p h) (sat_cons (step825 p h) (sat_nil p)))
def c1572 : List Lit := [(1364, true), (1335, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c1254, c831] c1572 (by decide) p (sat_cons (step1254 p h) (sat_cons (step831 p h) (sat_nil p)))
def c1573 : List Lit := [(1407, false), (1415, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c1240, c908] c1573 (by decide) p (sat_cons (step1240 p h) (sat_cons (step908 p h) (sat_nil p)))
def c1574 : List Lit := [(1408, false), (1416, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c1240, c909] c1574 (by decide) p (sat_cons (step1240 p h) (sat_cons (step909 p h) (sat_nil p)))
def c1575 : List Lit := [(1409, false), (1417, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c1240, c910] c1575 (by decide) p (sat_cons (step1240 p h) (sat_cons (step910 p h) (sat_nil p)))
def c1576 : List Lit := [(1410, false), (1418, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c1240, c911] c1576 (by decide) p (sat_cons (step1240 p h) (sat_cons (step911 p h) (sat_nil p)))
def c1577 : List Lit := [(1411, false), (1419, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c1240, c912] c1577 (by decide) p (sat_cons (step1240 p h) (sat_cons (step912 p h) (sat_nil p)))
end B112E161
