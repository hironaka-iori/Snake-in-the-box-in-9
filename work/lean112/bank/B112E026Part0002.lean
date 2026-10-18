import B112E026Part0001
namespace B112E026
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1530 : List Lit := [(3, false), (10, false)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true :=
  Snake9.LocalRup.prove_clause [c16, c1402, c3] c1530 (by decide) p (sat_cons (step16 p h) (sat_cons (step1402 p h) (sat_cons (step3 p h) (sat_nil p))))
def c1531 : List Lit := [(6, false), (10, false)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true :=
  Snake9.LocalRup.prove_clause [c16, c1402, c4] c1531 (by decide) p (sat_cons (step16 p h) (sat_cons (step1402 p h) (sat_cons (step4 p h) (sat_nil p))))
def c1532 : List Lit := [(123, false), (3, false)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true :=
  Snake9.LocalRup.prove_clause [c16, c5] c1532 (by decide) p (sat_cons (step16 p h) (sat_cons (step5 p h) (sat_nil p)))
def c1533 : List Lit := [(6, true), (123, true), (10, true), (3, true)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true :=
  Snake9.LocalRup.prove_clause [c1402, c6] c1533 (by decide) p (sat_cons (step1402 p h) (sat_cons (step6 p h) (sat_nil p)))
def c1534 : List Lit := [(4, false), (3, false), (16, false)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true :=
  Snake9.LocalRup.prove_clause [c1402, c8] c1534 (by decide) p (sat_cons (step1402 p h) (sat_cons (step8 p h) (sat_nil p)))
def c1535 : List Lit := [(7, true), (6, false), (61, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true :=
  Snake9.LocalRup.prove_clause [c631, c17] c1535 (by decide) p (sat_cons (step631 p h) (sat_cons (step17 p h) (sat_nil p)))
def c1536 : List Lit := [(8, false), (4, true)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true :=
  Snake9.LocalRup.prove_clause [c632, c20] c1536 (by decide) p (sat_cons (step632 p h) (sat_cons (step20 p h) (sat_nil p)))
def c1537 : List Lit := [(11, false), (9, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true :=
  Snake9.LocalRup.prove_clause [c633, c25] c1537 (by decide) p (sat_cons (step633 p h) (sat_cons (step25 p h) (sat_nil p)))
def c1538 : List Lit := [(11, false), (4, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true :=
  Snake9.LocalRup.prove_clause [c633, c26] c1538 (by decide) p (sat_cons (step633 p h) (sat_cons (step26 p h) (sat_nil p)))
def c1539 : List Lit := [(16, true), (13, false), (23, true), (15, true), (82, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true :=
  Snake9.LocalRup.prove_clause [c634, c39] c1539 (by decide) p (sat_cons (step634 p h) (sat_cons (step39 p h) (sat_nil p)))
def c1540 : List Lit := [(15, true), (23, true), (82, true), (12, true), (13, false)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true :=
  Snake9.LocalRup.prove_clause [c634, c40] c1540 (by decide) p (sat_cons (step634 p h) (sat_cons (step40 p h) (sat_nil p)))
def c1541 : List Lit := [(16, true), (13, false), (12, true), (82, true), (15, true)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true :=
  Snake9.LocalRup.prove_clause [c634, c41] c1541 (by decide) p (sat_cons (step634 p h) (sat_cons (step41 p h) (sat_nil p)))
def c1542 : List Lit := [(23, true), (16, true), (13, false), (12, true), (15, true)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true :=
  Snake9.LocalRup.prove_clause [c634, c42] c1542 (by decide) p (sat_cons (step634 p h) (sat_cons (step42 p h) (sat_nil p)))
def c1543 : List Lit := [(15, true), (12, true), (83, true), (14, false), (32, true), (24, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true :=
  Snake9.LocalRup.prove_clause [c635, c43] c1543 (by decide) p (sat_cons (step635 p h) (sat_cons (step43 p h) (sat_nil p)))
def c1544 : List Lit := [(15, true), (12, true), (83, true), (32, true), (14, false), (17, true)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true :=
  Snake9.LocalRup.prove_clause [c635, c44] c1544 (by decide) p (sat_cons (step635 p h) (sat_cons (step44 p h) (sat_nil p)))
def c1545 : List Lit := [(88, true), (27, true), (18, false)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true :=
  Snake9.LocalRup.prove_clause [c636, c70] c1545 (by decide) p (sat_cons (step636 p h) (sat_cons (step70 p h) (sat_nil p)))
def c1546 : List Lit := [(88, true), (18, false), (12, true)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true :=
  Snake9.LocalRup.prove_clause [c636, c71] c1546 (by decide) p (sat_cons (step636 p h) (sat_cons (step71 p h) (sat_nil p)))
def c1547 : List Lit := [(27, true), (12, true), (18, false)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true :=
  Snake9.LocalRup.prove_clause [c636, c72] c1547 (by decide) p (sat_cons (step636 p h) (sat_cons (step72 p h) (sat_nil p)))
def c1548 : List Lit := [(21, true), (19, false), (90, true), (38, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true :=
  Snake9.LocalRup.prove_clause [c637, c74] c1548 (by decide) p (sat_cons (step637 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1549 : List Lit := [(15, true), (19, false), (90, true), (38, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true :=
  Snake9.LocalRup.prove_clause [c637, c75] c1549 (by decide) p (sat_cons (step637 p h) (sat_cons (step75 p h) (sat_nil p)))
def c1550 : List Lit := [(21, true), (19, false), (15, true), (90, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true :=
  Snake9.LocalRup.prove_clause [c637, c76] c1550 (by decide) p (sat_cons (step637 p h) (sat_cons (step76 p h) (sat_nil p)))
def c1551 : List Lit := [(29, true), (21, true), (20, false)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true :=
  Snake9.LocalRup.prove_clause [c638, c77] c1551 (by decide) p (sat_cons (step638 p h) (sat_cons (step77 p h) (sat_nil p)))
def c1552 : List Lit := [(29, true), (16, true), (20, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true :=
  Snake9.LocalRup.prove_clause [c638, c78] c1552 (by decide) p (sat_cons (step638 p h) (sat_cons (step78 p h) (sat_nil p)))
def c1553 : List Lit := [(21, true), (16, true), (20, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true :=
  Snake9.LocalRup.prove_clause [c638, c79] c1553 (by decide) p (sat_cons (step638 p h) (sat_cons (step79 p h) (sat_nil p)))
def c1554 : List Lit := [(27, true), (12, true), (22, false), (24, true)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c639, c86] c1554 (by decide) p (sat_cons (step639 p h) (sat_cons (step86 p h) (sat_nil p)))
def c1555 : List Lit := [(12, true), (24, true), (23, true), (22, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c639, c87] c1555 (by decide) p (sat_cons (step639 p h) (sat_cons (step87 p h) (sat_nil p)))
def c1556 : List Lit := [(23, true), (24, true), (95, true), (25, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c640, c100] c1556 (by decide) p (sat_cons (step640 p h) (sat_cons (step100 p h) (sat_nil p)))
def c1557 : List Lit := [(15, true), (24, true), (95, true), (25, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c640, c101] c1557 (by decide) p (sat_cons (step640 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1558 : List Lit := [(23, true), (15, true), (25, false), (95, true)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c640, c102] c1558 (by decide) p (sat_cons (step640 p h) (sat_cons (step102 p h) (sat_nil p)))
def c1559 : List Lit := [(15, true), (23, true), (25, false), (24, true)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c640, c103] c1559 (by decide) p (sat_cons (step640 p h) (sat_cons (step103 p h) (sat_nil p)))
def c1560 : List Lit := [(30, true), (24, true), (26, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c641, c104] c1560 (by decide) p (sat_cons (step641 p h) (sat_cons (step104 p h) (sat_nil p)))
def c1561 : List Lit := [(30, true), (26, false), (17, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c641, c105] c1561 (by decide) p (sat_cons (step641 p h) (sat_cons (step105 p h) (sat_nil p)))
def c1562 : List Lit := [(24, true), (26, false), (17, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c641, c106] c1562 (by decide) p (sat_cons (step641 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1563 : List Lit := [(30, true), (29, true), (28, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c642, c118] c1563 (by decide) p (sat_cons (step642 p h) (sat_cons (step118 p h) (sat_nil p)))
def c1564 : List Lit := [(30, true), (27, true), (28, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c642, c119] c1564 (by decide) p (sat_cons (step642 p h) (sat_cons (step119 p h) (sat_nil p)))
def c1565 : List Lit := [(29, true), (27, true), (28, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c642, c120] c1565 (by decide) p (sat_cons (step642 p h) (sat_cons (step120 p h) (sat_nil p)))
def c1566 : List Lit := [(15, true), (32, true), (33, false), (38, true)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c643, c134] c1566 (by decide) p (sat_cons (step643 p h) (sat_cons (step134 p h) (sat_nil p)))
def c1567 : List Lit := [(9, true), (32, true), (33, false), (38, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c643, c135] c1567 (by decide) p (sat_cons (step643 p h) (sat_cons (step135 p h) (sat_nil p)))
def c1568 : List Lit := [(42, true), (16, true), (35, false)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c644, c143] c1568 (by decide) p (sat_cons (step644 p h) (sat_cons (step143 p h) (sat_nil p)))
def c1569 : List Lit := [(16, true), (34, true), (35, false)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c644, c144] c1569 (by decide) p (sat_cons (step644 p h) (sat_cons (step144 p h) (sat_nil p)))
def c1570 : List Lit := [(40, true), (32, true), (36, false), (34, true), (106, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c645, c145] c1570 (by decide) p (sat_cons (step645 p h) (sat_cons (step145 p h) (sat_nil p)))
def c1571 : List Lit := [(32, true), (34, true), (36, false), (106, true), (17, true)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c645, c146] c1571 (by decide) p (sat_cons (step645 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1572 : List Lit := [(40, true), (32, true), (17, true), (36, false), (34, true)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c645, c147] c1572 (by decide) p (sat_cons (step645 p h) (sat_cons (step147 p h) (sat_nil p)))
def c1573 : List Lit := [(46, true), (40, true), (37, false), (38, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c646, c149] c1573 (by decide) p (sat_cons (step646 p h) (sat_cons (step149 p h) (sat_nil p)))
def c1574 : List Lit := [(46, true), (37, false), (38, true), (32, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c646, c150] c1574 (by decide) p (sat_cons (step646 p h) (sat_cons (step150 p h) (sat_nil p)))
def c1575 : List Lit := [(40, true), (37, false), (38, true), (32, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c646, c151] c1575 (by decide) p (sat_cons (step646 p h) (sat_cons (step151 p h) (sat_nil p)))
def c1576 : List Lit := [(39, false), (40, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c647, c161] c1576 (by decide) p (sat_cons (step647 p h) (sat_cons (step161 p h) (sat_nil p)))
def c1577 : List Lit := [(39, false), (34, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c647, c162] c1577 (by decide) p (sat_cons (step647 p h) (sat_cons (step162 p h) (sat_nil p)))
def c1578 : List Lit := [(34, true), (41, false), (116, true)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c648, c167] c1578 (by decide) p (sat_cons (step648 p h) (sat_cons (step167 p h) (sat_nil p)))
def c1579 : List Lit := [(43, false), (48, true)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c649, c171] c1579 (by decide) p (sat_cons (step649 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1580 : List Lit := [(43, false), (42, true)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c649, c172] c1580 (by decide) p (sat_cons (step649 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1581 : List Lit := [(45, true), (46, true), (44, false)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c650, c173] c1581 (by decide) p (sat_cons (step650 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1582 : List Lit := [(48, true), (45, true), (38, true), (47, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c651, c184] c1582 (by decide) p (sat_cons (step651 p h) (sat_cons (step184 p h) (sat_nil p)))
def c1583 : List Lit := [(58, true), (50, false), (82, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c652, c196] c1583 (by decide) p (sat_cons (step652 p h) (sat_cons (step196 p h) (sat_nil p)))
def c1584 : List Lit := [(49, true), (50, false), (82, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c652, c197] c1584 (by decide) p (sat_cons (step652 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1585 : List Lit := [(49, true), (58, true), (50, false)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c652, c198] c1585 (by decide) p (sat_cons (step652 p h) (sat_cons (step198 p h) (sat_nil p)))
def c1586 : List Lit := [(56, true), (51, true), (52, false), (87, true)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c653, c205] c1586 (by decide) p (sat_cons (step653 p h) (sat_cons (step205 p h) (sat_nil p)))
def c1587 : List Lit := [(4, true), (51, true), (87, true), (52, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c653, c206] c1587 (by decide) p (sat_cons (step653 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1588 : List Lit := [(53, false), (88, true)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c654, c207] c1588 (by decide) p (sat_cons (step654 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1589 : List Lit := [(53, false), (49, true)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c654, c208] c1589 (by decide) p (sat_cons (step654 p h) (sat_cons (step208 p h) (sat_nil p)))
def c1590 : List Lit := [(54, false), (71, true), (90, true)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c655, c209] c1590 (by decide) p (sat_cons (step655 p h) (sat_cons (step209 p h) (sat_nil p)))
def c1591 : List Lit := [(54, false), (56, true), (90, true)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c655, c210] c1591 (by decide) p (sat_cons (step655 p h) (sat_cons (step210 p h) (sat_nil p)))
def c1592 : List Lit := [(56, true), (54, false), (71, true)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c655, c211] c1592 (by decide) p (sat_cons (step655 p h) (sat_cons (step211 p h) (sat_nil p)))
def c1593 : List Lit := [(55, false), (56, true)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c656, c212] c1593 (by decide) p (sat_cons (step656 p h) (sat_cons (step212 p h) (sat_nil p)))
end B112E026
