import B112E110Part0003
namespace B112E110
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1557 : List Lit := [(28, true), (18, true), (19, false), (21, true)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c577, c62] c1557 (by decide) p (sat_cons (step577 p h) (sat_cons (step62 p h) (sat_nil p)))
def c1558 : List Lit := [(18, true), (23, true), (19, false), (21, true)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c577, c63] c1558 (by decide) p (sat_cons (step577 p h) (sat_cons (step63 p h) (sat_nil p)))
def c1559 : List Lit := [(24, true), (80, true), (20, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c578, c64] c1559 (by decide) p (sat_cons (step578 p h) (sat_cons (step64 p h) (sat_nil p)))
def c1560 : List Lit := [(80, true), (20, false), (21, true)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c578, c65] c1560 (by decide) p (sat_cons (step578 p h) (sat_cons (step65 p h) (sat_nil p)))
def c1561 : List Lit := [(24, true), (20, false), (21, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c578, c66] c1561 (by decide) p (sat_cons (step578 p h) (sat_cons (step66 p h) (sat_nil p)))
def c1562 : List Lit := [(18, true), (83, true), (22, false), (23, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c579, c74] c1562 (by decide) p (sat_cons (step579 p h) (sat_cons (step74 p h) (sat_nil p)))
def c1563 : List Lit := [(1, true), (83, true), (22, false), (23, true)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c579, c75] c1563 (by decide) p (sat_cons (step579 p h) (sat_cons (step75 p h) (sat_nil p)))
def c1564 : List Lit := [(18, true), (1, true), (22, false), (83, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c579, c76] c1564 (by decide) p (sat_cons (step579 p h) (sat_cons (step76 p h) (sat_nil p)))
def c1565 : List Lit := [(33, true), (24, true), (23, true), (25, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c580, c93] c1565 (by decide) p (sat_cons (step580 p h) (sat_cons (step93 p h) (sat_nil p)))
def c1566 : List Lit := [(33, true), (23, true), (21, true), (25, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c580, c94] c1566 (by decide) p (sat_cons (step580 p h) (sat_cons (step94 p h) (sat_nil p)))
def c1567 : List Lit := [(24, true), (23, true), (21, true), (25, false)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c580, c95] c1567 (by decide) p (sat_cons (step580 p h) (sat_cons (step95 p h) (sat_nil p)))
def c1568 : List Lit := [(27, false), (28, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c581, c100] c1568 (by decide) p (sat_cons (step581 p h) (sat_cons (step100 p h) (sat_nil p)))
def c1569 : List Lit := [(27, false), (26, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c581, c101] c1569 (by decide) p (sat_cons (step581 p h) (sat_cons (step101 p h) (sat_nil p)))
def c1570 : List Lit := [(44, true), (29, false), (31, true)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c582, c106] c1570 (by decide) p (sat_cons (step582 p h) (sat_cons (step106 p h) (sat_nil p)))
def c1571 : List Lit := [(26, true), (29, false), (44, true)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c582, c107] c1571 (by decide) p (sat_cons (step582 p h) (sat_cons (step107 p h) (sat_nil p)))
def c1572 : List Lit := [(91, true), (26, true), (30, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c583, c110] c1572 (by decide) p (sat_cons (step583 p h) (sat_cons (step110 p h) (sat_nil p)))
def c1573 : List Lit := [(26, true), (31, true), (30, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c583, c111] c1573 (by decide) p (sat_cons (step583 p h) (sat_cons (step111 p h) (sat_nil p)))
def c1574 : List Lit := [(32, false), (33, true)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c584, c116] c1574 (by decide) p (sat_cons (step584 p h) (sat_cons (step116 p h) (sat_nil p)))
def c1575 : List Lit := [(32, false), (31, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c584, c117] c1575 (by decide) p (sat_cons (step584 p h) (sat_cons (step117 p h) (sat_nil p)))
def c1576 : List Lit := [(97, true), (39, true), (35, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c585, c126] c1576 (by decide) p (sat_cons (step585 p h) (sat_cons (step126 p h) (sat_nil p)))
def c1577 : List Lit := [(34, true), (97, true), (35, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c585, c127] c1577 (by decide) p (sat_cons (step585 p h) (sat_cons (step127 p h) (sat_nil p)))
def c1578 : List Lit := [(34, true), (39, true), (35, false)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c585, c128] c1578 (by decide) p (sat_cons (step585 p h) (sat_cons (step128 p h) (sat_nil p)))
def c1579 : List Lit := [(101, true), (36, true), (47, true), (37, false)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c586, c132] c1579 (by decide) p (sat_cons (step586 p h) (sat_cons (step132 p h) (sat_nil p)))
def c1580 : List Lit := [(101, true), (47, true), (21, true), (37, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c586, c133] c1580 (by decide) p (sat_cons (step586 p h) (sat_cons (step133 p h) (sat_nil p)))
def c1581 : List Lit := [(101, true), (36, true), (37, false), (21, true)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c586, c134] c1581 (by decide) p (sat_cons (step586 p h) (sat_cons (step134 p h) (sat_nil p)))
def c1582 : List Lit := [(36, true), (47, true), (21, true), (37, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c586, c135] c1582 (by decide) p (sat_cons (step586 p h) (sat_cons (step135 p h) (sat_nil p)))
def c1583 : List Lit := [(102, true), (41, true), (38, false), (39, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c587, c137] c1583 (by decide) p (sat_cons (step587 p h) (sat_cons (step137 p h) (sat_nil p)))
def c1584 : List Lit := [(102, true), (34, true), (38, false), (41, true)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c587, c138] c1584 (by decide) p (sat_cons (step587 p h) (sat_cons (step138 p h) (sat_nil p)))
def c1585 : List Lit := [(50, true), (7, true), (103, true), (40, false), (23, true)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c588, c146] c1585 (by decide) p (sat_cons (step588 p h) (sat_cons (step146 p h) (sat_nil p)))
def c1586 : List Lit := [(7, true), (103, true), (39, true), (40, false), (23, true)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c588, c147] c1586 (by decide) p (sat_cons (step588 p h) (sat_cons (step147 p h) (sat_nil p)))
def c1587 : List Lit := [(50, true), (7, true), (39, true), (40, false), (23, true)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c588, c148] c1587 (by decide) p (sat_cons (step588 p h) (sat_cons (step148 p h) (sat_nil p)))
def c1588 : List Lit := [(41, true), (106, true), (42, false)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c589, c153] c1588 (by decide) p (sat_cons (step589 p h) (sat_cons (step153 p h) (sat_nil p)))
def c1589 : List Lit := [(36, true), (106, true), (42, false)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c589, c154] c1589 (by decide) p (sat_cons (step589 p h) (sat_cons (step154 p h) (sat_nil p)))
def c1590 : List Lit := [(41, true), (36, true), (42, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c589, c155] c1590 (by decide) p (sat_cons (step589 p h) (sat_cons (step155 p h) (sat_nil p)))
def c1591 : List Lit := [(47, true), (51, true), (45, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c590, c168] c1591 (by decide) p (sat_cons (step590 p h) (sat_cons (step168 p h) (sat_nil p)))
def c1592 : List Lit := [(51, true), (44, true), (45, false)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c590, c169] c1592 (by decide) p (sat_cons (step590 p h) (sat_cons (step169 p h) (sat_nil p)))
def c1593 : List Lit := [(47, true), (44, true), (45, false)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c590, c170] c1593 (by decide) p (sat_cons (step590 p h) (sat_cons (step170 p h) (sat_nil p)))
def c1594 : List Lit := [(47, true), (36, true), (46, false), (44, true)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c591, c173] c1594 (by decide) p (sat_cons (step591 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1595 : List Lit := [(43, true), (47, true), (36, true), (46, false)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c591, c174] c1595 (by decide) p (sat_cons (step591 p h) (sat_cons (step174 p h) (sat_nil p)))
def c1596 : List Lit := [(43, true), (36, true), (46, false), (44, true)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c591, c175] c1596 (by decide) p (sat_cons (step591 p h) (sat_cons (step175 p h) (sat_nil p)))
def c1597 : List Lit := [(51, true), (50, true), (48, false)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c592, c179] c1597 (by decide) p (sat_cons (step592 p h) (sat_cons (step179 p h) (sat_nil p)))
def c1598 : List Lit := [(50, true), (48, false), (39, true)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c592, c181] c1598 (by decide) p (sat_cons (step592 p h) (sat_cons (step181 p h) (sat_nil p)))
def c1599 : List Lit := [(50, true), (49, false), (114, true)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c593, c182] c1599 (by decide) p (sat_cons (step593 p h) (sat_cons (step182 p h) (sat_nil p)))
def c1600 : List Lit := [(49, false), (43, true), (114, true)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c593, c183] c1600 (by decide) p (sat_cons (step593 p h) (sat_cons (step183 p h) (sat_nil p)))
def c1601 : List Lit := [(50, true), (49, false), (43, true)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c593, c184] c1601 (by decide) p (sat_cons (step593 p h) (sat_cons (step184 p h) (sat_nil p)))
def c1602 : List Lit := [(56, true), (52, false), (83, true)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c594, c192] c1602 (by decide) p (sat_cons (step594 p h) (sat_cons (step192 p h) (sat_nil p)))
def c1603 : List Lit := [(1, true), (83, true), (52, false)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c594, c193] c1603 (by decide) p (sat_cons (step594 p h) (sat_cons (step193 p h) (sat_nil p)))
def c1604 : List Lit := [(1, true), (56, true), (52, false)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c594, c194] c1604 (by decide) p (sat_cons (step594 p h) (sat_cons (step194 p h) (sat_nil p)))
def c1605 : List Lit := [(171, true), (55, true)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c1301, c195] c1605 (by decide) p (sat_cons (step1301 p h) (sat_cons (step195 p h) (sat_nil p)))
def c1606 : List Lit := [(55, false), (57, true)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c595, c198] c1606 (by decide) p (sat_cons (step595 p h) (sat_cons (step198 p h) (sat_nil p)))
def c1607 : List Lit := [(58, false), (56, true)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c596, c202] c1607 (by decide) p (sat_cons (step596 p h) (sat_cons (step202 p h) (sat_nil p)))
def c1608 : List Lit := [(60, false), (97, true)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c597, c207] c1608 (by decide) p (sat_cons (step597 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1609 : List Lit := [(60, false), (59, true)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c597, c208] c1609 (by decide) p (sat_cons (step597 p h) (sat_cons (step208 p h) (sat_nil p)))
def c1610 : List Lit := [(62, true), (61, false), (65, true)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c598, c210] c1610 (by decide) p (sat_cons (step598 p h) (sat_cons (step210 p h) (sat_nil p)))
def c1611 : List Lit := [(59, true), (61, false), (65, true)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c598, c211] c1611 (by decide) p (sat_cons (step598 p h) (sat_cons (step211 p h) (sat_nil p)))
def c1612 : List Lit := [(62, true), (59, true), (61, false)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c598, c212] c1612 (by decide) p (sat_cons (step598 p h) (sat_cons (step212 p h) (sat_nil p)))
def c1613 : List Lit := [(63, false), (65, true), (71, true), (102, true)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c599, c216] c1613 (by decide) p (sat_cons (step599 p h) (sat_cons (step216 p h) (sat_nil p)))
def c1614 : List Lit := [(59, true), (63, false), (71, true), (102, true)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c599, c217] c1614 (by decide) p (sat_cons (step599 p h) (sat_cons (step217 p h) (sat_nil p)))
def c1615 : List Lit := [(74, true), (103, true), (64, false)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c600, c218] c1615 (by decide) p (sat_cons (step600 p h) (sat_cons (step218 p h) (sat_nil p)))
def c1616 : List Lit := [(103, true), (64, false), (7, true)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c600, c219] c1616 (by decide) p (sat_cons (step600 p h) (sat_cons (step219 p h) (sat_nil p)))
def c1617 : List Lit := [(74, true), (64, false), (7, true)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c600, c220] c1617 (by decide) p (sat_cons (step600 p h) (sat_cons (step220 p h) (sat_nil p)))
def c1618 : List Lit := [(65, true), (66, false), (106, true)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c601, c225] c1618 (by decide) p (sat_cons (step601 p h) (sat_cons (step225 p h) (sat_nil p)))
def c1619 : List Lit := [(62, true), (66, false), (106, true)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c601, c226] c1619 (by decide) p (sat_cons (step601 p h) (sat_cons (step226 p h) (sat_nil p)))
def c1620 : List Lit := [(62, true), (65, true), (66, false)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c601, c227] c1620 (by decide) p (sat_cons (step601 p h) (sat_cons (step227 p h) (sat_nil p)))
end B112E110
