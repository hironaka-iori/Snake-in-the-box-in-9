import B112E024Part0002
namespace B112E024
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1554 : List Lit := [(29, true), (30, true), (28, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true :=
  Snake9.LocalRup.prove_clause [c589, c156] c1554 (by decide) p (sat_cons (step589 p h) (sat_cons (step156 p h) (sat_nil p)))
def c1555 : List Lit := [(30, true), (27, true), (28, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true :=
  Snake9.LocalRup.prove_clause [c589, c157] c1555 (by decide) p (sat_cons (step589 p h) (sat_cons (step157 p h) (sat_nil p)))
def c1556 : List Lit := [(29, true), (27, true), (28, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true :=
  Snake9.LocalRup.prove_clause [c589, c158] c1556 (by decide) p (sat_cons (step589 p h) (sat_cons (step158 p h) (sat_nil p)))
def c1557 : List Lit := [(32, true), (38, true), (33, false), (15, true)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true :=
  Snake9.LocalRup.prove_clause [c590, c175] c1557 (by decide) p (sat_cons (step590 p h) (sat_cons (step175 p h) (sat_nil p)))
def c1558 : List Lit := [(9, true), (38, true), (32, true), (33, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true :=
  Snake9.LocalRup.prove_clause [c590, c176] c1558 (by decide) p (sat_cons (step590 p h) (sat_cons (step176 p h) (sat_nil p)))
def c1559 : List Lit := [(9, true), (38, true), (15, true), (33, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true :=
  Snake9.LocalRup.prove_clause [c590, c177] c1559 (by decide) p (sat_cons (step590 p h) (sat_cons (step177 p h) (sat_nil p)))
def c1560 : List Lit := [(35, false), (34, true), (16, true)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true :=
  Snake9.LocalRup.prove_clause [c591, c186] c1560 (by decide) p (sat_cons (step591 p h) (sat_cons (step186 p h) (sat_nil p)))
def c1561 : List Lit := [(40, true), (37, false), (38, true), (46, true)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true :=
  Snake9.LocalRup.prove_clause [c592, c188] c1561 (by decide) p (sat_cons (step592 p h) (sat_cons (step188 p h) (sat_nil p)))
def c1562 : List Lit := [(37, false), (38, true), (46, true), (32, true)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true :=
  Snake9.LocalRup.prove_clause [c592, c189] c1562 (by decide) p (sat_cons (step592 p h) (sat_cons (step189 p h) (sat_nil p)))
def c1563 : List Lit := [(39, false), (40, true)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true :=
  Snake9.LocalRup.prove_clause [c593, c197] c1563 (by decide) p (sat_cons (step593 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1564 : List Lit := [(39, false), (34, true)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true :=
  Snake9.LocalRup.prove_clause [c593, c198] c1564 (by decide) p (sat_cons (step593 p h) (sat_cons (step198 p h) (sat_nil p)))
def c1565 : List Lit := [(34, true), (116, true), (41, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true :=
  Snake9.LocalRup.prove_clause [c594, c208] c1565 (by decide) p (sat_cons (step594 p h) (sat_cons (step208 p h) (sat_nil p)))
def c1566 : List Lit := [(43, false), (48, true)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true :=
  Snake9.LocalRup.prove_clause [c595, c211] c1566 (by decide) p (sat_cons (step595 p h) (sat_cons (step211 p h) (sat_nil p)))
def c1567 : List Lit := [(43, false), (42, true)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true :=
  Snake9.LocalRup.prove_clause [c595, c212] c1567 (by decide) p (sat_cons (step595 p h) (sat_cons (step212 p h) (sat_nil p)))
def c1568 : List Lit := [(45, true), (44, false), (46, true)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true :=
  Snake9.LocalRup.prove_clause [c596, c213] c1568 (by decide) p (sat_cons (step596 p h) (sat_cons (step213 p h) (sat_nil p)))
def c1569 : List Lit := [(27, true), (44, false), (46, true)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true :=
  Snake9.LocalRup.prove_clause [c596, c214] c1569 (by decide) p (sat_cons (step596 p h) (sat_cons (step214 p h) (sat_nil p)))
def c1570 : List Lit := [(45, true), (27, true), (44, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true :=
  Snake9.LocalRup.prove_clause [c596, c215] c1570 (by decide) p (sat_cons (step596 p h) (sat_cons (step215 p h) (sat_nil p)))
def c1571 : List Lit := [(48, true), (47, false), (38, true), (46, true)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true :=
  Snake9.LocalRup.prove_clause [c597, c225] c1571 (by decide) p (sat_cons (step597 p h) (sat_cons (step225 p h) (sat_nil p)))
def c1572 : List Lit := [(45, true), (47, false), (46, true), (38, true)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true :=
  Snake9.LocalRup.prove_clause [c597, c226] c1572 (by decide) p (sat_cons (step597 p h) (sat_cons (step226 p h) (sat_nil p)))
def c1573 : List Lit := [(59, true), (51, true), (50, false), (82, true)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true :=
  Snake9.LocalRup.prove_clause [c598, c234] c1573 (by decide) p (sat_cons (step598 p h) (sat_cons (step234 p h) (sat_nil p)))
def c1574 : List Lit := [(49, true), (51, true), (82, true), (50, false)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true :=
  Snake9.LocalRup.prove_clause [c598, c235] c1574 (by decide) p (sat_cons (step598 p h) (sat_cons (step235 p h) (sat_nil p)))
def c1575 : List Lit := [(57, true), (51, true), (87, true), (53, false), (52, true)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true :=
  Snake9.LocalRup.prove_clause [c599, c249] c1575 (by decide) p (sat_cons (step599 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1576 : List Lit := [(54, false), (88, true)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true :=
  Snake9.LocalRup.prove_clause [c600, c250] c1576 (by decide) p (sat_cons (step600 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1577 : List Lit := [(54, false), (49, true)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true :=
  Snake9.LocalRup.prove_clause [c600, c251] c1577 (by decide) p (sat_cons (step600 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1578 : List Lit := [(71, true), (90, true), (55, false)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true :=
  Snake9.LocalRup.prove_clause [c601, c253] c1578 (by decide) p (sat_cons (step601 p h) (sat_cons (step253 p h) (sat_nil p)))
def c1579 : List Lit := [(57, true), (90, true), (55, false)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true :=
  Snake9.LocalRup.prove_clause [c601, c254] c1579 (by decide) p (sat_cons (step601 p h) (sat_cons (step254 p h) (sat_nil p)))
def c1580 : List Lit := [(57, true), (71, true), (55, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true :=
  Snake9.LocalRup.prove_clause [c601, c255] c1580 (by decide) p (sat_cons (step601 p h) (sat_cons (step255 p h) (sat_nil p)))
def c1581 : List Lit := [(57, true), (51, true), (56, false)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true :=
  Snake9.LocalRup.prove_clause [c602, c257] c1581 (by decide) p (sat_cons (step602 p h) (sat_cons (step257 p h) (sat_nil p)))
def c1582 : List Lit := [(59, true), (58, false), (60, true)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true :=
  Snake9.LocalRup.prove_clause [c603, c263] c1582 (by decide) p (sat_cons (step603 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1583 : List Lit := [(49, true), (58, false), (60, true)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true :=
  Snake9.LocalRup.prove_clause [c603, c264] c1583 (by decide) p (sat_cons (step603 p h) (sat_cons (step264 p h) (sat_nil p)))
def c1584 : List Lit := [(95, true), (60, true), (61, false)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true :=
  Snake9.LocalRup.prove_clause [c604, c270] c1584 (by decide) p (sat_cons (step604 p h) (sat_cons (step270 p h) (sat_nil p)))
def c1585 : List Lit := [(59, true), (95, true), (61, false)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true :=
  Snake9.LocalRup.prove_clause [c604, c271] c1585 (by decide) p (sat_cons (step604 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1586 : List Lit := [(63, false), (65, true)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true :=
  Snake9.LocalRup.prove_clause [c606, c276] c1586 (by decide) p (sat_cons (step606 p h) (sat_cons (step276 p h) (sat_nil p)))
def c1587 : List Lit := [(63, false), (64, true)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true :=
  Snake9.LocalRup.prove_clause [c606, c277] c1587 (by decide) p (sat_cons (step606 p h) (sat_cons (step277 p h) (sat_nil p)))
def c1588 : List Lit := [(9, true), (71, true), (67, false)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true :=
  Snake9.LocalRup.prove_clause [c607, c281] c1588 (by decide) p (sat_cons (step607 p h) (sat_cons (step281 p h) (sat_nil p)))
def c1589 : List Lit := [(66, true), (9, true), (67, false)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true :=
  Snake9.LocalRup.prove_clause [c607, c282] c1589 (by decide) p (sat_cons (step607 p h) (sat_cons (step282 p h) (sat_nil p)))
def c1590 : List Lit := [(70, false), (71, true), (73, true)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true :=
  Snake9.LocalRup.prove_clause [c609, c289] c1590 (by decide) p (sat_cons (step609 p h) (sat_cons (step289 p h) (sat_nil p)))
def c1591 : List Lit := [(66, true), (71, true), (70, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true :=
  Snake9.LocalRup.prove_clause [c609, c290] c1591 (by decide) p (sat_cons (step609 p h) (sat_cons (step290 p h) (sat_nil p)))
def c1592 : List Lit := [(72, false), (73, true)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c610, c298] c1592 (by decide) p (sat_cons (step610 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1593 : List Lit := [(72, false), (68, true)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c610, c299] c1593 (by decide) p (sat_cons (step610 p h) (sat_cons (step299 p h) (sat_nil p)))
def c1594 : List Lit := [(68, true), (74, false), (116, true)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c611, c303] c1594 (by decide) p (sat_cons (step611 p h) (sat_cons (step303 p h) (sat_nil p)))
def c1595 : List Lit := [(76, false), (80, true)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c612, c306] c1595 (by decide) p (sat_cons (step612 p h) (sat_cons (step306 p h) (sat_nil p)))
def c1596 : List Lit := [(76, false), (75, true)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c612, c307] c1596 (by decide) p (sat_cons (step612 p h) (sat_cons (step307 p h) (sat_nil p)))
def c1597 : List Lit := [(78, false), (199, true)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c1364, c309] c1597 (by decide) p (sat_cons (step1364 p h) (sat_cons (step309 p h) (sat_nil p)))
def c1598 : List Lit := [(71, true), (78, true), (79, false)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c614, c310] c1598 (by decide) p (sat_cons (step614 p h) (sat_cons (step310 p h) (sat_nil p)))
def c1599 : List Lit := [(97, true), (51, true), (82, true), (85, false), (84, true), (87, true)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c615, c358] c1599 (by decide) p (sat_cons (step615 p h) (sat_cons (step358 p h) (sat_nil p)))
def c1600 : List Lit := [(97, true), (51, true), (82, true), (87, true), (85, false), (16, true)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c615, c359] c1600 (by decide) p (sat_cons (step615 p h) (sat_cons (step359 p h) (sat_nil p)))
def c1601 : List Lit := [(97, true), (51, true), (84, true), (82, true), (85, false), (16, true)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c615, c360] c1601 (by decide) p (sat_cons (step615 p h) (sat_cons (step360 p h) (sat_nil p)))
def c1602 : List Lit := [(51, true), (16, true), (82, true), (84, true), (87, true), (85, false)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c615, c361] c1602 (by decide) p (sat_cons (step615 p h) (sat_cons (step361 p h) (sat_nil p)))
def c1603 : List Lit := [(101, true), (92, true), (89, false), (90, true), (83, true)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c616, c427] c1603 (by decide) p (sat_cons (step616 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1604 : List Lit := [(101, true), (92, true), (88, true), (89, false), (83, true)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c616, c428] c1604 (by decide) p (sat_cons (step616 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1605 : List Lit := [(101, true), (90, true), (88, true), (89, false), (83, true)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c616, c429] c1605 (by decide) p (sat_cons (step616 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1606 : List Lit := [(92, true), (90, true), (89, false), (83, true), (88, true)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c616, c430] c1606 (by decide) p (sat_cons (step616 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1607 : List Lit := [(91, false), (92, true), (88, true)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c617, c449] c1607 (by decide) p (sat_cons (step617 p h) (sat_cons (step449 p h) (sat_nil p)))
def c1608 : List Lit := [(91, false), (84, true), (92, true)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c617, c450] c1608 (by decide) p (sat_cons (step617 p h) (sat_cons (step450 p h) (sat_nil p)))
def c1609 : List Lit := [(91, false), (84, true), (88, true)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c617, c451] c1609 (by decide) p (sat_cons (step617 p h) (sat_cons (step451 p h) (sat_nil p)))
def c1610 : List Lit := [(97, true), (116, true), (96, false)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c618, c484] c1610 (by decide) p (sat_cons (step618 p h) (sat_cons (step484 p h) (sat_nil p)))
def c1611 : List Lit := [(116, true), (84, true), (96, false)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c618, c485] c1611 (by decide) p (sat_cons (step618 p h) (sat_cons (step485 p h) (sat_nil p)))
def c1612 : List Lit := [(97, true), (84, true), (96, false)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c618, c486] c1612 (by decide) p (sat_cons (step618 p h) (sat_cons (step486 p h) (sat_nil p)))
def c1613 : List Lit := [(97, true), (95, true), (103, true), (98, false)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c619, c493] c1613 (by decide) p (sat_cons (step619 p h) (sat_cons (step493 p h) (sat_nil p)))
def c1614 : List Lit := [(97, true), (103, true), (87, true), (98, false)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c619, c494] c1614 (by decide) p (sat_cons (step619 p h) (sat_cons (step494 p h) (sat_nil p)))
def c1615 : List Lit := [(95, true), (103, true), (98, false), (87, true)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c619, c495] c1615 (by decide) p (sat_cons (step619 p h) (sat_cons (step495 p h) (sat_nil p)))
def c1616 : List Lit := [(97, true), (95, true), (98, false), (87, true)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c619, c496] c1616 (by decide) p (sat_cons (step619 p h) (sat_cons (step496 p h) (sat_nil p)))
def c1617 : List Lit := [(101, true), (100, true), (99, false), (88, true)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c620, c499] c1617 (by decide) p (sat_cons (step620 p h) (sat_cons (step499 p h) (sat_nil p)))
end B112E024
