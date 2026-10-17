import B112E186Part0002
namespace B112E186
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1592 : List Lit := [(47, true), (53, true), (48, false), (67, true)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true :=
  Snake9.LocalRup.prove_clause [c677, c168] c1592 (by decide) p (sat_cons (step677 p h) (sat_cons (step168 p h) (sat_nil p)))
def c1593 : List Lit := [(61, true), (51, false), (88, true)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true :=
  Snake9.LocalRup.prove_clause [c678, c173] c1593 (by decide) p (sat_cons (step678 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1594 : List Lit := [(53, true), (51, false), (88, true)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c678, c174] c1594 (by decide) p (sat_cons (step678 p h) (sat_cons (step174 p h) (sat_nil p)))
def c1595 : List Lit := [(61, true), (53, true), (51, false)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c678, c175] c1595 (by decide) p (sat_cons (step678 p h) (sat_cons (step175 p h) (sat_nil p)))
def c1596 : List Lit := [(55, true), (53, true), (89, true), (52, false)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c679, c177] c1596 (by decide) p (sat_cons (step679 p h) (sat_cons (step177 p h) (sat_nil p)))
def c1597 : List Lit := [(55, true), (52, false), (47, true), (89, true)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c679, c178] c1597 (by decide) p (sat_cons (step679 p h) (sat_cons (step178 p h) (sat_nil p)))
def c1598 : List Lit := [(53, true), (52, false), (47, true), (89, true)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c679, c179] c1598 (by decide) p (sat_cons (step679 p h) (sat_cons (step179 p h) (sat_nil p)))
def c1599 : List Lit := [(55, true), (53, true), (52, false), (47, true)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c679, c180] c1599 (by decide) p (sat_cons (step679 p h) (sat_cons (step180 p h) (sat_nil p)))
def c1600 : List Lit := [(55, true), (90, true), (54, false)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c680, c191] c1600 (by decide) p (sat_cons (step680 p h) (sat_cons (step191 p h) (sat_nil p)))
def c1601 : List Lit := [(49, true), (90, true), (54, false)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c680, c192] c1601 (by decide) p (sat_cons (step680 p h) (sat_cons (step192 p h) (sat_nil p)))
def c1602 : List Lit := [(49, true), (55, true), (54, false)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c680, c193] c1602 (by decide) p (sat_cons (step680 p h) (sat_cons (step193 p h) (sat_nil p)))
def c1603 : List Lit := [(49, true), (58, true), (57, false)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c681, c197] c1603 (by decide) p (sat_cons (step681 p h) (sat_cons (step197 p h) (sat_nil p)))
def c1604 : List Lit := [(49, true), (56, true), (57, false)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c681, c198] c1604 (by decide) p (sat_cons (step681 p h) (sat_cons (step198 p h) (sat_nil p)))
def c1605 : List Lit := [(59, false), (63, true)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c682, c200] c1605 (by decide) p (sat_cons (step682 p h) (sat_cons (step200 p h) (sat_nil p)))
def c1606 : List Lit := [(59, false), (58, true)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c682, c201] c1606 (by decide) p (sat_cons (step682 p h) (sat_cons (step201 p h) (sat_nil p)))
def c1607 : List Lit := [(77, true), (60, false), (99, true), (61, true)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c683, c204] c1607 (by decide) p (sat_cons (step683 p h) (sat_cons (step204 p h) (sat_nil p)))
def c1608 : List Lit := [(56, true), (77, true), (60, false), (99, true)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c683, c205] c1608 (by decide) p (sat_cons (step683 p h) (sat_cons (step205 p h) (sat_nil p)))
def c1609 : List Lit := [(56, true), (60, false), (99, true), (61, true)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c683, c206] c1609 (by decide) p (sat_cons (step683 p h) (sat_cons (step206 p h) (sat_nil p)))
def c1610 : List Lit := [(56, true), (77, true), (60, false), (61, true)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c683, c207] c1610 (by decide) p (sat_cons (step683 p h) (sat_cons (step207 p h) (sat_nil p)))
def c1611 : List Lit := [(63, true), (62, false), (61, true)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c684, c213] c1611 (by decide) p (sat_cons (step684 p h) (sat_cons (step213 p h) (sat_nil p)))
def c1612 : List Lit := [(53, true), (63, true), (62, false)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c684, c214] c1612 (by decide) p (sat_cons (step684 p h) (sat_cons (step214 p h) (sat_nil p)))
def c1613 : List Lit := [(53, true), (62, false), (61, true)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c684, c215] c1613 (by decide) p (sat_cons (step684 p h) (sat_cons (step215 p h) (sat_nil p)))
def c1614 : List Lit := [(73, true), (64, true), (65, false), (67, true)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c685, c222] c1614 (by decide) p (sat_cons (step685 p h) (sat_cons (step222 p h) (sat_nil p)))
def c1615 : List Lit := [(64, true), (68, true), (67, true), (65, false)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c685, c223] c1615 (by decide) p (sat_cons (step685 p h) (sat_cons (step223 p h) (sat_nil p)))
def c1616 : List Lit := [(74, true), (64, true), (67, true), (66, false), (106, true)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c686, c227] c1616 (by decide) p (sat_cons (step686 p h) (sat_cons (step227 p h) (sat_nil p)))
def c1617 : List Lit := [(74, true), (66, false), (47, true), (67, true), (106, true)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c686, c228] c1617 (by decide) p (sat_cons (step686 p h) (sat_cons (step228 p h) (sat_nil p)))
def c1618 : List Lit := [(64, true), (66, false), (106, true), (47, true), (67, true)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c686, c229] c1618 (by decide) p (sat_cons (step686 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1619 : List Lit := [(64, true), (77, true), (69, false), (111, true)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c687, c254] c1619 (by decide) p (sat_cons (step687 p h) (sat_cons (step254 p h) (sat_nil p)))
def c1620 : List Lit := [(2, true), (64, true), (69, false), (111, true)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c687, c255] c1620 (by decide) p (sat_cons (step687 p h) (sat_cons (step255 p h) (sat_nil p)))
def c1621 : List Lit := [(2, true), (77, true), (69, false), (64, true)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c687, c256] c1621 (by decide) p (sat_cons (step687 p h) (sat_cons (step256 p h) (sat_nil p)))
def c1622 : List Lit := [(72, true), (53, true), (70, false), (67, true)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c688, c257] c1622 (by decide) p (sat_cons (step688 p h) (sat_cons (step257 p h) (sat_nil p)))
def c1623 : List Lit := [(72, true), (4, true), (70, false), (67, true)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c688, c258] c1623 (by decide) p (sat_cons (step688 p h) (sat_cons (step258 p h) (sat_nil p)))
def c1624 : List Lit := [(4, true), (53, true), (70, false), (67, true)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c688, c259] c1624 (by decide) p (sat_cons (step688 p h) (sat_cons (step259 p h) (sat_nil p)))
def c1625 : List Lit := [(79, true), (72, true), (71, false)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c689, c261] c1625 (by decide) p (sat_cons (step689 p h) (sat_cons (step261 p h) (sat_nil p)))
def c1626 : List Lit := [(79, true), (68, true), (71, false)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c689, c262] c1626 (by decide) p (sat_cons (step689 p h) (sat_cons (step262 p h) (sat_nil p)))
def c1627 : List Lit := [(68, true), (72, true), (71, false)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c689, c263] c1627 (by decide) p (sat_cons (step689 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1628 : List Lit := [(74, true), (73, true), (75, false)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c690, c271] c1628 (by decide) p (sat_cons (step690 p h) (sat_cons (step271 p h) (sat_nil p)))
def c1629 : List Lit := [(74, true), (75, false), (67, true)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c690, c272] c1629 (by decide) p (sat_cons (step690 p h) (sat_cons (step272 p h) (sat_nil p)))
def c1630 : List Lit := [(73, true), (75, false), (67, true)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c690, c273] c1630 (by decide) p (sat_cons (step690 p h) (sat_cons (step273 p h) (sat_nil p)))
def c1631 : List Lit := [(76, false), (80, true)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c691, c274] c1631 (by decide) p (sat_cons (step691 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1632 : List Lit := [(76, false), (74, true)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c691, c275] c1632 (by decide) p (sat_cons (step691 p h) (sat_cons (step275 p h) (sat_nil p)))
def c1633 : List Lit := [(80, true), (79, true), (78, false)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c692, c277] c1633 (by decide) p (sat_cons (step692 p h) (sat_cons (step277 p h) (sat_nil p)))
def c1634 : List Lit := [(80, true), (77, true), (78, false)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c692, c278] c1634 (by decide) p (sat_cons (step692 p h) (sat_cons (step278 p h) (sat_nil p)))
def c1635 : List Lit := [(79, true), (77, true), (78, false)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c692, c279] c1635 (by decide) p (sat_cons (step692 p h) (sat_cons (step279 p h) (sat_nil p)))
def c1636 : List Lit := [(95, true), (86, true), (83, false), (85, true), (88, true)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c693, c296] c1636 (by decide) p (sat_cons (step693 p h) (sat_cons (step296 p h) (sat_nil p)))
def c1637 : List Lit := [(82, true), (95, true), (83, false), (86, true), (88, true)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c693, c297] c1637 (by decide) p (sat_cons (step693 p h) (sat_cons (step297 p h) (sat_nil p)))
def c1638 : List Lit := [(95, true), (82, true), (83, false), (85, true), (88, true)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c693, c298] c1638 (by decide) p (sat_cons (step693 p h) (sat_cons (step298 p h) (sat_nil p)))
def c1639 : List Lit := [(95, true), (82, true), (83, false), (86, true), (85, true)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c693, c299] c1639 (by decide) p (sat_cons (step693 p h) (sat_cons (step299 p h) (sat_nil p)))
def c1640 : List Lit := [(82, true), (86, true), (83, false), (88, true), (85, true)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c693, c300] c1640 (by decide) p (sat_cons (step693 p h) (sat_cons (step300 p h) (sat_nil p)))
def c1641 : List Lit := [(47, true), (82, true), (84, false), (85, true), (89, true), (96, true), (106, true)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c694, c315] c1641 (by decide) p (sat_cons (step694 p h) (sat_cons (step315 p h) (sat_nil p)))
def c1642 : List Lit := [(110, true), (93, true), (86, true), (87, false)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c695, c364] c1642 (by decide) p (sat_cons (step695 p h) (sat_cons (step364 p h) (sat_nil p)))
def c1643 : List Lit := [(93, true), (110, true), (85, true), (87, false)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c695, c365] c1643 (by decide) p (sat_cons (step695 p h) (sat_cons (step365 p h) (sat_nil p)))
def c1644 : List Lit := [(86, true), (110, true), (87, false), (85, true)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c695, c366] c1644 (by decide) p (sat_cons (step695 p h) (sat_cons (step366 p h) (sat_nil p)))
def c1645 : List Lit := [(86, true), (93, true), (85, true), (87, false)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c695, c367] c1645 (by decide) p (sat_cons (step695 p h) (sat_cons (step367 p h) (sat_nil p)))
def c1646 : List Lit := [(91, false), (90, true), (88, true), (93, true), (103, true)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c696, c426] c1646 (by decide) p (sat_cons (step696 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1647 : List Lit := [(103, true), (93, true), (90, true), (86, true), (91, false)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c696, c427] c1647 (by decide) p (sat_cons (step696 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1648 : List Lit := [(91, false), (93, true), (86, true), (88, true), (103, true)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c696, c428] c1648 (by decide) p (sat_cons (step696 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1649 : List Lit := [(91, false), (90, true), (86, true), (88, true), (103, true)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c696, c429] c1649 (by decide) p (sat_cons (step696 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1650 : List Lit := [(91, false), (90, true), (86, true), (88, true), (93, true)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c696, c430] c1650 (by decide) p (sat_cons (step696 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1651 : List Lit := [(95, true), (96, true), (97, false)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c697, c462] c1651 (by decide) p (sat_cons (step697 p h) (sat_cons (step462 p h) (sat_nil p)))
def c1652 : List Lit := [(97, false), (96, true), (85, true)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c697, c463] c1652 (by decide) p (sat_cons (step697 p h) (sat_cons (step463 p h) (sat_nil p)))
def c1653 : List Lit := [(95, true), (97, false), (85, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c697, c464] c1653 (by decide) p (sat_cons (step697 p h) (sat_cons (step464 p h) (sat_nil p)))
def c1654 : List Lit := [(104, true), (96, true), (98, false)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c698, c466] c1654 (by decide) p (sat_cons (step698 p h) (sat_cons (step466 p h) (sat_nil p)))
def c1655 : List Lit := [(104, true), (24, true), (98, false)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c698, c467] c1655 (by decide) p (sat_cons (step698 p h) (sat_cons (step467 p h) (sat_nil p)))
end B112E186
