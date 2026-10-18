import B112E026Part0002
namespace B112E026
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1594 : List Lit := [(58, true), (59, true), (57, false), (61, true)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true :=
  Snake9.LocalRup.prove_clause [c657, c220] c1594 (by decide) p (sat_cons (step657 p h) (sat_cons (step220 p h) (sat_nil p)))
def c1595 : List Lit := [(59, true), (49, true), (57, false), (61, true)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true :=
  Snake9.LocalRup.prove_clause [c657, c221] c1595 (by decide) p (sat_cons (step657 p h) (sat_cons (step221 p h) (sat_nil p)))
def c1596 : List Lit := [(58, true), (49, true), (57, false), (61, true)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true :=
  Snake9.LocalRup.prove_clause [c657, c222] c1596 (by decide) p (sat_cons (step657 p h) (sat_cons (step222 p h) (sat_nil p)))
def c1597 : List Lit := [(59, true), (60, false), (95, true)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true :=
  Snake9.LocalRup.prove_clause [c658, c232] c1597 (by decide) p (sat_cons (step658 p h) (sat_cons (step232 p h) (sat_nil p)))
def c1598 : List Lit := [(58, true), (60, false), (95, true)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true :=
  Snake9.LocalRup.prove_clause [c658, c233] c1598 (by decide) p (sat_cons (step658 p h) (sat_cons (step233 p h) (sat_nil p)))
def c1599 : List Lit := [(58, true), (59, true), (60, false)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true :=
  Snake9.LocalRup.prove_clause [c658, c234] c1599 (by decide) p (sat_cons (step658 p h) (sat_cons (step234 p h) (sat_nil p)))
def c1600 : List Lit := [(65, true), (62, false), (61, true), (59, true)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true :=
  Snake9.LocalRup.prove_clause [c659, c248] c1600 (by decide) p (sat_cons (step659 p h) (sat_cons (step248 p h) (sat_nil p)))
def c1601 : List Lit := [(61, true), (59, true), (62, false), (51, true)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true :=
  Snake9.LocalRup.prove_clause [c659, c249] c1601 (by decide) p (sat_cons (step659 p h) (sat_cons (step249 p h) (sat_nil p)))
def c1602 : List Lit := [(64, true), (63, false), (65, true)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true :=
  Snake9.LocalRup.prove_clause [c660, c250] c1602 (by decide) p (sat_cons (step660 p h) (sat_cons (step250 p h) (sat_nil p)))
def c1603 : List Lit := [(63, false), (65, true), (61, true)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c660, c251] c1603 (by decide) p (sat_cons (step660 p h) (sat_cons (step251 p h) (sat_nil p)))
def c1604 : List Lit := [(64, true), (63, false), (61, true)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c660, c252] c1604 (by decide) p (sat_cons (step660 p h) (sat_cons (step252 p h) (sat_nil p)))
def c1605 : List Lit := [(9, true), (71, true), (67, false)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c661, c256] c1605 (by decide) p (sat_cons (step661 p h) (sat_cons (step256 p h) (sat_nil p)))
def c1606 : List Lit := [(69, false), (75, true)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c662, c260] c1606 (by decide) p (sat_cons (step662 p h) (sat_cons (step260 p h) (sat_nil p)))
def c1607 : List Lit := [(70, false), (73, true), (71, true)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c663, c263] c1607 (by decide) p (sat_cons (step663 p h) (sat_cons (step263 p h) (sat_nil p)))
def c1608 : List Lit := [(72, false), (73, true)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c664, c273] c1608 (by decide) p (sat_cons (step664 p h) (sat_cons (step273 p h) (sat_nil p)))
def c1609 : List Lit := [(72, false), (68, true)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c664, c274] c1609 (by decide) p (sat_cons (step664 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1610 : List Lit := [(76, false), (80, true)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c665, c282] c1610 (by decide) p (sat_cons (step665 p h) (sat_cons (step282 p h) (sat_nil p)))
def c1611 : List Lit := [(76, false), (75, true)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c665, c283] c1611 (by decide) p (sat_cons (step665 p h) (sat_cons (step283 p h) (sat_nil p)))
def c1612 : List Lit := [(78, false), (79, true)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c1403, c285] c1612 (by decide) p (sat_cons (step1403 p h) (sat_cons (step285 p h) (sat_nil p)))
def c1613 : List Lit := [(78, false), (199, true)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c1403, c286] c1613 (by decide) p (sat_cons (step1403 p h) (sat_cons (step286 p h) (sat_nil p)))
def c1614 : List Lit := [(80, true), (71, true), (79, false)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c667, c288] c1614 (by decide) p (sat_cons (step667 p h) (sat_cons (step288 p h) (sat_nil p)))
def c1615 : List Lit := [(71, true), (78, true), (79, false)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c667, c289] c1615 (by decide) p (sat_cons (step667 p h) (sat_cons (step289 p h) (sat_nil p)))
def c1616 : List Lit := [(88, true), (104, true), (12, true), (83, true), (81, false), (82, true), (84, true)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c668, c310] c1616 (by decide) p (sat_cons (step668 p h) (sat_cons (step310 p h) (sat_nil p)))
def c1617 : List Lit := [(87, true), (82, true), (97, true), (84, true), (85, false)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c669, c354] c1617 (by decide) p (sat_cons (step669 p h) (sat_cons (step354 p h) (sat_nil p)))
def c1618 : List Lit := [(87, true), (16, true), (97, true), (85, false), (84, true)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c669, c355] c1618 (by decide) p (sat_cons (step669 p h) (sat_cons (step355 p h) (sat_nil p)))
def c1619 : List Lit := [(87, true), (82, true), (97, true), (16, true), (85, false)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c669, c356] c1619 (by decide) p (sat_cons (step669 p h) (sat_cons (step356 p h) (sat_nil p)))
def c1620 : List Lit := [(16, true), (82, true), (97, true), (84, true), (85, false)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c669, c357] c1620 (by decide) p (sat_cons (step669 p h) (sat_cons (step357 p h) (sat_nil p)))
def c1621 : List Lit := [(87, true), (82, true), (16, true), (85, false), (84, true)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c669, c358] c1621 (by decide) p (sat_cons (step669 p h) (sat_cons (step358 p h) (sat_nil p)))
def c1622 : List Lit := [(92, true), (83, true), (87, true), (86, false), (51, true), (84, true), (106, true)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c670, c372] c1622 (by decide) p (sat_cons (step670 p h) (sat_cons (step372 p h) (sat_nil p)))
def c1623 : List Lit := [(87, true), (83, true), (86, false), (92, true), (17, true), (51, true), (84, true)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c670, c373] c1623 (by decide) p (sat_cons (step670 p h) (sat_cons (step373 p h) (sat_nil p)))
def c1624 : List Lit := [(89, false), (88, true), (92, true), (90, true), (101, true)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c671, c429] c1624 (by decide) p (sat_cons (step671 p h) (sat_cons (step429 p h) (sat_nil p)))
def c1625 : List Lit := [(90, true), (101, true), (89, false), (83, true), (92, true)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c671, c430] c1625 (by decide) p (sat_cons (step671 p h) (sat_cons (step430 p h) (sat_nil p)))
def c1626 : List Lit := [(89, false), (88, true), (92, true), (83, true), (101, true)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c671, c431] c1626 (by decide) p (sat_cons (step671 p h) (sat_cons (step431 p h) (sat_nil p)))
def c1627 : List Lit := [(101, true), (88, true), (89, false), (83, true), (90, true)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c671, c432] c1627 (by decide) p (sat_cons (step671 p h) (sat_cons (step432 p h) (sat_nil p)))
def c1628 : List Lit := [(90, true), (88, true), (89, false), (92, true), (83, true)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c671, c433] c1628 (by decide) p (sat_cons (step671 p h) (sat_cons (step433 p h) (sat_nil p)))
def c1629 : List Lit := [(92, true), (88, true), (91, false)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c672, c454] c1629 (by decide) p (sat_cons (step672 p h) (sat_cons (step454 p h) (sat_nil p)))
def c1630 : List Lit := [(92, true), (84, true), (91, false)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c672, c455] c1630 (by decide) p (sat_cons (step672 p h) (sat_cons (step455 p h) (sat_nil p)))
def c1631 : List Lit := [(88, true), (84, true), (91, false)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c672, c456] c1631 (by decide) p (sat_cons (step672 p h) (sat_cons (step456 p h) (sat_nil p)))
def c1632 : List Lit := [(61, true), (116, true), (97, true), (96, false)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c673, c514] c1632 (by decide) p (sat_cons (step673 p h) (sat_cons (step514 p h) (sat_nil p)))
def c1633 : List Lit := [(61, true), (116, true), (96, false), (84, true)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c673, c515] c1633 (by decide) p (sat_cons (step673 p h) (sat_cons (step515 p h) (sat_nil p)))
def c1634 : List Lit := [(61, true), (84, true), (96, false), (97, true)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c673, c516] c1634 (by decide) p (sat_cons (step673 p h) (sat_cons (step516 p h) (sat_nil p)))
def c1635 : List Lit := [(103, true), (97, true), (98, false), (95, true)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c674, c527] c1635 (by decide) p (sat_cons (step674 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1636 : List Lit := [(87, true), (103, true), (98, false), (97, true)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c674, c528] c1636 (by decide) p (sat_cons (step674 p h) (sat_cons (step528 p h) (sat_nil p)))
def c1637 : List Lit := [(87, true), (103, true), (98, false), (95, true)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c674, c529] c1637 (by decide) p (sat_cons (step674 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1638 : List Lit := [(87, true), (97, true), (95, true), (98, false)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c674, c530] c1638 (by decide) p (sat_cons (step674 p h) (sat_cons (step530 p h) (sat_nil p)))
def c1639 : List Lit := [(100, true), (101, true), (99, false), (88, true)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c675, c533] c1639 (by decide) p (sat_cons (step675 p h) (sat_cons (step533 p h) (sat_nil p)))
def c1640 : List Lit := [(101, true), (27, true), (100, true), (99, false)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c675, c534] c1640 (by decide) p (sat_cons (step675 p h) (sat_cons (step534 p h) (sat_nil p)))
def c1641 : List Lit := [(27, true), (88, true), (99, false), (101, true)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c675, c535] c1641 (by decide) p (sat_cons (step675 p h) (sat_cons (step535 p h) (sat_nil p)))
def c1642 : List Lit := [(27, true), (88, true), (99, false), (100, true)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c675, c536] c1642 (by decide) p (sat_cons (step675 p h) (sat_cons (step536 p h) (sat_nil p)))
def c1643 : List Lit := [(101, true), (103, true), (102, false), (100, true), (95, true)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c676, c551] c1643 (by decide) p (sat_cons (step676 p h) (sat_cons (step551 p h) (sat_nil p)))
def c1644 : List Lit := [(101, true), (100, true), (103, true), (102, false), (90, true)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c676, c552] c1644 (by decide) p (sat_cons (step676 p h) (sat_cons (step552 p h) (sat_nil p)))
def c1645 : List Lit := [(101, true), (90, true), (102, false), (95, true), (103, true)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c676, c553] c1645 (by decide) p (sat_cons (step676 p h) (sat_cons (step553 p h) (sat_nil p)))
def c1646 : List Lit := [(100, true), (103, true), (95, true), (102, false), (90, true)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c676, c554] c1646 (by decide) p (sat_cons (step676 p h) (sat_cons (step554 p h) (sat_nil p)))
def c1647 : List Lit := [(101, true), (90, true), (95, true), (102, false), (100, true)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c676, c555] c1647 (by decide) p (sat_cons (step676 p h) (sat_cons (step555 p h) (sat_nil p)))
def c1648 : List Lit := [(82, true), (113, true), (105, false), (109, true)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c677, c569] c1648 (by decide) p (sat_cons (step677 p h) (sat_cons (step569 p h) (sat_nil p)))
def c1649 : List Lit := [(113, true), (82, true), (104, true), (105, false)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c677, c570] c1649 (by decide) p (sat_cons (step677 p h) (sat_cons (step570 p h) (sat_nil p)))
def c1650 : List Lit := [(82, true), (109, true), (104, true), (105, false)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c677, c571] c1650 (by decide) p (sat_cons (step677 p h) (sat_cons (step571 p h) (sat_nil p)))
def c1651 : List Lit := [(106, true), (107, false), (112, true)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c678, c577] c1651 (by decide) p (sat_cons (step678 p h) (sat_cons (step577 p h) (sat_nil p)))
def c1652 : List Lit := [(87, true), (107, false), (112, true)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c678, c578] c1652 (by decide) p (sat_cons (step678 p h) (sat_cons (step578 p h) (sat_nil p)))
def c1653 : List Lit := [(106, true), (87, true), (107, false)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c678, c579] c1653 (by decide) p (sat_cons (step678 p h) (sat_cons (step579 p h) (sat_nil p)))
def c1654 : List Lit := [(104, true), (109, true), (108, false)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c679, c580] c1654 (by decide) p (sat_cons (step679 p h) (sat_cons (step580 p h) (sat_nil p)))
def c1655 : List Lit := [(109, true), (88, true), (108, false)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c679, c581] c1655 (by decide) p (sat_cons (step679 p h) (sat_cons (step581 p h) (sat_nil p)))
def c1656 : List Lit := [(104, true), (88, true), (108, false)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c679, c582] c1656 (by decide) p (sat_cons (step679 p h) (sat_cons (step582 p h) (sat_nil p)))
def c1657 : List Lit := [(71, true), (90, true), (110, false), (112, true), (109, true)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c680, c588] c1657 (by decide) p (sat_cons (step680 p h) (sat_cons (step588 p h) (sat_nil p)))
end B112E026
