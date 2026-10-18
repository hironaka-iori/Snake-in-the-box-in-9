import B112E110Part0004
namespace B112E110
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1621 : List Lit := [(68, false), (75, true)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c602, c229] c1621 (by decide) p (sat_cons (step602 p h) (sat_cons (step229 p h) (sat_nil p)))
def c1622 : List Lit := [(68, false), (70, true)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c602, c230] c1622 (by decide) p (sat_cons (step602 p h) (sat_cons (step230 p h) (sat_nil p)))
def c1623 : List Lit := [(70, true), (69, false), (67, true)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c603, c231] c1623 (by decide) p (sat_cons (step603 p h) (sat_cons (step231 p h) (sat_nil p)))
def c1624 : List Lit := [(62, true), (70, true), (69, false)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c603, c232] c1624 (by decide) p (sat_cons (step603 p h) (sat_cons (step232 p h) (sat_nil p)))
def c1625 : List Lit := [(62, true), (69, false), (67, true)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c603, c233] c1625 (by decide) p (sat_cons (step603 p h) (sat_cons (step233 p h) (sat_nil p)))
def c1626 : List Lit := [(75, true), (74, true), (72, false)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c604, c241] c1626 (by decide) p (sat_cons (step604 p h) (sat_cons (step241 p h) (sat_nil p)))
def c1627 : List Lit := [(75, true), (72, false), (71, true)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c604, c242] c1627 (by decide) p (sat_cons (step604 p h) (sat_cons (step242 p h) (sat_nil p)))
def c1628 : List Lit := [(74, true), (72, false), (71, true)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c604, c243] c1628 (by decide) p (sat_cons (step604 p h) (sat_cons (step243 p h) (sat_nil p)))
def c1629 : List Lit := [(80, true), (97, true), (77, false)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c605, c272] c1629 (by decide) p (sat_cons (step605 p h) (sat_cons (step272 p h) (sat_nil p)))
def c1630 : List Lit := [(76, true), (97, true), (77, false)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c605, c273] c1630 (by decide) p (sat_cons (step605 p h) (sat_cons (step273 p h) (sat_nil p)))
def c1631 : List Lit := [(80, true), (76, true), (77, false)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c605, c274] c1631 (by decide) p (sat_cons (step605 p h) (sat_cons (step274 p h) (sat_nil p)))
def c1632 : List Lit := [(87, true), (81, true), (76, true), (83, true), (78, false), (98, true)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c606, c278] c1632 (by decide) p (sat_cons (step606 p h) (sat_cons (step278 p h) (sat_nil p)))
def c1633 : List Lit := [(87, true), (98, true), (76, true), (78, false), (83, true), (18, true)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c606, c279] c1633 (by decide) p (sat_cons (step606 p h) (sat_cons (step279 p h) (sat_nil p)))
def c1634 : List Lit := [(81, true), (85, true), (79, false), (76, true)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c607, c283] c1634 (by decide) p (sat_cons (step607 p h) (sat_cons (step283 p h) (sat_nil p)))
def c1635 : List Lit := [(80, true), (85, true), (79, false), (76, true)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c607, c284] c1635 (by decide) p (sat_cons (step607 p h) (sat_cons (step284 p h) (sat_nil p)))
def c1636 : List Lit := [(82, false), (102, true), (76, true), (83, true), (91, true)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c608, c301] c1636 (by decide) p (sat_cons (step608 p h) (sat_cons (step301 p h) (sat_nil p)))
def c1637 : List Lit := [(76, true), (85, true), (82, false), (102, true), (83, true)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c608, c302] c1637 (by decide) p (sat_cons (step608 p h) (sat_cons (step302 p h) (sat_nil p)))
def c1638 : List Lit := [(85, true), (76, true), (83, true), (82, false), (91, true)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c608, c303] c1638 (by decide) p (sat_cons (step608 p h) (sat_cons (step303 p h) (sat_nil p)))
def c1639 : List Lit := [(93, true), (103, true), (84, false), (83, true)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c609, c322] c1639 (by decide) p (sat_cons (step609 p h) (sat_cons (step322 p h) (sat_nil p)))
def c1640 : List Lit := [(93, true), (103, true), (23, true), (84, false)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c609, c323] c1640 (by decide) p (sat_cons (step609 p h) (sat_cons (step323 p h) (sat_nil p)))
def c1641 : List Lit := [(83, true), (103, true), (23, true), (84, false)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c609, c324] c1641 (by decide) p (sat_cons (step609 p h) (sat_cons (step324 p h) (sat_nil p)))
def c1642 : List Lit := [(93, true), (83, true), (23, true), (84, false)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c609, c325] c1642 (by decide) p (sat_cons (step609 p h) (sat_cons (step325 p h) (sat_nil p)))
def c1643 : List Lit := [(85, true), (106, true), (86, false), (83, true)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c610, c330] c1643 (by decide) p (sat_cons (step610 p h) (sat_cons (step330 p h) (sat_nil p)))
def c1644 : List Lit := [(81, true), (106, true), (86, false), (83, true)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c610, c332] c1644 (by decide) p (sat_cons (step610 p h) (sat_cons (step332 p h) (sat_nil p)))
def c1645 : List Lit := [(81, true), (85, true), (86, false), (83, true)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c610, c333] c1645 (by decide) p (sat_cons (step610 p h) (sat_cons (step333 p h) (sat_nil p)))
def c1646 : List Lit := [(90, true), (88, false), (94, true)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c611, c337] c1646 (by decide) p (sat_cons (step611 p h) (sat_cons (step337 p h) (sat_nil p)))
def c1647 : List Lit := [(94, true), (80, true), (88, false)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c611, c338] c1647 (by decide) p (sat_cons (step611 p h) (sat_cons (step338 p h) (sat_nil p)))
def c1648 : List Lit := [(87, true), (90, true), (89, false)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c612, c340] c1648 (by decide) p (sat_cons (step612 p h) (sat_cons (step340 p h) (sat_nil p)))
def c1649 : List Lit := [(90, true), (81, true), (89, false)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c612, c341] c1649 (by decide) p (sat_cons (step612 p h) (sat_cons (step341 p h) (sat_nil p)))
def c1650 : List Lit := [(87, true), (81, true), (89, false)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c612, c342] c1650 (by decide) p (sat_cons (step612 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1651 : List Lit := [(94, true), (92, false), (93, true)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c613, c350] c1651 (by decide) p (sat_cons (step613 p h) (sat_cons (step350 p h) (sat_nil p)))
def c1652 : List Lit := [(94, true), (92, false), (91, true)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c613, c351] c1652 (by decide) p (sat_cons (step613 p h) (sat_cons (step351 p h) (sat_nil p)))
def c1653 : List Lit := [(93, true), (92, false), (91, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c613, c352] c1653 (by decide) p (sat_cons (step613 p h) (sat_cons (step352 p h) (sat_nil p)))
def c1654 : List Lit := [(97, true), (101, true), (99, false), (103, true), (111, true)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c614, c420] c1654 (by decide) p (sat_cons (step614 p h) (sat_cons (step420 p h) (sat_nil p)))
def c1655 : List Lit := [(97, true), (98, true), (99, false), (103, true), (111, true)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c614, c421] c1655 (by decide) p (sat_cons (step614 p h) (sat_cons (step421 p h) (sat_nil p)))
def c1656 : List Lit := [(101, true), (97, true), (99, false), (98, true), (111, true)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c614, c422] c1656 (by decide) p (sat_cons (step614 p h) (sat_cons (step422 p h) (sat_nil p)))
def c1657 : List Lit := [(98, true), (103, true), (99, false), (97, true), (101, true)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c614, c423] c1657 (by decide) p (sat_cons (step614 p h) (sat_cons (step423 p h) (sat_nil p)))
def c1658 : List Lit := [(101, true), (97, true), (100, false), (105, true)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c615, c426] c1658 (by decide) p (sat_cons (step615 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1659 : List Lit := [(101, true), (80, true), (100, false), (105, true)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c615, c427] c1659 (by decide) p (sat_cons (step615 p h) (sat_cons (step427 p h) (sat_nil p)))
def c1660 : List Lit := [(80, true), (101, true), (100, false), (97, true)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c615, c428] c1660 (by decide) p (sat_cons (step615 p h) (sat_cons (step428 p h) (sat_nil p)))
def c1661 : List Lit := [(105, true), (106, true), (107, false), (103, true), (118, true)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c616, c500] c1661 (by decide) p (sat_cons (step616 p h) (sat_cons (step500 p h) (sat_nil p)))
def c1662 : List Lit := [(101, true), (106, true), (118, true), (105, true), (107, false)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c616, c501] c1662 (by decide) p (sat_cons (step616 p h) (sat_cons (step501 p h) (sat_nil p)))
def c1663 : List Lit := [(103, true), (101, true), (107, false), (118, true), (106, true)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c616, c502] c1663 (by decide) p (sat_cons (step616 p h) (sat_cons (step502 p h) (sat_nil p)))
def c1664 : List Lit := [(105, true), (101, true), (107, false), (103, true), (118, true)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c616, c503] c1664 (by decide) p (sat_cons (step616 p h) (sat_cons (step503 p h) (sat_nil p)))
def c1665 : List Lit := [(105, true), (103, true), (101, true), (106, true), (107, false)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c616, c504] c1665 (by decide) p (sat_cons (step616 p h) (sat_cons (step504 p h) (sat_nil p)))
def c1666 : List Lit := [(108, true), (111, true), (109, false)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c617, c515] c1666 (by decide) p (sat_cons (step617 p h) (sat_cons (step515 p h) (sat_nil p)))
def c1667 : List Lit := [(97, true), (111, true), (109, false)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c617, c516] c1667 (by decide) p (sat_cons (step617 p h) (sat_cons (step516 p h) (sat_nil p)))
def c1668 : List Lit := [(108, true), (97, true), (109, false)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c617, c517] c1668 (by decide) p (sat_cons (step617 p h) (sat_cons (step517 p h) (sat_nil p)))
def c1669 : List Lit := [(108, true), (116, true), (112, false)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c618, c523] c1669 (by decide) p (sat_cons (step618 p h) (sat_cons (step523 p h) (sat_nil p)))
def c1670 : List Lit := [(116, true), (112, false), (44, true)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c618, c524] c1670 (by decide) p (sat_cons (step618 p h) (sat_cons (step524 p h) (sat_nil p)))
def c1671 : List Lit := [(108, true), (112, false), (44, true)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c618, c525] c1671 (by decide) p (sat_cons (step618 p h) (sat_cons (step525 p h) (sat_nil p)))
def c1672 : List Lit := [(113, false), (108, true), (116, true), (71, true), (102, true), (114, true)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c619, c527] c1672 (by decide) p (sat_cons (step619 p h) (sat_cons (step527 p h) (sat_nil p)))
def c1673 : List Lit := [(113, false), (108, true), (71, true), (91, true), (114, true), (116, true)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c619, c528] c1673 (by decide) p (sat_cons (step619 p h) (sat_cons (step528 p h) (sat_nil p)))
def c1674 : List Lit := [(113, false), (108, true), (71, true), (102, true), (91, true), (114, true)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c619, c529] c1674 (by decide) p (sat_cons (step619 p h) (sat_cons (step529 p h) (sat_nil p)))
def c1675 : List Lit := [(116, true), (117, false), (118, true), (114, true)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c620, c560] c1675 (by decide) p (sat_cons (step620 p h) (sat_cons (step560 p h) (sat_nil p)))
def c1676 : List Lit := [(116, true), (106, true), (117, false), (118, true)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c620, c561] c1676 (by decide) p (sat_cons (step620 p h) (sat_cons (step561 p h) (sat_nil p)))
def c1677 : List Lit := [(117, false), (106, true), (114, true), (118, true)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c620, c562] c1677 (by decide) p (sat_cons (step620 p h) (sat_cons (step562 p h) (sat_nil p)))
def c1678 : List Lit := [(116, true), (106, true), (117, false), (114, true)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c620, c563] c1678 (by decide) p (sat_cons (step620 p h) (sat_cons (step563 p h) (sat_nil p)))
def c1679 : List Lit := [(119, false), (237, false)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c1315, c624] c1679 (by decide) p (sat_cons (step1315 p h) (sat_cons (step624 p h) (sat_nil p)))
def c1680 : List Lit := [(251, false), (257, false)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c1313, c634] c1680 (by decide) p (sat_cons (step1313 p h) (sat_cons (step634 p h) (sat_nil p)))
def c1681 : List Lit := [(247, false), (259, false)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c1311, c638] c1681 (by decide) p (sat_cons (step1311 p h) (sat_cons (step638 p h) (sat_nil p)))
def c1682 : List Lit := [(265, false), (271, false)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c1312, c647] c1682 (by decide) p (sat_cons (step1312 p h) (sat_cons (step647 p h) (sat_nil p)))
def c1683 : List Lit := [(273, false), (287, false)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c1310, c660] c1683 (by decide) p (sat_cons (step1310 p h) (sat_cons (step660 p h) (sat_nil p)))
def c1684 : List Lit := [(261, false), (289, false)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c1308, c665] c1684 (by decide) p (sat_cons (step1308 p h) (sat_cons (step665 p h) (sat_nil p)))
end B112E110
