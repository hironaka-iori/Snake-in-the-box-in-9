import B112E207Part0003
namespace B112E207
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1603 : List Lit := [(61, false), (62, true), (58, true), (49, true)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true :=
  Snake9.LocalRup.prove_clause [c651, c413] c1603 (by decide) p (sat_cons (step651 p h) (sat_cons (step413 p h) (sat_nil p)))
def c1604 : List Lit := [(61, false), (49, true), (58, true), (60, true)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true :=
  Snake9.LocalRup.prove_clause [c651, c414] c1604 (by decide) p (sat_cons (step651 p h) (sat_cons (step414 p h) (sat_nil p)))
def c1605 : List Lit := [(64, false), (66, true), (58, true)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true :=
  Snake9.LocalRup.prove_clause [c652, c425] c1605 (by decide) p (sat_cons (step652 p h) (sat_cons (step425 p h) (sat_nil p)))
def c1606 : List Lit := [(64, false), (63, true), (58, true)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true :=
  Snake9.LocalRup.prove_clause [c652, c426] c1606 (by decide) p (sat_cons (step652 p h) (sat_cons (step426 p h) (sat_nil p)))
def c1607 : List Lit := [(67, false), (66, true), (57, true)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true :=
  Snake9.LocalRup.prove_clause [c653, c443] c1607 (by decide) p (sat_cons (step653 p h) (sat_cons (step443 p h) (sat_nil p)))
def c1608 : List Lit := [(68, false), (69, true), (72, true)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true :=
  Snake9.LocalRup.prove_clause [c654, c445] c1608 (by decide) p (sat_cons (step654 p h) (sat_cons (step445 p h) (sat_nil p)))
def c1609 : List Lit := [(68, false), (72, true), (45, true)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true :=
  Snake9.LocalRup.prove_clause [c654, c446] c1609 (by decide) p (sat_cons (step654 p h) (sat_cons (step446 p h) (sat_nil p)))
def c1610 : List Lit := [(68, false), (69, true), (45, true)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true :=
  Snake9.LocalRup.prove_clause [c654, c447] c1610 (by decide) p (sat_cons (step654 p h) (sat_cons (step447 p h) (sat_nil p)))
def c1611 : List Lit := [(70, false), (80, true), (50, true)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true :=
  Snake9.LocalRup.prove_clause [c655, c452] c1611 (by decide) p (sat_cons (step655 p h) (sat_cons (step452 p h) (sat_nil p)))
def c1612 : List Lit := [(75, true), (73, false), (69, true), (74, true)]
theorem step1612 (p : Nat → Bool) (h : Constraints p) : clause p c1612 = true :=
  Snake9.LocalRup.prove_clause [c656, c467] c1612 (by decide) p (sat_cons (step656 p h) (sat_cons (step467 p h) (sat_nil p)))
def c1613 : List Lit := [(73, false), (69, true), (74, true), (72, true)]
theorem step1613 (p : Nat → Bool) (h : Constraints p) : clause p c1613 = true :=
  Snake9.LocalRup.prove_clause [c656, c469] c1613 (by decide) p (sat_cons (step656 p h) (sat_cons (step469 p h) (sat_nil p)))
def c1614 : List Lit := [(75, true), (76, false), (57, true), (74, true)]
theorem step1614 (p : Nat → Bool) (h : Constraints p) : clause p c1614 = true :=
  Snake9.LocalRup.prove_clause [c657, c482] c1614 (by decide) p (sat_cons (step657 p h) (sat_cons (step482 p h) (sat_nil p)))
def c1615 : List Lit := [(76, false), (71, true), (57, true), (74, true)]
theorem step1615 (p : Nat → Bool) (h : Constraints p) : clause p c1615 = true :=
  Snake9.LocalRup.prove_clause [c657, c483] c1615 (by decide) p (sat_cons (step657 p h) (sat_cons (step483 p h) (sat_nil p)))
def c1616 : List Lit := [(79, true), (77, false), (58, true)]
theorem step1616 (p : Nat → Bool) (h : Constraints p) : clause p c1616 = true :=
  Snake9.LocalRup.prove_clause [c658, c485] c1616 (by decide) p (sat_cons (step658 p h) (sat_cons (step485 p h) (sat_nil p)))
def c1617 : List Lit := [(83, false), (82, true)]
theorem step1617 (p : Nat → Bool) (h : Constraints p) : clause p c1617 = true :=
  Snake9.LocalRup.prove_clause [c659, c498] c1617 (by decide) p (sat_cons (step659 p h) (sat_cons (step498 p h) (sat_nil p)))
def c1618 : List Lit := [(83, false), (75, true)]
theorem step1618 (p : Nat → Bool) (h : Constraints p) : clause p c1618 = true :=
  Snake9.LocalRup.prove_clause [c659, c499] c1618 (by decide) p (sat_cons (step659 p h) (sat_cons (step499 p h) (sat_nil p)))
def c1619 : List Lit := [(80, true), (84, false), (82, true)]
theorem step1619 (p : Nat → Bool) (h : Constraints p) : clause p c1619 = true :=
  Snake9.LocalRup.prove_clause [c660, c501] c1619 (by decide) p (sat_cons (step660 p h) (sat_cons (step501 p h) (sat_nil p)))
def c1620 : List Lit := [(95, true), (86, true), (45, true), (90, true), (85, false)]
theorem step1620 (p : Nat → Bool) (h : Constraints p) : clause p c1620 = true :=
  Snake9.LocalRup.prove_clause [c661, c511] c1620 (by decide) p (sat_cons (step661 p h) (sat_cons (step511 p h) (sat_nil p)))
def c1621 : List Lit := [(95, true), (85, false), (45, true), (15, true), (90, true)]
theorem step1621 (p : Nat → Bool) (h : Constraints p) : clause p c1621 = true :=
  Snake9.LocalRup.prove_clause [c661, c512] c1621 (by decide) p (sat_cons (step661 p h) (sat_cons (step512 p h) (sat_nil p)))
def c1622 : List Lit := [(95, true), (86, true), (45, true), (85, false), (15, true)]
theorem step1622 (p : Nat → Bool) (h : Constraints p) : clause p c1622 = true :=
  Snake9.LocalRup.prove_clause [c661, c513] c1622 (by decide) p (sat_cons (step661 p h) (sat_cons (step513 p h) (sat_nil p)))
def c1623 : List Lit := [(86, true), (85, false), (15, true), (45, true), (90, true)]
theorem step1623 (p : Nat → Bool) (h : Constraints p) : clause p c1623 = true :=
  Snake9.LocalRup.prove_clause [c661, c514] c1623 (by decide) p (sat_cons (step661 p h) (sat_cons (step514 p h) (sat_nil p)))
def c1624 : List Lit := [(94, false), (93, true), (57, true), (92, true)]
theorem step1624 (p : Nat → Bool) (h : Constraints p) : clause p c1624 = true :=
  Snake9.LocalRup.prove_clause [c662, c563] c1624 (by decide) p (sat_cons (step662 p h) (sat_cons (step563 p h) (sat_nil p)))
def c1625 : List Lit := [(96, false), (98, true), (58, true), (95, true)]
theorem step1625 (p : Nat → Bool) (h : Constraints p) : clause p c1625 = true :=
  Snake9.LocalRup.prove_clause [c663, c573] c1625 (by decide) p (sat_cons (step663 p h) (sat_cons (step573 p h) (sat_nil p)))
def c1626 : List Lit := [(96, false), (98, true), (58, true), (86, true)]
theorem step1626 (p : Nat → Bool) (h : Constraints p) : clause p c1626 = true :=
  Snake9.LocalRup.prove_clause [c663, c574] c1626 (by decide) p (sat_cons (step663 p h) (sat_cons (step574 p h) (sat_nil p)))
def c1627 : List Lit := [(95, true), (96, false), (58, true), (86, true)]
theorem step1627 (p : Nat → Bool) (h : Constraints p) : clause p c1627 = true :=
  Snake9.LocalRup.prove_clause [c663, c575] c1627 (by decide) p (sat_cons (step663 p h) (sat_cons (step575 p h) (sat_nil p)))
def c1628 : List Lit := [(102, false), (93, true), (31, true)]
theorem step1628 (p : Nat → Bool) (h : Constraints p) : clause p c1628 = true :=
  Snake9.LocalRup.prove_clause [c664, c594] c1628 (by decide) p (sat_cons (step664 p h) (sat_cons (step594 p h) (sat_nil p)))
def c1629 : List Lit := [(103, false), (101, true), (100, true)]
theorem step1629 (p : Nat → Bool) (h : Constraints p) : clause p c1629 = true :=
  Snake9.LocalRup.prove_clause [c665, c596] c1629 (by decide) p (sat_cons (step665 p h) (sat_cons (step596 p h) (sat_nil p)))
def c1630 : List Lit := [(103, false), (99, true), (101, true)]
theorem step1630 (p : Nat → Bool) (h : Constraints p) : clause p c1630 = true :=
  Snake9.LocalRup.prove_clause [c665, c597] c1630 (by decide) p (sat_cons (step665 p h) (sat_cons (step597 p h) (sat_nil p)))
def c1631 : List Lit := [(103, false), (99, true), (100, true)]
theorem step1631 (p : Nat → Bool) (h : Constraints p) : clause p c1631 = true :=
  Snake9.LocalRup.prove_clause [c665, c598] c1631 (by decide) p (sat_cons (step665 p h) (sat_cons (step598 p h) (sat_nil p)))
def c1632 : List Lit := [(113, true), (106, false), (43, true)]
theorem step1632 (p : Nat → Bool) (h : Constraints p) : clause p c1632 = true :=
  Snake9.LocalRup.prove_clause [c666, c602] c1632 (by decide) p (sat_cons (step666 p h) (sat_cons (step602 p h) (sat_nil p)))
def c1633 : List Lit := [(106, false), (107, true), (43, true)]
theorem step1633 (p : Nat → Bool) (h : Constraints p) : clause p c1633 = true :=
  Snake9.LocalRup.prove_clause [c666, c603] c1633 (by decide) p (sat_cons (step666 p h) (sat_cons (step603 p h) (sat_nil p)))
def c1634 : List Lit := [(109, false), (108, true)]
theorem step1634 (p : Nat → Bool) (h : Constraints p) : clause p c1634 = true :=
  Snake9.LocalRup.prove_clause [c667, c608] c1634 (by decide) p (sat_cons (step667 p h) (sat_cons (step608 p h) (sat_nil p)))
def c1635 : List Lit := [(109, false), (107, true)]
theorem step1635 (p : Nat → Bool) (h : Constraints p) : clause p c1635 = true :=
  Snake9.LocalRup.prove_clause [c667, c609] c1635 (by decide) p (sat_cons (step667 p h) (sat_cons (step609 p h) (sat_nil p)))
def c1636 : List Lit := [(110, false), (112, true)]
theorem step1636 (p : Nat → Bool) (h : Constraints p) : clause p c1636 = true :=
  Snake9.LocalRup.prove_clause [c668, c610] c1636 (by decide) p (sat_cons (step668 p h) (sat_cons (step610 p h) (sat_nil p)))
def c1637 : List Lit := [(113, true), (114, true), (111, false)]
theorem step1637 (p : Nat → Bool) (h : Constraints p) : clause p c1637 = true :=
  Snake9.LocalRup.prove_clause [c669, c612] c1637 (by decide) p (sat_cons (step669 p h) (sat_cons (step612 p h) (sat_nil p)))
def c1638 : List Lit := [(116, false), (115, true)]
theorem step1638 (p : Nat → Bool) (h : Constraints p) : clause p c1638 = true :=
  Snake9.LocalRup.prove_clause [c670, c620] c1638 (by decide) p (sat_cons (step670 p h) (sat_cons (step620 p h) (sat_nil p)))
def c1639 : List Lit := [(116, false), (108, true)]
theorem step1639 (p : Nat → Bool) (h : Constraints p) : clause p c1639 = true :=
  Snake9.LocalRup.prove_clause [c670, c621] c1639 (by decide) p (sat_cons (step670 p h) (sat_cons (step621 p h) (sat_nil p)))
def c1640 : List Lit := [(117, false), (114, true), (115, true)]
theorem step1640 (p : Nat → Bool) (h : Constraints p) : clause p c1640 = true :=
  Snake9.LocalRup.prove_clause [c671, c623] c1640 (by decide) p (sat_cons (step671 p h) (sat_cons (step623 p h) (sat_nil p)))
def c1641 : List Lit := [(117, false), (113, true), (115, true)]
theorem step1641 (p : Nat → Bool) (h : Constraints p) : clause p c1641 = true :=
  Snake9.LocalRup.prove_clause [c671, c624] c1641 (by decide) p (sat_cons (step671 p h) (sat_cons (step624 p h) (sat_nil p)))
def c1642 : List Lit := [(121, false), (122, false)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c1396, c676] c1642 (by decide) p (sat_cons (step1396 p h) (sat_cons (step676 p h) (sat_nil p)))
def c1643 : List Lit := [(239, false), (241, false)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c1388, c680] c1643 (by decide) p (sat_cons (step1388 p h) (sat_cons (step680 p h) (sat_nil p)))
def c1644 : List Lit := [(237, false), (243, false)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c1378, c685] c1644 (by decide) p (sat_cons (step1378 p h) (sat_cons (step685 p h) (sat_nil p)))
def c1645 : List Lit := [(249, false), (255, false)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c1377, c693] c1645 (by decide) p (sat_cons (step1377 p h) (sat_cons (step693 p h) (sat_nil p)))
def c1646 : List Lit := [(245, false), (257, false)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c1364, c697] c1646 (by decide) p (sat_cons (step1364 p h) (sat_cons (step697 p h) (sat_nil p)))
def c1647 : List Lit := [(263, false), (269, false)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c1376, c704] c1647 (by decide) p (sat_cons (step1376 p h) (sat_cons (step704 p h) (sat_nil p)))
def c1648 : List Lit := [(273, false), (275, false)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c1387, c710] c1648 (by decide) p (sat_cons (step1387 p h) (sat_cons (step710 p h) (sat_nil p)))
def c1649 : List Lit := [(277, false), (283, false)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c1375, c715] c1649 (by decide) p (sat_cons (step1375 p h) (sat_cons (step715 p h) (sat_nil p)))
def c1650 : List Lit := [(271, false), (285, false)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c1363, c720] c1650 (by decide) p (sat_cons (step1363 p h) (sat_cons (step720 p h) (sat_nil p)))
def c1651 : List Lit := [(259, false), (287, false)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c1357, c725] c1651 (by decide) p (sat_cons (step1357 p h) (sat_cons (step725 p h) (sat_nil p)))
def c1652 : List Lit := [(293, false), (299, false)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c1374, c732] c1652 (by decide) p (sat_cons (step1374 p h) (sat_cons (step732 p h) (sat_nil p)))
def c1653 : List Lit := [(155, false), (156, false)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c1395, c735] c1653 (by decide) p (sat_cons (step1395 p h) (sat_cons (step735 p h) (sat_nil p)))
def c1654 : List Lit := [(301, false), (313, false)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c1362, c748] c1654 (by decide) p (sat_cons (step1362 p h) (sat_cons (step748 p h) (sat_nil p)))
def c1655 : List Lit := [(166, false), (167, false)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c1394, c754] c1655 (by decide) p (sat_cons (step1394 p h) (sat_cons (step754 p h) (sat_nil p)))
def c1656 : List Lit := [(333, false), (339, false)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c1371, c766] c1656 (by decide) p (sat_cons (step1371 p h) (sat_cons (step766 p h) (sat_nil p)))
def c1657 : List Lit := [(327, false), (341, false)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c1361, c770] c1657 (by decide) p (sat_cons (step1361 p h) (sat_cons (step770 p h) (sat_nil p)))
def c1658 : List Lit := [(315, false), (343, false)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c1356, c775] c1658 (by decide) p (sat_cons (step1356 p h) (sat_cons (step775 p h) (sat_nil p)))
def c1659 : List Lit := [(289, false), (345, false)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c1353, c780] c1659 (by decide) p (sat_cons (step1353 p h) (sat_cons (step780 p h) (sat_nil p)))
def c1660 : List Lit := [(179, false), (180, false)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c1393, c786] c1660 (by decide) p (sat_cons (step1393 p h) (sat_cons (step786 p h) (sat_nil p)))
def c1661 : List Lit := [(351, false), (357, false)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c1370, c792] c1661 (by decide) p (sat_cons (step1370 p h) (sat_cons (step792 p h) (sat_nil p)))
def c1662 : List Lit := [(188, false), (189, false)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c1392, c797] c1662 (by decide) p (sat_cons (step1392 p h) (sat_cons (step797 p h) (sat_nil p)))
def c1663 : List Lit := [(365, false), (367, false)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c1383, c801] c1663 (by decide) p (sat_cons (step1383 p h) (sat_cons (step801 p h) (sat_nil p)))
def c1664 : List Lit := [(359, false), (371, false)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c1360, c808] c1664 (by decide) p (sat_cons (step1360 p h) (sat_cons (step808 p h) (sat_nil p)))
def c1665 : List Lit := [(191, false), (192, false)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c1391, c812] c1665 (by decide) p (sat_cons (step1391 p h) (sat_cons (step812 p h) (sat_nil p)))
def c1666 : List Lit := [(387, false), (389, false)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c1381, c825] c1666 (by decide) p (sat_cons (step1381 p h) (sat_cons (step825 p h) (sat_nil p)))
end B112E207
