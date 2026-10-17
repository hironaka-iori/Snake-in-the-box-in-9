import B112E027Part0002
namespace B112E027
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1642 : List Lit := [(67, true), (75, true), (66, false), (55, true)]
theorem step1642 (p : Nat → Bool) (h : Constraints p) : clause p c1642 = true :=
  Snake9.LocalRup.prove_clause [c651, c305] c1642 (by decide) p (sat_cons (step651 p h) (sat_cons (step305 p h) (sat_nil p)))
def c1643 : List Lit := [(75, true), (66, false), (11, true), (55, true)]
theorem step1643 (p : Nat → Bool) (h : Constraints p) : clause p c1643 = true :=
  Snake9.LocalRup.prove_clause [c651, c306] c1643 (by decide) p (sat_cons (step651 p h) (sat_cons (step306 p h) (sat_nil p)))
def c1644 : List Lit := [(71, false), (70, true)]
theorem step1644 (p : Nat → Bool) (h : Constraints p) : clause p c1644 = true :=
  Snake9.LocalRup.prove_clause [c653, c319] c1644 (by decide) p (sat_cons (step653 p h) (sat_cons (step319 p h) (sat_nil p)))
def c1645 : List Lit := [(71, false), (67, true)]
theorem step1645 (p : Nat → Bool) (h : Constraints p) : clause p c1645 = true :=
  Snake9.LocalRup.prove_clause [c653, c320] c1645 (by decide) p (sat_cons (step653 p h) (sat_cons (step320 p h) (sat_nil p)))
def c1646 : List Lit := [(72, false), (74, true)]
theorem step1646 (p : Nat → Bool) (h : Constraints p) : clause p c1646 = true :=
  Snake9.LocalRup.prove_clause [c654, c321] c1646 (by decide) p (sat_cons (step654 p h) (sat_cons (step321 p h) (sat_nil p)))
def c1647 : List Lit := [(72, false), (64, true)]
theorem step1647 (p : Nat → Bool) (h : Constraints p) : clause p c1647 = true :=
  Snake9.LocalRup.prove_clause [c654, c322] c1647 (by decide) p (sat_cons (step654 p h) (sat_cons (step322 p h) (sat_nil p)))
def c1648 : List Lit := [(76, true), (75, true), (73, false)]
theorem step1648 (p : Nat → Bool) (h : Constraints p) : clause p c1648 = true :=
  Snake9.LocalRup.prove_clause [c655, c324] c1648 (by decide) p (sat_cons (step655 p h) (sat_cons (step324 p h) (sat_nil p)))
def c1649 : List Lit := [(73, false), (75, true), (74, true)]
theorem step1649 (p : Nat → Bool) (h : Constraints p) : clause p c1649 = true :=
  Snake9.LocalRup.prove_clause [c655, c325] c1649 (by decide) p (sat_cons (step655 p h) (sat_cons (step325 p h) (sat_nil p)))
def c1650 : List Lit := [(78, false), (77, true)]
theorem step1650 (p : Nat → Bool) (h : Constraints p) : clause p c1650 = true :=
  Snake9.LocalRup.prove_clause [c656, c335] c1650 (by decide) p (sat_cons (step656 p h) (sat_cons (step335 p h) (sat_nil p)))
def c1651 : List Lit := [(78, false), (70, true)]
theorem step1651 (p : Nat → Bool) (h : Constraints p) : clause p c1651 = true :=
  Snake9.LocalRup.prove_clause [c656, c336] c1651 (by decide) p (sat_cons (step656 p h) (sat_cons (step336 p h) (sat_nil p)))
def c1652 : List Lit := [(79, false), (77, true), (75, true)]
theorem step1652 (p : Nat → Bool) (h : Constraints p) : clause p c1652 = true :=
  Snake9.LocalRup.prove_clause [c657, c338] c1652 (by decide) p (sat_cons (step657 p h) (sat_cons (step338 p h) (sat_nil p)))
def c1653 : List Lit := [(76, true), (79, false), (75, true)]
theorem step1653 (p : Nat → Bool) (h : Constraints p) : clause p c1653 = true :=
  Snake9.LocalRup.prove_clause [c657, c339] c1653 (by decide) p (sat_cons (step657 p h) (sat_cons (step339 p h) (sat_nil p)))
def c1654 : List Lit := [(80, false), (92, true), (82, true), (81, true)]
theorem step1654 (p : Nat → Bool) (h : Constraints p) : clause p c1654 = true :=
  Snake9.LocalRup.prove_clause [c658, c342] c1654 (by decide) p (sat_cons (step658 p h) (sat_cons (step342 p h) (sat_nil p)))
def c1655 : List Lit := [(80, false), (15, true), (82, true), (92, true)]
theorem step1655 (p : Nat → Bool) (h : Constraints p) : clause p c1655 = true :=
  Snake9.LocalRup.prove_clause [c658, c343] c1655 (by decide) p (sat_cons (step658 p h) (sat_cons (step343 p h) (sat_nil p)))
def c1656 : List Lit := [(82, true), (52, true), (85, true), (83, false), (102, true), (95, true), (17, true)]
theorem step1656 (p : Nat → Bool) (h : Constraints p) : clause p c1656 = true :=
  Snake9.LocalRup.prove_clause [c659, c409] c1656 (by decide) p (sat_cons (step659 p h) (sat_cons (step409 p h) (sat_nil p)))
def c1657 : List Lit := [(17, true), (95, true), (102, true), (52, true), (81, true), (85, true), (83, false)]
theorem step1657 (p : Nat → Bool) (h : Constraints p) : clause p c1657 = true :=
  Snake9.LocalRup.prove_clause [c659, c410] c1657 (by decide) p (sat_cons (step659 p h) (sat_cons (step410 p h) (sat_nil p)))
def c1658 : List Lit := [(82, true), (17, true), (102, true), (81, true), (52, true), (85, true), (83, false)]
theorem step1658 (p : Nat → Bool) (h : Constraints p) : clause p c1658 = true :=
  Snake9.LocalRup.prove_clause [c659, c411] c1658 (by decide) p (sat_cons (step659 p h) (sat_cons (step411 p h) (sat_nil p)))
def c1659 : List Lit := [(82, true), (17, true), (95, true), (52, true), (81, true), (85, true), (83, false)]
theorem step1659 (p : Nat → Bool) (h : Constraints p) : clause p c1659 = true :=
  Snake9.LocalRup.prove_clause [c659, c412] c1659 (by decide) p (sat_cons (step659 p h) (sat_cons (step412 p h) (sat_nil p)))
def c1660 : List Lit := [(89, true), (54, true), (81, true), (84, false), (85, true)]
theorem step1660 (p : Nat → Bool) (h : Constraints p) : clause p c1660 = true :=
  Snake9.LocalRup.prove_clause [c660, c423] c1660 (by decide) p (sat_cons (step660 p h) (sat_cons (step423 p h) (sat_nil p)))
def c1661 : List Lit := [(87, false), (106, true), (56, true), (82, true), (97, true), (90, true)]
theorem step1661 (p : Nat → Bool) (h : Constraints p) : clause p c1661 = true :=
  Snake9.LocalRup.prove_clause [c662, c454] c1661 (by decide) p (sat_cons (step662 p h) (sat_cons (step454 p h) (sat_nil p)))
def c1662 : List Lit := [(91, false), (89, true), (90, true)]
theorem step1662 (p : Nat → Bool) (h : Constraints p) : clause p c1662 = true :=
  Snake9.LocalRup.prove_clause [c664, c498] c1662 (by decide) p (sat_cons (step664 p h) (sat_cons (step498 p h) (sat_nil p)))
def c1663 : List Lit := [(91, false), (85, true), (89, true)]
theorem step1663 (p : Nat → Bool) (h : Constraints p) : clause p c1663 = true :=
  Snake9.LocalRup.prove_clause [c664, c499] c1663 (by decide) p (sat_cons (step664 p h) (sat_cons (step499 p h) (sat_nil p)))
def c1664 : List Lit := [(93, false), (95, true), (92, true)]
theorem step1664 (p : Nat → Bool) (h : Constraints p) : clause p c1664 = true :=
  Snake9.LocalRup.prove_clause [c665, c507] c1664 (by decide) p (sat_cons (step665 p h) (sat_cons (step507 p h) (sat_nil p)))
def c1665 : List Lit := [(93, false), (92, true), (81, true)]
theorem step1665 (p : Nat → Bool) (h : Constraints p) : clause p c1665 = true :=
  Snake9.LocalRup.prove_clause [c665, c508] c1665 (by decide) p (sat_cons (step665 p h) (sat_cons (step508 p h) (sat_nil p)))
def c1666 : List Lit := [(99, false), (98, true)]
theorem step1666 (p : Nat → Bool) (h : Constraints p) : clause p c1666 = true :=
  Snake9.LocalRup.prove_clause [c667, c542] c1666 (by decide) p (sat_cons (step667 p h) (sat_cons (step542 p h) (sat_nil p)))
def c1667 : List Lit := [(99, false), (89, true)]
theorem step1667 (p : Nat → Bool) (h : Constraints p) : clause p c1667 = true :=
  Snake9.LocalRup.prove_clause [c667, c543] c1667 (by decide) p (sat_cons (step667 p h) (sat_cons (step543 p h) (sat_nil p)))
def c1668 : List Lit := [(100, false), (98, true), (90, true), (97, true)]
theorem step1668 (p : Nat → Bool) (h : Constraints p) : clause p c1668 = true :=
  Snake9.LocalRup.prove_clause [c668, c548] c1668 (by decide) p (sat_cons (step668 p h) (sat_cons (step548 p h) (sat_nil p)))
def c1669 : List Lit := [(100, false), (98, true), (90, true), (96, true)]
theorem step1669 (p : Nat → Bool) (h : Constraints p) : clause p c1669 = true :=
  Snake9.LocalRup.prove_clause [c668, c549] c1669 (by decide) p (sat_cons (step668 p h) (sat_cons (step549 p h) (sat_nil p)))
def c1670 : List Lit := [(97, true), (96, true), (90, true), (100, false)]
theorem step1670 (p : Nat → Bool) (h : Constraints p) : clause p c1670 = true :=
  Snake9.LocalRup.prove_clause [c668, c550] c1670 (by decide) p (sat_cons (step668 p h) (sat_cons (step550 p h) (sat_nil p)))
def c1671 : List Lit := [(101, false), (106, true), (102, true)]
theorem step1671 (p : Nat → Bool) (h : Constraints p) : clause p c1671 = true :=
  Snake9.LocalRup.prove_clause [c669, c552] c1671 (by decide) p (sat_cons (step669 p h) (sat_cons (step552 p h) (sat_nil p)))
def c1672 : List Lit := [(101, false), (106, true), (82, true)]
theorem step1672 (p : Nat → Bool) (h : Constraints p) : clause p c1672 = true :=
  Snake9.LocalRup.prove_clause [c669, c553] c1672 (by decide) p (sat_cons (step669 p h) (sat_cons (step553 p h) (sat_nil p)))
def c1673 : List Lit := [(101, false), (102, true), (82, true)]
theorem step1673 (p : Nat → Bool) (h : Constraints p) : clause p c1673 = true :=
  Snake9.LocalRup.prove_clause [c669, c554] c1673 (by decide) p (sat_cons (step669 p h) (sat_cons (step554 p h) (sat_nil p)))
def c1674 : List Lit := [(103, false), (111, true), (108, true)]
theorem step1674 (p : Nat → Bool) (h : Constraints p) : clause p c1674 = true :=
  Snake9.LocalRup.prove_clause [c670, c561] c1674 (by decide) p (sat_cons (step670 p h) (sat_cons (step561 p h) (sat_nil p)))
def c1675 : List Lit := [(103, false), (111, true), (104, true)]
theorem step1675 (p : Nat → Bool) (h : Constraints p) : clause p c1675 = true :=
  Snake9.LocalRup.prove_clause [c670, c562] c1675 (by decide) p (sat_cons (step670 p h) (sat_cons (step562 p h) (sat_nil p)))
def c1676 : List Lit := [(117, true), (105, true), (106, true), (107, false)]
theorem step1676 (p : Nat → Bool) (h : Constraints p) : clause p c1676 = true :=
  Snake9.LocalRup.prove_clause [c671, c580] c1676 (by decide) p (sat_cons (step671 p h) (sat_cons (step580 p h) (sat_nil p)))
def c1677 : List Lit := [(117, true), (105, true), (102, true), (107, false)]
theorem step1677 (p : Nat → Bool) (h : Constraints p) : clause p c1677 = true :=
  Snake9.LocalRup.prove_clause [c671, c581] c1677 (by decide) p (sat_cons (step671 p h) (sat_cons (step581 p h) (sat_nil p)))
def c1678 : List Lit := [(109, false), (108, true), (90, true)]
theorem step1678 (p : Nat → Bool) (h : Constraints p) : clause p c1678 = true :=
  Snake9.LocalRup.prove_clause [c672, c588] c1678 (by decide) p (sat_cons (step672 p h) (sat_cons (step588 p h) (sat_nil p)))
def c1679 : List Lit := [(109, false), (106, true), (90, true)]
theorem step1679 (p : Nat → Bool) (h : Constraints p) : clause p c1679 = true :=
  Snake9.LocalRup.prove_clause [c672, c589] c1679 (by decide) p (sat_cons (step672 p h) (sat_cons (step589 p h) (sat_nil p)))
def c1680 : List Lit := [(110, false), (115, true), (92, true)]
theorem step1680 (p : Nat → Bool) (h : Constraints p) : clause p c1680 = true :=
  Snake9.LocalRup.prove_clause [c673, c591] c1680 (by decide) p (sat_cons (step673 p h) (sat_cons (step591 p h) (sat_nil p)))
def c1681 : List Lit := [(110, false), (92, true), (111, true)]
theorem step1681 (p : Nat → Bool) (h : Constraints p) : clause p c1681 = true :=
  Snake9.LocalRup.prove_clause [c673, c592] c1681 (by decide) p (sat_cons (step673 p h) (sat_cons (step592 p h) (sat_nil p)))
def c1682 : List Lit := [(116, false), (117, true), (105, true)]
theorem step1682 (p : Nat → Bool) (h : Constraints p) : clause p c1682 = true :=
  Snake9.LocalRup.prove_clause [c676, c611] c1682 (by decide) p (sat_cons (step676 p h) (sat_cons (step611 p h) (sat_nil p)))
def c1683 : List Lit := [(116, false), (115, true), (105, true)]
theorem step1683 (p : Nat → Bool) (h : Constraints p) : clause p c1683 = true :=
  Snake9.LocalRup.prove_clause [c676, c612] c1683 (by decide) p (sat_cons (step676 p h) (sat_cons (step612 p h) (sat_nil p)))
def c1684 : List Lit := [(118, false), (117, true)]
theorem step1684 (p : Nat → Bool) (h : Constraints p) : clause p c1684 = true :=
  Snake9.LocalRup.prove_clause [c677, c617] c1684 (by decide) p (sat_cons (step677 p h) (sat_cons (step617 p h) (sat_nil p)))
def c1685 : List Lit := [(120, false), (121, false)]
theorem step1685 (p : Nat → Bool) (h : Constraints p) : clause p c1685 = true :=
  Snake9.LocalRup.prove_clause [c1497, c680] c1685 (by decide) p (sat_cons (step1497 p h) (sat_cons (step680 p h) (sat_nil p)))
def c1686 : List Lit := [(239, false), (245, false)]
theorem step1686 (p : Nat → Bool) (h : Constraints p) : clause p c1686 = true :=
  Snake9.LocalRup.prove_clause [c1479, c687] c1686 (by decide) p (sat_cons (step1479 p h) (sat_cons (step687 p h) (sat_nil p)))
def c1687 : List Lit := [(251, false), (257, false)]
theorem step1687 (p : Nat → Bool) (h : Constraints p) : clause p c1687 = true :=
  Snake9.LocalRup.prove_clause [c1478, c696] c1687 (by decide) p (sat_cons (step1478 p h) (sat_cons (step696 p h) (sat_nil p)))
def c1688 : List Lit := [(247, false), (259, false)]
theorem step1688 (p : Nat → Bool) (h : Constraints p) : clause p c1688 = true :=
  Snake9.LocalRup.prove_clause [c1464, c700] c1688 (by decide) p (sat_cons (step1464 p h) (sat_cons (step700 p h) (sat_nil p)))
def c1689 : List Lit := [(265, false), (271, false)]
theorem step1689 (p : Nat → Bool) (h : Constraints p) : clause p c1689 = true :=
  Snake9.LocalRup.prove_clause [c1477, c709] c1689 (by decide) p (sat_cons (step1477 p h) (sat_cons (step709 p h) (sat_nil p)))
def c1690 : List Lit := [(275, false), (277, false)]
theorem step1690 (p : Nat → Bool) (h : Constraints p) : clause p c1690 = true :=
  Snake9.LocalRup.prove_clause [c1491, c715] c1690 (by decide) p (sat_cons (step1491 p h) (sat_cons (step715 p h) (sat_nil p)))
def c1691 : List Lit := [(279, false), (285, false)]
theorem step1691 (p : Nat → Bool) (h : Constraints p) : clause p c1691 = true :=
  Snake9.LocalRup.prove_clause [c1476, c722] c1691 (by decide) p (sat_cons (step1476 p h) (sat_cons (step722 p h) (sat_nil p)))
def c1692 : List Lit := [(273, false), (287, false)]
theorem step1692 (p : Nat → Bool) (h : Constraints p) : clause p c1692 = true :=
  Snake9.LocalRup.prove_clause [c1463, c727] c1692 (by decide) p (sat_cons (step1463 p h) (sat_cons (step727 p h) (sat_nil p)))
def c1693 : List Lit := [(261, false), (289, false)]
theorem step1693 (p : Nat → Bool) (h : Constraints p) : clause p c1693 = true :=
  Snake9.LocalRup.prove_clause [c1456, c732] c1693 (by decide) p (sat_cons (step1456 p h) (sat_cons (step732 p h) (sat_nil p)))
def c1694 : List Lit := [(307, false), (313, false)]
theorem step1694 (p : Nat → Bool) (h : Constraints p) : clause p c1694 = true :=
  Snake9.LocalRup.prove_clause [c1475, c747] c1694 (by decide) p (sat_cons (step1475 p h) (sat_cons (step747 p h) (sat_nil p)))
def c1695 : List Lit := [(303, false), (315, false)]
theorem step1695 (p : Nat → Bool) (h : Constraints p) : clause p c1695 = true :=
  Snake9.LocalRup.prove_clause [c1462, c751] c1695 (by decide) p (sat_cons (step1462 p h) (sat_cons (step751 p h) (sat_nil p)))
def c1696 : List Lit := [(163, false), (164, false)]
theorem step1696 (p : Nat → Bool) (h : Constraints p) : clause p c1696 = true :=
  Snake9.LocalRup.prove_clause [c1496, c754] c1696 (by decide) p (sat_cons (step1496 p h) (sat_cons (step754 p h) (sat_nil p)))
def c1697 : List Lit := [(165, false), (166, false)]
theorem step1697 (p : Nat → Bool) (h : Constraints p) : clause p c1697 = true :=
  Snake9.LocalRup.prove_clause [c1495, c759] c1697 (by decide) p (sat_cons (step1495 p h) (sat_cons (step759 p h) (sat_nil p)))
def c1698 : List Lit := [(321, false), (327, false)]
theorem step1698 (p : Nat → Bool) (h : Constraints p) : clause p c1698 = true :=
  Snake9.LocalRup.prove_clause [c1474, c765] c1698 (by decide) p (sat_cons (step1474 p h) (sat_cons (step765 p h) (sat_nil p)))
def c1699 : List Lit := [(331, false), (333, false)]
theorem step1699 (p : Nat → Bool) (h : Constraints p) : clause p c1699 = true :=
  Snake9.LocalRup.prove_clause [c1488, c771] c1699 (by decide) p (sat_cons (step1488 p h) (sat_cons (step771 p h) (sat_nil p)))
def c1700 : List Lit := [(337, false), (339, false)]
theorem step1700 (p : Nat → Bool) (h : Constraints p) : clause p c1700 = true :=
  Snake9.LocalRup.prove_clause [c1487, c777] c1700 (by decide) p (sat_cons (step1487 p h) (sat_cons (step777 p h) (sat_nil p)))
def c1701 : List Lit := [(335, false), (341, false)]
theorem step1701 (p : Nat → Bool) (h : Constraints p) : clause p c1701 = true :=
  Snake9.LocalRup.prove_clause [c1473, c781] c1701 (by decide) p (sat_cons (step1473 p h) (sat_cons (step781 p h) (sat_nil p)))
def c1702 : List Lit := [(329, false), (343, false)]
theorem step1702 (p : Nat → Bool) (h : Constraints p) : clause p c1702 = true :=
  Snake9.LocalRup.prove_clause [c1461, c786] c1702 (by decide) p (sat_cons (step1461 p h) (sat_cons (step786 p h) (sat_nil p)))
def c1703 : List Lit := [(317, false), (345, false)]
theorem step1703 (p : Nat → Bool) (h : Constraints p) : clause p c1703 = true :=
  Snake9.LocalRup.prove_clause [c1455, c791] c1703 (by decide) p (sat_cons (step1455 p h) (sat_cons (step791 p h) (sat_nil p)))
def c1704 : List Lit := [(291, false), (347, false)]
theorem step1704 (p : Nat → Bool) (h : Constraints p) : clause p c1704 = true :=
  Snake9.LocalRup.prove_clause [c1452, c796] c1704 (by decide) p (sat_cons (step1452 p h) (sat_cons (step796 p h) (sat_nil p)))
def c1705 : List Lit := [(185, false), (363, false)]
theorem step1705 (p : Nat → Bool) (h : Constraints p) : clause p c1705 = true :=
  Snake9.LocalRup.prove_clause [c1485, c810] c1705 (by decide) p (sat_cons (step1485 p h) (sat_cons (step810 p h) (sat_nil p)))
end B112E027
