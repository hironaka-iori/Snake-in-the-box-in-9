import B112E089Part0227
namespace B112E089
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c16604 : List Lit := [(1583, false), (1601, false), (1553, false), (1759, false), (1666, false), (1750, false)]
theorem step16604 (p : Nat → Bool) (h : Constraints p) : clause p c16604 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9314] c16604 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9314 p h) (sat_nil p)))
def c16605 : List Lit := [(1751, false), (1761, false), (1784, true), (1666, false), (439, true)]
theorem step16605 (p : Nat → Bool) (h : Constraints p) : clause p c16605 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9705] c16605 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9705 p h) (sat_nil p)))
def c16606 : List Lit := [(1783, true), (1761, false), (1665, false), (439, true), (1751, false)]
theorem step16606 (p : Nat → Bool) (h : Constraints p) : clause p c16606 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9936] c16606 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9936 p h) (sat_nil p)))
def c16607 : List Lit := [(1667, false), (1750, false), (1784, true), (103, true)]
theorem step16607 (p : Nat → Bool) (h : Constraints p) : clause p c16607 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9483] c16607 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9483 p h) (sat_nil p)))
def c16608 : List Lit := [(1668, false), (1702, true), (1784, true), (1750, false)]
theorem step16608 (p : Nat → Bool) (h : Constraints p) : clause p c16608 = true :=
  Snake9.LocalRup.prove_clause [c15724, c10991] c16608 (by decide) p (sat_cons (step15724 p h) (sat_cons (step10991 p h) (sat_nil p)))
def c16609 : List Lit := [(1667, false), (439, true), (1784, true), (1760, false), (1750, false)]
theorem step16609 (p : Nat → Bool) (h : Constraints p) : clause p c16609 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9796] c16609 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9796 p h) (sat_nil p)))
def c16610 : List Lit := [(1667, false), (1701, true), (1784, true), (439, true), (1750, false)]
theorem step16610 (p : Nat → Bool) (h : Constraints p) : clause p c16610 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9794] c16610 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9794 p h) (sat_nil p)))
def c16611 : List Lit := [(1783, true), (1750, false), (1759, false), (1667, false)]
theorem step16611 (p : Nat → Bool) (h : Constraints p) : clause p c16611 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9001] c16611 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9001 p h) (sat_nil p)))
def c16612 : List Lit := [(1783, true), (1750, false), (103, true), (1666, false)]
theorem step16612 (p : Nat → Bool) (h : Constraints p) : clause p c16612 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9505] c16612 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9505 p h) (sat_nil p)))
def c16613 : List Lit := [(1617, false), (1783, true), (1666, false), (103, true), (1750, false)]
theorem step16613 (p : Nat → Bool) (h : Constraints p) : clause p c16613 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9234] c16613 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9234 p h) (sat_nil p)))
def c16614 : List Lit := [(1783, true), (1750, false), (439, true), (1666, false), (1760, false)]
theorem step16614 (p : Nat → Bool) (h : Constraints p) : clause p c16614 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9810] c16614 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9810 p h) (sat_nil p)))
def c16615 : List Lit := [(1667, false), (439, true), (1616, false), (1701, true), (1750, false)]
theorem step16615 (p : Nat → Bool) (h : Constraints p) : clause p c16615 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9399] c16615 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9399 p h) (sat_nil p)))
def c16616 : List Lit := [(1782, true), (1750, false), (1666, false), (1759, false)]
theorem step16616 (p : Nat → Bool) (h : Constraints p) : clause p c16616 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9299] c16616 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9299 p h) (sat_nil p)))
def c16617 : List Lit := [(1782, true), (1750, false), (1665, false), (103, true)]
theorem step16617 (p : Nat → Bool) (h : Constraints p) : clause p c16617 = true :=
  Snake9.LocalRup.prove_clause [c15724, c10827] c16617 (by decide) p (sat_cons (step15724 p h) (sat_cons (step10827 p h) (sat_nil p)))
def c16618 : List Lit := [(1780, true), (1759, false), (1664, false), (1750, false)]
theorem step16618 (p : Nat → Bool) (h : Constraints p) : clause p c16618 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9884] c16618 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9884 p h) (sat_nil p)))
def c16619 : List Lit := [(1762, false), (1666, false), (1616, false)]
theorem step16619 (p : Nat → Bool) (h : Constraints p) : clause p c16619 = true :=
  Snake9.LocalRup.prove_clause [c15724, c8658] c16619 (by decide) p (sat_cons (step15724 p h) (sat_cons (step8658 p h) (sat_nil p)))
def c16620 : List Lit := [(1783, true), (1727, true), (103, true), (1750, false), (1666, false)]
theorem step16620 (p : Nat → Bool) (h : Constraints p) : clause p c16620 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9162] c16620 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9162 p h) (sat_nil p)))
def c16621 : List Lit := [(1781, true), (1750, false), (1759, false), (1665, false)]
theorem step16621 (p : Nat → Bool) (h : Constraints p) : clause p c16621 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9301] c16621 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9301 p h) (sat_nil p)))
def c16622 : List Lit := [(1752, false), (1667, false), (1786, true), (103, true)]
theorem step16622 (p : Nat → Bool) (h : Constraints p) : clause p c16622 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9487] c16622 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9487 p h) (sat_nil p)))
def c16623 : List Lit := [(1751, false), (1761, false), (439, true), (1785, true), (1667, false)]
theorem step16623 (p : Nat → Bool) (h : Constraints p) : clause p c16623 = true :=
  Snake9.LocalRup.prove_clause [c15724, c9442] c16623 (by decide) p (sat_cons (step15724 p h) (sat_cons (step9442 p h) (sat_nil p)))
def c16624 : List Lit := [(120, true), (1569, false), (1667, false), (1691, true), (1784, true), (1785, true), (1727, true), (1750, false), (395, false), (1605, false)]
theorem step16624 (p : Nat → Bool) (h : Constraints p) : clause p c16624 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13224] c16624 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13224 p h) (sat_nil p)))
def c16625 : List Lit := [(1760, true), (1651, true), (1783, true), (393, false), (1572, true), (74, true)]
theorem step16625 (p : Nat → Bool) (h : Constraints p) : clause p c16625 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13655] c16625 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13655 p h) (sat_nil p)))
def c16626 : List Lit := [(305, true), (1762, false), (1637, true), (1615, false), (1666, false), (27, true)]
theorem step16626 (p : Nat → Bool) (h : Constraints p) : clause p c16626 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13411] c16626 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13411 p h) (sat_nil p)))
def c16627 : List Lit := [(1763, false), (1667, false), (1614, false)]
theorem step16627 (p : Nat → Bool) (h : Constraints p) : clause p c16627 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12823] c16627 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12823 p h) (sat_nil p)))
def c16628 : List Lit := [(107, true), (1761, false), (1667, false), (455, true), (103, true), (1785, true)]
theorem step16628 (p : Nat → Bool) (h : Constraints p) : clause p c16628 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13463] c16628 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13463 p h) (sat_nil p)))
def c16629 : List Lit := [(1762, true), (1784, true), (103, true), (56, false), (62, true), (487, true), (1666, false), (74, false), (120, true), (1750, false)]
theorem step16629 (p : Nat → Bool) (h : Constraints p) : clause p c16629 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13221] c16629 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13221 p h) (sat_nil p)))
def c16630 : List Lit := [(1751, false), (1785, true), (115, true), (1750, false), (114, true), (1651, false), (487, true), (103, true), (1660, false), (74, true), (1598, true)]
theorem step16630 (p : Nat → Bool) (h : Constraints p) : clause p c16630 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13525] c16630 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13525 p h) (sat_nil p)))
def c16631 : List Lit := [(107, true), (1750, false), (1785, true), (1666, false), (103, true), (455, true)]
theorem step16631 (p : Nat → Bool) (h : Constraints p) : clause p c16631 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13477] c16631 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13477 p h) (sat_nil p)))
def c16632 : List Lit := [(1782, true), (487, true), (1666, false), (1745, false), (49, true)]
theorem step16632 (p : Nat → Bool) (h : Constraints p) : clause p c16632 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13304] c16632 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13304 p h) (sat_nil p)))
def c16633 : List Lit := [(113, true), (1760, true), (1692, true), (395, false), (1572, true)]
theorem step16633 (p : Nat → Bool) (h : Constraints p) : clause p c16633 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13654] c16633 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13654 p h) (sat_nil p)))
def c16634 : List Lit := [(115, false), (1651, true), (1661, true), (197, true), (39, false), (69, true), (1784, true), (1783, true), (487, true), (1750, false), (1599, true), (56, false)]
theorem step16634 (p : Nat → Bool) (h : Constraints p) : clause p c16634 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12838] c16634 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12838 p h) (sat_nil p)))
def c16635 : List Lit := [(92, true), (91, false), (1666, false), (1786, true), (107, true), (439, true), (1717, false), (1751, false)]
theorem step16635 (p : Nat → Bool) (h : Constraints p) : clause p c16635 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12792] c16635 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12792 p h) (sat_nil p)))
def c16636 : List Lit := [(1668, false), (91, false), (1785, true), (67, true), (1726, false), (1598, true), (115, true), (1760, false)]
theorem step16636 (p : Nat → Bool) (h : Constraints p) : clause p c16636 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12820] c16636 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12820 p h) (sat_nil p)))
def c16637 : List Lit := [(439, true), (1761, false), (1666, false), (1751, false), (1616, false)]
theorem step16637 (p : Nat → Bool) (h : Constraints p) : clause p c16637 = true :=
  Snake9.LocalRup.prove_clause [c15724, c11683] c16637 (by decide) p (sat_cons (step15724 p h) (sat_cons (step11683 p h) (sat_nil p)))
def c16638 : List Lit := [(1651, true), (1666, true), (62, true), (91, true), (1639, true), (485, true), (1761, false), (103, false), (74, false)]
theorem step16638 (p : Nat → Bool) (h : Constraints p) : clause p c16638 = true :=
  Snake9.LocalRup.prove_clause [c15726, c12954] c16638 (by decide) p (sat_cons (step15726 p h) (sat_cons (step12954 p h) (sat_nil p)))
def c16639 : List Lit := [(1617, false), (1761, false), (1665, false), (91, true)]
theorem step16639 (p : Nat → Bool) (h : Constraints p) : clause p c16639 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12952] c16639 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12952 p h) (sat_nil p)))
def c16640 : List Lit := [(1782, true), (1751, false), (1665, false), (1750, false), (439, true)]
theorem step16640 (p : Nat → Bool) (h : Constraints p) : clause p c16640 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12455] c16640 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12455 p h) (sat_nil p)))
def c16641 : List Lit := [(91, false), (107, true), (103, true), (1786, true), (455, true), (1666, false), (439, true), (1751, false)]
theorem step16641 (p : Nat → Bool) (h : Constraints p) : clause p c16641 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12790] c16641 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12790 p h) (sat_nil p)))
def c16642 : List Lit := [(1783, true), (62, true), (69, true), (45, false), (487, true), (1759, false), (1750, false), (74, true)]
theorem step16642 (p : Nat → Bool) (h : Constraints p) : clause p c16642 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12835] c16642 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12835 p h) (sat_nil p)))
def c16643 : List Lit := [(1601, false), (427, false), (72, false), (75, false), (1665, false), (74, true), (1600, false), (46, true), (49, false), (73, false)]
theorem step16643 (p : Nat → Bool) (h : Constraints p) : clause p c16643 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13275] c16643 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13275 p h) (sat_nil p)))
def c16644 : List Lit := [(1783, true), (1760, false), (1666, false), (1750, false), (49, true)]
theorem step16644 (p : Nat → Bool) (h : Constraints p) : clause p c16644 = true :=
  Snake9.LocalRup.prove_clause [c15724, c11480] c16644 (by decide) p (sat_cons (step15724 p h) (sat_cons (step11480 p h) (sat_nil p)))
def c16645 : List Lit := [(305, true), (1761, false), (1598, true), (115, true), (1616, true), (27, true), (487, true), (67, true), (1615, false), (415, true), (1637, true), (1666, false)]
theorem step16645 (p : Nat → Bool) (h : Constraints p) : clause p c16645 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12810] c16645 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12810 p h) (sat_nil p)))
def c16646 : List Lit := [(1688, true), (1727, true), (103, true)]
theorem step16646 (p : Nat → Bool) (h : Constraints p) : clause p c16646 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12798] c16646 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12798 p h) (sat_nil p)))
def c16647 : List Lit := [(1761, false), (1782, true), (439, true), (1664, false), (1751, false)]
theorem step16647 (p : Nat → Bool) (h : Constraints p) : clause p c16647 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12257] c16647 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12257 p h) (sat_nil p)))
def c16648 : List Lit := [(1782, true), (121, true), (115, true), (1664, false), (120, true), (487, true)]
theorem step16648 (p : Nat → Bool) (h : Constraints p) : clause p c16648 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13059] c16648 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13059 p h) (sat_nil p)))
def c16649 : List Lit := [(119, false), (1783, true), (1666, false), (122, false), (1750, false), (103, false), (1719, false), (1760, false)]
theorem step16649 (p : Nat → Bool) (h : Constraints p) : clause p c16649 = true :=
  Snake9.LocalRup.prove_clause [c15724, c11734] c16649 (by decide) p (sat_cons (step15724 p h) (sat_cons (step11734 p h) (sat_nil p)))
def c16650 : List Lit := [(1752, false), (1783, true), (1726, false), (439, true), (1664, false)]
theorem step16650 (p : Nat → Bool) (h : Constraints p) : clause p c16650 = true :=
  Snake9.LocalRup.prove_clause [c15724, c12845] c16650 (by decide) p (sat_cons (step15724 p h) (sat_cons (step12845 p h) (sat_nil p)))
def c16651 : List Lit := [(27, true), (1688, true), (45, true), (103, false), (75, true), (49, false), (367, true), (74, true), (1637, true)]
theorem step16651 (p : Nat → Bool) (h : Constraints p) : clause p c16651 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13405] c16651 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13405 p h) (sat_nil p)))
def c16652 : List Lit := [(113, false), (120, false), (1660, false), (1761, false), (1651, false), (487, true), (1785, true), (103, true), (74, true)]
theorem step16652 (p : Nat → Bool) (h : Constraints p) : clause p c16652 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13476] c16652 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13476 p h) (sat_nil p)))
def c16653 : List Lit := [(1653, true), (1783, true), (1660, false), (67, false), (439, true), (1726, false), (74, true), (1651, true)]
theorem step16653 (p : Nat → Bool) (h : Constraints p) : clause p c16653 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13659] c16653 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13659 p h) (sat_nil p)))
def c16654 : List Lit := [(1698, true), (1657, false), (1650, false), (193, true), (57, false)]
theorem step16654 (p : Nat → Bool) (h : Constraints p) : clause p c16654 = true :=
  Snake9.LocalRup.prove_clause [c15726, c13208] c16654 (by decide) p (sat_cons (step15726 p h) (sat_cons (step13208 p h) (sat_nil p)))
def c16655 : List Lit := [(1783, true), (1727, true), (1751, false), (1666, false), (439, true)]
theorem step16655 (p : Nat → Bool) (h : Constraints p) : clause p c16655 = true :=
  Snake9.LocalRup.prove_clause [c15724, c11856] c16655 (by decide) p (sat_cons (step15724 p h) (sat_cons (step11856 p h) (sat_nil p)))
def c16656 : List Lit := [(1617, false), (395, false), (27, true), (1750, false), (74, true), (1666, false)]
theorem step16656 (p : Nat → Bool) (h : Constraints p) : clause p c16656 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13546] c16656 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13546 p h) (sat_nil p)))
def c16657 : List Lit := [(1783, true), (72, false), (49, true), (1666, false), (74, true), (487, true), (1750, false)]
theorem step16657 (p : Nat → Bool) (h : Constraints p) : clause p c16657 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13334] c16657 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13334 p h) (sat_nil p)))
def c16658 : List Lit := [(1782, true), (1750, false), (74, true), (1665, false), (487, true), (72, false)]
theorem step16658 (p : Nat → Bool) (h : Constraints p) : clause p c16658 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13366] c16658 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13366 p h) (sat_nil p)))
def c16659 : List Lit := [(1554, true), (25, true), (1750, false), (1690, true), (91, true), (1688, false), (27, true), (395, false), (1667, false)]
theorem step16659 (p : Nat → Bool) (h : Constraints p) : clause p c16659 = true :=
  Snake9.LocalRup.prove_clause [c15725, c13451] c16659 (by decide) p (sat_cons (step15725 p h) (sat_cons (step13451 p h) (sat_nil p)))
def c16660 : List Lit := [(89, true), (1751, false), (415, true), (1688, false), (1784, true), (1685, true), (439, true), (1665, false)]
theorem step16660 (p : Nat → Bool) (h : Constraints p) : clause p c16660 = true :=
  Snake9.LocalRup.prove_clause [c15725, c13013] c16660 (by decide) p (sat_cons (step15725 p h) (sat_cons (step13013 p h) (sat_nil p)))
def c16661 : List Lit := [(107, true), (74, true), (1761, false), (487, true), (1598, false), (1666, false), (75, false), (45, true), (73, false)]
theorem step16661 (p : Nat → Bool) (h : Constraints p) : clause p c16661 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13883] c16661 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13883 p h) (sat_nil p)))
def c16662 : List Lit := [(439, true), (1701, true), (1582, true), (305, true), (1750, false), (1616, false), (415, true), (1553, false), (1666, false), (1729, true), (1638, true), (27, true)]
theorem step16662 (p : Nat → Bool) (h : Constraints p) : clause p c16662 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13886] c16662 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13886 p h) (sat_nil p)))
def c16663 : List Lit := [(91, true), (1761, false), (1616, false), (1666, false)]
theorem step16663 (p : Nat → Bool) (h : Constraints p) : clause p c16663 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13889] c16663 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13889 p h) (sat_nil p)))
def c16664 : List Lit := [(1617, false), (1700, false), (1729, true), (439, true), (1750, false), (415, true), (27, true), (1666, false), (305, true), (1784, true), (1665, false)]
theorem step16664 (p : Nat → Bool) (h : Constraints p) : clause p c16664 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13894] c16664 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13894 p h) (sat_nil p)))
def c16665 : List Lit := [(91, true), (415, true), (1654, false), (45, true), (1729, true), (1688, false), (75, false), (1657, false), (1616, false), (305, true), (365, true), (193, true), (439, true), (27, true), (1750, false), (1598, false)]
theorem step16665 (p : Nat → Bool) (h : Constraints p) : clause p c16665 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13897] c16665 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13897 p h) (sat_nil p)))
def c16666 : List Lit := [(120, true), (1727, true), (1688, false), (1751, true), (62, true), (67, false), (75, false)]
theorem step16666 (p : Nat → Bool) (h : Constraints p) : clause p c16666 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13898] c16666 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13898 p h) (sat_nil p)))
def c16667 : List Lit := [(1606, false), (439, true), (305, true), (1729, true), (415, true), (27, true), (1616, false), (1750, false), (1666, false), (103, true)]
theorem step16667 (p : Nat → Bool) (h : Constraints p) : clause p c16667 = true :=
  Snake9.LocalRup.prove_clause [c15724, c13900] c16667 (by decide) p (sat_cons (step15724 p h) (sat_cons (step13900 p h) (sat_nil p)))
end B112E089
