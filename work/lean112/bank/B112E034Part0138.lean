import B112E034Part0137
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c10611 : List Lit := [(1617, true), (1584, true), (92, false), (37, true)]
theorem step10611 (p : Nat → Bool) (h : Constraints p) : clause p c10611 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5968] c10611 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5968 p h) (sat_nil p)))
def c10612 : List Lit := [(72, false), (1623, true), (114, true), (37, true), (117, false)]
theorem step10612 (p : Nat → Bool) (h : Constraints p) : clause p c10612 = true :=
  Snake9.LocalRup.prove_clause [c10424, c5271] c10612 (by decide) p (sat_cons (step10424 p h) (sat_cons (step5271 p h) (sat_nil p)))
def c10613 : List Lit := [(1758, true), (1737, false)]
theorem step10613 (p : Nat → Bool) (h : Constraints p) : clause p c10613 = true :=
  Snake9.LocalRup.prove_clause [c8660, c5645] c10613 (by decide) p (sat_cons (step8660 p h) (sat_cons (step5645 p h) (sat_nil p)))
def c10614 : List Lit := [(1829, true), (115, true), (1797, false), (1775, false), (107, false), (1805, false), (1803, false)]
theorem step10614 (p : Nat → Bool) (h : Constraints p) : clause p c10614 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6116] c10614 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6116 p h) (sat_nil p)))
def c10615 : List Lit := [(109, false), (1819, true), (115, true), (107, false), (1803, false), (117, true), (92, false)]
theorem step10615 (p : Nat → Bool) (h : Constraints p) : clause p c10615 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5833] c10615 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5833 p h) (sat_nil p)))
def c10616 : List Lit := [(1759, true), (1737, false), (86, true)]
theorem step10616 (p : Nat → Bool) (h : Constraints p) : clause p c10616 = true :=
  Snake9.LocalRup.prove_clause [c8660, c5671] c10616 (by decide) p (sat_cons (step8660 p h) (sat_cons (step5671 p h) (sat_nil p)))
def c10617 : List Lit := [(1738, false), (1831, false), (86, true), (1760, false), (1622, false)]
theorem step10617 (p : Nat → Bool) (h : Constraints p) : clause p c10617 = true :=
  Snake9.LocalRup.prove_clause [c10429, c5963] c10617 (by decide) p (sat_cons (step10429 p h) (sat_cons (step5963 p h) (sat_nil p)))
def c10618 : List Lit := [(103, false), (1805, true), (119, true), (1644, false), (1687, true), (1706, true), (1806, true), (1622, false), (115, true)]
theorem step10618 (p : Nat → Bool) (h : Constraints p) : clause p c10618 = true :=
  Snake9.LocalRup.prove_clause [c10424, c10428, c5825] c10618 (by decide) p (sat_cons (step10424 p h) (sat_cons (step10428 p h) (sat_cons (step5825 p h) (sat_nil p))))
def c10619 : List Lit := [(1790, false), (114, false), (1800, false), (1855, true), (92, false), (1737, false), (1644, true), (126, true), (117, true)]
theorem step10619 (p : Nat → Bool) (h : Constraints p) : clause p c10619 = true :=
  Snake9.LocalRup.prove_clause [c8660, c5163] c10619 (by decide) p (sat_cons (step8660 p h) (sat_cons (step5163 p h) (sat_nil p)))
def c10620 : List Lit := [(111, true), (118, false), (115, false)]
theorem step10620 (p : Nat → Bool) (h : Constraints p) : clause p c10620 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5726] c10620 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5726 p h) (sat_nil p)))
def c10621 : List Lit := [(1760, true), (1738, false), (86, true)]
theorem step10621 (p : Nat → Bool) (h : Constraints p) : clause p c10621 = true :=
  Snake9.LocalRup.prove_clause [c8660, c5624] c10621 (by decide) p (sat_cons (step8660 p h) (sat_cons (step5624 p h) (sat_nil p)))
def c10622 : List Lit := [(1759, true), (1738, false)]
theorem step10622 (p : Nat → Bool) (h : Constraints p) : clause p c10622 = true :=
  Snake9.LocalRup.prove_clause [c8660, c5611] c10622 (by decide) p (sat_cons (step8660 p h) (sat_cons (step5611 p h) (sat_nil p)))
def c10623 : List Lit := [(1739, false), (1760, true)]
theorem step10623 (p : Nat → Bool) (h : Constraints p) : clause p c10623 = true :=
  Snake9.LocalRup.prove_clause [c8660, c5621] c10623 (by decide) p (sat_cons (step8660 p h) (sat_cons (step5621 p h) (sat_nil p)))
def c10624 : List Lit := [(77, false), (1714, true)]
theorem step10624 (p : Nat → Bool) (h : Constraints p) : clause p c10624 = true :=
  Snake9.LocalRup.prove_clause [c8660, c5642] c10624 (by decide) p (sat_cons (step8660 p h) (sat_cons (step5642 p h) (sat_nil p)))
def c10625 : List Lit := [(1758, true), (86, true)]
theorem step10625 (p : Nat → Bool) (h : Constraints p) : clause p c10625 = true :=
  Snake9.LocalRup.prove_clause [c8660, c6211] c10625 (by decide) p (sat_cons (step8660 p h) (sat_cons (step6211 p h) (sat_nil p)))
def c10626 : List Lit := [(70, true), (1760, true), (1737, false), (1644, true)]
theorem step10626 (p : Nat → Bool) (h : Constraints p) : clause p c10626 = true :=
  Snake9.LocalRup.prove_clause [c8661, c8660, c5327] c10626 (by decide) p (sat_cons (step8661 p h) (sat_cons (step8660 p h) (sat_cons (step5327 p h) (sat_nil p))))
def c10627 : List Lit := [(1622, true), (42, true)]
theorem step10627 (p : Nat → Bool) (h : Constraints p) : clause p c10627 = true :=
  Snake9.LocalRup.prove_clause [c10424, c5037] c10627 (by decide) p (sat_cons (step10424 p h) (sat_cons (step5037 p h) (sat_nil p)))
def c10628 : List Lit := [(103, false), (1748, false), (1644, false), (1805, true), (119, true), (1806, true), (1829, false), (1687, true), (1714, false), (115, true), (1622, false)]
theorem step10628 (p : Nat → Bool) (h : Constraints p) : clause p c10628 = true :=
  Snake9.LocalRup.prove_clause [c10428, c10424, c6114] c10628 (by decide) p (sat_cons (step10428 p h) (sat_cons (step10424 p h) (sat_cons (step6114 p h) (sat_nil p))))
def c10629 : List Lit := [(1760, true), (1803, true), (1737, false), (1644, true)]
theorem step10629 (p : Nat → Bool) (h : Constraints p) : clause p c10629 = true :=
  Snake9.LocalRup.prove_clause [c8660, c5078] c10629 (by decide) p (sat_cons (step8660 p h) (sat_cons (step5078 p h) (sat_nil p)))
def c10630 : List Lit := [(1607, true), (35, true), (36, true), (1623, true), (115, true)]
theorem step10630 (p : Nat → Bool) (h : Constraints p) : clause p c10630 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6132] c10630 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6132 p h) (sat_nil p)))
def c10631 : List Lit := [(94, false), (114, true), (107, false), (117, false), (104, true), (115, true), (1785, true), (92, false)]
theorem step10631 (p : Nat → Bool) (h : Constraints p) : clause p c10631 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5838] c10631 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5838 p h) (sat_nil p)))
def c10632 : List Lit := [(1633, true), (51, true), (1806, true), (42, false)]
theorem step10632 (p : Nat → Bool) (h : Constraints p) : clause p c10632 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5340] c10632 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5340 p h) (sat_nil p)))
def c10633 : List Lit := [(95, true), (1784, false), (1831, true), (1789, false), (107, false), (117, true), (93, false), (1818, false), (1782, true)]
theorem step10633 (p : Nat → Bool) (h : Constraints p) : clause p c10633 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5841] c10633 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5841 p h) (sat_nil p)))
def c10634 : List Lit := [(1805, true), (114, true), (86, false), (107, false)]
theorem step10634 (p : Nat → Bool) (h : Constraints p) : clause p c10634 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5255] c10634 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5255 p h) (sat_nil p)))
def c10635 : List Lit := [(109, false), (1805, true), (107, false), (92, false), (115, true)]
theorem step10635 (p : Nat → Bool) (h : Constraints p) : clause p c10635 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5834] c10635 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5834 p h) (sat_nil p)))
def c10636 : List Lit := [(109, false), (1805, true), (115, true), (107, true), (92, false)]
theorem step10636 (p : Nat → Bool) (h : Constraints p) : clause p c10636 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6207] c10636 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6207 p h) (sat_nil p)))
def c10637 : List Lit := [(119, false), (109, false), (126, false), (107, false), (1805, true), (115, true)]
theorem step10637 (p : Nat → Bool) (h : Constraints p) : clause p c10637 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6154] c10637 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6154 p h) (sat_nil p)))
def c10638 : List Lit := [(1623, false), (1738, false), (1830, false), (1805, true), (1687, true)]
theorem step10638 (p : Nat → Bool) (h : Constraints p) : clause p c10638 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5857] c10638 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5857 p h) (sat_nil p)))
def c10639 : List Lit := [(87, true), (95, false), (117, false), (92, false)]
theorem step10639 (p : Nat → Bool) (h : Constraints p) : clause p c10639 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5965] c10639 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5965 p h) (sat_nil p)))
def c10640 : List Lit := [(1771, true), (92, false), (117, false), (86, false)]
theorem step10640 (p : Nat → Bool) (h : Constraints p) : clause p c10640 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5949] c10640 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5949 p h) (sat_nil p)))
def c10641 : List Lit := [(118, false), (115, true), (117, false)]
theorem step10641 (p : Nat → Bool) (h : Constraints p) : clause p c10641 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5784] c10641 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5784 p h) (sat_nil p)))
def c10642 : List Lit := [(124, true), (115, true), (106, true), (117, false)]
theorem step10642 (p : Nat → Bool) (h : Constraints p) : clause p c10642 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6096] c10642 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6096 p h) (sat_nil p)))
def c10643 : List Lit := [(1623, false), (1687, true), (1644, false), (126, false)]
theorem step10643 (p : Nat → Bool) (h : Constraints p) : clause p c10643 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5843] c10643 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5843 p h) (sat_nil p)))
def c10644 : List Lit := [(46, true), (109, false), (126, false), (115, true), (117, false), (1644, false), (36, true), (1687, true)]
theorem step10644 (p : Nat → Bool) (h : Constraints p) : clause p c10644 = true :=
  Snake9.LocalRup.prove_clause [c10428, c10424, c6156] c10644 (by decide) p (sat_cons (step10428 p h) (sat_cons (step10424 p h) (sat_cons (step6156 p h) (sat_nil p))))
def c10645 : List Lit := [(1646, false), (1737, true), (92, false), (126, false), (115, true), (1688, true), (1622, false), (93, false), (1791, true), (107, true), (86, false)]
theorem step10645 (p : Nat → Bool) (h : Constraints p) : clause p c10645 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6242] c10645 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6242 p h) (sat_nil p)))
def c10646 : List Lit := [(1829, true), (109, false), (107, false), (1775, false), (1805, true), (101, false), (115, true)]
theorem step10646 (p : Nat → Bool) (h : Constraints p) : clause p c10646 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6119] c10646 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6119 p h) (sat_nil p)))
def c10647 : List Lit := [(122, false), (1710, true), (79, false), (1803, true), (119, true), (1612, false), (1623, true)]
theorem step10647 (p : Nat → Bool) (h : Constraints p) : clause p c10647 = true :=
  Snake9.LocalRup.prove_clause [c10424, c5767] c10647 (by decide) p (sat_cons (step10424 p h) (sat_cons (step5767 p h) (sat_nil p)))
def c10648 : List Lit := [(122, false), (1800, true), (115, false), (117, true)]
theorem step10648 (p : Nat → Bool) (h : Constraints p) : clause p c10648 = true :=
  Snake9.LocalRup.prove_clause [c10428, c5389] c10648 (by decide) p (sat_cons (step10428 p h) (sat_cons (step5389 p h) (sat_nil p)))
def c10649 : List Lit := [(1806, false), (1801, false), (1788, false), (1803, false), (1760, false), (1644, false)]
theorem step10649 (p : Nat → Bool) (h : Constraints p) : clause p c10649 = true :=
  Snake9.LocalRup.prove_clause [c10426, c5836] c10649 (by decide) p (sat_cons (step10426 p h) (sat_cons (step5836 p h) (sat_nil p)))
def c10650 : List Lit := [(1661, true), (122, false), (92, false), (1685, true), (58, false)]
theorem step10650 (p : Nat → Bool) (h : Constraints p) : clause p c10650 = true :=
  Snake9.LocalRup.prove_clause [c10424, c5388] c10650 (by decide) p (sat_cons (step10424 p h) (sat_cons (step5388 p h) (sat_nil p)))
def c10651 : List Lit := [(1806, false), (1854, true), (117, false), (86, false), (92, false), (1735, false), (107, false)]
theorem step10651 (p : Nat → Bool) (h : Constraints p) : clause p c10651 = true :=
  Snake9.LocalRup.prove_clause [c8660, c10428, c6379] c10651 (by decide) p (sat_cons (step8660 p h) (sat_cons (step10428 p h) (sat_cons (step6379 p h) (sat_nil p))))
def c10652 : List Lit := [(109, false), (1795, false), (1803, true), (1687, true), (107, true), (115, true), (1644, false), (1819, true), (117, true)]
theorem step10652 (p : Nat → Bool) (h : Constraints p) : clause p c10652 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7893] c10652 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7893 p h) (sat_nil p)))
def c10653 : List Lit := [(109, false), (1819, true), (1803, false), (115, true), (107, true), (117, true), (92, false)]
theorem step10653 (p : Nat → Bool) (h : Constraints p) : clause p c10653 = true :=
  Snake9.LocalRup.prove_clause [c10428, c7263] c10653 (by decide) p (sat_cons (step10428 p h) (sat_cons (step7263 p h) (sat_nil p)))
def c10654 : List Lit := [(1758, true), (79, true), (93, false), (1646, true), (89, false)]
theorem step10654 (p : Nat → Bool) (h : Constraints p) : clause p c10654 = true :=
  Snake9.LocalRup.prove_clause [c10428, c8663, c6387] c10654 (by decide) p (sat_cons (step10428 p h) (sat_cons (step8663 p h) (sat_cons (step6387 p h) (sat_nil p))))
def c10655 : List Lit := [(1773, false), (1830, true), (92, false), (107, true), (93, false), (1775, false), (101, false), (115, true), (117, false)]
theorem step10655 (p : Nat → Bool) (h : Constraints p) : clause p c10655 = true :=
  Snake9.LocalRup.prove_clause [c10428, c7433] c10655 (by decide) p (sat_cons (step10428 p h) (sat_cons (step7433 p h) (sat_nil p)))
def c10656 : List Lit := [(119, false), (1806, true), (1687, true), (1644, false), (1803, true), (115, true)]
theorem step10656 (p : Nat → Bool) (h : Constraints p) : clause p c10656 = true :=
  Snake9.LocalRup.prove_clause [c10424, c10428, c7214] c10656 (by decide) p (sat_cons (step10424 p h) (sat_cons (step10428 p h) (sat_cons (step7214 p h) (sat_nil p))))
def c10657 : List Lit := [(1709, false), (79, false), (86, true), (93, false), (115, true), (1759, true), (1820, true), (107, false), (1819, true)]
theorem step10657 (p : Nat → Bool) (h : Constraints p) : clause p c10657 = true :=
  Snake9.LocalRup.prove_clause [c8660, c6523] c10657 (by decide) p (sat_cons (step8660 p h) (sat_cons (step6523 p h) (sat_nil p)))
def c10658 : List Lit := [(1775, true), (1789, true), (115, true), (1829, false), (1820, true), (107, false), (1853, true), (117, false)]
theorem step10658 (p : Nat → Bool) (h : Constraints p) : clause p c10658 = true :=
  Snake9.LocalRup.prove_clause [c10428, c8660, c6766] c10658 (by decide) p (sat_cons (step10428 p h) (sat_cons (step8660 p h) (sat_cons (step6766 p h) (sat_nil p))))
def c10659 : List Lit := [(125, false), (1748, true), (1737, false), (1760, true), (86, true), (114, true), (120, false)]
theorem step10659 (p : Nat → Bool) (h : Constraints p) : clause p c10659 = true :=
  Snake9.LocalRup.prove_clause [c8660, c6372] c10659 (by decide) p (sat_cons (step8660 p h) (sat_cons (step6372 p h) (sat_nil p)))
def c10660 : List Lit := [(119, true), (114, false), (120, false), (117, false), (93, false), (107, false), (1759, false)]
theorem step10660 (p : Nat → Bool) (h : Constraints p) : clause p c10660 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6724] c10660 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6724 p h) (sat_nil p)))
def c10661 : List Lit := [(1782, false), (1584, true), (115, true), (92, false), (126, false), (1623, true), (1775, false), (1805, true), (86, false), (107, true), (1803, false), (1831, true), (117, true)]
theorem step10661 (p : Nat → Bool) (h : Constraints p) : clause p c10661 = true :=
  Snake9.LocalRup.prove_clause [c10428, c8016] c10661 (by decide) p (sat_cons (step10428 p h) (sat_cons (step8016 p h) (sat_nil p)))
def c10662 : List Lit := [(1685, true), (1644, false)]
theorem step10662 (p : Nat → Bool) (h : Constraints p) : clause p c10662 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7674] c10662 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7674 p h) (sat_nil p)))
def c10663 : List Lit := [(1686, true), (115, true), (1644, false)]
theorem step10663 (p : Nat → Bool) (h : Constraints p) : clause p c10663 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7846] c10663 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7846 p h) (sat_nil p)))
def c10664 : List Lit := [(1623, false), (1687, true), (1644, false), (1806, true)]
theorem step10664 (p : Nat → Bool) (h : Constraints p) : clause p c10664 = true :=
  Snake9.LocalRup.prove_clause [c10428, c7255] c10664 (by decide) p (sat_cons (step10428 p h) (sat_cons (step7255 p h) (sat_nil p)))
def c10665 : List Lit := [(109, false), (114, true), (107, false), (1623, true), (117, false)]
theorem step10665 (p : Nat → Bool) (h : Constraints p) : clause p c10665 = true :=
  Snake9.LocalRup.prove_clause [c10424, c10428, c6760] c10665 (by decide) p (sat_cons (step10424 p h) (sat_cons (step10428 p h) (sat_cons (step6760 p h) (sat_nil p))))
def c10666 : List Lit := [(37, true), (1623, true), (1831, true), (107, true), (1819, true), (117, false), (126, true), (93, false), (115, false), (92, false)]
theorem step10666 (p : Nat → Bool) (h : Constraints p) : clause p c10666 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6467] c10666 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6467 p h) (sat_nil p)))
def c10667 : List Lit := [(1804, true), (125, false), (1623, true), (37, true), (1796, true), (107, true), (1831, true), (117, false), (1805, false), (93, false), (115, false)]
theorem step10667 (p : Nat → Bool) (h : Constraints p) : clause p c10667 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6469] c10667 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6469 p h) (sat_nil p)))
def c10668 : List Lit := [(39, false), (1623, true), (37, true), (117, false), (1617, false)]
theorem step10668 (p : Nat → Bool) (h : Constraints p) : clause p c10668 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6819] c10668 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6819 p h) (sat_nil p)))
def c10669 : List Lit := [(109, false), (1623, true), (37, true), (1803, true)]
theorem step10669 (p : Nat → Bool) (h : Constraints p) : clause p c10669 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7563] c10669 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7563 p h) (sat_nil p)))
def c10670 : List Lit := [(103, false), (119, true), (115, true), (1706, true), (1644, false), (1687, true)]
theorem step10670 (p : Nat → Bool) (h : Constraints p) : clause p c10670 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7921] c10670 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7921 p h) (sat_nil p)))
def c10671 : List Lit := [(1726, true), (79, true), (1758, true)]
theorem step10671 (p : Nat → Bool) (h : Constraints p) : clause p c10671 = true :=
  Snake9.LocalRup.prove_clause [c8660, c6481] c10671 (by decide) p (sat_cons (step8660 p h) (sat_cons (step6481 p h) (sat_nil p)))
def c10672 : List Lit := [(114, true), (119, true), (120, false), (126, false), (115, false), (125, false)]
theorem step10672 (p : Nat → Bool) (h : Constraints p) : clause p c10672 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6749] c10672 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6749 p h) (sat_nil p)))
def c10673 : List Lit := [(120, false), (119, true), (1617, false), (1623, true), (115, true)]
theorem step10673 (p : Nat → Bool) (h : Constraints p) : clause p c10673 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6573] c10673 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6573 p h) (sat_nil p)))
def c10674 : List Lit := [(109, false), (1758, true), (92, false), (117, false), (1688, true)]
theorem step10674 (p : Nat → Bool) (h : Constraints p) : clause p c10674 = true :=
  Snake9.LocalRup.prove_clause [c8660, c6475] c10674 (by decide) p (sat_cons (step8660 p h) (sat_cons (step6475 p h) (sat_nil p)))
end B112E034
