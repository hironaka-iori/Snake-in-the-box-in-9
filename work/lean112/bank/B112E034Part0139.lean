import B112E034Part0138
namespace B112E034
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c10675 : List Lit := [(114, true), (109, false), (86, false), (117, false), (115, true)]
theorem step10675 (p : Nat → Bool) (h : Constraints p) : clause p c10675 = true :=
  Snake9.LocalRup.prove_clause [c10428, c7457] c10675 (by decide) p (sat_cons (step10428 p h) (sat_cons (step7457 p h) (sat_nil p)))
def c10676 : List Lit := [(1795, false), (109, false), (115, true), (1803, true), (107, true), (1686, true), (1819, true), (117, true)]
theorem step10676 (p : Nat → Bool) (h : Constraints p) : clause p c10676 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7942] c10676 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7942 p h) (sat_nil p)))
def c10677 : List Lit := [(1784, false), (1789, true), (107, false), (1853, true), (117, false)]
theorem step10677 (p : Nat → Bool) (h : Constraints p) : clause p c10677 = true :=
  Snake9.LocalRup.prove_clause [c8660, c10428, c6767] c10677 (by decide) p (sat_cons (step8660 p h) (sat_cons (step10428 p h) (sat_cons (step6767 p h) (sat_nil p))))
def c10678 : List Lit := [(1829, true), (1853, true), (1818, false), (114, true), (1738, false), (86, true), (117, false)]
theorem step10678 (p : Nat → Bool) (h : Constraints p) : clause p c10678 = true :=
  Snake9.LocalRup.prove_clause [c8660, c6769] c10678 (by decide) p (sat_cons (step8660 p h) (sat_cons (step6769 p h) (sat_nil p)))
def c10679 : List Lit := [(109, false), (1738, false), (1719, false), (1688, true), (114, true), (1761, true), (86, true), (117, false)]
theorem step10679 (p : Nat → Bool) (h : Constraints p) : clause p c10679 = true :=
  Snake9.LocalRup.prove_clause [c8660, c6759] c10679 (by decide) p (sat_cons (step8660 p h) (sat_cons (step6759 p h) (sat_nil p)))
def c10680 : List Lit := [(79, true), (1790, true), (114, true), (93, false), (107, true), (1760, true), (117, false)]
theorem step10680 (p : Nat → Bool) (h : Constraints p) : clause p c10680 = true :=
  Snake9.LocalRup.prove_clause [c8660, c6409] c10680 (by decide) p (sat_cons (step8660 p h) (sat_cons (step6409 p h) (sat_nil p)))
def c10681 : List Lit := [(103, false), (42, false), (1622, false), (1706, true), (126, true), (1813, true), (1644, false), (1809, true), (1687, true)]
theorem step10681 (p : Nat → Bool) (h : Constraints p) : clause p c10681 = true :=
  Snake9.LocalRup.prove_clause [c10428, c7814] c10681 (by decide) p (sat_cons (step10428 p h) (sat_cons (step7814 p h) (sat_nil p)))
def c10682 : List Lit := [(35, true), (42, false), (115, true), (1623, true), (1610, true), (120, false), (107, false)]
theorem step10682 (p : Nat → Bool) (h : Constraints p) : clause p c10682 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6699] c10682 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6699 p h) (sat_nil p)))
def c10683 : List Lit := [(1622, true), (115, true)]
theorem step10683 (p : Nat → Bool) (h : Constraints p) : clause p c10683 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6393] c10683 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6393 p h) (sat_nil p)))
def c10684 : List Lit := [(1622, true), (37, true)]
theorem step10684 (p : Nat → Bool) (h : Constraints p) : clause p c10684 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7705] c10684 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7705 p h) (sat_nil p)))
def c10685 : List Lit := [(88, false), (115, true), (92, false), (107, true), (86, false), (98, true), (117, false), (1791, true)]
theorem step10685 (p : Nat → Bool) (h : Constraints p) : clause p c10685 = true :=
  Snake9.LocalRup.prove_clause [c10428, c7424] c10685 (by decide) p (sat_cons (step10428 p h) (sat_cons (step7424 p h) (sat_nil p)))
def c10686 : List Lit := [(98, true), (104, true), (1832, true), (115, true), (1790, false), (86, false), (1775, false), (126, true), (107, true), (1803, false), (117, true), (92, false)]
theorem step10686 (p : Nat → Bool) (h : Constraints p) : clause p c10686 = true :=
  Snake9.LocalRup.prove_clause [c10428, c7307] c10686 (by decide) p (sat_cons (step10428 p h) (sat_cons (step7307 p h) (sat_nil p)))
def c10687 : List Lit := [(1761, true), (1737, false), (58, false), (1720, false), (1706, false), (86, true), (117, false)]
theorem step10687 (p : Nat → Bool) (h : Constraints p) : clause p c10687 = true :=
  Snake9.LocalRup.prove_clause [c8660, c6604] c10687 (by decide) p (sat_cons (step8660 p h) (sat_cons (step6604 p h) (sat_nil p)))
def c10688 : List Lit := [(77, false), (70, true), (58, false), (1715, true)]
theorem step10688 (p : Nat → Bool) (h : Constraints p) : clause p c10688 = true :=
  Snake9.LocalRup.prove_clause [c8660, c6461] c10688 (by decide) p (sat_cons (step8660 p h) (sat_cons (step6461 p h) (sat_nil p)))
def c10689 : List Lit := [(37, true), (1686, true), (1584, true), (1803, true), (117, false), (92, false)]
theorem step10689 (p : Nat → Bool) (h : Constraints p) : clause p c10689 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6832] c10689 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6832 p h) (sat_nil p)))
def c10690 : List Lit := [(79, false), (1645, false), (115, true), (125, false), (1706, true), (1644, false), (1687, true)]
theorem step10690 (p : Nat → Bool) (h : Constraints p) : clause p c10690 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7847] c10690 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7847 p h) (sat_nil p)))
def c10691 : List Lit := [(125, false), (126, false), (92, false), (115, true), (106, true)]
theorem step10691 (p : Nat → Bool) (h : Constraints p) : clause p c10691 = true :=
  Snake9.LocalRup.prove_clause [c10428, c8036] c10691 (by decide) p (sat_cons (step10428 p h) (sat_cons (step8036 p h) (sat_nil p)))
def c10692 : List Lit := [(35, true), (38, false), (1623, true)]
theorem step10692 (p : Nat → Bool) (h : Constraints p) : clause p c10692 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7597] c10692 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7597 p h) (sat_nil p)))
def c10693 : List Lit := [(39, false), (1686, true), (117, false), (37, true)]
theorem step10693 (p : Nat → Bool) (h : Constraints p) : clause p c10693 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6838] c10693 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6838 p h) (sat_nil p)))
def c10694 : List Lit := [(1782, false), (1831, true), (1798, false), (1644, true), (1803, true), (1761, true), (86, true), (93, true), (37, true), (126, true)]
theorem step10694 (p : Nat → Bool) (h : Constraints p) : clause p c10694 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7573] c10694 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7573 p h) (sat_nil p)))
def c10695 : List Lit := [(97, false), (1774, true), (1806, true), (1819, true), (87, true), (126, true), (86, false), (117, true)]
theorem step10695 (p : Nat → Bool) (h : Constraints p) : clause p c10695 = true :=
  Snake9.LocalRup.prove_clause [c10428, c7993] c10695 (by decide) p (sat_cons (step10428 p h) (sat_cons (step7993 p h) (sat_nil p)))
def c10696 : List Lit := [(1800, true), (122, false), (117, true)]
theorem step10696 (p : Nat → Bool) (h : Constraints p) : clause p c10696 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6386] c10696 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6386 p h) (sat_nil p)))
def c10697 : List Lit := [(1685, true), (37, true)]
theorem step10697 (p : Nat → Bool) (h : Constraints p) : clause p c10697 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7647] c10697 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7647 p h) (sat_nil p)))
def c10698 : List Lit := [(1686, true), (37, true), (1644, false)]
theorem step10698 (p : Nat → Bool) (h : Constraints p) : clause p c10698 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7722] c10698 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7722 p h) (sat_nil p)))
def c10699 : List Lit := [(35, true), (1623, true), (1803, true), (37, true)]
theorem step10699 (p : Nat → Bool) (h : Constraints p) : clause p c10699 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6922] c10699 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6922 p h) (sat_nil p)))
def c10700 : List Lit := [(1623, false), (1831, true), (93, true), (37, true), (1622, false), (1803, true), (107, true), (1855, true), (1819, false)]
theorem step10700 (p : Nat → Bool) (h : Constraints p) : clause p c10700 = true :=
  Snake9.LocalRup.prove_clause [c10424, c7564] c10700 (by decide) p (sat_cons (step10424 p h) (sat_cons (step7564 p h) (sat_nil p)))
def c10701 : List Lit := [(1737, true), (37, true), (1831, true), (126, true), (93, false), (117, false), (115, false), (1623, true)]
theorem step10701 (p : Nat → Bool) (h : Constraints p) : clause p c10701 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6465] c10701 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6465 p h) (sat_nil p)))
def c10702 : List Lit := [(125, false), (1853, true), (120, false), (107, false), (93, false), (1819, true), (1803, true)]
theorem step10702 (p : Nat → Bool) (h : Constraints p) : clause p c10702 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6745] c10702 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6745 p h) (sat_nil p)))
def c10703 : List Lit := [(112, false), (125, false), (1623, true), (115, true), (117, false), (120, false)]
theorem step10703 (p : Nat → Bool) (h : Constraints p) : clause p c10703 = true :=
  Snake9.LocalRup.prove_clause [c10424, c6552] c10703 (by decide) p (sat_cons (step10424 p h) (sat_cons (step6552 p h) (sat_nil p)))
def c10704 : List Lit := [(1623, false), (1687, true), (125, false), (1644, false)]
theorem step10704 (p : Nat → Bool) (h : Constraints p) : clause p c10704 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6726] c10704 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6726 p h) (sat_nil p)))
def c10705 : List Lit := [(97, false), (119, false), (1819, true), (1806, true), (126, true), (1805, false), (117, true)]
theorem step10705 (p : Nat → Bool) (h : Constraints p) : clause p c10705 = true :=
  Snake9.LocalRup.prove_clause [c10428, c7290] c10705 (by decide) p (sat_cons (step10428 p h) (sat_cons (step7290 p h) (sat_nil p)))
def c10706 : List Lit := [(114, false), (1775, false), (1819, true), (86, false), (107, false), (93, false), (1719, false), (1789, true), (1797, false), (117, false), (115, true)]
theorem step10706 (p : Nat → Bool) (h : Constraints p) : clause p c10706 = true :=
  Snake9.LocalRup.prove_clause [c10428, c7446] c10706 (by decide) p (sat_cons (step10428 p h) (sat_cons (step7446 p h) (sat_nil p)))
def c10707 : List Lit := [(127, true), (128, true), (119, true), (125, false)]
theorem step10707 (p : Nat → Bool) (h : Constraints p) : clause p c10707 = true :=
  Snake9.LocalRup.prove_clause [c10428, c6746] c10707 (by decide) p (sat_cons (step10428 p h) (sat_cons (step6746 p h) (sat_nil p)))
def c10708 : List Lit := [(1622, true), (109, false), (117, false)]
theorem step10708 (p : Nat → Bool) (h : Constraints p) : clause p c10708 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8198] c10708 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8198 p h) (sat_nil p)))
def c10709 : List Lit := [(20, false), (1686, true), (1644, false), (92, false), (117, false)]
theorem step10709 (p : Nat → Bool) (h : Constraints p) : clause p c10709 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8211] c10709 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8211 p h) (sat_nil p)))
def c10710 : List Lit := [(114, true), (109, false), (1811, false), (1644, false), (1809, true), (1759, false), (126, true), (1789, false), (1797, false), (37, true), (117, false)]
theorem step10710 (p : Nat → Bool) (h : Constraints p) : clause p c10710 = true :=
  Snake9.LocalRup.prove_clause [c10428, c10424, c8215] c10710 (by decide) p (sat_cons (step10428 p h) (sat_cons (step10424 p h) (sat_cons (step8215 p h) (sat_nil p))))
def c10711 : List Lit := [(1819, false), (1759, false), (1644, false), (92, false), (107, true), (86, false), (117, false)]
theorem step10711 (p : Nat → Bool) (h : Constraints p) : clause p c10711 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8254] c10711 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8254 p h) (sat_nil p)))
def c10712 : List Lit := [(1760, false), (1854, true), (1644, false), (114, true), (1803, false), (126, true), (1797, false), (107, true), (37, true), (117, false)]
theorem step10712 (p : Nat → Bool) (h : Constraints p) : clause p c10712 = true :=
  Snake9.LocalRup.prove_clause [c10428, c10424, c8260] c10712 (by decide) p (sat_cons (step10428 p h) (sat_cons (step10424 p h) (sat_cons (step8260 p h) (sat_nil p))))
def c10713 : List Lit := [(1819, false), (1736, false), (1644, true), (1832, true), (86, false), (107, true), (117, false)]
theorem step10713 (p : Nat → Bool) (h : Constraints p) : clause p c10713 = true :=
  Snake9.LocalRup.prove_clause [c10429, c8299] c10713 (by decide) p (sat_cons (step10429 p h) (sat_cons (step8299 p h) (sat_nil p)))
def c10714 : List Lit := [(37, true), (20, false), (92, false), (1687, true), (1644, false), (1803, true), (117, false)]
theorem step10714 (p : Nat → Bool) (h : Constraints p) : clause p c10714 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8342] c10714 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8342 p h) (sat_nil p)))
def c10715 : List Lit := [(1623, false), (1687, true), (1809, true), (1644, false)]
theorem step10715 (p : Nat → Bool) (h : Constraints p) : clause p c10715 = true :=
  Snake9.LocalRup.prove_clause [c10428, c8405] c10715 (by decide) p (sat_cons (step10428 p h) (sat_cons (step8405 p h) (sat_nil p)))
def c10716 : List Lit := [(171, true), (20, false), (33, true), (92, false), (1687, true), (1644, false), (115, true)]
theorem step10716 (p : Nat → Bool) (h : Constraints p) : clause p c10716 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8411] c10716 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8411 p h) (sat_nil p)))
def c10717 : List Lit := [(109, false), (1818, true), (115, true), (1803, false), (107, true), (92, false)]
theorem step10717 (p : Nat → Bool) (h : Constraints p) : clause p c10717 = true :=
  Snake9.LocalRup.prove_clause [c10428, c8453] c10717 (by decide) p (sat_cons (step10428 p h) (sat_cons (step8453 p h) (sat_nil p)))
def c10718 : List Lit := [(1771, false), (1790, true), (126, false), (1805, true), (115, true), (1687, true), (79, false), (1781, false), (1644, false), (1706, true)]
theorem step10718 (p : Nat → Bool) (h : Constraints p) : clause p c10718 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8508] c10718 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8508 p h) (sat_nil p)))
def c10719 : List Lit := [(1686, true), (1803, true), (1644, false), (1819, true), (126, false), (117, true)]
theorem step10719 (p : Nat → Bool) (h : Constraints p) : clause p c10719 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8919] c10719 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8919 p h) (sat_nil p)))
def c10720 : List Lit := [(99, true), (1566, false), (122, false), (97, false), (42, false), (1812, true), (24, true), (45, false), (89, false), (1685, true), (126, true), (1803, false)]
theorem step10720 (p : Nat → Bool) (h : Constraints p) : clause p c10720 = true :=
  Snake9.LocalRup.prove_clause [c10426, c8813] c10720 (by decide) p (sat_cons (step10426 p h) (sat_cons (step8813 p h) (sat_nil p)))
def c10721 : List Lit := [(97, false), (96, true), (1644, true), (1720, false), (1738, false), (125, false), (1830, false), (93, true), (89, true), (86, true)]
theorem step10721 (p : Nat → Bool) (h : Constraints p) : clause p c10721 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8884] c10721 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8884 p h) (sat_nil p)))
def c10722 : List Lit := [(1819, false), (1782, false), (93, true), (86, true)]
theorem step10722 (p : Nat → Bool) (h : Constraints p) : clause p c10722 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8889] c10722 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8889 p h) (sat_nil p)))
def c10723 : List Lit := [(1819, false), (1831, true), (1803, true), (1720, false), (1781, false), (1644, true), (93, true), (86, true)]
theorem step10723 (p : Nat → Bool) (h : Constraints p) : clause p c10723 = true :=
  Snake9.LocalRup.prove_clause [c10429, c8923] c10723 (by decide) p (sat_cons (step10429 p h) (sat_cons (step8923 p h) (sat_nil p)))
def c10724 : List Lit := [(1622, true), (107, false)]
theorem step10724 (p : Nat → Bool) (h : Constraints p) : clause p c10724 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8942] c10724 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8942 p h) (sat_nil p)))
def c10725 : List Lit := [(114, false), (125, false), (37, true), (1737, false), (1760, true), (109, false), (1831, true), (115, false), (1687, true), (1820, true), (1644, false), (1803, false), (107, false), (117, true), (86, true)]
theorem step10725 (p : Nat → Bool) (h : Constraints p) : clause p c10725 = true :=
  Snake9.LocalRup.prove_clause [c10424, c8944] c10725 (by decide) p (sat_cons (step10424 p h) (sat_cons (step8944 p h) (sat_nil p)))
def c10726 : List Lit := [(1819, false), (1831, true), (86, true), (1803, true), (107, false), (93, true), (1644, true), (1781, false)]
theorem step10726 (p : Nat → Bool) (h : Constraints p) : clause p c10726 = true :=
  Snake9.LocalRup.prove_clause [c10429, c9035] c10726 (by decide) p (sat_cons (step10429 p h) (sat_cons (step9035 p h) (sat_nil p)))
def c10727 : List Lit := [(1686, true), (1644, false), (107, false), (117, false)]
theorem step10727 (p : Nat → Bool) (h : Constraints p) : clause p c10727 = true :=
  Snake9.LocalRup.prove_clause [c10424, c9060] c10727 (by decide) p (sat_cons (step10424 p h) (sat_cons (step9060 p h) (sat_nil p)))
def c10728 : List Lit := [(125, false), (1781, false), (93, true), (1818, false), (1760, true), (37, true), (1644, false), (117, false), (86, true)]
theorem step10728 (p : Nat → Bool) (h : Constraints p) : clause p c10728 = true :=
  Snake9.LocalRup.prove_clause [c10424, c9061] c10728 (by decide) p (sat_cons (step10424 p h) (sat_cons (step9061 p h) (sat_nil p)))
def c10729 : List Lit := [(1782, false), (1818, false), (93, true), (92, false), (1644, true), (117, false), (86, true)]
theorem step10729 (p : Nat → Bool) (h : Constraints p) : clause p c10729 = true :=
  Snake9.LocalRup.prove_clause [c10429, c9122] c10729 (by decide) p (sat_cons (step10429 p h) (sat_cons (step9122 p h) (sat_nil p)))
def c10730 : List Lit := [(114, true), (37, true), (1737, false), (1760, true), (1830, false), (1644, false), (117, false), (86, true)]
theorem step10730 (p : Nat → Bool) (h : Constraints p) : clause p c10730 = true :=
  Snake9.LocalRup.prove_clause [c10424, c9149] c10730 (by decide) p (sat_cons (step10424 p h) (sat_cons (step9149 p h) (sat_nil p)))
def c10731 : List Lit := [(72, false), (33, true), (1623, true), (117, false)]
theorem step10731 (p : Nat → Bool) (h : Constraints p) : clause p c10731 = true :=
  Snake9.LocalRup.prove_clause [c10424, c9163] c10731 (by decide) p (sat_cons (step10424 p h) (sat_cons (step9163 p h) (sat_nil p)))
def c10732 : List Lit := [(1685, true), (115, true), (1803, true)]
theorem step10732 (p : Nat → Bool) (h : Constraints p) : clause p c10732 = true :=
  Snake9.LocalRup.prove_clause [c10424, c9236] c10732 (by decide) p (sat_cons (step10424 p h) (sat_cons (step9236 p h) (sat_nil p)))
def c10733 : List Lit := [(42, false), (120, false), (1644, false), (89, false), (1686, true)]
theorem step10733 (p : Nat → Bool) (h : Constraints p) : clause p c10733 = true :=
  Snake9.LocalRup.prove_clause [c10424, c9267] c10733 (by decide) p (sat_cons (step10424 p h) (sat_cons (step9267 p h) (sat_nil p)))
def c10734 : List Lit := [(1633, false), (28, false), (1686, true), (1706, true), (1644, false)]
theorem step10734 (p : Nat → Bool) (h : Constraints p) : clause p c10734 = true :=
  Snake9.LocalRup.prove_clause [c10426, c9287] c10734 (by decide) p (sat_cons (step10426 p h) (sat_cons (step9287 p h) (sat_nil p)))
def c10735 : List Lit := [(1832, false), (88, true), (89, false), (37, true), (1854, true), (1803, true), (1644, false), (86, false)]
theorem step10735 (p : Nat → Bool) (h : Constraints p) : clause p c10735 = true :=
  Snake9.LocalRup.prove_clause [c10424, c9373] c10735 (by decide) p (sat_cons (step10424 p h) (sat_cons (step9373 p h) (sat_nil p)))
def c10736 : List Lit := [(1820, false), (1832, true), (107, true), (86, false), (1644, true)]
theorem step10736 (p : Nat → Bool) (h : Constraints p) : clause p c10736 = true :=
  Snake9.LocalRup.prove_clause [c10429, c9389] c10736 (by decide) p (sat_cons (step10429 p h) (sat_cons (step9389 p h) (sat_nil p)))
def c10737 : List Lit := [(120, true), (97, false), (126, true), (1685, true), (1813, true), (119, false)]
theorem step10737 (p : Nat → Bool) (h : Constraints p) : clause p c10737 = true :=
  Snake9.LocalRup.prove_clause [c10424, c9392] c10737 (by decide) p (sat_cons (step10424 p h) (sat_cons (step9392 p h) (sat_nil p)))
def c10738 : List Lit := [(89, true), (97, true), (1644, true), (93, true), (1819, false), (107, true), (86, false)]
theorem step10738 (p : Nat → Bool) (h : Constraints p) : clause p c10738 = true :=
  Snake9.LocalRup.prove_clause [c10429, c9393] c10738 (by decide) p (sat_cons (step10429 p h) (sat_cons (step9393 p h) (sat_nil p)))
end B112E034
