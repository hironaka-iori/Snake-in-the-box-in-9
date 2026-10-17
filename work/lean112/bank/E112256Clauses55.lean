import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec55 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1761 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1627 = true := by
  have hs : count1627 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1627)) (countLit q [-64]) (countLit q [-66]) (count1627 q) 1 (meaningNeg66 q) (meaning1627 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1761 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1627 = true := counterClause1761 (baseVal q)

theorem counterClause1762 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1627 = false ∨ valuationOf q 1630 = true := by
  have hs : count1629 q = (countLit q [-59]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-64, -66])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1630)) (countLit q [-59]) (countLit q [-64, -66]) (count1629 q) 1 1 (meaningNeg59 q) (meaning1627 q) (meaning1630 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1762 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1627 = false ∨ valuation q 1630 = true := counterClause1762 (baseVal q)

theorem counterClause1763 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1634 = true := by
  have hs : count1632 q = (countLit q [-55, -56]) + (countLit q [-59, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-55, -56]) (l₂ := [-59, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1634)) (countLit q [-55, -56]) (countLit q [-59, -64, -66]) (count1632 q) 1 2 (meaning1625 q) (meaning1630 q) (meaning1634 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1763 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1630 = false ∨ valuation q 1634 = true := counterClause1763 (baseVal q)

theorem counterClause1764 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-50, -51, -52, -54]) + (countLit q [-55, -56, -59, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -52, -54]) (l₂ := [-55, -56, -59, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1640)) (countLit q [-50, -51, -52, -54]) (countLit q [-55, -56, -59, -64, -66]) (count1637 q) 1 3 (meaning1621 q) (meaning1634 q) (meaning1640 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1764 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1634 = false ∨ valuation q 1640 = true := counterClause1764 (baseVal q)

theorem counterClause1765 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1653 = true := by
  have hs : count1646 q = (countLit q [-32, -35, -37, -38, -39, -40, -46, -48]) + (countLit q [-50, -51, -52, -54, -55, -56, -59, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -40, -46, -48]) (l₂ := [-50, -51, -52, -54, -55, -56, -59, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1653)) (countLit q [-32, -35, -37, -38, -39, -40, -46, -48]) (countLit q [-50, -51, -52, -54, -55, -56, -59, -64, -66]) (count1646 q) 4 4 (meaning1612 q) (meaning1640 q) (meaning1653 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1765 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1640 = false ∨ valuation q 1653 = true := counterClause1765 (baseVal q)

theorem counterClause1766 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1677 = true := by
  have hs : count1663 q = (countLit q [-3, -4, -6, -8, -9, -12, -13, -16, -17, -20, -22, -24, -26, -27, -29, -31]) + (countLit q [-32, -35, -37, -38, -39, -40, -46, -48, -50, -51, -52, -54, -55, -56, -59, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -9, -12, -13, -16, -17, -20, -22, -24, -26, -27, -29, -31]) (l₂ := [-32, -35, -37, -38, -39, -40, -46, -48, -50, -51, -52, -54, -55, -56, -59, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1677)) (countLit q [-3, -4, -6, -8, -9, -12, -13, -16, -17, -20, -22, -24, -26, -27, -29, -31]) (countLit q [-32, -35, -37, -38, -39, -40, -46, -48, -50, -51, -52, -54, -55, -56, -59, -64, -66]) (count1663 q) 7 8 (meaning1583 q) (meaning1653 q) (meaning1677 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1766 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1653 = false ∨ valuation q 1677 = true := counterClause1766 (baseVal q)

theorem counterClause1767 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1690 = true := by
  have hs : count1689 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1690)) (countLit q [-69]) (countLit q [-71]) (count1689 q) 1 1 (meaningNeg69 q) (meaningNeg71 q) (meaning1690 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1767 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 71 = true ∨ valuation q 1690 = true := counterClause1767 (baseVal q)

theorem counterClause1768 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1694 = true := by
  have hs : count1693 q = (countLit q [-69, -71]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-69, -71]) (l₂ := [-72, -73])
  have hm := merge_left (literal (valuationOf q) (1690)) (literal (valuationOf q) (1694)) (countLit q [-69, -71]) (countLit q [-72, -73]) (count1693 q) 2 (meaning1690 q) (meaning1694 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1768 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1694 = true := counterClause1768 (baseVal q)

theorem counterClause1769 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1699)) (countLit q [-80]) (countLit q [-81]) (count1699 q) 1 (meaningNeg81 q) (meaning1699 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1769 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1699 = true := counterClause1769 (baseVal q)

theorem counterClause1770 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1700)) (countLit q [-80]) (countLit q [-81]) (count1699 q) 1 1 (meaningNeg80 q) (meaningNeg81 q) (meaning1700 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1770 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 1700 = true := counterClause1770 (baseVal q)

theorem counterClause1771 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1701 = true := by
  have hs : count1701 q = (countLit q [-75, -77]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (1699)) (literal (valuationOf q) (1701)) (countLit q [-75, -77]) (countLit q [-80, -81]) (count1701 q) 1 (meaning1699 q) (meaning1701 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1771 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1701 = true := counterClause1771 (baseVal q)

theorem counterClause1772 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1702 = true := by
  have hs : count1701 q = (countLit q [-75, -77]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (1700)) (literal (valuationOf q) (1702)) (countLit q [-75, -77]) (countLit q [-80, -81]) (count1701 q) 2 (meaning1700 q) (meaning1702 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1772 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1702 = true := counterClause1772 (baseVal q)

theorem counterClause1773 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1707 = true := by
  have hs : count1705 q = (countLit q [-69, -71, -72, -73]) + (countLit q [-75, -77, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -72, -73]) (l₂ := [-75, -77, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1701)) (literal (valuationOf q) (1707)) (countLit q [-69, -71, -72, -73]) (countLit q [-75, -77, -80, -81]) (count1705 q) 2 1 (meaning1694 q) (meaning1701 q) (meaning1707 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1773 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1701 = false ∨ valuation q 1707 = true := counterClause1773 (baseVal q)

theorem counterClause1774 (q : Nat → Bool) : valuationOf q 1694 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1708 = true := by
  have hs : count1705 q = (countLit q [-69, -71, -72, -73]) + (countLit q [-75, -77, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -72, -73]) (l₂ := [-75, -77, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1694)) (literal (valuationOf q) (1702)) (literal (valuationOf q) (1708)) (countLit q [-69, -71, -72, -73]) (countLit q [-75, -77, -80, -81]) (count1705 q) 2 2 (meaning1694 q) (meaning1702 q) (meaning1708 q) hs
  change valuationOf q 1694 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1774 (q : Snake 81) (h : Conditions q) : valuation q 1694 = false ∨ valuation q 1702 = false ∨ valuation q 1708 = true := counterClause1774 (baseVal q)

theorem counterClause1775 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1715 = true := by
  have hs : count1715 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1715)) (countLit q [-86]) (countLit q [-87]) (count1715 q) 1 (meaningNeg86 q) (meaning1715 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1775 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1715 = true := counterClause1775 (baseVal q)

theorem counterClause1776 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1716 = true := by
  have hs : count1715 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1716)) (countLit q [-86]) (countLit q [-87]) (count1715 q) 1 1 (meaningNeg86 q) (meaningNeg87 q) (meaning1716 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1776 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 1716 = true := counterClause1776 (baseVal q)

theorem counterClause1777 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-82, -85]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-86, -87])
  have hm := merge_right (literal (valuationOf q) (1715)) (literal (valuationOf q) (1717)) (countLit q [-82, -85]) (countLit q [-86, -87]) (count1717 q) 1 (meaning1715 q) (meaning1717 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1777 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1717 = true := counterClause1777 (baseVal q)

theorem counterClause1778 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1718 = true := by
  have hs : count1717 q = (countLit q [-82, -85]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-86, -87])
  have hm := merge_right (literal (valuationOf q) (1716)) (literal (valuationOf q) (1718)) (countLit q [-82, -85]) (countLit q [-86, -87]) (count1717 q) 2 (meaning1716 q) (meaning1718 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1778 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1718 = true := counterClause1778 (baseVal q)

theorem counterClause1779 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1721 = true := by
  have hs : count1721 q = (countLit q [-89]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1721)) (countLit q [-89]) (countLit q [-92]) (count1721 q) 1 (meaningNeg92 q) (meaning1721 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1779 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1721 = true := counterClause1779 (baseVal q)

theorem counterClause1780 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1722 = true := by
  have hs : count1721 q = (countLit q [-89]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1722)) (countLit q [-89]) (countLit q [-92]) (count1721 q) 1 1 (meaningNeg89 q) (meaningNeg92 q) (meaning1722 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1780 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 92 = true ∨ valuation q 1722 = true := counterClause1780 (baseVal q)

theorem counterClause1781 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1723)) (countLit q [-94]) (countLit q [-95]) (count1723 q) 1 (meaningNeg95 q) (meaning1723 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1781 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1723 = true := counterClause1781 (baseVal q)

theorem counterClause1782 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1726 = true := by
  have hs : count1725 q = (countLit q [-89, -92]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-89, -92]) (l₂ := [-94, -95])
  have hm := merge_two (literal (valuationOf q) (1721)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1726)) (countLit q [-89, -92]) (countLit q [-94, -95]) (count1725 q) 1 1 (meaning1721 q) (meaning1723 q) (meaning1726 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1782 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1723 = false ∨ valuation q 1726 = true := counterClause1782 (baseVal q)

theorem counterClause1783 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-89, -92]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-89, -92]) (l₂ := [-94, -95])
  have hm := merge_two (literal (valuationOf q) (1722)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1727)) (countLit q [-89, -92]) (countLit q [-94, -95]) (count1725 q) 2 1 (meaning1722 q) (meaning1723 q) (meaning1727 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1783 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1723 = false ∨ valuation q 1727 = true := counterClause1783 (baseVal q)

theorem counterClause1784 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1731 = true := by
  have hs : count1729 q = (countLit q [-82, -85, -86, -87]) + (countLit q [-89, -92, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86, -87]) (l₂ := [-89, -92, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1731)) (countLit q [-82, -85, -86, -87]) (countLit q [-89, -92, -94, -95]) (count1729 q) 1 2 (meaning1717 q) (meaning1726 q) (meaning1731 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1784 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1726 = false ∨ valuation q 1731 = true := counterClause1784 (baseVal q)

theorem counterClause1785 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1732 = true := by
  have hs : count1729 q = (countLit q [-82, -85, -86, -87]) + (countLit q [-89, -92, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86, -87]) (l₂ := [-89, -92, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1727)) (literal (valuationOf q) (1732)) (countLit q [-82, -85, -86, -87]) (countLit q [-89, -92, -94, -95]) (count1729 q) 1 3 (meaning1717 q) (meaning1727 q) (meaning1732 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1785 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1727 = false ∨ valuation q 1732 = true := counterClause1785 (baseVal q)

theorem counterClause1786 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1732 = true := by
  have hs : count1729 q = (countLit q [-82, -85, -86, -87]) + (countLit q [-89, -92, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -85, -86, -87]) (l₂ := [-89, -92, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1718)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1732)) (countLit q [-82, -85, -86, -87]) (countLit q [-89, -92, -94, -95]) (count1729 q) 2 2 (meaning1718 q) (meaning1726 q) (meaning1732 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1786 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1726 = false ∨ valuation q 1732 = true := counterClause1786 (baseVal q)

theorem counterClause1787 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1743 = true := by
  have hs : count1737 q = (countLit q [-69, -71, -72, -73, -75, -77, -80, -81]) + (countLit q [-82, -85, -86, -87, -89, -92, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -72, -73, -75, -77, -80, -81]) (l₂ := [-82, -85, -86, -87, -89, -92, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1743)) (countLit q [-69, -71, -72, -73, -75, -77, -80, -81]) (countLit q [-82, -85, -86, -87, -89, -92, -94, -95]) (count1737 q) 3 4 (meaning1707 q) (meaning1732 q) (meaning1743 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1787 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1732 = false ∨ valuation q 1743 = true := counterClause1787 (baseVal q)

theorem counterClause1788 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1743 = true := by
  have hs : count1737 q = (countLit q [-69, -71, -72, -73, -75, -77, -80, -81]) + (countLit q [-82, -85, -86, -87, -89, -92, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -72, -73, -75, -77, -80, -81]) (l₂ := [-82, -85, -86, -87, -89, -92, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1708)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1743)) (countLit q [-69, -71, -72, -73, -75, -77, -80, -81]) (countLit q [-82, -85, -86, -87, -89, -92, -94, -95]) (count1737 q) 4 3 (meaning1708 q) (meaning1731 q) (meaning1743 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1788 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1731 = false ∨ valuation q 1743 = true := counterClause1788 (baseVal q)

theorem counterClause1789 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1755 = true := by
  have hs : count1755 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1755)) (countLit q [-99]) (countLit q [-100]) (count1755 q) 1 (meaningNeg100 q) (meaning1755 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1789 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1755 = true := counterClause1789 (baseVal q)

theorem counterClause1790 (q : Nat → Bool) : valuationOf q 1755 = false ∨ valuationOf q 1757 = true := by
  have hs : count1757 q = (countLit q [-97, -98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-97, -98]) (l₂ := [-99, -100])
  have hm := merge_right (literal (valuationOf q) (1755)) (literal (valuationOf q) (1757)) (countLit q [-97, -98]) (countLit q [-99, -100]) (count1757 q) 1 (meaning1755 q) (meaning1757 q) hs
  change valuationOf q 1755 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1790 (q : Snake 81) (h : Conditions q) : valuation q 1755 = false ∨ valuation q 1757 = true := counterClause1790 (baseVal q)

theorem counterClause1791 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1761 = true := by
  have hs : count1761 q = (countLit q [-102]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1761)) (countLit q [-102]) (countLit q [-104]) (count1761 q) 1 (meaningNeg102 q) (meaning1761 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1791 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1761 = true := counterClause1791 (baseVal q)

theorem counterClause1792 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1763 = true := by
  have hs : count1763 q = (countLit q [-107]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1763)) (countLit q [-107]) (countLit q [-110]) (count1763 q) 1 (meaningNeg107 q) (meaning1763 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1792 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1763 = true := counterClause1792 (baseVal q)

theorem block55 (q : Snake 81) (h : Conditions q) : B112E256.Block55 (valuation q) :=
  ⟨clause1761 q h, clause1762 q h, clause1763 q h, clause1764 q h, clause1765 q h, clause1766 q h, clause1767 q h, clause1768 q h, clause1769 q h, clause1770 q h, clause1771 q h, clause1772 q h, clause1773 q h, clause1774 q h, clause1775 q h, clause1776 q h, clause1777 q h, clause1778 q h, clause1779 q h, clause1780 q h, clause1781 q h, clause1782 q h, clause1783 q h, clause1784 q h, clause1785 q h, clause1786 q h, clause1787 q h, clause1788 q h, clause1789 q h, clause1790 q h, clause1791 q h, clause1792 q h⟩

end
end Snake9.Regrowth.E112256
