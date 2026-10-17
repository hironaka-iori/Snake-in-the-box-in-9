import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1760 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1760)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 2 2 (meaning1746 q) (meaning1754 q) (meaning1760 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1754 = false ∨ valuation q 1760 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1761 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1761)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 2 3 (meaning1746 q) (meaning1755 q) (meaning1761 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1755 = false ∨ valuation q 1761 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1762 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1762)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 2 4 (meaning1746 q) (meaning1756 q) (meaning1762 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1756 = false ∨ valuation q 1762 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1759 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_left (literal (valuationOf q) (1747)) (literal (valuationOf q) (1759)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 3 (meaning1747 q) (meaning1759 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1759 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1760 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1760)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 3 1 (meaning1747 q) (meaning1753 q) (meaning1760 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1753 = false ∨ valuation q 1760 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1761 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1761)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 3 2 (meaning1747 q) (meaning1754 q) (meaning1761 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1754 = false ∨ valuation q 1761 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1762 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1762)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 3 3 (meaning1747 q) (meaning1755 q) (meaning1762 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1755 = false ∨ valuation q 1762 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1763 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1763)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 3 4 (meaning1747 q) (meaning1756 q) (meaning1763 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1756 = false ∨ valuation q 1763 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1760 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_left (literal (valuationOf q) (1748)) (literal (valuationOf q) (1760)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 4 (meaning1748 q) (meaning1760 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1760 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1761 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1748)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1761)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 4 1 (meaning1748 q) (meaning1753 q) (meaning1761 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1753 = false ∨ valuation q 1761 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1762 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1748)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1762)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 4 2 (meaning1748 q) (meaning1754 q) (meaning1762 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1754 = false ∨ valuation q 1762 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1763 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1748)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1763)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 4 3 (meaning1748 q) (meaning1755 q) (meaning1763 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1755 = false ∨ valuation q 1763 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1764 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1748)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1764)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 4 4 (meaning1748 q) (meaning1756 q) (meaning1764 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1756 = false ∨ valuation q 1764 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 1762 = false ∨ valuationOf q 1770 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_right (literal (valuationOf q) (1762)) (literal (valuationOf q) (1770)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 6 (meaning1762 q) (meaning1770 q) hs
  change valuationOf q 1762 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false ∨ valuation q 1770 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1767 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1767)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 1 2 (meaning1733 q) (meaning1758 q) (meaning1767 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1758 = false ∨ valuation q 1767 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1768 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1768)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 1 3 (meaning1733 q) (meaning1759 q) (meaning1768 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1759 = false ∨ valuation q 1768 = true := counterClause1648 (baseVal q)

theorem counterClause1649 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1769 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1769)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 1 4 (meaning1733 q) (meaning1760 q) (meaning1769 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1760 = false ∨ valuation q 1769 = true := counterClause1649 (baseVal q)

theorem counterClause1650 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1770 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1770)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 1 5 (meaning1733 q) (meaning1761 q) (meaning1770 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1761 = false ∨ valuation q 1770 = true := counterClause1650 (baseVal q)

theorem counterClause1651 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1771 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1771)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 1 6 (meaning1733 q) (meaning1762 q) (meaning1771 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1762 = false ∨ valuation q 1771 = true := counterClause1651 (baseVal q)

theorem counterClause1652 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1772 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1772)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 1 7 (meaning1733 q) (meaning1763 q) (meaning1772 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1763 = false ∨ valuation q 1772 = true := counterClause1652 (baseVal q)

theorem counterClause1653 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1773 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1773)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 1 8 (meaning1733 q) (meaning1764 q) (meaning1773 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1764 = false ∨ valuation q 1773 = true := counterClause1653 (baseVal q)

theorem counterClause1654 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1767 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1767)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 2 1 (meaning1734 q) (meaning1757 q) (meaning1767 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1757 = false ∨ valuation q 1767 = true := counterClause1654 (baseVal q)

theorem counterClause1655 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1768 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1768)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 2 2 (meaning1734 q) (meaning1758 q) (meaning1768 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1758 = false ∨ valuation q 1768 = true := counterClause1655 (baseVal q)

theorem counterClause1656 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1769 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1769)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 2 3 (meaning1734 q) (meaning1759 q) (meaning1769 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1759 = false ∨ valuation q 1769 = true := counterClause1656 (baseVal q)

theorem counterClause1657 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1770 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1770)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 2 4 (meaning1734 q) (meaning1760 q) (meaning1770 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1760 = false ∨ valuation q 1770 = true := counterClause1657 (baseVal q)

theorem counterClause1658 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1771 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1771)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 2 5 (meaning1734 q) (meaning1761 q) (meaning1771 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1761 = false ∨ valuation q 1771 = true := counterClause1658 (baseVal q)

theorem counterClause1659 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1772 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1772)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 2 6 (meaning1734 q) (meaning1762 q) (meaning1772 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1762 = false ∨ valuation q 1772 = true := counterClause1659 (baseVal q)

theorem counterClause1660 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1773 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1773)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 2 7 (meaning1734 q) (meaning1763 q) (meaning1773 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1763 = false ∨ valuation q 1773 = true := counterClause1660 (baseVal q)

theorem counterClause1661 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1774 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1774)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 2 8 (meaning1734 q) (meaning1764 q) (meaning1774 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1764 = false ∨ valuation q 1774 = true := counterClause1661 (baseVal q)

theorem counterClause1662 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1767 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_left (literal (valuationOf q) (1735)) (literal (valuationOf q) (1767)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 3 (meaning1735 q) (meaning1767 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1767 = true := counterClause1662 (baseVal q)

theorem counterClause1663 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1768 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1768)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 3 1 (meaning1735 q) (meaning1757 q) (meaning1768 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1757 = false ∨ valuation q 1768 = true := counterClause1663 (baseVal q)

theorem counterClause1664 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1769 = true := by
  have hs : count1765 q = (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) + (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-64, -67, -69, -71, -72, -75, -77, -79]) (l₂ := [-81, -82, -85, -86, -89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1769)) (countLit q [-64, -67, -69, -71, -72, -75, -77, -79]) (countLit q [-81, -82, -85, -86, -89, -93, -94, -98]) (count1765 q) 3 2 (meaning1735 q) (meaning1758 q) (meaning1769 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1758 = false ∨ valuation q 1769 = true := counterClause1664 (baseVal q)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E055.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112055
