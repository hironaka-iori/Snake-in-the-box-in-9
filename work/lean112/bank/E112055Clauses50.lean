import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1601 (q : Nat → Bool) : valuationOf q 1744 = false ∨ valuationOf q 1746 = true := by
  have hs : count1745 q = (countLit q [-81, -82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1744)) (literal (valuationOf q) (1746)) (countLit q [-81, -82]) (countLit q [-85, -86]) (count1745 q) 2 (meaning1744 q) (meaning1746 q) hs
  change valuationOf q 1744 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false ∨ valuation q 1746 = true := counterClause1601 (baseVal q)

theorem counterClause1602 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1745 = true := by
  have hs : count1745 q = (countLit q [-81, -82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (1741)) (literal (valuationOf q) (1745)) (countLit q [-81, -82]) (countLit q [-85, -86]) (count1745 q) 1 (meaning1741 q) (meaning1745 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1745 = true := counterClause1602 (baseVal q)

theorem counterClause1603 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1746 = true := by
  have hs : count1745 q = (countLit q [-81, -82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1741)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1746)) (countLit q [-81, -82]) (countLit q [-85, -86]) (count1745 q) 1 1 (meaning1741 q) (meaning1743 q) (meaning1746 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1743 = false ∨ valuation q 1746 = true := counterClause1603 (baseVal q)

theorem counterClause1604 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1747 = true := by
  have hs : count1745 q = (countLit q [-81, -82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1741)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1747)) (countLit q [-81, -82]) (countLit q [-85, -86]) (count1745 q) 1 2 (meaning1741 q) (meaning1744 q) (meaning1747 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1744 = false ∨ valuation q 1747 = true := counterClause1604 (baseVal q)

theorem counterClause1605 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1746 = true := by
  have hs : count1745 q = (countLit q [-81, -82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (1742)) (literal (valuationOf q) (1746)) (countLit q [-81, -82]) (countLit q [-85, -86]) (count1745 q) 2 (meaning1742 q) (meaning1746 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1746 = true := counterClause1605 (baseVal q)

theorem counterClause1606 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1747 = true := by
  have hs : count1745 q = (countLit q [-81, -82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1742)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1747)) (countLit q [-81, -82]) (countLit q [-85, -86]) (count1745 q) 2 1 (meaning1742 q) (meaning1743 q) (meaning1747 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1743 = false ∨ valuation q 1747 = true := counterClause1606 (baseVal q)

theorem counterClause1607 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1748 = true := by
  have hs : count1745 q = (countLit q [-81, -82]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1742)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1748)) (countLit q [-81, -82]) (countLit q [-85, -86]) (count1745 q) 2 2 (meaning1742 q) (meaning1744 q) (meaning1748 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1744 = false ∨ valuation q 1748 = true := counterClause1607 (baseVal q)

theorem counterClause1608 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1749 = true := by
  have hs : count1749 q = (countLit q [-89]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1749)) (countLit q [-89]) (countLit q [-93]) (count1749 q) 1 (meaningNeg93 q) (meaning1749 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1749 = true := counterClause1608 (baseVal q)

theorem counterClause1609 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1749 = true := by
  have hs : count1749 q = (countLit q [-89]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1749)) (countLit q [-89]) (countLit q [-93]) (count1749 q) 1 (meaningNeg89 q) (meaning1749 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1749 = true := counterClause1609 (baseVal q)

theorem counterClause1610 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1750 = true := by
  have hs : count1749 q = (countLit q [-89]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1750)) (countLit q [-89]) (countLit q [-93]) (count1749 q) 1 1 (meaningNeg89 q) (meaningNeg93 q) (meaning1750 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 93 = true ∨ valuation q 1750 = true := counterClause1610 (baseVal q)

theorem counterClause1611 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1751 = true := by
  have hs : count1751 q = (countLit q [-94]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1751)) (countLit q [-94]) (countLit q [-98]) (count1751 q) 1 (meaningNeg98 q) (meaning1751 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1751 = true := counterClause1611 (baseVal q)

theorem counterClause1612 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1751 = true := by
  have hs : count1751 q = (countLit q [-94]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1751)) (countLit q [-94]) (countLit q [-98]) (count1751 q) 1 (meaningNeg94 q) (meaning1751 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1612 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1751 = true := counterClause1612 (baseVal q)

theorem counterClause1613 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1752 = true := by
  have hs : count1751 q = (countLit q [-94]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1752)) (countLit q [-94]) (countLit q [-98]) (count1751 q) 1 1 (meaningNeg94 q) (meaningNeg98 q) (meaning1752 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1613 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 98 = true ∨ valuation q 1752 = true := counterClause1613 (baseVal q)

theorem counterClause1614 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1753 = true := by
  have hs : count1753 q = (countLit q [-89, -93]) + (countLit q [-94, -98]) := List.countP_append (p := literal q) (l₁ := [-89, -93]) (l₂ := [-94, -98])
  have hm := merge_right (literal (valuationOf q) (1751)) (literal (valuationOf q) (1753)) (countLit q [-89, -93]) (countLit q [-94, -98]) (count1753 q) 1 (meaning1751 q) (meaning1753 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1614 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1753 = true := counterClause1614 (baseVal q)

theorem counterClause1615 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1754 = true := by
  have hs : count1753 q = (countLit q [-89, -93]) + (countLit q [-94, -98]) := List.countP_append (p := literal q) (l₁ := [-89, -93]) (l₂ := [-94, -98])
  have hm := merge_right (literal (valuationOf q) (1752)) (literal (valuationOf q) (1754)) (countLit q [-89, -93]) (countLit q [-94, -98]) (count1753 q) 2 (meaning1752 q) (meaning1754 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1615 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1754 = true := counterClause1615 (baseVal q)

theorem counterClause1616 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1753 = true := by
  have hs : count1753 q = (countLit q [-89, -93]) + (countLit q [-94, -98]) := List.countP_append (p := literal q) (l₁ := [-89, -93]) (l₂ := [-94, -98])
  have hm := merge_left (literal (valuationOf q) (1749)) (literal (valuationOf q) (1753)) (countLit q [-89, -93]) (countLit q [-94, -98]) (count1753 q) 1 (meaning1749 q) (meaning1753 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1616 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1753 = true := counterClause1616 (baseVal q)

theorem counterClause1617 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1754 = true := by
  have hs : count1753 q = (countLit q [-89, -93]) + (countLit q [-94, -98]) := List.countP_append (p := literal q) (l₁ := [-89, -93]) (l₂ := [-94, -98])
  have hm := merge_two (literal (valuationOf q) (1749)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1754)) (countLit q [-89, -93]) (countLit q [-94, -98]) (count1753 q) 1 1 (meaning1749 q) (meaning1751 q) (meaning1754 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1617 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1751 = false ∨ valuation q 1754 = true := counterClause1617 (baseVal q)

theorem counterClause1618 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1755 = true := by
  have hs : count1753 q = (countLit q [-89, -93]) + (countLit q [-94, -98]) := List.countP_append (p := literal q) (l₁ := [-89, -93]) (l₂ := [-94, -98])
  have hm := merge_two (literal (valuationOf q) (1749)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1755)) (countLit q [-89, -93]) (countLit q [-94, -98]) (count1753 q) 1 2 (meaning1749 q) (meaning1752 q) (meaning1755 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1618 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1752 = false ∨ valuation q 1755 = true := counterClause1618 (baseVal q)

theorem counterClause1619 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1754 = true := by
  have hs : count1753 q = (countLit q [-89, -93]) + (countLit q [-94, -98]) := List.countP_append (p := literal q) (l₁ := [-89, -93]) (l₂ := [-94, -98])
  have hm := merge_left (literal (valuationOf q) (1750)) (literal (valuationOf q) (1754)) (countLit q [-89, -93]) (countLit q [-94, -98]) (count1753 q) 2 (meaning1750 q) (meaning1754 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1619 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1754 = true := counterClause1619 (baseVal q)

theorem counterClause1620 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1755 = true := by
  have hs : count1753 q = (countLit q [-89, -93]) + (countLit q [-94, -98]) := List.countP_append (p := literal q) (l₁ := [-89, -93]) (l₂ := [-94, -98])
  have hm := merge_two (literal (valuationOf q) (1750)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1755)) (countLit q [-89, -93]) (countLit q [-94, -98]) (count1753 q) 2 1 (meaning1750 q) (meaning1751 q) (meaning1755 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1620 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1751 = false ∨ valuation q 1755 = true := counterClause1620 (baseVal q)

theorem counterClause1621 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1756 = true := by
  have hs : count1753 q = (countLit q [-89, -93]) + (countLit q [-94, -98]) := List.countP_append (p := literal q) (l₁ := [-89, -93]) (l₂ := [-94, -98])
  have hm := merge_two (literal (valuationOf q) (1750)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1756)) (countLit q [-89, -93]) (countLit q [-94, -98]) (count1753 q) 2 2 (meaning1750 q) (meaning1752 q) (meaning1756 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1621 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1752 = false ∨ valuation q 1756 = true := counterClause1621 (baseVal q)

theorem counterClause1622 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1757 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_right (literal (valuationOf q) (1753)) (literal (valuationOf q) (1757)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 1 (meaning1753 q) (meaning1757 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1622 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1757 = true := counterClause1622 (baseVal q)

theorem counterClause1623 (q : Nat → Bool) : valuationOf q 1754 = false ∨ valuationOf q 1758 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_right (literal (valuationOf q) (1754)) (literal (valuationOf q) (1758)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 2 (meaning1754 q) (meaning1758 q) hs
  change valuationOf q 1754 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1623 (q : Snake 81) (h : Conditions q) : valuation q 1754 = false ∨ valuation q 1758 = true := counterClause1623 (baseVal q)

theorem counterClause1624 (q : Nat → Bool) : valuationOf q 1755 = false ∨ valuationOf q 1759 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_right (literal (valuationOf q) (1755)) (literal (valuationOf q) (1759)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 3 (meaning1755 q) (meaning1759 q) hs
  change valuationOf q 1755 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1624 (q : Snake 81) (h : Conditions q) : valuation q 1755 = false ∨ valuation q 1759 = true := counterClause1624 (baseVal q)

theorem counterClause1625 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1760 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_right (literal (valuationOf q) (1756)) (literal (valuationOf q) (1760)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 4 (meaning1756 q) (meaning1760 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1625 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1760 = true := counterClause1625 (baseVal q)

theorem counterClause1626 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1757 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_left (literal (valuationOf q) (1745)) (literal (valuationOf q) (1757)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 1 (meaning1745 q) (meaning1757 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1626 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1757 = true := counterClause1626 (baseVal q)

theorem counterClause1627 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1758 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1745)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1758)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 1 1 (meaning1745 q) (meaning1753 q) (meaning1758 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1627 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1753 = false ∨ valuation q 1758 = true := counterClause1627 (baseVal q)

theorem counterClause1628 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1759 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1745)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1759)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 1 2 (meaning1745 q) (meaning1754 q) (meaning1759 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1628 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1754 = false ∨ valuation q 1759 = true := counterClause1628 (baseVal q)

theorem counterClause1629 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1760 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1745)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1760)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 1 3 (meaning1745 q) (meaning1755 q) (meaning1760 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1629 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1755 = false ∨ valuation q 1760 = true := counterClause1629 (baseVal q)

theorem counterClause1630 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1761 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1745)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1761)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 1 4 (meaning1745 q) (meaning1756 q) (meaning1761 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1630 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1756 = false ∨ valuation q 1761 = true := counterClause1630 (baseVal q)

theorem counterClause1631 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1758 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_left (literal (valuationOf q) (1746)) (literal (valuationOf q) (1758)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 2 (meaning1746 q) (meaning1758 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1631 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1758 = true := counterClause1631 (baseVal q)

theorem counterClause1632 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1759 = true := by
  have hs : count1757 q = (countLit q [-81, -82, -85, -86]) + (countLit q [-89, -93, -94, -98]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -85, -86]) (l₂ := [-89, -93, -94, -98])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1759)) (countLit q [-81, -82, -85, -86]) (countLit q [-89, -93, -94, -98]) (count1757 q) 2 1 (meaning1746 q) (meaning1753 q) (meaning1759 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1632 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1753 = false ∨ valuation q 1759 = true := counterClause1632 (baseVal q)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E055.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h, clause1612 q h, clause1613 q h, clause1614 q h, clause1615 q h, clause1616 q h, clause1617 q h, clause1618 q h, clause1619 q h, clause1620 q h, clause1621 q h, clause1622 q h, clause1623 q h, clause1624 q h, clause1625 q h, clause1626 q h, clause1627 q h, clause1628 q h, clause1629 q h, clause1630 q h, clause1631 q h, clause1632 q h⟩

end
end Snake9.Regrowth.E112055
