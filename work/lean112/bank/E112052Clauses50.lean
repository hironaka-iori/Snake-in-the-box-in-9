import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1601 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 95 = true ∨ valuationOf q 1730 = true := by
  have hs : count1729 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-95)) (literal (valuationOf q) (1730)) (countLit q [-94]) (countLit q [-95]) (count1729 q) 1 1 (meaningNeg94 q) (meaningNeg95 q) (meaning1730 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 95)) = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 95 = true ∨ valuation q 1730 = true := counterClause1601 (baseVal q)

theorem counterClause1602 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1731 = true := by
  have hs : count1731 q = (countLit q [-90, -91]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-94, -95])
  have hm := merge_right (literal (valuationOf q) (1729)) (literal (valuationOf q) (1731)) (countLit q [-90, -91]) (countLit q [-94, -95]) (count1731 q) 1 (meaning1729 q) (meaning1731 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1731 = true := counterClause1602 (baseVal q)

theorem counterClause1603 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1732 = true := by
  have hs : count1731 q = (countLit q [-90, -91]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-94, -95])
  have hm := merge_right (literal (valuationOf q) (1730)) (literal (valuationOf q) (1732)) (countLit q [-90, -91]) (countLit q [-94, -95]) (count1731 q) 2 (meaning1730 q) (meaning1732 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1732 = true := counterClause1603 (baseVal q)

theorem counterClause1604 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1731 = true := by
  have hs : count1731 q = (countLit q [-90, -91]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-94, -95])
  have hm := merge_left (literal (valuationOf q) (1727)) (literal (valuationOf q) (1731)) (countLit q [-90, -91]) (countLit q [-94, -95]) (count1731 q) 1 (meaning1727 q) (meaning1731 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1731 = true := counterClause1604 (baseVal q)

theorem counterClause1605 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1732 = true := by
  have hs : count1731 q = (countLit q [-90, -91]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-94, -95])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1729)) (literal (valuationOf q) (1732)) (countLit q [-90, -91]) (countLit q [-94, -95]) (count1731 q) 1 1 (meaning1727 q) (meaning1729 q) (meaning1732 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1729 = false ∨ valuation q 1732 = true := counterClause1605 (baseVal q)

theorem counterClause1606 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1733 = true := by
  have hs : count1731 q = (countLit q [-90, -91]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-94, -95])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1730)) (literal (valuationOf q) (1733)) (countLit q [-90, -91]) (countLit q [-94, -95]) (count1731 q) 1 2 (meaning1727 q) (meaning1730 q) (meaning1733 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1730 = false ∨ valuation q 1733 = true := counterClause1606 (baseVal q)

theorem counterClause1607 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1732 = true := by
  have hs : count1731 q = (countLit q [-90, -91]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-94, -95])
  have hm := merge_left (literal (valuationOf q) (1728)) (literal (valuationOf q) (1732)) (countLit q [-90, -91]) (countLit q [-94, -95]) (count1731 q) 2 (meaning1728 q) (meaning1732 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1732 = true := counterClause1607 (baseVal q)

theorem counterClause1608 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1733 = true := by
  have hs : count1731 q = (countLit q [-90, -91]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-94, -95])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1729)) (literal (valuationOf q) (1733)) (countLit q [-90, -91]) (countLit q [-94, -95]) (count1731 q) 2 1 (meaning1728 q) (meaning1729 q) (meaning1733 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1729 = false ∨ valuation q 1733 = true := counterClause1608 (baseVal q)

theorem counterClause1609 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1734 = true := by
  have hs : count1731 q = (countLit q [-90, -91]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-94, -95])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1730)) (literal (valuationOf q) (1734)) (countLit q [-90, -91]) (countLit q [-94, -95]) (count1731 q) 2 2 (meaning1728 q) (meaning1730 q) (meaning1734 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1730 = false ∨ valuation q 1734 = true := counterClause1609 (baseVal q)

theorem counterClause1610 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_right (literal (valuationOf q) (1731)) (literal (valuationOf q) (1735)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 1 (meaning1731 q) (meaning1735 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1735 = true := counterClause1610 (baseVal q)

theorem counterClause1611 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_right (literal (valuationOf q) (1732)) (literal (valuationOf q) (1736)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 2 (meaning1732 q) (meaning1736 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1736 = true := counterClause1611 (baseVal q)

theorem counterClause1612 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1737 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_right (literal (valuationOf q) (1733)) (literal (valuationOf q) (1737)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 3 (meaning1733 q) (meaning1737 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1612 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1737 = true := counterClause1612 (baseVal q)

theorem counterClause1613 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1738 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_right (literal (valuationOf q) (1734)) (literal (valuationOf q) (1738)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 4 (meaning1734 q) (meaning1738 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1613 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1738 = true := counterClause1613 (baseVal q)

theorem counterClause1614 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_left (literal (valuationOf q) (1723)) (literal (valuationOf q) (1735)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 1 (meaning1723 q) (meaning1735 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1614 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1735 = true := counterClause1614 (baseVal q)

theorem counterClause1615 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1736)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 1 1 (meaning1723 q) (meaning1731 q) (meaning1736 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1615 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1731 = false ∨ valuation q 1736 = true := counterClause1615 (baseVal q)

theorem counterClause1616 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1737 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1737)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 1 2 (meaning1723 q) (meaning1732 q) (meaning1737 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1616 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1732 = false ∨ valuation q 1737 = true := counterClause1616 (baseVal q)

theorem counterClause1617 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1738 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1738)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 1 3 (meaning1723 q) (meaning1733 q) (meaning1738 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1617 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1733 = false ∨ valuation q 1738 = true := counterClause1617 (baseVal q)

theorem counterClause1618 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1739 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1739)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 1 4 (meaning1723 q) (meaning1734 q) (meaning1739 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1618 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1734 = false ∨ valuation q 1739 = true := counterClause1618 (baseVal q)

theorem counterClause1619 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_left (literal (valuationOf q) (1724)) (literal (valuationOf q) (1736)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 2 (meaning1724 q) (meaning1736 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1619 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1736 = true := counterClause1619 (baseVal q)

theorem counterClause1620 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1737 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1737)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 2 1 (meaning1724 q) (meaning1731 q) (meaning1737 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1620 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1731 = false ∨ valuation q 1737 = true := counterClause1620 (baseVal q)

theorem counterClause1621 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1738 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1738)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 2 2 (meaning1724 q) (meaning1732 q) (meaning1738 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1621 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1732 = false ∨ valuation q 1738 = true := counterClause1621 (baseVal q)

theorem counterClause1622 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1739 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1739)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 2 3 (meaning1724 q) (meaning1733 q) (meaning1739 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1622 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1733 = false ∨ valuation q 1739 = true := counterClause1622 (baseVal q)

theorem counterClause1623 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1740 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1740)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 2 4 (meaning1724 q) (meaning1734 q) (meaning1740 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1740 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1623 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1734 = false ∨ valuation q 1740 = true := counterClause1623 (baseVal q)

theorem counterClause1624 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1737 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_left (literal (valuationOf q) (1725)) (literal (valuationOf q) (1737)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 3 (meaning1725 q) (meaning1737 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1624 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1737 = true := counterClause1624 (baseVal q)

theorem counterClause1625 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1738 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1738)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 3 1 (meaning1725 q) (meaning1731 q) (meaning1738 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1625 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1731 = false ∨ valuation q 1738 = true := counterClause1625 (baseVal q)

theorem counterClause1626 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1739 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1739)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 3 2 (meaning1725 q) (meaning1732 q) (meaning1739 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1626 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1732 = false ∨ valuation q 1739 = true := counterClause1626 (baseVal q)

theorem counterClause1627 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1740 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1740)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 3 3 (meaning1725 q) (meaning1733 q) (meaning1740 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1740 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1627 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1733 = false ∨ valuation q 1740 = true := counterClause1627 (baseVal q)

theorem counterClause1628 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1741 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1741)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 3 4 (meaning1725 q) (meaning1734 q) (meaning1741 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1628 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1734 = false ∨ valuation q 1741 = true := counterClause1628 (baseVal q)

theorem counterClause1629 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1738 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_left (literal (valuationOf q) (1726)) (literal (valuationOf q) (1738)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 4 (meaning1726 q) (meaning1738 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1629 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1738 = true := counterClause1629 (baseVal q)

theorem counterClause1630 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1739 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1739)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 4 1 (meaning1726 q) (meaning1731 q) (meaning1739 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1630 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1731 = false ∨ valuation q 1739 = true := counterClause1630 (baseVal q)

theorem counterClause1631 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1740 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1740)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 4 2 (meaning1726 q) (meaning1732 q) (meaning1740 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1740 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1631 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1732 = false ∨ valuation q 1740 = true := counterClause1631 (baseVal q)

theorem counterClause1632 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1741 = true := by
  have hs : count1735 q = (countLit q [-82, -84, -86, -87]) + (countLit q [-90, -91, -94, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -84, -86, -87]) (l₂ := [-90, -91, -94, -95])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1741)) (countLit q [-82, -84, -86, -87]) (countLit q [-90, -91, -94, -95]) (count1735 q) 4 3 (meaning1726 q) (meaning1733 q) (meaning1741 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1632 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1733 = false ∨ valuation q 1741 = true := counterClause1632 (baseVal q)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E052.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h, clause1612 q h, clause1613 q h, clause1614 q h, clause1615 q h, clause1616 q h, clause1617 q h, clause1618 q h, clause1619 q h, clause1620 q h, clause1621 q h, clause1622 q h, clause1623 q h, clause1624 q h, clause1625 q h, clause1626 q h, clause1627 q h, clause1628 q h, clause1629 q h, clause1630 q h, clause1631 q h, clause1632 q h⟩

end
end Snake9.Regrowth.E112052
