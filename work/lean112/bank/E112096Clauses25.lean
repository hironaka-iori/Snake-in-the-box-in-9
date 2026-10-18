import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-80, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-80, -81]) (countLit q [-85, -86]) (count1583 q) 1 (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1583 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-80, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1584)) (countLit q [-80, -81]) (countLit q [-85, -86]) (count1583 q) 1 1 (meaning1579 q) (meaning1581 q) (meaning1584 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1581 = false ∨ valuation q 1584 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true := by
  have hs : count1583 q = (countLit q [-80, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1585)) (countLit q [-80, -81]) (countLit q [-85, -86]) (count1583 q) 1 2 (meaning1579 q) (meaning1582 q) (meaning1585 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1582 = false ∨ valuation q 1585 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-80, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-80, -81]) (countLit q [-85, -86]) (count1583 q) 2 (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1584 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1583 q = (countLit q [-80, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-80, -81]) (countLit q [-85, -86]) (count1583 q) 2 1 (meaning1580 q) (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1581 = false ∨ valuation q 1585 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1586 = true := by
  have hs : count1583 q = (countLit q [-80, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-80, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1586)) (countLit q [-80, -81]) (countLit q [-85, -86]) (count1583 q) 2 2 (meaning1580 q) (meaning1582 q) (meaning1586 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1582 = false ∨ valuation q 1586 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_right (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 1 (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1587 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_right (literal (valuationOf q) (1584)) (literal (valuationOf q) (1588)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 2 (meaning1584 q) (meaning1588 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1588 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_right (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 3 (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1589 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_right (literal (valuationOf q) (1586)) (literal (valuationOf q) (1590)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 4 (meaning1586 q) (meaning1590 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1590 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1587)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 1 (meaning1575 q) (meaning1587 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1587 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1588)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 1 1 (meaning1575 q) (meaning1583 q) (meaning1588 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1583 = false ∨ valuation q 1588 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1589)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 1 2 (meaning1575 q) (meaning1584 q) (meaning1589 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1584 = false ∨ valuation q 1589 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1590)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 1 3 (meaning1575 q) (meaning1585 q) (meaning1590 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1585 = false ∨ valuation q 1590 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1591 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1591)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 1 4 (meaning1575 q) (meaning1586 q) (meaning1591 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1586 = false ∨ valuation q 1591 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_left (literal (valuationOf q) (1576)) (literal (valuationOf q) (1588)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 2 (meaning1576 q) (meaning1588 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1588 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1589)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 2 1 (meaning1576 q) (meaning1583 q) (meaning1589 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1583 = false ∨ valuation q 1589 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1590)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 2 2 (meaning1576 q) (meaning1584 q) (meaning1590 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1584 = false ∨ valuation q 1590 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1591 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1591)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 2 3 (meaning1576 q) (meaning1585 q) (meaning1591 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1585 = false ∨ valuation q 1591 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_left (literal (valuationOf q) (1577)) (literal (valuationOf q) (1589)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 3 (meaning1577 q) (meaning1589 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1589 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1590)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 3 1 (meaning1577 q) (meaning1583 q) (meaning1590 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1583 = false ∨ valuation q 1590 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1591 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1591)) (countLit q [-72, -73, -77, -78]) (countLit q [-80, -81, -85, -86]) (count1587 q) 3 2 (meaning1577 q) (meaning1584 q) (meaning1591 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1584 = false ∨ valuation q 1591 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1596)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 1 1 (meaning1564 q) (meaning1587 q) (meaning1596 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1587 = false ∨ valuation q 1596 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1597)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 1 2 (meaning1564 q) (meaning1588 q) (meaning1597 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1588 = false ∨ valuation q 1597 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1598)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 1 3 (meaning1564 q) (meaning1589 q) (meaning1598 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1589 = false ∨ valuation q 1598 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1599)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 1 4 (meaning1564 q) (meaning1590 q) (meaning1599 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1590 = false ∨ valuation q 1599 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1597)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 2 1 (meaning1565 q) (meaning1587 q) (meaning1597 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1587 = false ∨ valuation q 1597 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1598)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 2 2 (meaning1565 q) (meaning1588 q) (meaning1598 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1588 = false ∨ valuation q 1598 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1599)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 2 3 (meaning1565 q) (meaning1589 q) (meaning1599 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1589 = false ∨ valuation q 1599 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1600)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 2 4 (meaning1565 q) (meaning1590 q) (meaning1600 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1590 = false ∨ valuation q 1600 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1601 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1601)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 2 5 (meaning1565 q) (meaning1591 q) (meaning1601 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1591 = false ∨ valuation q 1601 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1598)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 3 1 (meaning1566 q) (meaning1587 q) (meaning1598 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1587 = false ∨ valuation q 1598 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E096.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112096
