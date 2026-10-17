import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1590)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 1 3 (meaning1575 q) (meaning1585 q) (meaning1590 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1585 = false ∨ valuation q 1590 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_left (literal (valuationOf q) (1576)) (literal (valuationOf q) (1588)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 2 (meaning1576 q) (meaning1588 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1588 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1589)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 2 1 (meaning1576 q) (meaning1583 q) (meaning1589 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1583 = false ∨ valuation q 1589 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1590)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 2 2 (meaning1576 q) (meaning1584 q) (meaning1590 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1584 = false ∨ valuation q 1590 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1591 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1591)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 2 3 (meaning1576 q) (meaning1585 q) (meaning1591 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1585 = false ∨ valuation q 1591 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1592 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1592)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 2 4 (meaning1576 q) (meaning1586 q) (meaning1592 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1586 = false ∨ valuation q 1592 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_left (literal (valuationOf q) (1577)) (literal (valuationOf q) (1589)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 3 (meaning1577 q) (meaning1589 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1589 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1590)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 3 1 (meaning1577 q) (meaning1583 q) (meaning1590 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1583 = false ∨ valuation q 1590 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1591 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1591)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 3 2 (meaning1577 q) (meaning1584 q) (meaning1591 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1584 = false ∨ valuation q 1591 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1592 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1592)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 3 3 (meaning1577 q) (meaning1585 q) (meaning1592 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1585 = false ∨ valuation q 1592 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_left (literal (valuationOf q) (1578)) (literal (valuationOf q) (1590)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 4 (meaning1578 q) (meaning1590 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1590 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1591 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1591)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 4 1 (meaning1578 q) (meaning1583 q) (meaning1591 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1583 = false ∨ valuation q 1591 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1598)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 4 (meaning1590 q) (meaning1598 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1598 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_right (literal (valuationOf q) (1591)) (literal (valuationOf q) (1599)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 5 (meaning1591 q) (meaning1599 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1599 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1596)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 1 1 (meaning1564 q) (meaning1587 q) (meaning1596 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1587 = false ∨ valuation q 1596 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1597)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 1 2 (meaning1564 q) (meaning1588 q) (meaning1597 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1588 = false ∨ valuation q 1597 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1598)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 1 3 (meaning1564 q) (meaning1589 q) (meaning1598 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1589 = false ∨ valuation q 1598 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1599)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 1 4 (meaning1564 q) (meaning1590 q) (meaning1599 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1590 = false ∨ valuation q 1599 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1600)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 1 5 (meaning1564 q) (meaning1591 q) (meaning1600 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1591 = false ∨ valuation q 1600 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1597)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 2 1 (meaning1565 q) (meaning1587 q) (meaning1597 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1587 = false ∨ valuation q 1597 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1598)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 2 2 (meaning1565 q) (meaning1588 q) (meaning1598 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1588 = false ∨ valuation q 1598 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1599)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 2 3 (meaning1565 q) (meaning1589 q) (meaning1599 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1589 = false ∨ valuation q 1599 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1600)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 2 4 (meaning1565 q) (meaning1590 q) (meaning1600 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1590 = false ∨ valuation q 1600 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1601 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1601)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 2 5 (meaning1565 q) (meaning1591 q) (meaning1601 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1591 = false ∨ valuation q 1601 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1602 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1602)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 2 6 (meaning1565 q) (meaning1592 q) (meaning1602 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1592 = false ∨ valuation q 1602 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1598)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 3 1 (meaning1566 q) (meaning1587 q) (meaning1598 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1587 = false ∨ valuation q 1598 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1599)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 3 2 (meaning1566 q) (meaning1588 q) (meaning1599 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1588 = false ∨ valuation q 1599 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1600)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 3 3 (meaning1566 q) (meaning1589 q) (meaning1600 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1589 = false ∨ valuation q 1600 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1601 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1601)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 3 4 (meaning1566 q) (meaning1590 q) (meaning1601 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1590 = false ∨ valuation q 1601 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1602 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1602)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 3 5 (meaning1566 q) (meaning1591 q) (meaning1602 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1591 = false ∨ valuation q 1602 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1603 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1603)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 3 6 (meaning1566 q) (meaning1592 q) (meaning1603 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1592 = false ∨ valuation q 1603 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1599)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 4 1 (meaning1567 q) (meaning1587 q) (meaning1599 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1587 = false ∨ valuation q 1599 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E110.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112110
