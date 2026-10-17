import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-47, -50, -51, -52]) + (countLit q [-55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -51, -52]) (l₂ := [-55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1593)) (countLit q [-47, -50, -51, -52]) (countLit q [-55, -58, -61, -63]) (count1591 q) 1 2 (meaning1579 q) (meaning1588 q) (meaning1593 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1588 = false ∨ valuation q 1593 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-47, -50, -51, -52]) + (countLit q [-55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -51, -52]) (l₂ := [-55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1594)) (countLit q [-47, -50, -51, -52]) (countLit q [-55, -58, -61, -63]) (count1591 q) 1 3 (meaning1579 q) (meaning1589 q) (meaning1594 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1589 = false ∨ valuation q 1594 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-47, -50, -51, -52]) + (countLit q [-55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -51, -52]) (l₂ := [-55, -58, -61, -63])
  have hm := merge_left (literal (valuationOf q) (1580)) (literal (valuationOf q) (1592)) (countLit q [-47, -50, -51, -52]) (countLit q [-55, -58, -61, -63]) (count1591 q) 2 (meaning1580 q) (meaning1592 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1592 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-47, -50, -51, -52]) + (countLit q [-55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -51, -52]) (l₂ := [-55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1593)) (countLit q [-47, -50, -51, -52]) (countLit q [-55, -58, -61, -63]) (count1591 q) 2 1 (meaning1580 q) (meaning1587 q) (meaning1593 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1587 = false ∨ valuation q 1593 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-47, -50, -51, -52]) + (countLit q [-55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -51, -52]) (l₂ := [-55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1594)) (countLit q [-47, -50, -51, -52]) (countLit q [-55, -58, -61, -63]) (count1591 q) 2 2 (meaning1580 q) (meaning1588 q) (meaning1594 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1588 = false ∨ valuation q 1594 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1599 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_right (literal (valuationOf q) (1591)) (literal (valuationOf q) (1599)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 1 (meaning1591 q) (meaning1599 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1599 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1600 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_right (literal (valuationOf q) (1592)) (literal (valuationOf q) (1600)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 2 (meaning1592 q) (meaning1600 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1600 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1601 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_right (literal (valuationOf q) (1593)) (literal (valuationOf q) (1601)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 3 (meaning1593 q) (meaning1601 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1601 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1602 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_right (literal (valuationOf q) (1594)) (literal (valuationOf q) (1602)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 4 (meaning1594 q) (meaning1602 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1602 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1600 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1600)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 1 1 (meaning1568 q) (meaning1591 q) (meaning1600 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1591 = false ∨ valuation q 1600 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1601 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1601)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 1 2 (meaning1568 q) (meaning1592 q) (meaning1601 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1592 = false ∨ valuation q 1601 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1602 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1602)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 1 3 (meaning1568 q) (meaning1593 q) (meaning1602 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1593 = false ∨ valuation q 1602 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1603 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1603)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 1 4 (meaning1568 q) (meaning1594 q) (meaning1603 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1594 = false ∨ valuation q 1603 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1600 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_left (literal (valuationOf q) (1569)) (literal (valuationOf q) (1600)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 2 (meaning1569 q) (meaning1600 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1600 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1601 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1601)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 2 1 (meaning1569 q) (meaning1591 q) (meaning1601 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1591 = false ∨ valuation q 1601 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1602 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1602)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 2 2 (meaning1569 q) (meaning1592 q) (meaning1602 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1592 = false ∨ valuation q 1602 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1603 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1603)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 2 3 (meaning1569 q) (meaning1593 q) (meaning1603 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1593 = false ∨ valuation q 1603 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1604 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1604)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 2 4 (meaning1569 q) (meaning1594 q) (meaning1604 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1594 = false ∨ valuation q 1604 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1601 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_left (literal (valuationOf q) (1570)) (literal (valuationOf q) (1601)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 3 (meaning1570 q) (meaning1601 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1601 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1602 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1602)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 3 1 (meaning1570 q) (meaning1591 q) (meaning1602 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1591 = false ∨ valuation q 1602 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1603 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1603)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 3 2 (meaning1570 q) (meaning1592 q) (meaning1603 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1592 = false ∨ valuation q 1603 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1604 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1604)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 3 3 (meaning1570 q) (meaning1593 q) (meaning1604 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1593 = false ∨ valuation q 1604 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1603 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1603)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 4 1 (meaning1571 q) (meaning1591 q) (meaning1603 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1591 = false ∨ valuation q 1603 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1604 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1604)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 4 2 (meaning1571 q) (meaning1592 q) (meaning1604 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1592 = false ∨ valuation q 1604 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1605 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1605)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 4 3 (meaning1571 q) (meaning1593 q) (meaning1605 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1593 = false ∨ valuation q 1605 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1605 = true := by
  have hs : count1599 q = (countLit q [-33, -35, -37, -39, -41, -43, -44]) + (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -39, -41, -43, -44]) (l₂ := [-47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1605)) (countLit q [-33, -35, -37, -39, -41, -43, -44]) (countLit q [-47, -50, -51, -52, -55, -58, -61, -63]) (count1599 q) 5 2 (meaning1572 q) (meaning1592 q) (meaning1605 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1592 = false ∨ valuation q 1605 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1616 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1616)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 1 2 (meaning1541 q) (meaning1600 q) (meaning1616 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1600 = false ∨ valuation q 1616 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1617 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1617)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 1 3 (meaning1541 q) (meaning1601 q) (meaning1617 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1601 = false ∨ valuation q 1617 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1618 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1618)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 1 4 (meaning1541 q) (meaning1602 q) (meaning1618 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1602 = false ∨ valuation q 1618 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1619 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1619)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 1 5 (meaning1541 q) (meaning1603 q) (meaning1619 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1603 = false ∨ valuation q 1619 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1620 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1620)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 1 6 (meaning1541 q) (meaning1604 q) (meaning1620 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1604 = false ∨ valuation q 1620 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1616 = true := by
  have hs : count1614 q = (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) + (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (l₂ := [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1616)) (countLit q [-2, -5, -8, -12, -13, -15, -17, -18, -21, -22, -25, -28, -29, -31]) (countLit q [-33, -35, -37, -39, -41, -43, -44, -47, -50, -51, -52, -55, -58, -61, -63]) (count1614 q) 2 1 (meaning1542 q) (meaning1599 q) (meaning1616 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1599 = false ∨ valuation q 1616 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E258.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112258
