import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1545)) (literal (valuationOf q) (1553)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 5 (meaning1545 q) (meaning1553 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1553 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1546)) (literal (valuationOf q) (1554)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 6 (meaning1546 q) (meaning1554 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1554 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1552)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 1 3 (meaning1518 q) (meaning1543 q) (meaning1552 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1543 = false ∨ valuation q 1552 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1553)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 1 4 (meaning1518 q) (meaning1544 q) (meaning1553 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1544 = false ∨ valuation q 1553 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1554)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 1 5 (meaning1518 q) (meaning1545 q) (meaning1554 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1545 = false ∨ valuation q 1554 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1555)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 1 6 (meaning1518 q) (meaning1546 q) (meaning1555 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1546 = false ∨ valuation q 1555 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1556 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1556)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 1 7 (meaning1518 q) (meaning1547 q) (meaning1556 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1547 = false ∨ valuation q 1556 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1552)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 2 2 (meaning1519 q) (meaning1542 q) (meaning1552 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1542 = false ∨ valuation q 1552 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1553)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 2 3 (meaning1519 q) (meaning1543 q) (meaning1553 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1543 = false ∨ valuation q 1553 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1554)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 2 4 (meaning1519 q) (meaning1544 q) (meaning1554 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1544 = false ∨ valuation q 1554 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1555)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 2 5 (meaning1519 q) (meaning1545 q) (meaning1555 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1545 = false ∨ valuation q 1555 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1556 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1556)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 2 6 (meaning1519 q) (meaning1546 q) (meaning1556 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1546 = false ∨ valuation q 1556 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1557 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 2 7 (meaning1519 q) (meaning1547 q) (meaning1557 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1547 = false ∨ valuation q 1557 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1553)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 3 2 (meaning1520 q) (meaning1542 q) (meaning1553 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1542 = false ∨ valuation q 1553 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1554)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 3 3 (meaning1520 q) (meaning1543 q) (meaning1554 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1543 = false ∨ valuation q 1554 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1555)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 3 4 (meaning1520 q) (meaning1544 q) (meaning1555 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1544 = false ∨ valuation q 1555 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1556 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1556)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 3 5 (meaning1520 q) (meaning1545 q) (meaning1556 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1545 = false ∨ valuation q 1556 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1557 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 3 6 (meaning1520 q) (meaning1546 q) (meaning1557 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1546 = false ∨ valuation q 1557 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1554)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 4 2 (meaning1521 q) (meaning1542 q) (meaning1554 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1542 = false ∨ valuation q 1554 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1555)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 4 3 (meaning1521 q) (meaning1543 q) (meaning1555 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1543 = false ∨ valuation q 1555 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1556 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1556)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 4 4 (meaning1521 q) (meaning1544 q) (meaning1556 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1544 = false ∨ valuation q 1556 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1557 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 4 5 (meaning1521 q) (meaning1545 q) (meaning1557 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1545 = false ∨ valuation q 1557 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1558 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 4 6 (meaning1521 q) (meaning1546 q) (meaning1558 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1546 = false ∨ valuation q 1558 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1555)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 5 2 (meaning1522 q) (meaning1542 q) (meaning1555 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1542 = false ∨ valuation q 1555 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1556 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1556)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 5 3 (meaning1522 q) (meaning1543 q) (meaning1556 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1543 = false ∨ valuation q 1556 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1557 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 5 4 (meaning1522 q) (meaning1544 q) (meaning1557 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1544 = false ∨ valuation q 1557 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1558 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 5 5 (meaning1522 q) (meaning1545 q) (meaning1558 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1545 = false ∨ valuation q 1558 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1556 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1556)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 6 2 (meaning1523 q) (meaning1542 q) (meaning1556 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1542 = false ∨ valuation q 1556 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1557 = true := by
  have hs : count1549 q = (countLit q [-3, -5, -6, -8, -10, -12, -13]) + (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13]) (l₂ := [-14, -17, -19, -20, -21, -24, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -6, -8, -10, -12, -13]) (countLit q [-14, -17, -19, -20, -21, -24, -25, -26]) (count1549 q) 6 3 (meaning1523 q) (meaning1543 q) (meaning1557 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1543 = false ∨ valuation q 1557 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1564)) (countLit q [-28]) (countLit q [-29]) (count1564 q) 1 (meaningNeg29 q) (meaning1564 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1564 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1564)) (countLit q [-28]) (countLit q [-29]) (count1564 q) 1 (meaningNeg28 q) (meaning1564 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1564 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 29 = true ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (1565)) (countLit q [-28]) (countLit q [-29]) (count1564 q) 1 1 (meaningNeg28 q) (meaningNeg29 q) (meaning1565 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 29 = true ∨ valuation q 1565 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E008.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112008
