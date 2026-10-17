import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1545)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 2 3 (meaning1511 q) (meaning1535 q) (meaning1545 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1535 = false ∨ valuation q 1545 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1546)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 2 4 (meaning1511 q) (meaning1536 q) (meaning1546 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1536 = false ∨ valuation q 1546 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1547)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 2 5 (meaning1511 q) (meaning1537 q) (meaning1547 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1537 = false ∨ valuation q 1547 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1548)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 2 6 (meaning1511 q) (meaning1538 q) (meaning1548 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1538 = false ∨ valuation q 1548 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1549 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1549)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 2 7 (meaning1511 q) (meaning1539 q) (meaning1549 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1539 = false ∨ valuation q 1549 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1550 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1550)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 2 8 (meaning1511 q) (meaning1540 q) (meaning1550 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1540 = false ∨ valuation q 1550 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1546)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 3 3 (meaning1512 q) (meaning1535 q) (meaning1546 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1535 = false ∨ valuation q 1546 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1547)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 3 4 (meaning1512 q) (meaning1536 q) (meaning1547 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1536 = false ∨ valuation q 1547 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1548)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 3 5 (meaning1512 q) (meaning1537 q) (meaning1548 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1537 = false ∨ valuation q 1548 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1549 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1549)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 3 6 (meaning1512 q) (meaning1538 q) (meaning1549 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1538 = false ∨ valuation q 1549 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1551 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1551)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 3 8 (meaning1512 q) (meaning1540 q) (meaning1551 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1540 = false ∨ valuation q 1551 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1547)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 4 3 (meaning1513 q) (meaning1535 q) (meaning1547 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1535 = false ∨ valuation q 1547 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1548)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 4 4 (meaning1513 q) (meaning1536 q) (meaning1548 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1536 = false ∨ valuation q 1548 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1549)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 4 5 (meaning1513 q) (meaning1537 q) (meaning1549 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1537 = false ∨ valuation q 1549 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1550)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 4 6 (meaning1513 q) (meaning1538 q) (meaning1550 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1538 = false ∨ valuation q 1550 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1547)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 5 2 (meaning1514 q) (meaning1534 q) (meaning1547 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1534 = false ∨ valuation q 1547 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1548)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 5 3 (meaning1514 q) (meaning1535 q) (meaning1548 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1535 = false ∨ valuation q 1548 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1549 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1549)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 5 4 (meaning1514 q) (meaning1536 q) (meaning1549 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1536 = false ∨ valuation q 1549 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1549 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1549)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 6 3 (meaning1515 q) (meaning1535 q) (meaning1549 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1535 = false ∨ valuation q 1549 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1550 = true := by
  have hs : count1541 q = (countLit q [-2, -3, -5, -6, -8, -9, -12]) + (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12]) (l₂ := [-13, -15, -16, -18, -21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1550)) (countLit q [-2, -3, -5, -6, -8, -9, -12]) (countLit q [-13, -15, -16, -18, -21, -22, -24, -27]) (count1541 q) 6 4 (meaning1515 q) (meaning1536 q) (meaning1550 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1536 = false ∨ valuation q 1550 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1556)) (countLit q [-29]) (countLit q [-30]) (count1556 q) 1 (meaningNeg30 q) (meaning1556 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1556 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1556)) (countLit q [-29]) (countLit q [-30]) (count1556 q) 1 (meaningNeg29 q) (meaning1556 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1556 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1557 = true := by
  have hs : count1556 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1557)) (countLit q [-29]) (countLit q [-30]) (count1556 q) 1 1 (meaningNeg29 q) (meaningNeg30 q) (meaning1557 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 1557 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (1558)) (countLit q [-31]) (countLit q [-34]) (count1558 q) 1 (meaningNeg34 q) (meaning1558 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1558 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1558)) (countLit q [-31]) (countLit q [-34]) (count1558 q) 1 (meaningNeg31 q) (meaning1558 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1558 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 34 = true ∨ valuationOf q 1559 = true := by
  have hs : count1558 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-34)) (literal (valuationOf q) (1559)) (countLit q [-31]) (countLit q [-34]) (count1558 q) 1 1 (meaningNeg31 q) (meaningNeg34 q) (meaning1559 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 34)) = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 34 = true ∨ valuation q 1559 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-29, -30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-29, -30]) (l₂ := [-31, -34])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1560)) (countLit q [-29, -30]) (countLit q [-31, -34]) (count1560 q) 1 (meaning1558 q) (meaning1560 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1560 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-29, -30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-29, -30]) (l₂ := [-31, -34])
  have hm := merge_right (literal (valuationOf q) (1559)) (literal (valuationOf q) (1561)) (countLit q [-29, -30]) (countLit q [-31, -34]) (count1560 q) 2 (meaning1559 q) (meaning1561 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1561 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-29, -30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-29, -30]) (l₂ := [-31, -34])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-29, -30]) (countLit q [-31, -34]) (count1560 q) 1 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-29, -30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-29, -30]) (l₂ := [-31, -34])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1561)) (countLit q [-29, -30]) (countLit q [-31, -34]) (count1560 q) 1 1 (meaning1556 q) (meaning1558 q) (meaning1561 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = false ∨ valuation q 1561 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-29, -30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-29, -30]) (l₂ := [-31, -34])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1562)) (countLit q [-29, -30]) (countLit q [-31, -34]) (count1560 q) 1 2 (meaning1556 q) (meaning1559 q) (meaning1562 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1559 = false ∨ valuation q 1562 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-29, -30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-29, -30]) (l₂ := [-31, -34])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-29, -30]) (countLit q [-31, -34]) (count1560 q) 2 (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1561 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E020.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112020
