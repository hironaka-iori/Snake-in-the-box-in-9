import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1604 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1604)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 3 7 (meaning1565 q) (meaning1593 q) (meaning1604 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1593 = false ∨ valuation q 1604 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1605 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1605)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 3 8 (meaning1565 q) (meaning1594 q) (meaning1605 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1594 = false ∨ valuation q 1605 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1602 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1602)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 4 4 (meaning1566 q) (meaning1590 q) (meaning1602 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1590 = false ∨ valuation q 1602 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1603 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1603)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 4 5 (meaning1566 q) (meaning1591 q) (meaning1603 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1591 = false ∨ valuation q 1603 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1604 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1604)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 4 6 (meaning1566 q) (meaning1592 q) (meaning1604 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1592 = false ∨ valuation q 1604 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1605 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1605)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 4 7 (meaning1566 q) (meaning1593 q) (meaning1605 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1593 = false ∨ valuation q 1605 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1606 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1606)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 4 8 (meaning1566 q) (meaning1594 q) (meaning1606 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1594 = false ∨ valuation q 1606 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1602 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1602)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 5 3 (meaning1567 q) (meaning1589 q) (meaning1602 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1589 = false ∨ valuation q 1602 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1603 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1603)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 5 4 (meaning1567 q) (meaning1590 q) (meaning1603 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1590 = false ∨ valuation q 1603 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1604 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1604)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 5 5 (meaning1567 q) (meaning1591 q) (meaning1604 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1591 = false ∨ valuation q 1604 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1605 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1605)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 5 6 (meaning1567 q) (meaning1592 q) (meaning1605 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1592 = false ∨ valuation q 1605 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1607 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1607)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 5 8 (meaning1567 q) (meaning1594 q) (meaning1607 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1594 = false ∨ valuation q 1607 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1604 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1604)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 6 4 (meaning1568 q) (meaning1590 q) (meaning1604 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1590 = false ∨ valuation q 1604 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1605 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1605)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 6 5 (meaning1568 q) (meaning1591 q) (meaning1605 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1591 = false ∨ valuation q 1605 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1606 = true := by
  have hs : count1595 q = (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) + (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -11, -13, -16]) (l₂ := [-17, -19, -21, -23, -25, -26, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1606)) (countLit q [-2, -4, -7, -8, -9, -11, -13, -16]) (countLit q [-17, -19, -21, -23, -25, -26, -27, -28]) (count1595 q) 6 6 (meaning1568 q) (meaning1592 q) (meaning1606 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1592 = false ∨ valuation q 1606 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1611 = true := by
  have hs : count1611 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1611)) (countLit q [-32]) (countLit q [-33]) (count1611 q) 1 (meaningNeg33 q) (meaning1611 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1611 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1611 = true := by
  have hs : count1611 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1611)) (countLit q [-32]) (countLit q [-33]) (count1611 q) 1 (meaningNeg32 q) (meaning1611 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1611 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1612)) (countLit q [-32]) (countLit q [-33]) (count1611 q) 1 1 (meaningNeg32 q) (meaningNeg33 q) (meaning1612 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 33 = true ∨ valuation q 1612 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1613 = true := by
  have hs : count1613 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1613)) (countLit q [-37]) (countLit q [-38]) (count1613 q) 1 (meaningNeg38 q) (meaning1613 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1613 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1613 = true := by
  have hs : count1613 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1613)) (countLit q [-37]) (countLit q [-38]) (count1613 q) 1 (meaningNeg37 q) (meaning1613 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1613 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1614 = true := by
  have hs : count1613 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1614)) (countLit q [-37]) (countLit q [-38]) (count1613 q) 1 1 (meaningNeg37 q) (meaningNeg38 q) (meaning1614 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 1614 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-32, -33]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-37, -38])
  have hm := merge_right (literal (valuationOf q) (1613)) (literal (valuationOf q) (1615)) (countLit q [-32, -33]) (countLit q [-37, -38]) (count1615 q) 1 (meaning1613 q) (meaning1615 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1615 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1616 = true := by
  have hs : count1615 q = (countLit q [-32, -33]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-37, -38])
  have hm := merge_right (literal (valuationOf q) (1614)) (literal (valuationOf q) (1616)) (countLit q [-32, -33]) (countLit q [-37, -38]) (count1615 q) 2 (meaning1614 q) (meaning1616 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1616 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-32, -33]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-37, -38])
  have hm := merge_left (literal (valuationOf q) (1611)) (literal (valuationOf q) (1615)) (countLit q [-32, -33]) (countLit q [-37, -38]) (count1615 q) 1 (meaning1611 q) (meaning1615 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1615 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1616 = true := by
  have hs : count1615 q = (countLit q [-32, -33]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1616)) (countLit q [-32, -33]) (countLit q [-37, -38]) (count1615 q) 1 1 (meaning1611 q) (meaning1613 q) (meaning1616 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1613 = false ∨ valuation q 1616 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1617 = true := by
  have hs : count1615 q = (countLit q [-32, -33]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1617)) (countLit q [-32, -33]) (countLit q [-37, -38]) (count1615 q) 1 2 (meaning1611 q) (meaning1614 q) (meaning1617 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1614 = false ∨ valuation q 1617 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1616 = true := by
  have hs : count1615 q = (countLit q [-32, -33]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-37, -38])
  have hm := merge_left (literal (valuationOf q) (1612)) (literal (valuationOf q) (1616)) (countLit q [-32, -33]) (countLit q [-37, -38]) (count1615 q) 2 (meaning1612 q) (meaning1616 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1616 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1617 = true := by
  have hs : count1615 q = (countLit q [-32, -33]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1617)) (countLit q [-32, -33]) (countLit q [-37, -38]) (count1615 q) 2 1 (meaning1612 q) (meaning1613 q) (meaning1617 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1613 = false ∨ valuation q 1617 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1618 = true := by
  have hs : count1615 q = (countLit q [-32, -33]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1618)) (countLit q [-32, -33]) (countLit q [-37, -38]) (count1615 q) 2 2 (meaning1612 q) (meaning1614 q) (meaning1618 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1614 = false ∨ valuation q 1618 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1619)) (countLit q [-39]) (countLit q [-41]) (count1619 q) 1 (meaningNeg41 q) (meaning1619 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1619 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1619)) (countLit q [-39]) (countLit q [-41]) (count1619 q) 1 (meaningNeg39 q) (meaning1619 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1619 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1620)) (countLit q [-39]) (countLit q [-41]) (count1619 q) 1 1 (meaningNeg39 q) (meaningNeg41 q) (meaning1620 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 1620 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E036.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112036
