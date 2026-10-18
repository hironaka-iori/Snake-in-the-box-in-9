import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1598 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1598)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 1 4 (meaning1582 q) (meaning1593 q) (meaning1598 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1593 = false ∨ valuation q 1598 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1595 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1595)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 2 (meaning1583 q) (meaning1595 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1595 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1596 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1596)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 2 1 (meaning1583 q) (meaning1590 q) (meaning1596 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1590 = false ∨ valuation q 1596 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1597 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1597)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 2 2 (meaning1583 q) (meaning1591 q) (meaning1597 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1591 = false ∨ valuation q 1597 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1598 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1598)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 2 3 (meaning1583 q) (meaning1592 q) (meaning1598 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1592 = false ∨ valuation q 1598 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1599 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1599)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 2 4 (meaning1583 q) (meaning1593 q) (meaning1599 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1593 = false ∨ valuation q 1599 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1596 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1596)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 3 (meaning1584 q) (meaning1596 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1596 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1597 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1597)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 3 1 (meaning1584 q) (meaning1590 q) (meaning1597 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1590 = false ∨ valuation q 1597 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1598 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1598)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 3 2 (meaning1584 q) (meaning1591 q) (meaning1598 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1591 = false ∨ valuation q 1598 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1597 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1597)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 4 (meaning1585 q) (meaning1597 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1597 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1598 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1598)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 4 1 (meaning1585 q) (meaning1590 q) (meaning1598 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1590 = false ∨ valuation q 1598 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1600 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1600)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 4 3 (meaning1585 q) (meaning1592 q) (meaning1600 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1592 = false ∨ valuation q 1600 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1604)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 2 1 (meaning1571 q) (meaning1594 q) (meaning1604 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1594 = false ∨ valuation q 1604 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1606)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 2 3 (meaning1571 q) (meaning1596 q) (meaning1606 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1596 = false ∨ valuation q 1606 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1607)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 2 4 (meaning1571 q) (meaning1597 q) (meaning1607 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1597 = false ∨ valuation q 1607 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1605)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 3 1 (meaning1572 q) (meaning1594 q) (meaning1605 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1594 = false ∨ valuation q 1605 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1606)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 3 2 (meaning1572 q) (meaning1595 q) (meaning1606 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1595 = false ∨ valuation q 1606 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1607)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 3 3 (meaning1572 q) (meaning1596 q) (meaning1607 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1596 = false ∨ valuation q 1607 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1608 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1608)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 3 4 (meaning1572 q) (meaning1597 q) (meaning1608 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1597 = false ∨ valuation q 1608 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1609 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1609)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 3 5 (meaning1572 q) (meaning1598 q) (meaning1609 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1598 = false ∨ valuation q 1609 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1611 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1611)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 3 7 (meaning1572 q) (meaning1600 q) (meaning1611 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1600 = false ∨ valuation q 1611 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1606)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 4 1 (meaning1573 q) (meaning1594 q) (meaning1606 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1594 = false ∨ valuation q 1606 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1607)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 4 2 (meaning1573 q) (meaning1595 q) (meaning1607 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1595 = false ∨ valuation q 1607 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1608 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1608)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 4 3 (meaning1573 q) (meaning1596 q) (meaning1608 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1596 = false ∨ valuation q 1608 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1609 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1609)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 4 4 (meaning1573 q) (meaning1597 q) (meaning1609 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1597 = false ∨ valuation q 1609 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1610 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1610)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 4 5 (meaning1573 q) (meaning1598 q) (meaning1610 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1598 = false ∨ valuation q 1610 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1607)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 5 1 (meaning1574 q) (meaning1594 q) (meaning1607 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1594 = false ∨ valuation q 1607 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1608 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1608)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 5 2 (meaning1574 q) (meaning1595 q) (meaning1608 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1595 = false ∨ valuation q 1608 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1609 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1609)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 5 3 (meaning1574 q) (meaning1596 q) (meaning1609 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1596 = false ∨ valuation q 1609 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1610 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1610)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 5 4 (meaning1574 q) (meaning1597 q) (meaning1610 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1597 = false ∨ valuation q 1610 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1611 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1611)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 5 5 (meaning1574 q) (meaning1598 q) (meaning1611 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1598 = false ∨ valuation q 1611 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1612 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1612)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 5 6 (meaning1574 q) (meaning1599 q) (meaning1612 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1599 = false ∨ valuation q 1612 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E050.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112050
