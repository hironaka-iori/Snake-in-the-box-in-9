import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1582)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 2 1 (meaning1569 q) (meaning1576 q) (meaning1582 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1576 = false ∨ valuation q 1582 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1583 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1583)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 2 2 (meaning1569 q) (meaning1577 q) (meaning1583 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1577 = false ∨ valuation q 1583 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1584 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1584)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 2 3 (meaning1569 q) (meaning1578 q) (meaning1584 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1578 = false ∨ valuation q 1584 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1585 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1585)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 2 4 (meaning1569 q) (meaning1579 q) (meaning1585 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1579 = false ∨ valuation q 1585 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_left (literal (valuationOf q) (1570)) (literal (valuationOf q) (1582)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 3 (meaning1570 q) (meaning1582 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1582 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1583 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1583)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 3 1 (meaning1570 q) (meaning1576 q) (meaning1583 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1576 = false ∨ valuation q 1583 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1584 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1584)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 3 2 (meaning1570 q) (meaning1577 q) (meaning1584 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1577 = false ∨ valuation q 1584 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1585 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1585)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 3 3 (meaning1570 q) (meaning1578 q) (meaning1585 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1578 = false ∨ valuation q 1585 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1586 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1586)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 3 4 (meaning1570 q) (meaning1579 q) (meaning1586 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1579 = false ∨ valuation q 1586 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1583 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_left (literal (valuationOf q) (1571)) (literal (valuationOf q) (1583)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 4 (meaning1571 q) (meaning1583 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1583 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1584 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1584)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 4 1 (meaning1571 q) (meaning1576 q) (meaning1584 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1576 = false ∨ valuation q 1584 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1585 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1585)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 4 2 (meaning1571 q) (meaning1577 q) (meaning1585 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1577 = false ∨ valuation q 1585 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1586 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1586)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 4 3 (meaning1571 q) (meaning1578 q) (meaning1586 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1578 = false ∨ valuation q 1586 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1587 = true := by
  have hs : count1580 q = (countLit q [-15, -16, -18, -19]) + (countLit q [-21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18, -19]) (l₂ := [-21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1587)) (countLit q [-15, -16, -18, -19]) (countLit q [-21, -23, -24, -25]) (count1580 q) 4 4 (meaning1571 q) (meaning1579 q) (meaning1587 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1579 = false ∨ valuation q 1587 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1592 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1592)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 3 2 (meaning1558 q) (meaning1581 q) (meaning1592 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1581 = false ∨ valuation q 1592 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1593 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1593)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 3 3 (meaning1558 q) (meaning1582 q) (meaning1593 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1582 = false ∨ valuation q 1593 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1594 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1594)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 3 4 (meaning1558 q) (meaning1583 q) (meaning1594 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1583 = false ∨ valuation q 1594 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1595 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1595)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 3 5 (meaning1558 q) (meaning1584 q) (meaning1595 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1584 = false ∨ valuation q 1595 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1596)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 3 6 (meaning1558 q) (meaning1585 q) (meaning1596 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1585 = false ∨ valuation q 1596 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1597 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1597)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 3 7 (meaning1558 q) (meaning1586 q) (meaning1597 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1586 = false ∨ valuation q 1597 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1598 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1598)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 3 8 (meaning1558 q) (meaning1587 q) (meaning1598 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1587 = false ∨ valuation q 1598 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1593 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1593)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 4 2 (meaning1559 q) (meaning1581 q) (meaning1593 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1581 = false ∨ valuation q 1593 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1594 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1594)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 4 3 (meaning1559 q) (meaning1582 q) (meaning1594 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1582 = false ∨ valuation q 1594 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1595 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1595)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 4 4 (meaning1559 q) (meaning1583 q) (meaning1595 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1583 = false ∨ valuation q 1595 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1596)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 4 5 (meaning1559 q) (meaning1584 q) (meaning1596 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1584 = false ∨ valuation q 1596 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1597 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1597)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 4 6 (meaning1559 q) (meaning1585 q) (meaning1597 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1585 = false ∨ valuation q 1597 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1598 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1598)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 4 7 (meaning1559 q) (meaning1586 q) (meaning1598 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1586 = false ∨ valuation q 1598 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1599 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1599)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 4 8 (meaning1559 q) (meaning1587 q) (meaning1599 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1587 = false ∨ valuation q 1599 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1594 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1594)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 5 2 (meaning1560 q) (meaning1581 q) (meaning1594 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1581 = false ∨ valuation q 1594 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1595 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1595)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 5 3 (meaning1560 q) (meaning1582 q) (meaning1595 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1582 = false ∨ valuation q 1595 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1596)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 5 4 (meaning1560 q) (meaning1583 q) (meaning1596 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1583 = false ∨ valuation q 1596 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1597 = true := by
  have hs : count1588 q = (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) + (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6, -7, -8, -9, -11, -13]) (l₂ := [-15, -16, -18, -19, -21, -23, -24, -25])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1597)) (countLit q [-2, -3, -6, -7, -8, -9, -11, -13]) (countLit q [-15, -16, -18, -19, -21, -23, -24, -25]) (count1588 q) 5 5 (meaning1560 q) (meaning1584 q) (meaning1597 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1584 = false ∨ valuation q 1597 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E034.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112034
