import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-61]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (1562)) (countLit q [-61]) (countLit q [-64]) (count1562 q) 1 (meaningNeg64 q) (meaning1562 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1562 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-59]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -64])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1564)) (countLit q [-59]) (countLit q [-61, -64]) (count1564 q) 1 (meaning1562 q) (meaning1564 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1564 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-59]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -64])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1564)) (countLit q [-59]) (countLit q [-61, -64]) (count1564 q) 1 (meaningNeg59 q) (meaning1564 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1564 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-59]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -64])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1565)) (countLit q [-59]) (countLit q [-61, -64]) (count1564 q) 1 1 (meaningNeg59 q) (meaning1562 q) (meaning1565 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1562 = false ∨ valuation q 1565 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1567 = true := by
  have hs : count1567 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1567)) (countLit q [-67]) (countLit q [-68]) (count1567 q) 1 (meaningNeg68 q) (meaning1567 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1567 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1567 = true := by
  have hs : count1567 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1567)) (countLit q [-67]) (countLit q [-68]) (count1567 q) 1 (meaningNeg67 q) (meaning1567 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1567 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 68 = true ∨ valuationOf q 1568 = true := by
  have hs : count1567 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (1568)) (countLit q [-67]) (countLit q [-68]) (count1567 q) 1 1 (meaningNeg67 q) (meaningNeg68 q) (meaning1568 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 68 = true ∨ valuation q 1568 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-70]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1569)) (countLit q [-70]) (countLit q [-74]) (count1569 q) 1 (meaningNeg74 q) (meaning1569 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1569 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-70]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1569)) (countLit q [-70]) (countLit q [-74]) (count1569 q) 1 (meaningNeg70 q) (meaning1569 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1569 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1570 = true := by
  have hs : count1569 q = (countLit q [-70]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1570)) (countLit q [-70]) (countLit q [-74]) (count1569 q) 1 1 (meaningNeg70 q) (meaningNeg74 q) (meaning1570 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 1570 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_right (literal (valuationOf q) (1569)) (literal (valuationOf q) (1571)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count1571 q) 1 (meaning1569 q) (meaning1571 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1571 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_right (literal (valuationOf q) (1570)) (literal (valuationOf q) (1572)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count1571 q) 2 (meaning1570 q) (meaning1572 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1572 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_left (literal (valuationOf q) (1567)) (literal (valuationOf q) (1571)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count1571 q) 1 (meaning1567 q) (meaning1571 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1571 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1572)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count1571 q) 1 1 (meaning1567 q) (meaning1569 q) (meaning1572 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1569 = false ∨ valuation q 1572 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1573 = true := by
  have hs : count1571 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1573)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count1571 q) 1 2 (meaning1567 q) (meaning1570 q) (meaning1573 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1570 = false ∨ valuation q 1573 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_left (literal (valuationOf q) (1568)) (literal (valuationOf q) (1572)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count1571 q) 2 (meaning1568 q) (meaning1572 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1572 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1573 = true := by
  have hs : count1571 q = (countLit q [-67, -68]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -74])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1573)) (countLit q [-67, -68]) (countLit q [-70, -74]) (count1571 q) 2 1 (meaning1568 q) (meaning1569 q) (meaning1573 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1569 = false ∨ valuation q 1573 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_right (literal (valuationOf q) (1571)) (literal (valuationOf q) (1575)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 1 (meaning1571 q) (meaning1575 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1575 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_right (literal (valuationOf q) (1572)) (literal (valuationOf q) (1576)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 2 (meaning1572 q) (meaning1576 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1576 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_right (literal (valuationOf q) (1573)) (literal (valuationOf q) (1577)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 3 (meaning1573 q) (meaning1577 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1577 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_left (literal (valuationOf q) (1564)) (literal (valuationOf q) (1575)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 1 (meaning1564 q) (meaning1575 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1575 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1576)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 1 1 (meaning1564 q) (meaning1571 q) (meaning1576 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1571 = false ∨ valuation q 1576 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1577)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 1 2 (meaning1564 q) (meaning1572 q) (meaning1577 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1572 = false ∨ valuation q 1577 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1578 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1578)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 1 3 (meaning1564 q) (meaning1573 q) (meaning1578 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1573 = false ∨ valuation q 1578 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_left (literal (valuationOf q) (1565)) (literal (valuationOf q) (1576)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 2 (meaning1565 q) (meaning1576 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1576 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1577)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 2 1 (meaning1565 q) (meaning1571 q) (meaning1577 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1571 = false ∨ valuation q 1577 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1578 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1578)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 2 2 (meaning1565 q) (meaning1572 q) (meaning1578 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1572 = false ∨ valuation q 1578 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1579 = true := by
  have hs : count1575 q = (countLit q [-59, -61, -64]) + (countLit q [-67, -68, -70, -74]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64]) (l₂ := [-67, -68, -70, -74])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1579)) (countLit q [-59, -61, -64]) (countLit q [-67, -68, -70, -74]) (count1575 q) 2 3 (meaning1565 q) (meaning1573 q) (meaning1579 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1573 = false ∨ valuation q 1579 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1582)) (countLit q [-76]) (countLit q [-77]) (count1582 q) 1 (meaningNeg77 q) (meaning1582 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1582 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1582)) (countLit q [-76]) (countLit q [-77]) (count1582 q) 1 (meaningNeg76 q) (meaning1582 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1582 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1583)) (countLit q [-76]) (countLit q [-77]) (count1582 q) 1 1 (meaningNeg76 q) (meaningNeg77 q) (meaning1583 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 77 = true ∨ valuation q 1583 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1584 = true := by
  have hs : count1584 q = (countLit q [-75]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1582)) (literal (valuationOf q) (1584)) (countLit q [-75]) (countLit q [-76, -77]) (count1584 q) 1 (meaning1582 q) (meaning1584 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1584 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E027.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112027
