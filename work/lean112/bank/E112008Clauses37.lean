import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1597)) (countLit q [-53]) (countLit q [-54]) (count1596 q) 1 1 (meaningNeg53 q) (meaningNeg54 q) (meaning1597 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 54 = true ∨ valuation q 1597 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1598)) (countLit q [-56]) (countLit q [-57]) (count1598 q) 1 (meaningNeg57 q) (meaning1598 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1598 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1598)) (countLit q [-56]) (countLit q [-57]) (count1598 q) 1 (meaningNeg56 q) (meaning1598 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1598 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1599)) (countLit q [-56]) (countLit q [-57]) (count1598 q) 1 1 (meaningNeg56 q) (meaningNeg57 q) (meaning1599 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 57 = true ∨ valuation q 1599 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-53, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-56, -57])
  have hm := merge_right (literal (valuationOf q) (1598)) (literal (valuationOf q) (1600)) (countLit q [-53, -54]) (countLit q [-56, -57]) (count1600 q) 1 (meaning1598 q) (meaning1600 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1600 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-53, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-56, -57])
  have hm := merge_right (literal (valuationOf q) (1599)) (literal (valuationOf q) (1601)) (countLit q [-53, -54]) (countLit q [-56, -57]) (count1600 q) 2 (meaning1599 q) (meaning1601 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1601 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-53, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-56, -57])
  have hm := merge_left (literal (valuationOf q) (1596)) (literal (valuationOf q) (1600)) (countLit q [-53, -54]) (countLit q [-56, -57]) (count1600 q) 1 (meaning1596 q) (meaning1600 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1600 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-53, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1601)) (countLit q [-53, -54]) (countLit q [-56, -57]) (count1600 q) 1 1 (meaning1596 q) (meaning1598 q) (meaning1601 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1598 = false ∨ valuation q 1601 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1602 = true := by
  have hs : count1600 q = (countLit q [-53, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1602)) (countLit q [-53, -54]) (countLit q [-56, -57]) (count1600 q) 1 2 (meaning1596 q) (meaning1599 q) (meaning1602 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1599 = false ∨ valuation q 1602 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-53, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-56, -57])
  have hm := merge_left (literal (valuationOf q) (1597)) (literal (valuationOf q) (1601)) (countLit q [-53, -54]) (countLit q [-56, -57]) (count1600 q) 2 (meaning1597 q) (meaning1601 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1601 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1602 = true := by
  have hs : count1600 q = (countLit q [-53, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1602)) (countLit q [-53, -54]) (countLit q [-56, -57]) (count1600 q) 2 1 (meaning1597 q) (meaning1598 q) (meaning1602 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1598 = false ∨ valuation q 1602 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1603 = true := by
  have hs : count1600 q = (countLit q [-53, -54]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1603)) (countLit q [-53, -54]) (countLit q [-56, -57]) (count1600 q) 2 2 (meaning1597 q) (meaning1599 q) (meaning1603 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1599 = false ∨ valuation q 1603 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 2 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1592)) (literal (valuationOf q) (1604)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 1 (meaning1592 q) (meaning1604 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1604 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1605)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 1 1 (meaning1592 q) (meaning1600 q) (meaning1605 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1600 = false ∨ valuation q 1605 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1606)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 1 2 (meaning1592 q) (meaning1601 q) (meaning1606 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1601 = false ∨ valuation q 1606 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1607)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 1 3 (meaning1592 q) (meaning1602 q) (meaning1607 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1602 = false ∨ valuation q 1607 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1608)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 1 4 (meaning1592 q) (meaning1603 q) (meaning1608 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1603 = false ∨ valuation q 1608 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1593)) (literal (valuationOf q) (1605)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 2 (meaning1593 q) (meaning1605 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1605 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1606)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 2 1 (meaning1593 q) (meaning1600 q) (meaning1606 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1600 = false ∨ valuation q 1606 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1607)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 2 2 (meaning1593 q) (meaning1601 q) (meaning1607 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1601 = false ∨ valuation q 1607 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1608)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 2 3 (meaning1593 q) (meaning1602 q) (meaning1608 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1602 = false ∨ valuation q 1608 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1609)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 2 4 (meaning1593 q) (meaning1603 q) (meaning1609 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1603 = false ∨ valuation q 1609 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1594)) (literal (valuationOf q) (1606)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 3 (meaning1594 q) (meaning1606 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1606 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1607)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 3 1 (meaning1594 q) (meaning1600 q) (meaning1607 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1600 = false ∨ valuation q 1607 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1608)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 3 2 (meaning1594 q) (meaning1601 q) (meaning1608 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1601 = false ∨ valuation q 1608 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1609)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 3 3 (meaning1594 q) (meaning1602 q) (meaning1609 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1602 = false ∨ valuation q 1609 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1610 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1610)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 3 4 (meaning1594 q) (meaning1603 q) (meaning1610 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1603 = false ∨ valuation q 1610 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-44, -45, -48, -51]) + (countLit q [-53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-44, -45, -48, -51]) (l₂ := [-53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1609)) (countLit q [-44, -45, -48, -51]) (countLit q [-53, -54, -56, -57]) (count1604 q) 4 2 (meaning1595 q) (meaning1601 q) (meaning1609 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1601 = false ∨ valuation q 1609 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1605)) (literal (valuationOf q) (1613)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 2 (meaning1605 q) (meaning1613 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1613 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1613)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 1 1 (meaning1580 q) (meaning1604 q) (meaning1613 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1604 = false ∨ valuation q 1613 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) + (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -33, -34, -35, -38, -40, -42]) (l₂ := [-44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1614)) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42]) (countLit q [-44, -45, -48, -51, -53, -54, -56, -57]) (count1612 q) 1 2 (meaning1580 q) (meaning1605 q) (meaning1614 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1605 = false ∨ valuation q 1614 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E008.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112008
