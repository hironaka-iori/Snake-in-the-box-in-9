import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1598)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 3 1 (meaning1586 q) (meaning1591 q) (meaning1598 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1591 = false ∨ valuation q 1598 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1599)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 3 2 (meaning1586 q) (meaning1592 q) (meaning1599 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1592 = false ∨ valuation q 1599 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1600)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 3 3 (meaning1586 q) (meaning1593 q) (meaning1600 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1593 = false ∨ valuation q 1600 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1601 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1601)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 3 4 (meaning1586 q) (meaning1594 q) (meaning1601 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1594 = false ∨ valuation q 1601 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_right (literal (valuationOf q) (1595)) (literal (valuationOf q) (1602)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 1 (meaning1595 q) (meaning1602 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1602 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_right (literal (valuationOf q) (1596)) (literal (valuationOf q) (1603)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 2 (meaning1596 q) (meaning1603 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1603 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_right (literal (valuationOf q) (1597)) (literal (valuationOf q) (1604)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 3 (meaning1597 q) (meaning1604 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1604 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_right (literal (valuationOf q) (1598)) (literal (valuationOf q) (1605)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 4 (meaning1598 q) (meaning1605 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1605 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_right (literal (valuationOf q) (1599)) (literal (valuationOf q) (1606)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 5 (meaning1599 q) (meaning1606 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1606 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_right (literal (valuationOf q) (1600)) (literal (valuationOf q) (1607)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 6 (meaning1600 q) (meaning1607 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1607 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1608 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_right (literal (valuationOf q) (1601)) (literal (valuationOf q) (1608)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 7 (meaning1601 q) (meaning1608 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1608 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1602)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 1 (meaning1575 q) (meaning1602 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1602 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1603)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 1 1 (meaning1575 q) (meaning1595 q) (meaning1603 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1595 = false ∨ valuation q 1603 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1604)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 1 2 (meaning1575 q) (meaning1596 q) (meaning1604 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1596 = false ∨ valuation q 1604 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1605)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 1 3 (meaning1575 q) (meaning1597 q) (meaning1605 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1597 = false ∨ valuation q 1605 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1606)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 1 4 (meaning1575 q) (meaning1598 q) (meaning1606 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1598 = false ∨ valuation q 1606 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1607)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 1 5 (meaning1575 q) (meaning1599 q) (meaning1607 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1599 = false ∨ valuation q 1607 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1608 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1608)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 1 6 (meaning1575 q) (meaning1600 q) (meaning1608 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1600 = false ∨ valuation q 1608 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1609 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1609)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 1 7 (meaning1575 q) (meaning1601 q) (meaning1609 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1601 = false ∨ valuation q 1609 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_left (literal (valuationOf q) (1576)) (literal (valuationOf q) (1603)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 2 (meaning1576 q) (meaning1603 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1603 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1604)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 2 1 (meaning1576 q) (meaning1595 q) (meaning1604 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1595 = false ∨ valuation q 1604 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1605)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 2 2 (meaning1576 q) (meaning1596 q) (meaning1605 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1596 = false ∨ valuation q 1605 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1606)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 2 3 (meaning1576 q) (meaning1597 q) (meaning1606 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1597 = false ∨ valuation q 1606 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1607)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 2 4 (meaning1576 q) (meaning1598 q) (meaning1607 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1598 = false ∨ valuation q 1607 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1608 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1608)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 2 5 (meaning1576 q) (meaning1599 q) (meaning1608 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1599 = false ∨ valuation q 1608 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1609 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1609)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 2 6 (meaning1576 q) (meaning1600 q) (meaning1609 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1600 = false ∨ valuation q 1609 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_left (literal (valuationOf q) (1577)) (literal (valuationOf q) (1604)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 3 (meaning1577 q) (meaning1604 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1604 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1605)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 3 1 (meaning1577 q) (meaning1595 q) (meaning1605 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1595 = false ∨ valuation q 1605 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1606)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 3 2 (meaning1577 q) (meaning1596 q) (meaning1606 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1596 = false ∨ valuation q 1606 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1607)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 3 3 (meaning1577 q) (meaning1597 q) (meaning1607 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1597 = false ∨ valuation q 1607 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1608 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1608)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 3 4 (meaning1577 q) (meaning1598 q) (meaning1608 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1598 = false ∨ valuation q 1608 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1609 = true := by
  have hs : count1602 q = (countLit q [-59, -61, -64, -67, -68, -70, -74]) + (countLit q [-75, -76, -77, -81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74]) (l₂ := [-75, -76, -77, -81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1609)) (countLit q [-59, -61, -64, -67, -68, -70, -74]) (countLit q [-75, -76, -77, -81, -82, -85, -89]) (count1602 q) 3 5 (meaning1577 q) (meaning1599 q) (meaning1609 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1599 = false ∨ valuation q 1609 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E027.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112027
