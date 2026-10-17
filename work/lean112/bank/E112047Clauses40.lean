import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-84, -85]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-89, -91])
  have hm := merge_right (literal (valuationOf q) (1596)) (literal (valuationOf q) (1598)) (countLit q [-84, -85]) (countLit q [-89, -91]) (count1598 q) 1 (meaning1596 q) (meaning1598 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1598 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-84, -85]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-89, -91])
  have hm := merge_right (literal (valuationOf q) (1597)) (literal (valuationOf q) (1599)) (countLit q [-84, -85]) (countLit q [-89, -91]) (count1598 q) 2 (meaning1597 q) (meaning1599 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1599 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-84, -85]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-89, -91])
  have hm := merge_left (literal (valuationOf q) (1594)) (literal (valuationOf q) (1598)) (countLit q [-84, -85]) (countLit q [-89, -91]) (count1598 q) 1 (meaning1594 q) (meaning1598 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1598 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-84, -85]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1599)) (countLit q [-84, -85]) (countLit q [-89, -91]) (count1598 q) 1 1 (meaning1594 q) (meaning1596 q) (meaning1599 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1596 = false ∨ valuation q 1599 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1600 = true := by
  have hs : count1598 q = (countLit q [-84, -85]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1600)) (countLit q [-84, -85]) (countLit q [-89, -91]) (count1598 q) 1 2 (meaning1594 q) (meaning1597 q) (meaning1600 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1597 = false ∨ valuation q 1600 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-84, -85]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-89, -91])
  have hm := merge_left (literal (valuationOf q) (1595)) (literal (valuationOf q) (1599)) (countLit q [-84, -85]) (countLit q [-89, -91]) (count1598 q) 2 (meaning1595 q) (meaning1599 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1599 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1600 = true := by
  have hs : count1598 q = (countLit q [-84, -85]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1600)) (countLit q [-84, -85]) (countLit q [-89, -91]) (count1598 q) 2 1 (meaning1595 q) (meaning1596 q) (meaning1600 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1596 = false ∨ valuation q 1600 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1601 = true := by
  have hs : count1598 q = (countLit q [-84, -85]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1601)) (countLit q [-84, -85]) (countLit q [-89, -91]) (count1598 q) 2 2 (meaning1595 q) (meaning1597 q) (meaning1601 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1597 = false ∨ valuation q 1601 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1598)) (literal (valuationOf q) (1602)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 1 (meaning1598 q) (meaning1602 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1602 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1599)) (literal (valuationOf q) (1603)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 2 (meaning1599 q) (meaning1603 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1603 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1600)) (literal (valuationOf q) (1604)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 3 (meaning1600 q) (meaning1604 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1604 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 4 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1591)) (literal (valuationOf q) (1602)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 1 (meaning1591 q) (meaning1602 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1602 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1603)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 1 1 (meaning1591 q) (meaning1598 q) (meaning1603 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1598 = false ∨ valuation q 1603 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1604)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 1 2 (meaning1591 q) (meaning1599 q) (meaning1604 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1599 = false ∨ valuation q 1604 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1605)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 1 3 (meaning1591 q) (meaning1600 q) (meaning1605 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1600 = false ∨ valuation q 1605 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1606)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 1 4 (meaning1591 q) (meaning1601 q) (meaning1606 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1601 = false ∨ valuation q 1606 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1592)) (literal (valuationOf q) (1603)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 2 (meaning1592 q) (meaning1603 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1603 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1604)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 2 1 (meaning1592 q) (meaning1598 q) (meaning1604 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1598 = false ∨ valuation q 1604 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1605)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 2 2 (meaning1592 q) (meaning1599 q) (meaning1605 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1599 = false ∨ valuation q 1605 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1606)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 2 3 (meaning1592 q) (meaning1600 q) (meaning1606 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1600 = false ∨ valuation q 1606 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1607)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 2 4 (meaning1592 q) (meaning1601 q) (meaning1607 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1601 = false ∨ valuation q 1607 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1593)) (literal (valuationOf q) (1604)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 3 (meaning1593 q) (meaning1604 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1604 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1605 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1605)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 3 1 (meaning1593 q) (meaning1598 q) (meaning1605 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1598 = false ∨ valuation q 1605 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1606 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1606)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 3 2 (meaning1593 q) (meaning1599 q) (meaning1606 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1599 = false ∨ valuation q 1606 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1607 = true := by
  have hs : count1602 q = (countLit q [-76, -80, -82]) + (countLit q [-84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -80, -82]) (l₂ := [-84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1607)) (countLit q [-76, -80, -82]) (countLit q [-84, -85, -89, -91]) (count1602 q) 3 3 (meaning1593 q) (meaning1600 q) (meaning1607 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1600 = false ∨ valuation q 1607 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1602)) (literal (valuationOf q) (1609)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 1 (meaning1602 q) (meaning1609 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1609 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1604)) (literal (valuationOf q) (1611)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 3 (meaning1604 q) (meaning1611 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1611 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1605)) (literal (valuationOf q) (1612)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 4 (meaning1605 q) (meaning1612 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1612 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1610)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 1 1 (meaning1582 q) (meaning1602 q) (meaning1610 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1602 = false ∨ valuation q 1610 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1611)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 1 2 (meaning1582 q) (meaning1603 q) (meaning1611 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1603 = false ∨ valuation q 1611 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-63, -64, -66, -67, -71, -73, -75]) + (countLit q [-76, -80, -82, -84, -85, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75]) (l₂ := [-76, -80, -82, -84, -85, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1612)) (countLit q [-63, -64, -66, -67, -71, -73, -75]) (countLit q [-76, -80, -82, -84, -85, -89, -91]) (count1609 q) 1 3 (meaning1582 q) (meaning1604 q) (meaning1612 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1604 = false ∨ valuation q 1612 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E047.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112047
