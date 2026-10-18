import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1587 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1587)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 3 2 (meaning1573 q) (meaning1580 q) (meaning1587 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1580 = false ∨ valuation q 1587 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1587 = true := by
  have hs : count1583 q = (countLit q [-15, -17, -18, -20]) + (countLit q [-24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18, -20]) (l₂ := [-24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1587)) (countLit q [-15, -17, -18, -20]) (countLit q [-24, -25, -27, -28]) (count1583 q) 4 1 (meaning1574 q) (meaning1579 q) (meaning1587 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1579 = false ∨ valuation q 1587 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1595 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1595)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 2 3 (meaning1560 q) (meaning1585 q) (meaning1595 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1585 = false ∨ valuation q 1595 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1597 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1597)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 2 5 (meaning1560 q) (meaning1587 q) (meaning1597 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1587 = false ∨ valuation q 1597 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_left (literal (valuationOf q) (1561)) (literal (valuationOf q) (1593)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 3 (meaning1561 q) (meaning1593 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1593 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1594)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 3 1 (meaning1561 q) (meaning1583 q) (meaning1594 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1583 = false ∨ valuation q 1594 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1595 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1595)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 3 2 (meaning1561 q) (meaning1584 q) (meaning1595 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1584 = false ∨ valuation q 1595 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1596 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1596)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 3 3 (meaning1561 q) (meaning1585 q) (meaning1596 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1585 = false ∨ valuation q 1596 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1597 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1597)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 3 4 (meaning1561 q) (meaning1586 q) (meaning1597 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1586 = false ∨ valuation q 1597 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1598 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1598)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 3 5 (meaning1561 q) (meaning1587 q) (meaning1598 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1587 = false ∨ valuation q 1598 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1595 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1595)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 4 1 (meaning1562 q) (meaning1583 q) (meaning1595 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1583 = false ∨ valuation q 1595 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1596 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1596)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 4 2 (meaning1562 q) (meaning1584 q) (meaning1596 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1584 = false ∨ valuation q 1596 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1597 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1597)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 4 3 (meaning1562 q) (meaning1585 q) (meaning1597 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1585 = false ∨ valuation q 1597 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1598 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1598)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 4 4 (meaning1562 q) (meaning1586 q) (meaning1598 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1586 = false ∨ valuation q 1598 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1599 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1599)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 4 5 (meaning1562 q) (meaning1587 q) (meaning1599 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1587 = false ∨ valuation q 1599 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1596 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1596)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 5 1 (meaning1563 q) (meaning1583 q) (meaning1596 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1583 = false ∨ valuation q 1596 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1597 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1597)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 5 2 (meaning1563 q) (meaning1584 q) (meaning1597 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1584 = false ∨ valuation q 1597 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1598 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1598)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 5 3 (meaning1563 q) (meaning1585 q) (meaning1598 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1585 = false ∨ valuation q 1598 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1599 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1599)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 5 4 (meaning1563 q) (meaning1586 q) (meaning1599 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1586 = false ∨ valuation q 1599 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1596 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_left (literal (valuationOf q) (1564)) (literal (valuationOf q) (1596)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 6 (meaning1564 q) (meaning1596 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1596 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1597 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1597)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 6 1 (meaning1564 q) (meaning1583 q) (meaning1597 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1583 = false ∨ valuation q 1597 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1598 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1598)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 6 2 (meaning1564 q) (meaning1584 q) (meaning1598 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1584 = false ∨ valuation q 1598 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1599 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1599)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 6 3 (meaning1564 q) (meaning1585 q) (meaning1599 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1585 = false ∨ valuation q 1599 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1600 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1600)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 6 4 (meaning1564 q) (meaning1586 q) (meaning1600 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1586 = false ∨ valuation q 1600 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1601 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1601)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 6 5 (meaning1564 q) (meaning1587 q) (meaning1601 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1587 = false ∨ valuation q 1601 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1597 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_left (literal (valuationOf q) (1565)) (literal (valuationOf q) (1597)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 7 (meaning1565 q) (meaning1597 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1597 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1598 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1598)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 7 1 (meaning1565 q) (meaning1583 q) (meaning1598 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1583 = false ∨ valuation q 1598 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1599 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1599)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 7 2 (meaning1565 q) (meaning1584 q) (meaning1599 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1584 = false ∨ valuation q 1599 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1600 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1600)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 7 3 (meaning1565 q) (meaning1585 q) (meaning1600 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1585 = false ∨ valuation q 1600 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1601 = true := by
  have hs : count1591 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -20, -24, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1601)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -20, -24, -25, -27, -28]) (count1591 q) 7 4 (meaning1565 q) (meaning1586 q) (meaning1601 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1586 = false ∨ valuation q 1601 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1607 = true := by
  have hs : count1607 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1607)) (countLit q [-30]) (countLit q [-33]) (count1607 q) 1 (meaningNeg33 q) (meaning1607 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1607 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1607 = true := by
  have hs : count1607 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1607)) (countLit q [-30]) (countLit q [-33]) (count1607 q) 1 (meaningNeg30 q) (meaning1607 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1607 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E052.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112052
