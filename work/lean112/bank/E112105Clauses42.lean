import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1559)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 1 2 (meaning1526 q) (meaning1550 q) (meaning1559 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1550 = false ∨ valuation q 1559 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1560 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1560)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 1 3 (meaning1526 q) (meaning1551 q) (meaning1560 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1551 = false ∨ valuation q 1560 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1561 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1561)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 1 4 (meaning1526 q) (meaning1552 q) (meaning1561 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1552 = false ∨ valuation q 1561 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1562 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1562)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 1 5 (meaning1526 q) (meaning1553 q) (meaning1562 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1553 = false ∨ valuation q 1562 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1559)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 2 1 (meaning1527 q) (meaning1549 q) (meaning1559 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1549 = false ∨ valuation q 1559 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1560 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1560)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 2 2 (meaning1527 q) (meaning1550 q) (meaning1560 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1550 = false ∨ valuation q 1560 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1561 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1561)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 2 3 (meaning1527 q) (meaning1551 q) (meaning1561 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1551 = false ∨ valuation q 1561 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1562 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1562)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 2 4 (meaning1527 q) (meaning1552 q) (meaning1562 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1552 = false ∨ valuation q 1562 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1563 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1563)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 2 5 (meaning1527 q) (meaning1553 q) (meaning1563 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1553 = false ∨ valuation q 1563 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1564 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1564)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 2 6 (meaning1527 q) (meaning1554 q) (meaning1564 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1554 = false ∨ valuation q 1564 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1560 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1560)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 3 1 (meaning1528 q) (meaning1549 q) (meaning1560 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1549 = false ∨ valuation q 1560 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1561 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1561)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 3 2 (meaning1528 q) (meaning1550 q) (meaning1561 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1550 = false ∨ valuation q 1561 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1562 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1562)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 3 3 (meaning1528 q) (meaning1551 q) (meaning1562 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1551 = false ∨ valuation q 1562 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1563 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1563)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 3 4 (meaning1528 q) (meaning1552 q) (meaning1563 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1552 = false ∨ valuation q 1563 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1564 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1564)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 3 5 (meaning1528 q) (meaning1553 q) (meaning1564 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1553 = false ∨ valuation q 1564 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1561 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1561)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 4 1 (meaning1529 q) (meaning1549 q) (meaning1561 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1549 = false ∨ valuation q 1561 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1562 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1562)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 4 2 (meaning1529 q) (meaning1550 q) (meaning1562 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1550 = false ∨ valuation q 1562 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1563 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1563)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 4 3 (meaning1529 q) (meaning1551 q) (meaning1563 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1551 = false ∨ valuation q 1563 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1564 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1564)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 4 4 (meaning1529 q) (meaning1552 q) (meaning1564 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1552 = false ∨ valuation q 1564 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1563 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1563)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 5 2 (meaning1530 q) (meaning1550 q) (meaning1563 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1550 = false ∨ valuation q 1563 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1565 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1565)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 5 4 (meaning1530 q) (meaning1552 q) (meaning1565 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1552 = false ∨ valuation q 1565 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1572 = true := by
  have hs : count1572 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1572)) (countLit q [-35]) (countLit q [-37]) (count1572 q) 1 (meaningNeg37 q) (meaning1572 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1572 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1572 = true := by
  have hs : count1572 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1572)) (countLit q [-35]) (countLit q [-37]) (count1572 q) 1 (meaningNeg35 q) (meaning1572 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1572 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1573 = true := by
  have hs : count1572 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1573)) (countLit q [-35]) (countLit q [-37]) (count1572 q) 1 1 (meaningNeg35 q) (meaningNeg37 q) (meaning1573 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 37 = true ∨ valuation q 1573 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1572)) (literal (valuationOf q) (1574)) (countLit q [-33]) (countLit q [-35, -37]) (count1574 q) 1 (meaning1572 q) (meaning1574 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1574 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1575 = true := by
  have hs : count1574 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1573)) (literal (valuationOf q) (1575)) (countLit q [-33]) (countLit q [-35, -37]) (count1574 q) 2 (meaning1573 q) (meaning1575 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1575 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1574)) (countLit q [-33]) (countLit q [-35, -37]) (count1574 q) 1 (meaningNeg33 q) (meaning1574 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1574 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1572 = false ∨ valuationOf q 1575 = true := by
  have hs : count1574 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1575)) (countLit q [-33]) (countLit q [-35, -37]) (count1574 q) 1 1 (meaningNeg33 q) (meaning1572 q) (meaning1575 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1572 = false ∨ valuation q 1575 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true := by
  have hs : count1574 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1576)) (countLit q [-33]) (countLit q [-35, -37]) (count1574 q) 1 2 (meaningNeg33 q) (meaning1573 q) (meaning1576 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1573 = false ∨ valuation q 1576 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1577 = true := by
  have hs : count1577 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1577)) (countLit q [-40]) (countLit q [-41]) (count1577 q) 1 (meaningNeg41 q) (meaning1577 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1577 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1577 = true := by
  have hs : count1577 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1577)) (countLit q [-40]) (countLit q [-41]) (count1577 q) 1 (meaningNeg40 q) (meaning1577 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1577 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1578 = true := by
  have hs : count1577 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1578)) (countLit q [-40]) (countLit q [-41]) (count1577 q) 1 1 (meaningNeg40 q) (meaningNeg41 q) (meaning1578 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 41 = true ∨ valuation q 1578 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E105.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112105
