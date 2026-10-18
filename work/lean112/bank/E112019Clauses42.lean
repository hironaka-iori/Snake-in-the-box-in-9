import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1568 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1568)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 1 3 (meaning1553 q) (meaning1563 q) (meaning1568 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1563 = false ∨ valuation q 1568 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1566 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_left (literal (valuationOf q) (1554)) (literal (valuationOf q) (1566)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 2 (meaning1554 q) (meaning1566 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1566 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1567 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1567)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 2 1 (meaning1554 q) (meaning1561 q) (meaning1567 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1561 = false ∨ valuation q 1567 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1568 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1568)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 2 2 (meaning1554 q) (meaning1562 q) (meaning1568 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1562 = false ∨ valuation q 1568 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1567 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_left (literal (valuationOf q) (1555)) (literal (valuationOf q) (1567)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 3 (meaning1555 q) (meaning1567 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1567 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1568 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1568)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 3 1 (meaning1555 q) (meaning1561 q) (meaning1568 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1561 = false ∨ valuation q 1568 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1569 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1569)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 3 2 (meaning1555 q) (meaning1562 q) (meaning1569 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1562 = false ∨ valuation q 1569 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1570 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1570)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 3 3 (meaning1555 q) (meaning1563 q) (meaning1570 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1563 = false ∨ valuation q 1570 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1569 = true := by
  have hs : count1565 q = (countLit q [-46, -48, -51, -52]) + (countLit q [-54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -51, -52]) (l₂ := [-54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1569)) (countLit q [-46, -48, -51, -52]) (countLit q [-54, -55, -58, -61]) (count1565 q) 4 1 (meaning1556 q) (meaning1561 q) (meaning1569 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1561 = false ∨ valuation q 1569 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1575 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_right (literal (valuationOf q) (1567)) (literal (valuationOf q) (1575)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 3 (meaning1567 q) (meaning1575 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1575 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_left (literal (valuationOf q) (1542)) (literal (valuationOf q) (1573)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 1 (meaning1542 q) (meaning1573 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1573 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1574 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1574)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 1 1 (meaning1542 q) (meaning1565 q) (meaning1574 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1565 = false ∨ valuation q 1574 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1575 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1575)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 1 2 (meaning1542 q) (meaning1566 q) (meaning1575 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1566 = false ∨ valuation q 1575 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1576 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1576)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 1 3 (meaning1542 q) (meaning1567 q) (meaning1576 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1567 = false ∨ valuation q 1576 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1577 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1577)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 1 4 (meaning1542 q) (meaning1568 q) (meaning1577 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1568 = false ∨ valuation q 1577 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1578 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1578)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 1 5 (meaning1542 q) (meaning1569 q) (meaning1578 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1569 = false ∨ valuation q 1578 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1579 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1579)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 1 6 (meaning1542 q) (meaning1570 q) (meaning1579 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1570 = false ∨ valuation q 1579 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1574 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_left (literal (valuationOf q) (1543)) (literal (valuationOf q) (1574)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 2 (meaning1543 q) (meaning1574 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1574 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1575 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1575)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 2 1 (meaning1543 q) (meaning1565 q) (meaning1575 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1565 = false ∨ valuation q 1575 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1576 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1576)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 2 2 (meaning1543 q) (meaning1566 q) (meaning1576 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1566 = false ∨ valuation q 1576 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1577 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1577)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 2 3 (meaning1543 q) (meaning1567 q) (meaning1577 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1567 = false ∨ valuation q 1577 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1578 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1578)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 2 4 (meaning1543 q) (meaning1568 q) (meaning1578 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1568 = false ∨ valuation q 1578 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1579 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1579)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 2 5 (meaning1543 q) (meaning1569 q) (meaning1579 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1569 = false ∨ valuation q 1579 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1575 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_left (literal (valuationOf q) (1544)) (literal (valuationOf q) (1575)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 3 (meaning1544 q) (meaning1575 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1575 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1576 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1576)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 3 1 (meaning1544 q) (meaning1565 q) (meaning1576 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1565 = false ∨ valuation q 1576 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1577 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1577)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 3 2 (meaning1544 q) (meaning1566 q) (meaning1577 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1566 = false ∨ valuation q 1577 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1578 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1578)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 3 3 (meaning1544 q) (meaning1567 q) (meaning1578 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1567 = false ∨ valuation q 1578 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1579 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1579)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 3 4 (meaning1544 q) (meaning1568 q) (meaning1579 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1568 = false ∨ valuation q 1579 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1576 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_left (literal (valuationOf q) (1545)) (literal (valuationOf q) (1576)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 4 (meaning1545 q) (meaning1576 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1576 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1577 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1577)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 4 1 (meaning1545 q) (meaning1565 q) (meaning1577 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1565 = false ∨ valuation q 1577 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1578 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1578)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 4 2 (meaning1545 q) (meaning1566 q) (meaning1578 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1566 = false ∨ valuation q 1578 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1579 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1579)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 4 3 (meaning1545 q) (meaning1567 q) (meaning1579 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1567 = false ∨ valuation q 1579 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E019.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112019
