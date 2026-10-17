import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1567 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1567)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 4 5 (meaning1488 q) (meaning1548 q) (meaning1567 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1548 = false ∨ valuation q 1567 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1568 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1568)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 4 6 (meaning1488 q) (meaning1549 q) (meaning1568 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1549 = false ∨ valuation q 1568 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1569)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 4 7 (meaning1488 q) (meaning1550 q) (meaning1569 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1550 = false ∨ valuation q 1569 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1570)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 4 8 (meaning1488 q) (meaning1551 q) (meaning1570 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1551 = false ∨ valuation q 1570 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1571)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 4 9 (meaning1488 q) (meaning1552 q) (meaning1571 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1552 = false ∨ valuation q 1571 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1572)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 4 10 (meaning1488 q) (meaning1553 q) (meaning1572 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1553 = false ∨ valuation q 1572 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1573)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 4 11 (meaning1488 q) (meaning1554 q) (meaning1573 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1554 = false ∨ valuation q 1573 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1566 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1566)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 5 3 (meaning1489 q) (meaning1546 q) (meaning1566 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1546 = false ∨ valuation q 1566 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1567 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1567)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 5 4 (meaning1489 q) (meaning1547 q) (meaning1567 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1547 = false ∨ valuation q 1567 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1568 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1568)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 5 5 (meaning1489 q) (meaning1548 q) (meaning1568 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1548 = false ∨ valuation q 1568 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1569)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 5 6 (meaning1489 q) (meaning1549 q) (meaning1569 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1549 = false ∨ valuation q 1569 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1570)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 5 7 (meaning1489 q) (meaning1550 q) (meaning1570 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1550 = false ∨ valuation q 1570 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1571)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 5 8 (meaning1489 q) (meaning1551 q) (meaning1571 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1551 = false ∨ valuation q 1571 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1572)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 5 9 (meaning1489 q) (meaning1552 q) (meaning1572 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1552 = false ∨ valuation q 1572 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1573)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 5 10 (meaning1489 q) (meaning1553 q) (meaning1573 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1553 = false ∨ valuation q 1573 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1567 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1567)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 6 3 (meaning1490 q) (meaning1546 q) (meaning1567 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1546 = false ∨ valuation q 1567 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1568 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1568)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 6 4 (meaning1490 q) (meaning1547 q) (meaning1568 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1547 = false ∨ valuation q 1568 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1569)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 6 5 (meaning1490 q) (meaning1548 q) (meaning1569 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1548 = false ∨ valuation q 1569 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1570)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 6 6 (meaning1490 q) (meaning1549 q) (meaning1570 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1549 = false ∨ valuation q 1570 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1571)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 6 7 (meaning1490 q) (meaning1550 q) (meaning1571 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1550 = false ∨ valuation q 1571 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1572)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 6 8 (meaning1490 q) (meaning1551 q) (meaning1572 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1551 = false ∨ valuation q 1572 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1573)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 6 9 (meaning1490 q) (meaning1552 q) (meaning1573 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1552 = false ∨ valuation q 1573 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1574 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1574)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 6 10 (meaning1490 q) (meaning1553 q) (meaning1574 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1553 = false ∨ valuation q 1574 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1569)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 7 4 (meaning1491 q) (meaning1547 q) (meaning1569 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1547 = false ∨ valuation q 1569 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1570)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 7 5 (meaning1491 q) (meaning1548 q) (meaning1570 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1548 = false ∨ valuation q 1570 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1571)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 7 6 (meaning1491 q) (meaning1549 q) (meaning1571 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1549 = false ∨ valuation q 1571 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1572)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 7 7 (meaning1491 q) (meaning1550 q) (meaning1572 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1550 = false ∨ valuation q 1572 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1573)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 7 8 (meaning1491 q) (meaning1551 q) (meaning1573 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1551 = false ∨ valuation q 1573 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1574 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1574)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 7 9 (meaning1491 q) (meaning1552 q) (meaning1574 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1552 = false ∨ valuation q 1574 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1569)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 8 3 (meaning1492 q) (meaning1546 q) (meaning1569 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1546 = false ∨ valuation q 1569 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1571)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 8 5 (meaning1492 q) (meaning1548 q) (meaning1571 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1548 = false ∨ valuation q 1571 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1572)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 8 6 (meaning1492 q) (meaning1549 q) (meaning1572 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1549 = false ∨ valuation q 1572 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E004.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112004
