import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1570)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 4 8 (meaning1488 q) (meaning1551 q) (meaning1570 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1551 = false ∨ valuation q 1570 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1571)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 4 9 (meaning1488 q) (meaning1552 q) (meaning1571 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1552 = false ∨ valuation q 1571 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1572)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 4 10 (meaning1488 q) (meaning1553 q) (meaning1572 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1553 = false ∨ valuation q 1572 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1573)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 4 11 (meaning1488 q) (meaning1554 q) (meaning1573 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1554 = false ∨ valuation q 1573 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1567 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1567)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 5 4 (meaning1489 q) (meaning1547 q) (meaning1567 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1547 = false ∨ valuation q 1567 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1568 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1568)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 5 5 (meaning1489 q) (meaning1548 q) (meaning1568 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1548 = false ∨ valuation q 1568 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1569)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 5 6 (meaning1489 q) (meaning1549 q) (meaning1569 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1549 = false ∨ valuation q 1569 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1570)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 5 7 (meaning1489 q) (meaning1550 q) (meaning1570 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1550 = false ∨ valuation q 1570 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1571)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 5 8 (meaning1489 q) (meaning1551 q) (meaning1571 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1551 = false ∨ valuation q 1571 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1572)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 5 9 (meaning1489 q) (meaning1552 q) (meaning1572 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1552 = false ∨ valuation q 1572 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1573)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 5 10 (meaning1489 q) (meaning1553 q) (meaning1573 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1553 = false ∨ valuation q 1573 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1574 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1574)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 5 11 (meaning1489 q) (meaning1554 q) (meaning1574 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1554 = false ∨ valuation q 1574 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1567 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1567)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 6 3 (meaning1490 q) (meaning1546 q) (meaning1567 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1546 = false ∨ valuation q 1567 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1568 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1568)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 6 4 (meaning1490 q) (meaning1547 q) (meaning1568 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1547 = false ∨ valuation q 1568 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1569)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 6 5 (meaning1490 q) (meaning1548 q) (meaning1569 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1548 = false ∨ valuation q 1569 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1570)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 6 6 (meaning1490 q) (meaning1549 q) (meaning1570 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1549 = false ∨ valuation q 1570 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1571)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 6 7 (meaning1490 q) (meaning1550 q) (meaning1571 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1550 = false ∨ valuation q 1571 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1572)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 6 8 (meaning1490 q) (meaning1551 q) (meaning1572 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1551 = false ∨ valuation q 1572 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1573)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 6 9 (meaning1490 q) (meaning1552 q) (meaning1573 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1552 = false ∨ valuation q 1573 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1574 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1574)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 6 10 (meaning1490 q) (meaning1553 q) (meaning1574 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1553 = false ∨ valuation q 1574 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1575 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1575)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 6 11 (meaning1490 q) (meaning1554 q) (meaning1575 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1554 = false ∨ valuation q 1575 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1568 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1568)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 7 3 (meaning1491 q) (meaning1546 q) (meaning1568 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1546 = false ∨ valuation q 1568 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1569)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 7 4 (meaning1491 q) (meaning1547 q) (meaning1569 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1547 = false ∨ valuation q 1569 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1570)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 7 5 (meaning1491 q) (meaning1548 q) (meaning1570 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1548 = false ∨ valuation q 1570 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1571)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 7 6 (meaning1491 q) (meaning1549 q) (meaning1571 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1549 = false ∨ valuation q 1571 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1572)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 7 7 (meaning1491 q) (meaning1550 q) (meaning1572 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1550 = false ∨ valuation q 1572 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1573)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 7 8 (meaning1491 q) (meaning1551 q) (meaning1573 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1551 = false ∨ valuation q 1573 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1574 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1574)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 7 9 (meaning1491 q) (meaning1552 q) (meaning1574 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1552 = false ∨ valuation q 1574 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1575 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1575)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 7 10 (meaning1491 q) (meaning1553 q) (meaning1575 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1553 = false ∨ valuation q 1575 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1569)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 8 3 (meaning1492 q) (meaning1546 q) (meaning1569 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1546 = false ∨ valuation q 1569 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1570)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 8 4 (meaning1492 q) (meaning1547 q) (meaning1570 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1547 = false ∨ valuation q 1570 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1571)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 8 5 (meaning1492 q) (meaning1548 q) (meaning1571 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1548 = false ∨ valuation q 1571 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E040.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112040
