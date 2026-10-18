import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1361)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1432)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 3 3 (meaning1361 q) (meaning1415 q) (meaning1432 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1415 = false ∨ valuation q 1432 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1361)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1433)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 3 4 (meaning1361 q) (meaning1416 q) (meaning1433 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1416 = false ∨ valuation q 1433 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1434 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1361)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1434)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 3 5 (meaning1361 q) (meaning1417 q) (meaning1434 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1417 = false ∨ valuation q 1434 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1435 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1361)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1435)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 3 6 (meaning1361 q) (meaning1418 q) (meaning1435 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1418 = false ∨ valuation q 1435 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1436 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1361)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1436)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 3 7 (meaning1361 q) (meaning1419 q) (meaning1436 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1419 = false ∨ valuation q 1436 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1432)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 4 2 (meaning1362 q) (meaning1414 q) (meaning1432 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1414 = false ∨ valuation q 1432 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1433)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 4 3 (meaning1362 q) (meaning1415 q) (meaning1433 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1415 = false ∨ valuation q 1433 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1434 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1434)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 4 4 (meaning1362 q) (meaning1416 q) (meaning1434 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1416 = false ∨ valuation q 1434 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1435 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1435)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 4 5 (meaning1362 q) (meaning1417 q) (meaning1435 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1417 = false ∨ valuation q 1435 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1436 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1436)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 4 6 (meaning1362 q) (meaning1418 q) (meaning1436 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1418 = false ∨ valuation q 1436 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1437 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1437)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 4 7 (meaning1362 q) (meaning1419 q) (meaning1437 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1419 = false ∨ valuation q 1437 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1433)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 5 2 (meaning1363 q) (meaning1414 q) (meaning1433 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1414 = false ∨ valuation q 1433 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1434 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1434)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 5 3 (meaning1363 q) (meaning1415 q) (meaning1434 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1415 = false ∨ valuation q 1434 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1435 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1435)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 5 4 (meaning1363 q) (meaning1416 q) (meaning1435 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1416 = false ∨ valuation q 1435 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1436 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1436)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 5 5 (meaning1363 q) (meaning1417 q) (meaning1436 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1417 = false ∨ valuation q 1436 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1437 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1437)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 5 6 (meaning1363 q) (meaning1418 q) (meaning1437 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1418 = false ∨ valuation q 1437 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1438 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1438)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 5 7 (meaning1363 q) (meaning1419 q) (meaning1438 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1419 = false ∨ valuation q 1438 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1434 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1434)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 6 2 (meaning1364 q) (meaning1414 q) (meaning1434 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1414 = false ∨ valuation q 1434 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1435 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1435)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 6 3 (meaning1364 q) (meaning1415 q) (meaning1435 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1415 = false ∨ valuation q 1435 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1436 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1436)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 6 4 (meaning1364 q) (meaning1416 q) (meaning1436 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1416 = false ∨ valuation q 1436 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1437 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1437)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 6 5 (meaning1364 q) (meaning1417 q) (meaning1437 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1417 = false ∨ valuation q 1437 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1438 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1438)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 6 6 (meaning1364 q) (meaning1418 q) (meaning1438 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1418 = false ∨ valuation q 1438 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1435 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1435)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 7 2 (meaning1365 q) (meaning1414 q) (meaning1435 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1414 = false ∨ valuation q 1435 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1436 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1436)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 7 3 (meaning1365 q) (meaning1415 q) (meaning1436 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1415 = false ∨ valuation q 1436 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1437 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1437)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 7 4 (meaning1365 q) (meaning1416 q) (meaning1437 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1416 = false ∨ valuation q 1437 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1438 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1438)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 7 5 (meaning1365 q) (meaning1417 q) (meaning1438 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1417 = false ∨ valuation q 1438 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1436 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1436)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 8 2 (meaning1366 q) (meaning1414 q) (meaning1436 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1414 = false ∨ valuation q 1436 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1437 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1437)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 8 3 (meaning1366 q) (meaning1415 q) (meaning1437 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1415 = false ∨ valuation q 1437 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1438 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1438)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 8 4 (meaning1366 q) (meaning1416 q) (meaning1438 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1416 = false ∨ valuation q 1438 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1437 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1437)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 9 2 (meaning1367 q) (meaning1414 q) (meaning1437 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1414 = false ∨ valuation q 1437 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1438 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1438)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 9 3 (meaning1367 q) (meaning1415 q) (meaning1438 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1415 = false ∨ valuation q 1438 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1443)) (countLit q [-57]) (countLit q [-58]) (count1443 q) 1 (meaningNeg58 q) (meaning1443 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1443 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E161.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112161
