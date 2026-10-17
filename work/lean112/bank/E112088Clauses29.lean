import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1506 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1506)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 5 4 (meaning1429 q) (meaning1486 q) (meaning1506 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1486 = false ∨ valuation q 1506 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1507 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1507)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 5 5 (meaning1429 q) (meaning1487 q) (meaning1507 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1487 = false ∨ valuation q 1507 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1508 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1508)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 5 6 (meaning1429 q) (meaning1488 q) (meaning1508 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1488 = false ∨ valuation q 1508 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1509 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1509)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 5 7 (meaning1429 q) (meaning1489 q) (meaning1509 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1489 = false ∨ valuation q 1509 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1510 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1510)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 5 8 (meaning1429 q) (meaning1490 q) (meaning1510 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1490 = false ∨ valuation q 1510 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1507 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1507)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 6 4 (meaning1430 q) (meaning1486 q) (meaning1507 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1486 = false ∨ valuation q 1507 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1508 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1508)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 6 5 (meaning1430 q) (meaning1487 q) (meaning1508 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1487 = false ∨ valuation q 1508 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1509 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1509)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 6 6 (meaning1430 q) (meaning1488 q) (meaning1509 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1488 = false ∨ valuation q 1509 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1510 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1510)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 6 7 (meaning1430 q) (meaning1489 q) (meaning1510 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1489 = false ∨ valuation q 1510 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1512 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1512)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 6 9 (meaning1430 q) (meaning1491 q) (meaning1512 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1491 = false ∨ valuation q 1512 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1507 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1507)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 7 3 (meaning1431 q) (meaning1485 q) (meaning1507 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1485 = false ∨ valuation q 1507 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1508 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1508)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 7 4 (meaning1431 q) (meaning1486 q) (meaning1508 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1486 = false ∨ valuation q 1508 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1510 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1510)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 7 6 (meaning1431 q) (meaning1488 q) (meaning1510 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1488 = false ∨ valuation q 1510 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1510 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1510)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 8 5 (meaning1432 q) (meaning1487 q) (meaning1510 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1487 = false ∨ valuation q 1510 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1517)) (countLit q [-61]) (countLit q [-63]) (count1517 q) 1 (meaningNeg63 q) (meaning1517 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1517 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1517 = true := by
  have hs : count1517 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1517)) (countLit q [-61]) (countLit q [-63]) (count1517 q) 1 (meaningNeg61 q) (meaning1517 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1517 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1518 = true := by
  have hs : count1517 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1518)) (countLit q [-61]) (countLit q [-63]) (count1517 q) 1 1 (meaningNeg61 q) (meaningNeg63 q) (meaning1518 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 1518 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1517)) (literal (valuationOf q) (1519)) (countLit q [-59]) (countLit q [-61, -63]) (count1519 q) 1 (meaning1517 q) (meaning1519 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1519 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1518)) (literal (valuationOf q) (1520)) (countLit q [-59]) (countLit q [-61, -63]) (count1519 q) 2 (meaning1518 q) (meaning1520 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1520 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1519)) (countLit q [-59]) (countLit q [-61, -63]) (count1519 q) 1 (meaningNeg59 q) (meaning1519 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1519 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1517 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1520)) (countLit q [-59]) (countLit q [-61, -63]) (count1519 q) 1 1 (meaningNeg59 q) (meaning1517 q) (meaning1520 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1517 = false ∨ valuation q 1520 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1522)) (countLit q [-64]) (countLit q [-66]) (count1522 q) 1 (meaningNeg64 q) (meaning1522 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1522 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1523 = true := by
  have hs : count1522 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1523)) (countLit q [-64]) (countLit q [-66]) (count1522 q) 1 1 (meaningNeg64 q) (meaningNeg66 q) (meaning1523 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 1523 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1524)) (countLit q [-69]) (countLit q [-71]) (count1524 q) 1 (meaningNeg71 q) (meaning1524 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1524 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1524)) (countLit q [-69]) (countLit q [-71]) (count1524 q) 1 (meaningNeg69 q) (meaning1524 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1524 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1525)) (countLit q [-69]) (countLit q [-71]) (count1524 q) 1 1 (meaningNeg69 q) (meaningNeg71 q) (meaning1525 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 71 = true ∨ valuation q 1525 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-64, -66]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-69, -71])
  have hm := merge_left (literal (valuationOf q) (1522)) (literal (valuationOf q) (1526)) (countLit q [-64, -66]) (countLit q [-69, -71]) (count1526 q) 1 (meaning1522 q) (meaning1526 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1526 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-64, -66]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-69, -71])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1527)) (countLit q [-64, -66]) (countLit q [-69, -71]) (count1526 q) 1 1 (meaning1522 q) (meaning1524 q) (meaning1527 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1524 = false ∨ valuation q 1527 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1528 = true := by
  have hs : count1526 q = (countLit q [-64, -66]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-69, -71])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1528)) (countLit q [-64, -66]) (countLit q [-69, -71]) (count1526 q) 1 2 (meaning1522 q) (meaning1525 q) (meaning1528 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1525 = false ∨ valuation q 1528 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-64, -66]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-69, -71])
  have hm := merge_left (literal (valuationOf q) (1523)) (literal (valuationOf q) (1527)) (countLit q [-64, -66]) (countLit q [-69, -71]) (count1526 q) 2 (meaning1523 q) (meaning1527 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1527 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1528 = true := by
  have hs : count1526 q = (countLit q [-64, -66]) + (countLit q [-69, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-69, -71])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1528)) (countLit q [-64, -66]) (countLit q [-69, -71]) (count1526 q) 2 1 (meaning1523 q) (meaning1524 q) (meaning1528 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1524 = false ∨ valuation q 1528 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-59, -61, -63]) + (countLit q [-64, -66, -69, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-64, -66, -69, -71])
  have hm := merge_right (literal (valuationOf q) (1526)) (literal (valuationOf q) (1530)) (countLit q [-59, -61, -63]) (countLit q [-64, -66, -69, -71]) (count1530 q) 1 (meaning1526 q) (meaning1530 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1530 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E088.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112088
