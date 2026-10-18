import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1554 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1554)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 5 5 (meaning1518 q) (meaning1541 q) (meaning1554 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1541 = false ∨ valuation q 1554 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1553)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 6 3 (meaning1519 q) (meaning1539 q) (meaning1553 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1539 = false ∨ valuation q 1553 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1568 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1568)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 1 8 (meaning1487 q) (meaning1552 q) (meaning1568 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1552 = false ∨ valuation q 1568 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1569 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1569)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 1 9 (meaning1487 q) (meaning1553 q) (meaning1569 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1553 = false ∨ valuation q 1569 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1570 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1570)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 1 10 (meaning1487 q) (meaning1554 q) (meaning1570 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1554 = false ∨ valuation q 1570 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1568 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1568)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 2 7 (meaning1488 q) (meaning1551 q) (meaning1568 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1551 = false ∨ valuation q 1568 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1569 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1569)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 2 8 (meaning1488 q) (meaning1552 q) (meaning1569 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1552 = false ∨ valuation q 1569 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1570 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1570)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 2 9 (meaning1488 q) (meaning1553 q) (meaning1570 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1553 = false ∨ valuation q 1570 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1571 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1571)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 2 10 (meaning1488 q) (meaning1554 q) (meaning1571 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1554 = false ∨ valuation q 1571 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1572 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1572)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 2 11 (meaning1488 q) (meaning1555 q) (meaning1572 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1555 = false ∨ valuation q 1572 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1568 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1568)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 3 6 (meaning1489 q) (meaning1550 q) (meaning1568 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1550 = false ∨ valuation q 1568 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1569 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1569)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 3 7 (meaning1489 q) (meaning1551 q) (meaning1569 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1551 = false ∨ valuation q 1569 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1570 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1570)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 3 8 (meaning1489 q) (meaning1552 q) (meaning1570 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1552 = false ∨ valuation q 1570 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1571 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1571)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 3 9 (meaning1489 q) (meaning1553 q) (meaning1571 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1553 = false ∨ valuation q 1571 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1572 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1572)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 3 10 (meaning1489 q) (meaning1554 q) (meaning1572 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1554 = false ∨ valuation q 1572 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1568 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1568)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 4 5 (meaning1490 q) (meaning1549 q) (meaning1568 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1549 = false ∨ valuation q 1568 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1569 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1569)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 4 6 (meaning1490 q) (meaning1550 q) (meaning1569 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1550 = false ∨ valuation q 1569 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1570 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1570)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 4 7 (meaning1490 q) (meaning1551 q) (meaning1570 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1551 = false ∨ valuation q 1570 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1571 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1571)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 4 8 (meaning1490 q) (meaning1552 q) (meaning1571 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1552 = false ∨ valuation q 1571 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1572 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1572)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 4 9 (meaning1490 q) (meaning1553 q) (meaning1572 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1553 = false ∨ valuation q 1572 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1573 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1573)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 4 10 (meaning1490 q) (meaning1554 q) (meaning1573 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1554 = false ∨ valuation q 1573 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1569 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1569)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 5 5 (meaning1491 q) (meaning1549 q) (meaning1569 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1549 = false ∨ valuation q 1569 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1570 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1570)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 5 6 (meaning1491 q) (meaning1550 q) (meaning1570 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1550 = false ∨ valuation q 1570 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1571 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1571)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 5 7 (meaning1491 q) (meaning1551 q) (meaning1571 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1551 = false ∨ valuation q 1571 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1572 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1572)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 5 8 (meaning1491 q) (meaning1552 q) (meaning1572 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1552 = false ∨ valuation q 1572 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1573 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1573)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 5 9 (meaning1491 q) (meaning1553 q) (meaning1573 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1553 = false ∨ valuation q 1573 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1569 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1569)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 6 4 (meaning1492 q) (meaning1548 q) (meaning1569 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1548 = false ∨ valuation q 1569 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1570 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1570)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 6 5 (meaning1492 q) (meaning1549 q) (meaning1570 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1549 = false ∨ valuation q 1570 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1571 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1571)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 6 6 (meaning1492 q) (meaning1550 q) (meaning1571 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1550 = false ∨ valuation q 1571 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1572 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1572)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 6 7 (meaning1492 q) (meaning1551 q) (meaning1572 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1551 = false ∨ valuation q 1572 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1573 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1573)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 6 8 (meaning1492 q) (meaning1552 q) (meaning1573 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1552 = false ∨ valuation q 1573 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1569 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1569)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 7 3 (meaning1493 q) (meaning1547 q) (meaning1569 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1547 = false ∨ valuation q 1569 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E078.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112078
