import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1564 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_right (literal (valuationOf q) (1560)) (literal (valuationOf q) (1564)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 2 (meaning1560 q) (meaning1564 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1564 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_right (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 3 (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1565 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1566 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1566)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 4 (meaning1562 q) (meaning1566 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1566 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1563 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_left (literal (valuationOf q) (1551)) (literal (valuationOf q) (1563)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 1 (meaning1551 q) (meaning1563 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1563 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1564 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1564)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 1 1 (meaning1551 q) (meaning1559 q) (meaning1564 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1559 = false ∨ valuation q 1564 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1565)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 1 2 (meaning1551 q) (meaning1560 q) (meaning1565 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1560 = false ∨ valuation q 1565 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1566)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 1 3 (meaning1551 q) (meaning1561 q) (meaning1566 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1561 = false ∨ valuation q 1566 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1567)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 1 4 (meaning1551 q) (meaning1562 q) (meaning1567 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1562 = false ∨ valuation q 1567 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1564 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_left (literal (valuationOf q) (1552)) (literal (valuationOf q) (1564)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 2 (meaning1552 q) (meaning1564 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1564 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1565 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1565)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 2 1 (meaning1552 q) (meaning1559 q) (meaning1565 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1559 = false ∨ valuation q 1565 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1566 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1566)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 2 2 (meaning1552 q) (meaning1560 q) (meaning1566 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1560 = false ∨ valuation q 1566 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1567 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1567)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 2 3 (meaning1552 q) (meaning1561 q) (meaning1567 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1561 = false ∨ valuation q 1567 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1565 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_left (literal (valuationOf q) (1553)) (literal (valuationOf q) (1565)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 3 (meaning1553 q) (meaning1565 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1565 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1566 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1566)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 3 1 (meaning1553 q) (meaning1559 q) (meaning1566 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1559 = false ∨ valuation q 1566 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1567 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1567)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 3 2 (meaning1553 q) (meaning1560 q) (meaning1567 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1560 = false ∨ valuation q 1567 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1568 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1568)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 3 3 (meaning1553 q) (meaning1561 q) (meaning1568 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1561 = false ∨ valuation q 1568 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1566 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_left (literal (valuationOf q) (1554)) (literal (valuationOf q) (1566)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 4 (meaning1554 q) (meaning1566 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1566 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1567 = true := by
  have hs : count1563 q = (countLit q [-2, -4, -7, -8]) + (countLit q [-9, -11, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8]) (l₂ := [-9, -11, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1567)) (countLit q [-2, -4, -7, -8]) (countLit q [-9, -11, -13, -16]) (count1563 q) 4 1 (meaning1554 q) (meaning1559 q) (meaning1567 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1559 = false ∨ valuation q 1567 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1571)) (countLit q [-17]) (countLit q [-19]) (count1571 q) 1 (meaningNeg19 q) (meaning1571 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1571 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1571)) (countLit q [-17]) (countLit q [-19]) (count1571 q) 1 (meaningNeg17 q) (meaning1571 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1571 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1572)) (countLit q [-17]) (countLit q [-19]) (count1571 q) 1 1 (meaningNeg17 q) (meaningNeg19 q) (meaning1572 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 1572 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1573)) (countLit q [-21]) (countLit q [-23]) (count1573 q) 1 (meaningNeg23 q) (meaning1573 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1573 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1573)) (countLit q [-21]) (countLit q [-23]) (count1573 q) 1 (meaningNeg21 q) (meaning1573 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1573 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1574 = true := by
  have hs : count1573 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1574)) (countLit q [-21]) (countLit q [-23]) (count1573 q) 1 1 (meaningNeg21 q) (meaningNeg23 q) (meaning1574 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 1574 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-17, -19]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-21, -23])
  have hm := merge_right (literal (valuationOf q) (1573)) (literal (valuationOf q) (1575)) (countLit q [-17, -19]) (countLit q [-21, -23]) (count1575 q) 1 (meaning1573 q) (meaning1575 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1575 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-17, -19]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-21, -23])
  have hm := merge_left (literal (valuationOf q) (1571)) (literal (valuationOf q) (1575)) (countLit q [-17, -19]) (countLit q [-21, -23]) (count1575 q) 1 (meaning1571 q) (meaning1575 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1575 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-17, -19]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-21, -23])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1576)) (countLit q [-17, -19]) (countLit q [-21, -23]) (count1575 q) 1 1 (meaning1571 q) (meaning1573 q) (meaning1576 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1573 = false ∨ valuation q 1576 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-17, -19]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-21, -23])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1577)) (countLit q [-17, -19]) (countLit q [-21, -23]) (count1575 q) 1 2 (meaning1571 q) (meaning1574 q) (meaning1577 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1574 = false ∨ valuation q 1577 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-17, -19]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-21, -23])
  have hm := merge_left (literal (valuationOf q) (1572)) (literal (valuationOf q) (1576)) (countLit q [-17, -19]) (countLit q [-21, -23]) (count1575 q) 2 (meaning1572 q) (meaning1576 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1576 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-17, -19]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-21, -23])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1577)) (countLit q [-17, -19]) (countLit q [-21, -23]) (count1575 q) 2 1 (meaning1572 q) (meaning1573 q) (meaning1577 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1573 = false ∨ valuation q 1577 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1578 = true := by
  have hs : count1575 q = (countLit q [-17, -19]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-21, -23])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1578)) (countLit q [-17, -19]) (countLit q [-21, -23]) (count1575 q) 2 2 (meaning1572 q) (meaning1574 q) (meaning1578 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1574 = false ∨ valuation q 1578 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1580)) (countLit q [-25]) (countLit q [-26]) (count1579 q) 1 1 (meaningNeg25 q) (meaningNeg26 q) (meaning1580 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 1580 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E036.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112036
