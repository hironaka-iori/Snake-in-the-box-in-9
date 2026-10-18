import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1548)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 5 3 (meaning1518 q) (meaning1536 q) (meaning1548 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1536 = false ∨ valuation q 1548 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1549)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 5 4 (meaning1518 q) (meaning1537 q) (meaning1549 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1537 = false ∨ valuation q 1549 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1550)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 5 5 (meaning1518 q) (meaning1538 q) (meaning1550 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1538 = false ∨ valuation q 1550 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1519)) (literal (valuationOf q) (1546)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 6 (meaning1519 q) (meaning1546 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1546 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1547)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 6 1 (meaning1519 q) (meaning1534 q) (meaning1547 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1534 = false ∨ valuation q 1547 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1548)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 6 2 (meaning1519 q) (meaning1535 q) (meaning1548 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1535 = false ∨ valuation q 1548 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1549 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1549)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 6 3 (meaning1519 q) (meaning1536 q) (meaning1549 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1536 = false ∨ valuation q 1549 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1555)) (countLit q [-35]) (countLit q [-37]) (count1555 q) 1 (meaningNeg37 q) (meaning1555 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1555 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1555)) (countLit q [-35]) (countLit q [-37]) (count1555 q) 1 (meaningNeg35 q) (meaning1555 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1555 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1556)) (countLit q [-35]) (countLit q [-37]) (count1555 q) 1 1 (meaningNeg35 q) (meaningNeg37 q) (meaning1556 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 37 = true ∨ valuation q 1556 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1555)) (literal (valuationOf q) (1557)) (countLit q [-33]) (countLit q [-35, -37]) (count1557 q) 1 (meaning1555 q) (meaning1557 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1557 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (countLit q [-33]) (countLit q [-35, -37]) (count1557 q) 2 (meaning1556 q) (meaning1558 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1557)) (countLit q [-33]) (countLit q [-35, -37]) (count1557 q) 1 (meaningNeg33 q) (meaning1557 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1557 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1555 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1558)) (countLit q [-33]) (countLit q [-35, -37]) (count1557 q) 1 1 (meaningNeg33 q) (meaning1555 q) (meaning1558 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1555 = false ∨ valuation q 1558 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1556 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1559)) (countLit q [-33]) (countLit q [-35, -37]) (count1557 q) 1 2 (meaningNeg33 q) (meaning1556 q) (meaning1559 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1556 = false ∨ valuation q 1559 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1560)) (countLit q [-39]) (countLit q [-41]) (count1560 q) 1 (meaningNeg41 q) (meaning1560 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1560 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1560)) (countLit q [-39]) (countLit q [-41]) (count1560 q) 1 (meaningNeg39 q) (meaning1560 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1560 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1561)) (countLit q [-39]) (countLit q [-41]) (count1560 q) 1 1 (meaningNeg39 q) (meaningNeg41 q) (meaning1561 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 1561 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1562)) (countLit q [-43]) (countLit q [-44]) (count1562 q) 1 (meaningNeg44 q) (meaning1562 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1562 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1562)) (countLit q [-43]) (countLit q [-44]) (count1562 q) 1 (meaningNeg43 q) (meaning1562 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1562 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1563 = true := by
  have hs : count1562 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1563)) (countLit q [-43]) (countLit q [-44]) (count1562 q) 1 1 (meaningNeg43 q) (meaningNeg44 q) (meaning1563 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 1563 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-39, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1564)) (countLit q [-39, -41]) (countLit q [-43, -44]) (count1564 q) 1 (meaning1562 q) (meaning1564 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1564 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-39, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (1563)) (literal (valuationOf q) (1565)) (countLit q [-39, -41]) (countLit q [-43, -44]) (count1564 q) 2 (meaning1563 q) (meaning1565 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1565 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-39, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (1560)) (literal (valuationOf q) (1564)) (countLit q [-39, -41]) (countLit q [-43, -44]) (count1564 q) 1 (meaning1560 q) (meaning1564 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1564 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-39, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1565)) (countLit q [-39, -41]) (countLit q [-43, -44]) (count1564 q) 1 1 (meaning1560 q) (meaning1562 q) (meaning1565 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1562 = false ∨ valuation q 1565 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-39, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-39, -41]) (countLit q [-43, -44]) (count1564 q) 2 (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1565 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-39, -41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1566)) (countLit q [-39, -41]) (countLit q [-43, -44]) (count1564 q) 2 1 (meaning1561 q) (meaning1562 q) (meaning1566 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1562 = false ∨ valuation q 1566 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_right (literal (valuationOf q) (1564)) (literal (valuationOf q) (1568)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 1 (meaning1564 q) (meaning1568 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1568 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_right (literal (valuationOf q) (1565)) (literal (valuationOf q) (1569)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 2 (meaning1565 q) (meaning1569 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1569 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_right (literal (valuationOf q) (1566)) (literal (valuationOf q) (1570)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 3 (meaning1566 q) (meaning1570 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1570 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1568)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 1 (meaning1557 q) (meaning1568 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1568 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1564)) (literal (valuationOf q) (1569)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 1 1 (meaning1557 q) (meaning1564 q) (meaning1569 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1564 = false ∨ valuation q 1569 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E258.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112258
