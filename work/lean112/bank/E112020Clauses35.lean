import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1560 q = (countLit q [-29, -30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-29, -30]) (l₂ := [-31, -34])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-29, -30]) (countLit q [-31, -34]) (count1560 q) 2 1 (meaning1557 q) (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1558 = false ∨ valuation q 1562 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1563 = true := by
  have hs : count1560 q = (countLit q [-29, -30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-29, -30]) (l₂ := [-31, -34])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1563)) (countLit q [-29, -30]) (countLit q [-31, -34]) (count1560 q) 2 2 (meaning1557 q) (meaning1559 q) (meaning1563 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1559 = false ∨ valuation q 1563 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1564)) (countLit q [-35]) (countLit q [-37]) (count1564 q) 1 (meaningNeg37 q) (meaning1564 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1564 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1564)) (countLit q [-35]) (countLit q [-37]) (count1564 q) 1 (meaningNeg35 q) (meaning1564 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1564 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1565)) (countLit q [-35]) (countLit q [-37]) (count1564 q) 1 1 (meaningNeg35 q) (meaningNeg37 q) (meaning1565 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 37 = true ∨ valuation q 1565 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1566)) (countLit q [-38]) (countLit q [-40]) (count1566 q) 1 (meaningNeg40 q) (meaning1566 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1566 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1566)) (countLit q [-38]) (countLit q [-40]) (count1566 q) 1 (meaningNeg38 q) (meaning1566 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1566 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 40 = true ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (1567)) (countLit q [-38]) (countLit q [-40]) (count1566 q) 1 1 (meaningNeg38 q) (meaningNeg40 q) (meaning1567 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 1567 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-35, -37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1566)) (literal (valuationOf q) (1568)) (countLit q [-35, -37]) (countLit q [-38, -40]) (count1568 q) 1 (meaning1566 q) (meaning1568 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1568 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-35, -37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1567)) (literal (valuationOf q) (1569)) (countLit q [-35, -37]) (countLit q [-38, -40]) (count1568 q) 2 (meaning1567 q) (meaning1569 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1569 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-35, -37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-38, -40])
  have hm := merge_left (literal (valuationOf q) (1564)) (literal (valuationOf q) (1568)) (countLit q [-35, -37]) (countLit q [-38, -40]) (count1568 q) 1 (meaning1564 q) (meaning1568 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1568 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-35, -37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-38, -40])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1569)) (countLit q [-35, -37]) (countLit q [-38, -40]) (count1568 q) 1 1 (meaning1564 q) (meaning1566 q) (meaning1569 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1566 = false ∨ valuation q 1569 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-35, -37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-38, -40])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1570)) (countLit q [-35, -37]) (countLit q [-38, -40]) (count1568 q) 1 2 (meaning1564 q) (meaning1567 q) (meaning1570 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1567 = false ∨ valuation q 1570 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-35, -37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-38, -40])
  have hm := merge_left (literal (valuationOf q) (1565)) (literal (valuationOf q) (1569)) (countLit q [-35, -37]) (countLit q [-38, -40]) (count1568 q) 2 (meaning1565 q) (meaning1569 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1569 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-35, -37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-38, -40])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1570)) (countLit q [-35, -37]) (countLit q [-38, -40]) (count1568 q) 2 1 (meaning1565 q) (meaning1566 q) (meaning1570 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1566 = false ∨ valuation q 1570 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1571 = true := by
  have hs : count1568 q = (countLit q [-35, -37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-38, -40])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1571)) (countLit q [-35, -37]) (countLit q [-38, -40]) (count1568 q) 2 2 (meaning1565 q) (meaning1567 q) (meaning1571 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1567 = false ∨ valuation q 1571 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1573 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1569)) (literal (valuationOf q) (1573)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 2 (meaning1569 q) (meaning1573 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1573 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1574 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1570)) (literal (valuationOf q) (1574)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 3 (meaning1570 q) (meaning1574 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1574 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1575 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1571)) (literal (valuationOf q) (1575)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 4 (meaning1571 q) (meaning1575 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1575 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1573 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1573)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 1 1 (meaning1560 q) (meaning1568 q) (meaning1573 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1568 = false ∨ valuation q 1573 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1574 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1574)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 1 2 (meaning1560 q) (meaning1569 q) (meaning1574 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1569 = false ∨ valuation q 1574 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1575 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1575)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 1 3 (meaning1560 q) (meaning1570 q) (meaning1575 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1570 = false ∨ valuation q 1575 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1576 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1576)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 1 4 (meaning1560 q) (meaning1571 q) (meaning1576 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1571 = false ∨ valuation q 1576 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1574 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1574)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 2 1 (meaning1561 q) (meaning1568 q) (meaning1574 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1568 = false ∨ valuation q 1574 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1575 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1575)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 2 2 (meaning1561 q) (meaning1569 q) (meaning1575 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1569 = false ∨ valuation q 1575 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1576 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1576)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 2 3 (meaning1561 q) (meaning1570 q) (meaning1576 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1570 = false ∨ valuation q 1576 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1575 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1575)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 3 1 (meaning1562 q) (meaning1568 q) (meaning1575 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1568 = false ∨ valuation q 1575 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1576 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1576)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 3 2 (meaning1562 q) (meaning1569 q) (meaning1576 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1569 = false ∨ valuation q 1576 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1577 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1577)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 3 3 (meaning1562 q) (meaning1570 q) (meaning1577 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1570 = false ∨ valuation q 1577 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1576 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1576)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 4 1 (meaning1563 q) (meaning1568 q) (meaning1576 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1568 = false ∨ valuation q 1576 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1577 = true := by
  have hs : count1572 q = (countLit q [-29, -30, -31, -34]) + (countLit q [-35, -37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -30, -31, -34]) (l₂ := [-35, -37, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1577)) (countLit q [-29, -30, -31, -34]) (countLit q [-35, -37, -38, -40]) (count1572 q) 4 2 (meaning1563 q) (meaning1569 q) (meaning1577 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1569 = false ∨ valuation q 1577 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1580)) (countLit q [-42]) (countLit q [-45]) (count1580 q) 1 (meaningNeg45 q) (meaning1580 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1580 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E020.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112020
