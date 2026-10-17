import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1486 = true := by
  have hs : count1484 q = (countLit q [-39, -41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1486)) (countLit q [-39, -41]) (countLit q [-42, -44]) (count1484 q) 2 1 (meaning1481 q) (meaning1482 q) (meaning1486 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1482 = false ∨ valuation q 1486 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1487 = true := by
  have hs : count1484 q = (countLit q [-39, -41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1487)) (countLit q [-39, -41]) (countLit q [-42, -44]) (count1484 q) 2 2 (meaning1481 q) (meaning1483 q) (meaning1487 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1483 = false ∨ valuation q 1487 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1484)) (literal (valuationOf q) (1488)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 1 (meaning1484 q) (meaning1488 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1488 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1485)) (literal (valuationOf q) (1489)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 2 (meaning1485 q) (meaning1489 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1489 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1486)) (literal (valuationOf q) (1490)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 3 (meaning1486 q) (meaning1490 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1490 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1487)) (literal (valuationOf q) (1491)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 4 (meaning1487 q) (meaning1491 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1491 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_left (literal (valuationOf q) (1477)) (literal (valuationOf q) (1488)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 1 (meaning1477 q) (meaning1488 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1488 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1489)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 1 1 (meaning1477 q) (meaning1484 q) (meaning1489 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1484 = false ∨ valuation q 1489 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1490)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 1 2 (meaning1477 q) (meaning1485 q) (meaning1490 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1485 = false ∨ valuation q 1490 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1491)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 1 3 (meaning1477 q) (meaning1486 q) (meaning1491 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1486 = false ∨ valuation q 1491 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1492 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1492)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 1 4 (meaning1477 q) (meaning1487 q) (meaning1492 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1487 = false ∨ valuation q 1492 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_left (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 2 (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1489 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1490)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 2 1 (meaning1478 q) (meaning1484 q) (meaning1490 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1484 = false ∨ valuation q 1490 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1491)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 2 2 (meaning1478 q) (meaning1485 q) (meaning1491 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1485 = false ∨ valuation q 1491 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1492 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1492)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 2 3 (meaning1478 q) (meaning1486 q) (meaning1492 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1486 = false ∨ valuation q 1492 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_left (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 3 (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1490 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1491)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 3 1 (meaning1479 q) (meaning1484 q) (meaning1491 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1484 = false ∨ valuation q 1491 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1492 = true := by
  have hs : count1488 q = (countLit q [-32, -34, -35]) + (countLit q [-39, -41, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35]) (l₂ := [-39, -41, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1492)) (countLit q [-32, -34, -35]) (countLit q [-39, -41, -42, -44]) (count1488 q) 3 2 (meaning1479 q) (meaning1485 q) (meaning1492 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1485 = false ∨ valuation q 1492 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1495 = true := by
  have hs : count1495 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1495)) (countLit q [-45]) (countLit q [-48]) (count1495 q) 1 (meaningNeg48 q) (meaning1495 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1495 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1495 = true := by
  have hs : count1495 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1495)) (countLit q [-45]) (countLit q [-48]) (count1495 q) 1 (meaningNeg45 q) (meaning1495 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1495 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1496 = true := by
  have hs : count1495 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1496)) (countLit q [-45]) (countLit q [-48]) (count1495 q) 1 1 (meaningNeg45 q) (meaningNeg48 q) (meaning1496 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 1496 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1497)) (countLit q [-50]) (countLit q [-51]) (count1497 q) 1 (meaningNeg51 q) (meaning1497 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1497 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1497)) (countLit q [-50]) (countLit q [-51]) (count1497 q) 1 (meaningNeg50 q) (meaning1497 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1497 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1498 = true := by
  have hs : count1497 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1498)) (countLit q [-50]) (countLit q [-51]) (count1497 q) 1 1 (meaningNeg50 q) (meaningNeg51 q) (meaning1498 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 1498 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_right (literal (valuationOf q) (1497)) (literal (valuationOf q) (1499)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count1499 q) 1 (meaning1497 q) (meaning1499 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1499 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_right (literal (valuationOf q) (1498)) (literal (valuationOf q) (1500)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count1499 q) 2 (meaning1498 q) (meaning1500 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1500 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_left (literal (valuationOf q) (1495)) (literal (valuationOf q) (1499)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count1499 q) 1 (meaning1495 q) (meaning1499 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1499 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1500)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count1499 q) 1 1 (meaning1495 q) (meaning1497 q) (meaning1500 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1497 = false ∨ valuation q 1500 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1501)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count1499 q) 1 2 (meaning1495 q) (meaning1498 q) (meaning1501 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1498 = false ∨ valuation q 1501 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_left (literal (valuationOf q) (1496)) (literal (valuationOf q) (1500)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count1499 q) 2 (meaning1496 q) (meaning1500 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1500 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1501)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count1499 q) 2 1 (meaning1496 q) (meaning1497 q) (meaning1501 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1497 = false ∨ valuation q 1501 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1502 = true := by
  have hs : count1499 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1502)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count1499 q) 2 2 (meaning1496 q) (meaning1498 q) (meaning1502 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1498 = false ∨ valuation q 1502 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E158.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112158
