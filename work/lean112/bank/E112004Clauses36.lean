import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 2 (meaning1472 q) (meaning1474 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (1469)) (literal (valuationOf q) (1473)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 1 (meaning1469 q) (meaning1473 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1473 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1474)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 1 1 (meaning1469 q) (meaning1471 q) (meaning1474 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1471 = false ∨ valuation q 1474 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 1 2 (meaning1469 q) (meaning1472 q) (meaning1475 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1472 = false ∨ valuation q 1475 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (1470)) (literal (valuationOf q) (1474)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 2 (meaning1470 q) (meaning1474 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1474 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1475 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1475)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 2 1 (meaning1470 q) (meaning1471 q) (meaning1475 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1471 = false ∨ valuation q 1475 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1476 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1476)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 2 2 (meaning1470 q) (meaning1472 q) (meaning1476 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1472 = false ∨ valuation q 1476 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1477)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 1 (meaning1473 q) (meaning1477 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1477 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 2 (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1478 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1479)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 3 (meaning1475 q) (meaning1479 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1479 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1480)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 4 (meaning1476 q) (meaning1480 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1480 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1478)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 1 1 (meaning1465 q) (meaning1473 q) (meaning1478 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1473 = false ∨ valuation q 1478 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1479)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 1 2 (meaning1465 q) (meaning1474 q) (meaning1479 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1474 = false ∨ valuation q 1479 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1480)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 1 3 (meaning1465 q) (meaning1475 q) (meaning1480 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1475 = false ∨ valuation q 1480 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1479)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 2 1 (meaning1466 q) (meaning1473 q) (meaning1479 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1473 = false ∨ valuation q 1479 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1480)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 2 2 (meaning1466 q) (meaning1474 q) (meaning1480 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1474 = false ∨ valuation q 1480 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1481)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 2 3 (meaning1466 q) (meaning1475 q) (meaning1481 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1475 = false ∨ valuation q 1481 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1480)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 3 1 (meaning1467 q) (meaning1473 q) (meaning1480 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1473 = false ∨ valuation q 1480 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1481 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1481)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 3 2 (meaning1467 q) (meaning1474 q) (meaning1481 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1474 = false ∨ valuation q 1481 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1482 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1482)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 3 3 (meaning1467 q) (meaning1475 q) (meaning1482 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1475 = false ∨ valuation q 1482 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1468)) (literal (valuationOf q) (1480)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 4 (meaning1468 q) (meaning1480 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1480 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1481 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1481)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 4 1 (meaning1468 q) (meaning1473 q) (meaning1481 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1473 = false ∨ valuation q 1481 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1482 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1482)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 4 2 (meaning1468 q) (meaning1474 q) (meaning1482 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1474 = false ∨ valuation q 1482 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1483 = true := by
  have hs : count1477 q = (countLit q [-18, -20, -21, -22]) + (countLit q [-24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -21, -22]) (l₂ := [-24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1483)) (countLit q [-18, -20, -21, -22]) (countLit q [-24, -26, -28, -30]) (count1477 q) 4 3 (meaning1468 q) (meaning1475 q) (meaning1483 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1475 = false ∨ valuation q 1483 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1478)) (literal (valuationOf q) (1486)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 2 (meaning1478 q) (meaning1486 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1486 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 4 (meaning1480 q) (meaning1488 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1488 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1481)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 5 (meaning1481 q) (meaning1489 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1489 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 6 (meaning1482 q) (meaning1490 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1490 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1486)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 1 (meaning1454 q) (meaning1477 q) (meaning1486 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1477 = false ∨ valuation q 1486 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1487)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 2 (meaning1454 q) (meaning1478 q) (meaning1487 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1478 = false ∨ valuation q 1487 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 3 (meaning1454 q) (meaning1479 q) (meaning1488 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1479 = false ∨ valuation q 1488 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-2, -3, -5, -6, -12, -13, -15]) + (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15]) (l₂ := [-18, -20, -21, -22, -24, -26, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -6, -12, -13, -15]) (countLit q [-18, -20, -21, -22, -24, -26, -28, -30]) (count1485 q) 1 4 (meaning1454 q) (meaning1480 q) (meaning1489 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1480 = false ∨ valuation q 1489 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E004.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112004
