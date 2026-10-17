import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1545 = true := by
  have hs : count1545 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1545)) (countLit q [-5]) (countLit q [-7]) (count1545 q) 1 (meaningNeg5 q) (meaning1545 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1545 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1546 = true := by
  have hs : count1545 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-5)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1546)) (countLit q [-5]) (countLit q [-7]) (count1545 q) 1 1 (meaningNeg5 q) (meaningNeg7 q) (meaning1546 q) hs
  change (! (valuationOf q 5)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 7 = true ∨ valuation q 1546 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-1, -3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-5, -7])
  have hm := merge_right (literal (valuationOf q) (1545)) (literal (valuationOf q) (1547)) (countLit q [-1, -3]) (countLit q [-5, -7]) (count1547 q) 1 (meaning1545 q) (meaning1547 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1547 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1548 = true := by
  have hs : count1547 q = (countLit q [-1, -3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-5, -7])
  have hm := merge_right (literal (valuationOf q) (1546)) (literal (valuationOf q) (1548)) (countLit q [-1, -3]) (countLit q [-5, -7]) (count1547 q) 2 (meaning1546 q) (meaning1548 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1548 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-1, -3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-5, -7])
  have hm := merge_left (literal (valuationOf q) (1543)) (literal (valuationOf q) (1547)) (countLit q [-1, -3]) (countLit q [-5, -7]) (count1547 q) 1 (meaning1543 q) (meaning1547 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1547 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1548 = true := by
  have hs : count1547 q = (countLit q [-1, -3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-5, -7])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1548)) (countLit q [-1, -3]) (countLit q [-5, -7]) (count1547 q) 1 1 (meaning1543 q) (meaning1545 q) (meaning1548 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1545 = false ∨ valuation q 1548 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1549 = true := by
  have hs : count1547 q = (countLit q [-1, -3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-5, -7])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1549)) (countLit q [-1, -3]) (countLit q [-5, -7]) (count1547 q) 1 2 (meaning1543 q) (meaning1546 q) (meaning1549 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1546 = false ∨ valuation q 1549 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1551)) (countLit q [-8]) (countLit q [-10]) (count1551 q) 1 (meaningNeg10 q) (meaning1551 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1551 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 10 = true ∨ valuationOf q 1552 = true := by
  have hs : count1551 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (1552)) (countLit q [-8]) (countLit q [-10]) (count1551 q) 1 1 (meaningNeg8 q) (meaningNeg10 q) (meaning1552 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 1552 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1554)) (countLit q [-11]) (countLit q [-12]) (count1553 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning1554 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 1554 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (1554)) (literal (valuationOf q) (1556)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1555 q) 2 (meaning1554 q) (meaning1556 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1556 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1557 = true := by
  have hs : count1555 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1557)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1555 q) 1 2 (meaning1551 q) (meaning1554 q) (meaning1557 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1554 = false ∨ valuation q 1557 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1558 = true := by
  have hs : count1555 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1558)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1555 q) 2 2 (meaning1552 q) (meaning1554 q) (meaning1558 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1554 = false ∨ valuation q 1558 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1559 q) 2 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1557)) (literal (valuationOf q) (1561)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1559 q) 3 (meaning1557 q) (meaning1561 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1561 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1559 q) 4 (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1562 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1562)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1559 q) 1 3 (meaning1547 q) (meaning1557 q) (meaning1562 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1557 = false ∨ valuation q 1562 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1563 = true := by
  have hs : count1559 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1563)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1559 q) 1 4 (meaning1547 q) (meaning1558 q) (meaning1563 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1558 = false ∨ valuation q 1563 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1562 = true := by
  have hs : count1559 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1562)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1559 q) 2 2 (meaning1548 q) (meaning1556 q) (meaning1562 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1556 = false ∨ valuation q 1562 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1563 = true := by
  have hs : count1559 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1563)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1559 q) 2 3 (meaning1548 q) (meaning1557 q) (meaning1563 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1557 = false ∨ valuation q 1563 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1564 = true := by
  have hs : count1559 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1564)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1559 q) 2 4 (meaning1548 q) (meaning1558 q) (meaning1564 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1558 = false ∨ valuation q 1564 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1565 = true := by
  have hs : count1559 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1565)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1559 q) 3 4 (meaning1549 q) (meaning1558 q) (meaning1565 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1558 = false ∨ valuation q 1565 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1567 = true := by
  have hs : count1567 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1567)) (countLit q [-15]) (countLit q [-17]) (count1567 q) 1 (meaningNeg17 q) (meaning1567 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1567 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1567 = true := by
  have hs : count1567 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1567)) (countLit q [-15]) (countLit q [-17]) (count1567 q) 1 (meaningNeg15 q) (meaning1567 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1567 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1568 = true := by
  have hs : count1567 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1568)) (countLit q [-15]) (countLit q [-17]) (count1567 q) 1 1 (meaningNeg15 q) (meaningNeg17 q) (meaning1568 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 17 = true ∨ valuation q 1568 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1569)) (countLit q [-18]) (countLit q [-20]) (count1569 q) 1 (meaningNeg20 q) (meaning1569 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1569 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1569)) (countLit q [-18]) (countLit q [-20]) (count1569 q) 1 (meaningNeg18 q) (meaning1569 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1569 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1570 = true := by
  have hs : count1569 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1570)) (countLit q [-18]) (countLit q [-20]) (count1569 q) 1 1 (meaningNeg18 q) (meaningNeg20 q) (meaning1570 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 20 = true ∨ valuation q 1570 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-15, -17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-15, -17]) (l₂ := [-18, -20])
  have hm := merge_right (literal (valuationOf q) (1569)) (literal (valuationOf q) (1571)) (countLit q [-15, -17]) (countLit q [-18, -20]) (count1571 q) 1 (meaning1569 q) (meaning1571 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1571 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-15, -17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-15, -17]) (l₂ := [-18, -20])
  have hm := merge_right (literal (valuationOf q) (1570)) (literal (valuationOf q) (1572)) (countLit q [-15, -17]) (countLit q [-18, -20]) (count1571 q) 2 (meaning1570 q) (meaning1572 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1572 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-15, -17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-15, -17]) (l₂ := [-18, -20])
  have hm := merge_left (literal (valuationOf q) (1567)) (literal (valuationOf q) (1571)) (countLit q [-15, -17]) (countLit q [-18, -20]) (count1571 q) 1 (meaning1567 q) (meaning1571 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1571 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-15, -17]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-15, -17]) (l₂ := [-18, -20])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1572)) (countLit q [-15, -17]) (countLit q [-18, -20]) (count1571 q) 1 1 (meaning1567 q) (meaning1569 q) (meaning1572 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1569 = false ∨ valuation q 1572 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E052.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112052
