import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 68 = true ∨ valuationOf q 1559 = true := by
  have hs : count1558 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (1559)) (countLit q [-65]) (countLit q [-68]) (count1558 q) 1 1 (meaningNeg65 q) (meaningNeg68 q) (meaning1559 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 1559 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1560)) (countLit q [-71]) (countLit q [-73]) (count1560 q) 1 (meaningNeg73 q) (meaning1560 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1560 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1560)) (countLit q [-71]) (countLit q [-73]) (count1560 q) 1 (meaningNeg71 q) (meaning1560 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1560 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1561)) (countLit q [-71]) (countLit q [-73]) (count1560 q) 1 1 (meaningNeg71 q) (meaningNeg73 q) (meaning1561 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 1561 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-65, -68]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -68]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1560)) (literal (valuationOf q) (1562)) (countLit q [-65, -68]) (countLit q [-71, -73]) (count1562 q) 1 (meaning1560 q) (meaning1562 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1562 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1563 = true := by
  have hs : count1562 q = (countLit q [-65, -68]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -68]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1561)) (literal (valuationOf q) (1563)) (countLit q [-65, -68]) (countLit q [-71, -73]) (count1562 q) 2 (meaning1561 q) (meaning1563 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1563 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-65, -68]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -68]) (l₂ := [-71, -73])
  have hm := merge_left (literal (valuationOf q) (1558)) (literal (valuationOf q) (1562)) (countLit q [-65, -68]) (countLit q [-71, -73]) (count1562 q) 1 (meaning1558 q) (meaning1562 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1562 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1563 = true := by
  have hs : count1562 q = (countLit q [-65, -68]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -68]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1563)) (countLit q [-65, -68]) (countLit q [-71, -73]) (count1562 q) 1 1 (meaning1558 q) (meaning1560 q) (meaning1563 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1560 = false ∨ valuation q 1563 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1564 = true := by
  have hs : count1562 q = (countLit q [-65, -68]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -68]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1564)) (countLit q [-65, -68]) (countLit q [-71, -73]) (count1562 q) 1 2 (meaning1558 q) (meaning1561 q) (meaning1564 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1561 = false ∨ valuation q 1564 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1563 = true := by
  have hs : count1562 q = (countLit q [-65, -68]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -68]) (l₂ := [-71, -73])
  have hm := merge_left (literal (valuationOf q) (1559)) (literal (valuationOf q) (1563)) (countLit q [-65, -68]) (countLit q [-71, -73]) (count1562 q) 2 (meaning1559 q) (meaning1563 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1563 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1564 = true := by
  have hs : count1562 q = (countLit q [-65, -68]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -68]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1564)) (countLit q [-65, -68]) (countLit q [-71, -73]) (count1562 q) 2 1 (meaning1559 q) (meaning1560 q) (meaning1564 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1560 = false ∨ valuation q 1564 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1562 q = (countLit q [-65, -68]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-65, -68]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-65, -68]) (countLit q [-71, -73]) (count1562 q) 2 2 (meaning1559 q) (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1561 = false ∨ valuation q 1565 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1566)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 1 (meaning1562 q) (meaning1566 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1566 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1563)) (literal (valuationOf q) (1567)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 2 (meaning1563 q) (meaning1567 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1567 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1564)) (literal (valuationOf q) (1568)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 3 (meaning1564 q) (meaning1568 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1568 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1565)) (literal (valuationOf q) (1569)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 4 (meaning1565 q) (meaning1569 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1569 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_left (literal (valuationOf q) (1555)) (literal (valuationOf q) (1566)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 1 (meaning1555 q) (meaning1566 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1566 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1567)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 1 1 (meaning1555 q) (meaning1562 q) (meaning1567 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1562 = false ∨ valuation q 1567 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1568)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 1 2 (meaning1555 q) (meaning1563 q) (meaning1568 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1563 = false ∨ valuation q 1568 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1564)) (literal (valuationOf q) (1569)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 1 3 (meaning1555 q) (meaning1564 q) (meaning1569 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1564 = false ∨ valuation q 1569 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1570)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 1 4 (meaning1555 q) (meaning1565 q) (meaning1570 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1565 = false ∨ valuation q 1570 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1567)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 2 (meaning1556 q) (meaning1567 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1567 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1568)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 2 1 (meaning1556 q) (meaning1562 q) (meaning1568 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1562 = false ∨ valuation q 1568 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1569)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 2 2 (meaning1556 q) (meaning1563 q) (meaning1569 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1563 = false ∨ valuation q 1569 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1564)) (literal (valuationOf q) (1570)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 2 3 (meaning1556 q) (meaning1564 q) (meaning1570 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1564 = false ∨ valuation q 1570 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1571 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1571)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 2 4 (meaning1556 q) (meaning1565 q) (meaning1571 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1565 = false ∨ valuation q 1571 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1568)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 3 (meaning1557 q) (meaning1568 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1568 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1569)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 3 1 (meaning1557 q) (meaning1562 q) (meaning1569 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1562 = false ∨ valuation q 1569 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1570 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1570)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 3 2 (meaning1557 q) (meaning1563 q) (meaning1570 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1563 = false ∨ valuation q 1570 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1571 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1564)) (literal (valuationOf q) (1571)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 3 3 (meaning1557 q) (meaning1564 q) (meaning1571 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1564 = false ∨ valuation q 1571 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1572 = true := by
  have hs : count1566 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -68, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -68, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1572)) (countLit q [-59, -61, -63]) (countLit q [-65, -68, -71, -73]) (count1566 q) 3 4 (meaning1557 q) (meaning1565 q) (meaning1572 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1565 = false ∨ valuation q 1572 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-74]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1573)) (countLit q [-74]) (countLit q [-77]) (count1573 q) 1 (meaningNeg77 q) (meaning1573 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1573 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E158.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112158
