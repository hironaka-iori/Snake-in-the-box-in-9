import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-21, -23]) + (countLit q [-24, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-24, -26])
  have hm := merge_left (literal (valuationOf q) (1355)) (literal (valuationOf q) (1359)) (countLit q [-21, -23]) (countLit q [-24, -26]) (count1358 q) 2 (meaning1355 q) (meaning1359 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1359 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1360 = true := by
  have hs : count1358 q = (countLit q [-21, -23]) + (countLit q [-24, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-24, -26])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1360)) (countLit q [-21, -23]) (countLit q [-24, -26]) (count1358 q) 2 1 (meaning1355 q) (meaning1356 q) (meaning1360 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1356 = false ∨ valuation q 1360 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1361 = true := by
  have hs : count1358 q = (countLit q [-21, -23]) + (countLit q [-24, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-24, -26])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1361)) (countLit q [-21, -23]) (countLit q [-24, -26]) (count1358 q) 2 2 (meaning1355 q) (meaning1357 q) (meaning1361 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1357 = false ∨ valuation q 1361 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_right (literal (valuationOf q) (1358)) (literal (valuationOf q) (1362)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 1 (meaning1358 q) (meaning1362 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1362 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_right (literal (valuationOf q) (1359)) (literal (valuationOf q) (1363)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 2 (meaning1359 q) (meaning1363 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1363 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_right (literal (valuationOf q) (1360)) (literal (valuationOf q) (1364)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 3 (meaning1360 q) (meaning1364 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1364 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1365 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_right (literal (valuationOf q) (1361)) (literal (valuationOf q) (1365)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 4 (meaning1361 q) (meaning1365 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1365 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_left (literal (valuationOf q) (1351)) (literal (valuationOf q) (1362)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 1 (meaning1351 q) (meaning1362 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1362 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1363)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 1 1 (meaning1351 q) (meaning1358 q) (meaning1363 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1358 = false ∨ valuation q 1363 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1364)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 1 2 (meaning1351 q) (meaning1359 q) (meaning1364 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1359 = false ∨ valuation q 1364 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1365 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1365)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 1 3 (meaning1351 q) (meaning1360 q) (meaning1365 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1360 = false ∨ valuation q 1365 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_left (literal (valuationOf q) (1352)) (literal (valuationOf q) (1363)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 2 (meaning1352 q) (meaning1363 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1363 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1364)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 2 1 (meaning1352 q) (meaning1358 q) (meaning1364 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1358 = false ∨ valuation q 1364 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1365 = true := by
  have hs : count1362 q = (countLit q [-14, -16, -19]) + (countLit q [-21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1365)) (countLit q [-14, -16, -19]) (countLit q [-21, -23, -24, -26]) (count1362 q) 2 2 (meaning1352 q) (meaning1359 q) (meaning1365 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1359 = false ∨ valuation q 1365 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1370)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 2 (meaning1363 q) (meaning1370 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1370 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_right (literal (valuationOf q) (1364)) (literal (valuationOf q) (1371)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 3 (meaning1364 q) (meaning1371 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1371 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_left (literal (valuationOf q) (1343)) (literal (valuationOf q) (1369)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 1 (meaning1343 q) (meaning1369 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1369 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1370)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 1 1 (meaning1343 q) (meaning1362 q) (meaning1370 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1362 = false ∨ valuation q 1370 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1371)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 1 2 (meaning1343 q) (meaning1363 q) (meaning1371 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1363 = false ∨ valuation q 1371 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1372 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1372)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 1 3 (meaning1343 q) (meaning1364 q) (meaning1372 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1364 = false ∨ valuation q 1372 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1373 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1373)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 1 4 (meaning1343 q) (meaning1365 q) (meaning1373 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1365 = false ∨ valuation q 1373 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_left (literal (valuationOf q) (1344)) (literal (valuationOf q) (1370)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 2 (meaning1344 q) (meaning1370 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1370 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1371)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 2 1 (meaning1344 q) (meaning1362 q) (meaning1371 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1362 = false ∨ valuation q 1371 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1372 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1372)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 2 2 (meaning1344 q) (meaning1363 q) (meaning1372 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1363 = false ∨ valuation q 1372 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1373 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1373)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 2 3 (meaning1344 q) (meaning1364 q) (meaning1373 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1364 = false ∨ valuation q 1373 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1374 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1374)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 2 4 (meaning1344 q) (meaning1365 q) (meaning1374 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1365 = false ∨ valuation q 1374 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_left (literal (valuationOf q) (1345)) (literal (valuationOf q) (1371)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 3 (meaning1345 q) (meaning1371 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1371 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1372 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1372)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 3 1 (meaning1345 q) (meaning1362 q) (meaning1372 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1362 = false ∨ valuation q 1372 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1373 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1373)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 3 2 (meaning1345 q) (meaning1363 q) (meaning1373 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1363 = false ∨ valuation q 1373 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1374 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1374)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 3 3 (meaning1345 q) (meaning1364 q) (meaning1374 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1364 = false ∨ valuation q 1374 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1373 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1346)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1373)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 4 1 (meaning1346 q) (meaning1362 q) (meaning1373 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1362 = false ∨ valuation q 1373 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1374 = true := by
  have hs : count1369 q = (countLit q [-2, -3, -7, -8, -10, -13]) + (countLit q [-14, -16, -19, -21, -23, -24, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13]) (l₂ := [-14, -16, -19, -21, -23, -24, -26])
  have hm := merge_two (literal (valuationOf q) (1346)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1374)) (countLit q [-2, -3, -7, -8, -10, -13]) (countLit q [-14, -16, -19, -21, -23, -24, -26]) (count1369 q) 4 2 (meaning1346 q) (meaning1363 q) (meaning1374 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1363 = false ∨ valuation q 1374 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E183.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112183
