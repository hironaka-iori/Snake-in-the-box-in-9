import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-17, -18, -20]) + (countLit q [-22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-22, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1427)) (countLit q [-17, -18, -20]) (countLit q [-22, -24, -25, -27]) (count1426 q) 1 1 (meaning1415 q) (meaning1422 q) (meaning1427 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1422 = false ∨ valuation q 1427 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-17, -18, -20]) + (countLit q [-22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-22, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1416)) (literal (valuationOf q) (1427)) (countLit q [-17, -18, -20]) (countLit q [-22, -24, -25, -27]) (count1426 q) 2 (meaning1416 q) (meaning1427 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1427 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1428 = true := by
  have hs : count1426 q = (countLit q [-17, -18, -20]) + (countLit q [-22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-22, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1417)) (literal (valuationOf q) (1428)) (countLit q [-17, -18, -20]) (countLit q [-22, -24, -25, -27]) (count1426 q) 3 (meaning1417 q) (meaning1428 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1428 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-3, -5, -8, -9, -10, -13, -14]) + (countLit q [-17, -18, -20, -22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14]) (l₂ := [-17, -18, -20, -22, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1406)) (literal (valuationOf q) (1433)) (countLit q [-3, -5, -8, -9, -10, -13, -14]) (countLit q [-17, -18, -20, -22, -24, -25, -27]) (count1433 q) 1 (meaning1406 q) (meaning1433 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1433 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-3, -5, -8, -9, -10, -13, -14]) + (countLit q [-17, -18, -20, -22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14]) (l₂ := [-17, -18, -20, -22, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1426)) (literal (valuationOf q) (1434)) (countLit q [-3, -5, -8, -9, -10, -13, -14]) (countLit q [-17, -18, -20, -22, -24, -25, -27]) (count1433 q) 1 1 (meaning1406 q) (meaning1426 q) (meaning1434 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1426 = false ∨ valuation q 1434 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-3, -5, -8, -9, -10, -13, -14]) + (countLit q [-17, -18, -20, -22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14]) (l₂ := [-17, -18, -20, -22, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1407)) (literal (valuationOf q) (1434)) (countLit q [-3, -5, -8, -9, -10, -13, -14]) (countLit q [-17, -18, -20, -22, -24, -25, -27]) (count1433 q) 2 (meaning1407 q) (meaning1434 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1434 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1435 = true := by
  have hs : count1433 q = (countLit q [-3, -5, -8, -9, -10, -13, -14]) + (countLit q [-17, -18, -20, -22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14]) (l₂ := [-17, -18, -20, -22, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1426)) (literal (valuationOf q) (1435)) (countLit q [-3, -5, -8, -9, -10, -13, -14]) (countLit q [-17, -18, -20, -22, -24, -25, -27]) (count1433 q) 2 1 (meaning1407 q) (meaning1426 q) (meaning1435 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1426 = false ∨ valuation q 1435 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1436 = true := by
  have hs : count1433 q = (countLit q [-3, -5, -8, -9, -10, -13, -14]) + (countLit q [-17, -18, -20, -22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14]) (l₂ := [-17, -18, -20, -22, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1427)) (literal (valuationOf q) (1436)) (countLit q [-3, -5, -8, -9, -10, -13, -14]) (countLit q [-17, -18, -20, -22, -24, -25, -27]) (count1433 q) 2 2 (meaning1407 q) (meaning1427 q) (meaning1436 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1427 = false ∨ valuation q 1436 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1437 = true := by
  have hs : count1433 q = (countLit q [-3, -5, -8, -9, -10, -13, -14]) + (countLit q [-17, -18, -20, -22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14]) (l₂ := [-17, -18, -20, -22, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1437)) (countLit q [-3, -5, -8, -9, -10, -13, -14]) (countLit q [-17, -18, -20, -22, -24, -25, -27]) (count1433 q) 2 3 (meaning1407 q) (meaning1428 q) (meaning1437 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1428 = false ∨ valuation q 1437 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1436 = true := by
  have hs : count1433 q = (countLit q [-3, -5, -8, -9, -10, -13, -14]) + (countLit q [-17, -18, -20, -22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14]) (l₂ := [-17, -18, -20, -22, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1426)) (literal (valuationOf q) (1436)) (countLit q [-3, -5, -8, -9, -10, -13, -14]) (countLit q [-17, -18, -20, -22, -24, -25, -27]) (count1433 q) 3 1 (meaning1408 q) (meaning1426 q) (meaning1436 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1426 = false ∨ valuation q 1436 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1437 = true := by
  have hs : count1433 q = (countLit q [-3, -5, -8, -9, -10, -13, -14]) + (countLit q [-17, -18, -20, -22, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14]) (l₂ := [-17, -18, -20, -22, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1427)) (literal (valuationOf q) (1437)) (countLit q [-3, -5, -8, -9, -10, -13, -14]) (countLit q [-17, -18, -20, -22, -24, -25, -27]) (count1433 q) 3 2 (meaning1408 q) (meaning1427 q) (meaning1437 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1427 = false ∨ valuation q 1437 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1452)) (countLit q [-35]) (countLit q [-36]) (count1452 q) 1 (meaningNeg36 q) (meaning1452 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1452 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1452)) (countLit q [-35]) (countLit q [-36]) (count1452 q) 1 (meaningNeg35 q) (meaning1452 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1452 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 36 = true ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (1453)) (countLit q [-35]) (countLit q [-36]) (count1452 q) 1 1 (meaningNeg35 q) (meaningNeg36 q) (meaning1453 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 1453 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1454)) (countLit q [-37]) (countLit q [-38]) (count1454 q) 1 (meaningNeg37 q) (meaning1454 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1454 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-35, -36]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-37, -38])
  have hm := merge_left (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-35, -36]) (countLit q [-37, -38]) (count1456 q) 1 (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1456 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-35, -36]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1457)) (countLit q [-35, -36]) (countLit q [-37, -38]) (count1456 q) 1 1 (meaning1452 q) (meaning1454 q) (meaning1457 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1454 = false ∨ valuation q 1457 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-35, -36]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-37, -38])
  have hm := merge_left (literal (valuationOf q) (1453)) (literal (valuationOf q) (1457)) (countLit q [-35, -36]) (countLit q [-37, -38]) (count1456 q) 2 (meaning1453 q) (meaning1457 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1457 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-29, -31, -33]) + (countLit q [-35, -36, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33]) (l₂ := [-35, -36, -37, -38])
  have hm := merge_right (literal (valuationOf q) (1456)) (literal (valuationOf q) (1460)) (countLit q [-29, -31, -33]) (countLit q [-35, -36, -37, -38]) (count1460 q) 1 (meaning1456 q) (meaning1460 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1460 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1461 = true := by
  have hs : count1460 q = (countLit q [-29, -31, -33]) + (countLit q [-35, -36, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33]) (l₂ := [-35, -36, -37, -38])
  have hm := merge_right (literal (valuationOf q) (1457)) (literal (valuationOf q) (1461)) (countLit q [-29, -31, -33]) (countLit q [-35, -36, -37, -38]) (count1460 q) 2 (meaning1457 q) (meaning1461 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1461 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1467)) (countLit q [-39]) (countLit q [-41]) (count1467 q) 1 (meaningNeg39 q) (meaning1467 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1467 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-43]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1469)) (countLit q [-43]) (countLit q [-47]) (count1469 q) 1 (meaningNeg47 q) (meaning1469 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1469 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-43]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1469)) (countLit q [-43]) (countLit q [-47]) (count1469 q) 1 (meaningNeg43 q) (meaning1469 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1469 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-39, -41]) + (countLit q [-43, -47]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -47])
  have hm := merge_right (literal (valuationOf q) (1469)) (literal (valuationOf q) (1471)) (countLit q [-39, -41]) (countLit q [-43, -47]) (count1471 q) 1 (meaning1469 q) (meaning1471 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1471 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-39, -41]) + (countLit q [-43, -47]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-43, -47])
  have hm := merge_left (literal (valuationOf q) (1467)) (literal (valuationOf q) (1471)) (countLit q [-39, -41]) (countLit q [-43, -47]) (count1471 q) 1 (meaning1467 q) (meaning1471 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1471 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1477)) (countLit q [-55]) (countLit q [-56]) (count1477 q) 1 (meaningNeg56 q) (meaning1477 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1477 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1477)) (countLit q [-55]) (countLit q [-56]) (count1477 q) 1 (meaningNeg55 q) (meaning1477 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1477 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-51, -53]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -53]) (l₂ := [-55, -56])
  have hm := merge_right (literal (valuationOf q) (1477)) (literal (valuationOf q) (1479)) (countLit q [-51, -53]) (countLit q [-55, -56]) (count1479 q) 1 (meaning1477 q) (meaning1479 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1479 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-39, -41, -43, -47]) + (countLit q [-51, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -43, -47]) (l₂ := [-51, -53, -55, -56])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1483)) (countLit q [-39, -41, -43, -47]) (countLit q [-51, -53, -55, -56]) (count1483 q) 1 (meaning1479 q) (meaning1483 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1483 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-39, -41, -43, -47]) + (countLit q [-51, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-39, -41, -43, -47]) (l₂ := [-51, -53, -55, -56])
  have hm := merge_left (literal (valuationOf q) (1471)) (literal (valuationOf q) (1483)) (countLit q [-39, -41, -43, -47]) (countLit q [-51, -53, -55, -56]) (count1483 q) 1 (meaning1471 q) (meaning1483 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1483 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true := by
  have hs : count1491 q = (countLit q [-29, -31, -33, -35, -36, -37, -38]) + (countLit q [-39, -41, -43, -47, -51, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33, -35, -36, -37, -38]) (l₂ := [-39, -41, -43, -47, -51, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1492)) (countLit q [-29, -31, -33, -35, -36, -37, -38]) (countLit q [-39, -41, -43, -47, -51, -53, -55, -56]) (count1491 q) 1 1 (meaning1460 q) (meaning1483 q) (meaning1492 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1483 = false ∨ valuation q 1492 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true := by
  have hs : count1491 q = (countLit q [-29, -31, -33, -35, -36, -37, -38]) + (countLit q [-39, -41, -43, -47, -51, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33, -35, -36, -37, -38]) (l₂ := [-39, -41, -43, -47, -51, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1493)) (countLit q [-29, -31, -33, -35, -36, -37, -38]) (countLit q [-39, -41, -43, -47, -51, -53, -55, -56]) (count1491 q) 2 1 (meaning1461 q) (meaning1483 q) (meaning1493 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1483 = false ∨ valuation q 1493 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E257.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112257
