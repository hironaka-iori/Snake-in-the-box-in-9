import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-16, -18, -20]) + (countLit q [-22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20]) (l₂ := [-22, -24, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1416)) (literal (valuationOf q) (1427)) (countLit q [-16, -18, -20]) (countLit q [-22, -24, -26, -28]) (count1426 q) 2 (meaning1416 q) (meaning1427 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1427 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1428 = true := by
  have hs : count1426 q = (countLit q [-16, -18, -20]) + (countLit q [-22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20]) (l₂ := [-22, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1428)) (countLit q [-16, -18, -20]) (countLit q [-22, -24, -26, -28]) (count1426 q) 2 1 (meaning1416 q) (meaning1422 q) (meaning1428 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1422 = false ∨ valuation q 1428 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1429 = true := by
  have hs : count1426 q = (countLit q [-16, -18, -20]) + (countLit q [-22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20]) (l₂ := [-22, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1429)) (countLit q [-16, -18, -20]) (countLit q [-22, -24, -26, -28]) (count1426 q) 2 2 (meaning1416 q) (meaning1423 q) (meaning1429 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1423 = false ∨ valuation q 1429 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1436 = true := by
  have hs : count1433 q = (countLit q [-3, -4, -5, -8, -9, -12, -13]) + (countLit q [-16, -18, -20, -22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13]) (l₂ := [-16, -18, -20, -22, -24, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1429)) (literal (valuationOf q) (1436)) (countLit q [-3, -4, -5, -8, -9, -12, -13]) (countLit q [-16, -18, -20, -22, -24, -26, -28]) (count1433 q) 4 (meaning1429 q) (meaning1436 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1436 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1435 = true := by
  have hs : count1433 q = (countLit q [-3, -4, -5, -8, -9, -12, -13]) + (countLit q [-16, -18, -20, -22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13]) (l₂ := [-16, -18, -20, -22, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1427)) (literal (valuationOf q) (1435)) (countLit q [-3, -4, -5, -8, -9, -12, -13]) (countLit q [-16, -18, -20, -22, -24, -26, -28]) (count1433 q) 1 2 (meaning1406 q) (meaning1427 q) (meaning1435 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1427 = false ∨ valuation q 1435 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1436 = true := by
  have hs : count1433 q = (countLit q [-3, -4, -5, -8, -9, -12, -13]) + (countLit q [-16, -18, -20, -22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13]) (l₂ := [-16, -18, -20, -22, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1436)) (countLit q [-3, -4, -5, -8, -9, -12, -13]) (countLit q [-16, -18, -20, -22, -24, -26, -28]) (count1433 q) 1 3 (meaning1406 q) (meaning1428 q) (meaning1436 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1428 = false ∨ valuation q 1436 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1435 = true := by
  have hs : count1433 q = (countLit q [-3, -4, -5, -8, -9, -12, -13]) + (countLit q [-16, -18, -20, -22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13]) (l₂ := [-16, -18, -20, -22, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1426)) (literal (valuationOf q) (1435)) (countLit q [-3, -4, -5, -8, -9, -12, -13]) (countLit q [-16, -18, -20, -22, -24, -26, -28]) (count1433 q) 2 1 (meaning1407 q) (meaning1426 q) (meaning1435 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1426 = false ∨ valuation q 1435 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1436 = true := by
  have hs : count1433 q = (countLit q [-3, -4, -5, -8, -9, -12, -13]) + (countLit q [-16, -18, -20, -22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13]) (l₂ := [-16, -18, -20, -22, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1427)) (literal (valuationOf q) (1436)) (countLit q [-3, -4, -5, -8, -9, -12, -13]) (countLit q [-16, -18, -20, -22, -24, -26, -28]) (count1433 q) 2 2 (meaning1407 q) (meaning1427 q) (meaning1436 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1427 = false ∨ valuation q 1436 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1435 = true := by
  have hs : count1433 q = (countLit q [-3, -4, -5, -8, -9, -12, -13]) + (countLit q [-16, -18, -20, -22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13]) (l₂ := [-16, -18, -20, -22, -24, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1408)) (literal (valuationOf q) (1435)) (countLit q [-3, -4, -5, -8, -9, -12, -13]) (countLit q [-16, -18, -20, -22, -24, -26, -28]) (count1433 q) 3 (meaning1408 q) (meaning1435 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1435 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1436 = true := by
  have hs : count1433 q = (countLit q [-3, -4, -5, -8, -9, -12, -13]) + (countLit q [-16, -18, -20, -22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13]) (l₂ := [-16, -18, -20, -22, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1426)) (literal (valuationOf q) (1436)) (countLit q [-3, -4, -5, -8, -9, -12, -13]) (countLit q [-16, -18, -20, -22, -24, -26, -28]) (count1433 q) 3 1 (meaning1408 q) (meaning1426 q) (meaning1436 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1426 = false ∨ valuation q 1436 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1436 = true := by
  have hs : count1433 q = (countLit q [-3, -4, -5, -8, -9, -12, -13]) + (countLit q [-16, -18, -20, -22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13]) (l₂ := [-16, -18, -20, -22, -24, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1409)) (literal (valuationOf q) (1436)) (countLit q [-3, -4, -5, -8, -9, -12, -13]) (countLit q [-16, -18, -20, -22, -24, -26, -28]) (count1433 q) 4 (meaning1409 q) (meaning1436 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1436 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1447)) (countLit q [-31]) (countLit q [-33]) (count1447 q) 1 (meaningNeg33 q) (meaning1447 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1447 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1447)) (countLit q [-31]) (countLit q [-33]) (count1447 q) 1 (meaningNeg31 q) (meaning1447 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1447 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1448 = true := by
  have hs : count1447 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1448)) (countLit q [-31]) (countLit q [-33]) (count1447 q) 1 1 (meaningNeg31 q) (meaningNeg33 q) (meaning1448 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 33 = true ∨ valuation q 1448 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-29]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31, -33])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (countLit q [-29]) (countLit q [-31, -33]) (count1449 q) 1 (meaning1447 q) (meaning1449 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-29]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31, -33])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1450)) (countLit q [-29]) (countLit q [-31, -33]) (count1449 q) 2 (meaning1448 q) (meaning1450 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1450 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-29]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31, -33])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1450)) (countLit q [-29]) (countLit q [-31, -33]) (count1449 q) 1 1 (meaningNeg29 q) (meaning1447 q) (meaning1450 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1447 = false ∨ valuation q 1450 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1452)) (countLit q [-35]) (countLit q [-37]) (count1452 q) 1 (meaningNeg35 q) (meaning1452 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1452 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-35, -37]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-40, -41])
  have hm := merge_left (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-35, -37]) (countLit q [-40, -41]) (count1456 q) 1 (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1456 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-29, -31, -33]) + (countLit q [-35, -37, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33]) (l₂ := [-35, -37, -40, -41])
  have hm := merge_left (literal (valuationOf q) (1449)) (literal (valuationOf q) (1460)) (countLit q [-29, -31, -33]) (countLit q [-35, -37, -40, -41]) (count1460 q) 1 (meaning1449 q) (meaning1460 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1460 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1461 = true := by
  have hs : count1460 q = (countLit q [-29, -31, -33]) + (countLit q [-35, -37, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33]) (l₂ := [-35, -37, -40, -41])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1461)) (countLit q [-29, -31, -33]) (countLit q [-35, -37, -40, -41]) (count1460 q) 1 1 (meaning1449 q) (meaning1456 q) (meaning1461 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1456 = false ∨ valuation q 1461 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1462 = true := by
  have hs : count1460 q = (countLit q [-29, -31, -33]) + (countLit q [-35, -37, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33]) (l₂ := [-35, -37, -40, -41])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1462)) (countLit q [-29, -31, -33]) (countLit q [-35, -37, -40, -41]) (count1460 q) 2 1 (meaning1450 q) (meaning1456 q) (meaning1462 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1456 = false ∨ valuation q 1462 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1477)) (countLit q [-54]) (countLit q [-56]) (count1477 q) 1 (meaningNeg56 q) (meaning1477 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1477 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1477)) (countLit q [-54]) (countLit q [-56]) (count1477 q) 1 (meaningNeg54 q) (meaning1477 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1477 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1478)) (countLit q [-54]) (countLit q [-56]) (count1477 q) 1 1 (meaningNeg54 q) (meaningNeg56 q) (meaning1478 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 1478 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-51, -53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -53]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (1477)) (literal (valuationOf q) (1479)) (countLit q [-51, -53]) (countLit q [-54, -56]) (count1479 q) 1 (meaning1477 q) (meaning1479 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1479 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1480 = true := by
  have hs : count1479 q = (countLit q [-51, -53]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -53]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (1478)) (literal (valuationOf q) (1480)) (countLit q [-51, -53]) (countLit q [-54, -56]) (count1479 q) 2 (meaning1478 q) (meaning1480 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1480 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-43, -45, -47, -49]) + (countLit q [-51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -49]) (l₂ := [-51, -53, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1483)) (countLit q [-43, -45, -47, -49]) (countLit q [-51, -53, -54, -56]) (count1483 q) 1 (meaning1479 q) (meaning1483 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1483 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1483 q = (countLit q [-43, -45, -47, -49]) + (countLit q [-51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -49]) (l₂ := [-51, -53, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-43, -45, -47, -49]) (countLit q [-51, -53, -54, -56]) (count1483 q) 2 (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1484 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1491 = true := by
  have hs : count1491 q = (countLit q [-29, -31, -33, -35, -37, -40, -41]) + (countLit q [-43, -45, -47, -49, -51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33, -35, -37, -40, -41]) (l₂ := [-43, -45, -47, -49, -51, -53, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1483)) (literal (valuationOf q) (1491)) (countLit q [-29, -31, -33, -35, -37, -40, -41]) (countLit q [-43, -45, -47, -49, -51, -53, -54, -56]) (count1491 q) 1 (meaning1483 q) (meaning1491 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1491 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1491 = true := by
  have hs : count1491 q = (countLit q [-29, -31, -33, -35, -37, -40, -41]) + (countLit q [-43, -45, -47, -49, -51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33, -35, -37, -40, -41]) (l₂ := [-43, -45, -47, -49, -51, -53, -54, -56])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1491)) (countLit q [-29, -31, -33, -35, -37, -40, -41]) (countLit q [-43, -45, -47, -49, -51, -53, -54, -56]) (count1491 q) 1 (meaning1460 q) (meaning1491 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1491 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true := by
  have hs : count1491 q = (countLit q [-29, -31, -33, -35, -37, -40, -41]) + (countLit q [-43, -45, -47, -49, -51, -53, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33, -35, -37, -40, -41]) (l₂ := [-43, -45, -47, -49, -51, -53, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1493)) (countLit q [-29, -31, -33, -35, -37, -40, -41]) (countLit q [-43, -45, -47, -49, -51, -53, -54, -56]) (count1491 q) 2 1 (meaning1461 q) (meaning1483 q) (meaning1493 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1483 = false ∨ valuation q 1493 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E259.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112259
