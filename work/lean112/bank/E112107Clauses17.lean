import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_right (literal (valuationOf q) (1405)) (literal (valuationOf q) (1412)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 3 (meaning1405 q) (meaning1412 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1412 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1411)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 1 1 (meaning1384 q) (meaning1403 q) (meaning1411 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1403 = false ∨ valuation q 1411 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1412)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 1 2 (meaning1384 q) (meaning1404 q) (meaning1412 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1404 = false ∨ valuation q 1412 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1413 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1413)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 1 3 (meaning1384 q) (meaning1405 q) (meaning1413 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1405 = false ∨ valuation q 1413 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1414 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1414)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 1 4 (meaning1384 q) (meaning1406 q) (meaning1414 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1406 = false ∨ valuation q 1414 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1412)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 2 1 (meaning1385 q) (meaning1403 q) (meaning1412 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1403 = false ∨ valuation q 1412 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1413 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1413)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 2 2 (meaning1385 q) (meaning1404 q) (meaning1413 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1404 = false ∨ valuation q 1413 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1414 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1414)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 2 3 (meaning1385 q) (meaning1405 q) (meaning1414 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1405 = false ∨ valuation q 1414 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1413 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1413)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 3 1 (meaning1386 q) (meaning1403 q) (meaning1413 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1403 = false ∨ valuation q 1413 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1414 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1414)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 3 2 (meaning1386 q) (meaning1404 q) (meaning1414 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1404 = false ∨ valuation q 1414 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1427 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1361)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1427)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 1 4 (meaning1361 q) (meaning1413 q) (meaning1427 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1413 = false ∨ valuation q 1427 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1426 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1426)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 2 2 (meaning1362 q) (meaning1411 q) (meaning1426 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1411 = false ∨ valuation q 1426 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1427 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1427)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 2 3 (meaning1362 q) (meaning1412 q) (meaning1427 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1412 = false ∨ valuation q 1427 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1428)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 2 4 (meaning1362 q) (meaning1413 q) (meaning1428 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1413 = false ∨ valuation q 1428 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1429)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 2 5 (meaning1362 q) (meaning1414 q) (meaning1429 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1414 = false ∨ valuation q 1429 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1427 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1427)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 3 2 (meaning1363 q) (meaning1411 q) (meaning1427 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1411 = false ∨ valuation q 1427 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1428)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 3 3 (meaning1363 q) (meaning1412 q) (meaning1428 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1412 = false ∨ valuation q 1428 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1429)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 3 4 (meaning1363 q) (meaning1413 q) (meaning1429 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1413 = false ∨ valuation q 1429 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1430)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 3 5 (meaning1363 q) (meaning1414 q) (meaning1430 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1414 = false ∨ valuation q 1430 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1428)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 4 2 (meaning1364 q) (meaning1411 q) (meaning1428 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1411 = false ∨ valuation q 1428 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1429)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 4 3 (meaning1364 q) (meaning1412 q) (meaning1429 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1412 = false ∨ valuation q 1429 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1430)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 4 4 (meaning1364 q) (meaning1413 q) (meaning1430 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1413 = false ∨ valuation q 1430 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1429)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 5 2 (meaning1365 q) (meaning1411 q) (meaning1429 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1411 = false ∨ valuation q 1429 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1430)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 5 3 (meaning1365 q) (meaning1412 q) (meaning1430 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1412 = false ∨ valuation q 1430 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1431 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1431)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 5 4 (meaning1365 q) (meaning1413 q) (meaning1431 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1413 = false ∨ valuation q 1431 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1430)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 6 2 (meaning1366 q) (meaning1411 q) (meaning1430 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1411 = false ∨ valuation q 1430 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1430)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 7 1 (meaning1367 q) (meaning1410 q) (meaning1430 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1410 = false ∨ valuation q 1430 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1431 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1431)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 7 2 (meaning1367 q) (meaning1411 q) (meaning1431 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1411 = false ∨ valuation q 1431 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1432 = true := by
  have hs : count1423 q = (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) + (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (l₂ := [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1432)) (countLit q [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]) (countLit q [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]) (count1423 q) 7 3 (meaning1367 q) (meaning1412 q) (meaning1432 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1412 = false ∨ valuation q 1432 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (1436)) (countLit q [-59]) (countLit q [-60]) (count1436 q) 1 (meaningNeg60 q) (meaning1436 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1436 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1436)) (countLit q [-59]) (countLit q [-60]) (count1436 q) 1 (meaningNeg59 q) (meaning1436 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1436 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 60 = true ∨ valuationOf q 1437 = true := by
  have hs : count1436 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (1437)) (countLit q [-59]) (countLit q [-60]) (count1436 q) 1 1 (meaningNeg59 q) (meaningNeg60 q) (meaning1437 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 60 = true ∨ valuation q 1437 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E107.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112107
