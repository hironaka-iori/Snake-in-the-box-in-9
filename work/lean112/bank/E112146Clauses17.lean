import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-30]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1404)) (countLit q [-30]) (countLit q [-31]) (count1403 q) 1 1 (meaningNeg30 q) (meaningNeg31 q) (meaning1404 q) hs
  change (! (valuationOf q 30)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 31 = true ∨ valuation q 1404 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1405 = true := by
  have hs : count1405 q = (countLit q [-26]) + (countLit q [-30, -31]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-30, -31])
  have hm := merge_right (literal (valuationOf q) (1403)) (literal (valuationOf q) (1405)) (countLit q [-26]) (countLit q [-30, -31]) (count1405 q) 1 (meaning1403 q) (meaning1405 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1405 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1406 = true := by
  have hs : count1405 q = (countLit q [-26]) + (countLit q [-30, -31]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-30, -31])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1406)) (countLit q [-26]) (countLit q [-30, -31]) (count1405 q) 2 (meaning1404 q) (meaning1406 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1406 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1405 = true := by
  have hs : count1405 q = (countLit q [-26]) + (countLit q [-30, -31]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-30, -31])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1405)) (countLit q [-26]) (countLit q [-30, -31]) (count1405 q) 1 (meaningNeg26 q) (meaning1405 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1405 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1403 = false ∨ valuationOf q 1406 = true := by
  have hs : count1405 q = (countLit q [-26]) + (countLit q [-30, -31]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-30, -31])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1406)) (countLit q [-26]) (countLit q [-30, -31]) (count1405 q) 1 1 (meaningNeg26 q) (meaning1403 q) (meaning1406 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1403 = false ∨ valuation q 1406 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1404 = false ∨ valuationOf q 1407 = true := by
  have hs : count1405 q = (countLit q [-26]) + (countLit q [-30, -31]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-30, -31])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1407)) (countLit q [-26]) (countLit q [-30, -31]) (count1405 q) 1 2 (meaningNeg26 q) (meaning1404 q) (meaning1407 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1404 = false ∨ valuation q 1407 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1408 = true := by
  have hs : count1408 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1408)) (countLit q [-33]) (countLit q [-35]) (count1408 q) 1 (meaningNeg35 q) (meaning1408 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1408 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1408 = true := by
  have hs : count1408 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1408)) (countLit q [-33]) (countLit q [-35]) (count1408 q) 1 (meaningNeg33 q) (meaning1408 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1408 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1409 = true := by
  have hs : count1408 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1409)) (countLit q [-33]) (countLit q [-35]) (count1408 q) 1 1 (meaningNeg33 q) (meaningNeg35 q) (meaning1409 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 1409 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1410)) (countLit q [-37]) (countLit q [-39]) (count1410 q) 1 (meaningNeg39 q) (meaning1410 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1410 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1410)) (countLit q [-37]) (countLit q [-39]) (count1410 q) 1 (meaningNeg37 q) (meaning1410 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1410 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 39 = true ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (1411)) (countLit q [-37]) (countLit q [-39]) (count1410 q) 1 1 (meaningNeg37 q) (meaningNeg39 q) (meaning1411 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 1411 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1412 = true := by
  have hs : count1412 q = (countLit q [-33, -35]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -39])
  have hm := merge_right (literal (valuationOf q) (1410)) (literal (valuationOf q) (1412)) (countLit q [-33, -35]) (countLit q [-37, -39]) (count1412 q) 1 (meaning1410 q) (meaning1412 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1412 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1413 = true := by
  have hs : count1412 q = (countLit q [-33, -35]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -39])
  have hm := merge_right (literal (valuationOf q) (1411)) (literal (valuationOf q) (1413)) (countLit q [-33, -35]) (countLit q [-37, -39]) (count1412 q) 2 (meaning1411 q) (meaning1413 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1413 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1412 = true := by
  have hs : count1412 q = (countLit q [-33, -35]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -39])
  have hm := merge_left (literal (valuationOf q) (1408)) (literal (valuationOf q) (1412)) (countLit q [-33, -35]) (countLit q [-37, -39]) (count1412 q) 1 (meaning1408 q) (meaning1412 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1412 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1413 = true := by
  have hs : count1412 q = (countLit q [-33, -35]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1413)) (countLit q [-33, -35]) (countLit q [-37, -39]) (count1412 q) 1 1 (meaning1408 q) (meaning1410 q) (meaning1413 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1410 = false ∨ valuation q 1413 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1414 = true := by
  have hs : count1412 q = (countLit q [-33, -35]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1414)) (countLit q [-33, -35]) (countLit q [-37, -39]) (count1412 q) 1 2 (meaning1408 q) (meaning1411 q) (meaning1414 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1411 = false ∨ valuation q 1414 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1413 = true := by
  have hs : count1412 q = (countLit q [-33, -35]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -39])
  have hm := merge_left (literal (valuationOf q) (1409)) (literal (valuationOf q) (1413)) (countLit q [-33, -35]) (countLit q [-37, -39]) (count1412 q) 2 (meaning1409 q) (meaning1413 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1413 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1414 = true := by
  have hs : count1412 q = (countLit q [-33, -35]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1414)) (countLit q [-33, -35]) (countLit q [-37, -39]) (count1412 q) 2 1 (meaning1409 q) (meaning1410 q) (meaning1414 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1410 = false ∨ valuation q 1414 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1415 = true := by
  have hs : count1412 q = (countLit q [-33, -35]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1415)) (countLit q [-33, -35]) (countLit q [-37, -39]) (count1412 q) 2 2 (meaning1409 q) (meaning1411 q) (meaning1415 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1411 = false ∨ valuation q 1415 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_right (literal (valuationOf q) (1413)) (literal (valuationOf q) (1417)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 2 (meaning1413 q) (meaning1417 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1417 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_right (literal (valuationOf q) (1414)) (literal (valuationOf q) (1418)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 3 (meaning1414 q) (meaning1418 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1418 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_right (literal (valuationOf q) (1415)) (literal (valuationOf q) (1419)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 4 (meaning1415 q) (meaning1419 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1419 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_left (literal (valuationOf q) (1405)) (literal (valuationOf q) (1416)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 1 (meaning1405 q) (meaning1416 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1416 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1417)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 1 1 (meaning1405 q) (meaning1412 q) (meaning1417 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1412 = false ∨ valuation q 1417 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1418)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 1 2 (meaning1405 q) (meaning1413 q) (meaning1418 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1413 = false ∨ valuation q 1418 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1419)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 1 3 (meaning1405 q) (meaning1414 q) (meaning1419 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1414 = false ∨ valuation q 1419 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1420 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1420)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 1 4 (meaning1405 q) (meaning1415 q) (meaning1420 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1415 = false ∨ valuation q 1420 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_left (literal (valuationOf q) (1406)) (literal (valuationOf q) (1417)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 2 (meaning1406 q) (meaning1417 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1417 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1418)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 2 1 (meaning1406 q) (meaning1412 q) (meaning1418 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1412 = false ∨ valuation q 1418 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1419)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 2 2 (meaning1406 q) (meaning1413 q) (meaning1419 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1413 = false ∨ valuation q 1419 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1420 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1420)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 2 3 (meaning1406 q) (meaning1414 q) (meaning1420 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1414 = false ∨ valuation q 1420 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E146.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112146
