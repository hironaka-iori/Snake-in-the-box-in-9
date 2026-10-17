import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1404 = true := by
  have hs : count1404 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1404)) (countLit q [-54]) (countLit q [-56]) (count1404 q) 1 (meaningNeg54 q) (meaning1404 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1404 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1405 = true := by
  have hs : count1404 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1405)) (countLit q [-54]) (countLit q [-56]) (count1404 q) 1 1 (meaningNeg54 q) (meaningNeg56 q) (meaning1405 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 1405 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-47, -49]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-47, -49]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1406)) (countLit q [-47, -49]) (countLit q [-54, -56]) (count1406 q) 1 (meaning1404 q) (meaning1406 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1406 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-47, -49]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-47, -49]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (1405)) (literal (valuationOf q) (1407)) (countLit q [-47, -49]) (countLit q [-54, -56]) (count1406 q) 2 (meaning1405 q) (meaning1407 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1407 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-47, -49]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-47, -49]) (l₂ := [-54, -56])
  have hm := merge_left (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-47, -49]) (countLit q [-54, -56]) (count1406 q) 1 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-47, -49]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-47, -49]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1407)) (countLit q [-47, -49]) (countLit q [-54, -56]) (count1406 q) 1 1 (meaning1402 q) (meaning1404 q) (meaning1407 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1404 = false ∨ valuation q 1407 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-47, -49]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-47, -49]) (l₂ := [-54, -56])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1408)) (countLit q [-47, -49]) (countLit q [-54, -56]) (count1406 q) 1 2 (meaning1402 q) (meaning1405 q) (meaning1408 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1405 = false ∨ valuation q 1408 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-41, -43, -46]) + (countLit q [-47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-47, -49, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1406)) (literal (valuationOf q) (1410)) (countLit q [-41, -43, -46]) (countLit q [-47, -49, -54, -56]) (count1410 q) 1 (meaning1406 q) (meaning1410 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1410 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-41, -43, -46]) + (countLit q [-47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-47, -49, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1407)) (literal (valuationOf q) (1411)) (countLit q [-41, -43, -46]) (countLit q [-47, -49, -54, -56]) (count1410 q) 2 (meaning1407 q) (meaning1411 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1411 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-41, -43, -46]) + (countLit q [-47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-47, -49, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1408)) (literal (valuationOf q) (1412)) (countLit q [-41, -43, -46]) (countLit q [-47, -49, -54, -56]) (count1410 q) 3 (meaning1408 q) (meaning1412 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1412 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-41, -43, -46]) + (countLit q [-47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-47, -49, -54, -56])
  have hm := merge_left (literal (valuationOf q) (1399)) (literal (valuationOf q) (1410)) (countLit q [-41, -43, -46]) (countLit q [-47, -49, -54, -56]) (count1410 q) 1 (meaning1399 q) (meaning1410 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1410 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-41, -43, -46]) + (countLit q [-47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1411)) (countLit q [-41, -43, -46]) (countLit q [-47, -49, -54, -56]) (count1410 q) 1 1 (meaning1399 q) (meaning1406 q) (meaning1411 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1406 = false ∨ valuation q 1411 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-41, -43, -46]) + (countLit q [-47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1412)) (countLit q [-41, -43, -46]) (countLit q [-47, -49, -54, -56]) (count1410 q) 1 2 (meaning1399 q) (meaning1407 q) (meaning1412 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1407 = false ∨ valuation q 1412 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-41, -43, -46]) + (countLit q [-47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1412)) (countLit q [-41, -43, -46]) (countLit q [-47, -49, -54, -56]) (count1410 q) 2 1 (meaning1400 q) (meaning1406 q) (meaning1412 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1406 = false ∨ valuation q 1412 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1410)) (literal (valuationOf q) (1417)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 1 (meaning1410 q) (meaning1417 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1417 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_right (literal (valuationOf q) (1411)) (literal (valuationOf q) (1418)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 2 (meaning1411 q) (meaning1418 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1418 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1418)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 1 1 (meaning1391 q) (meaning1410 q) (meaning1418 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1410 = false ∨ valuation q 1418 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1419)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 1 2 (meaning1391 q) (meaning1411 q) (meaning1419 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1411 = false ∨ valuation q 1419 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1420)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 1 3 (meaning1391 q) (meaning1412 q) (meaning1420 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1412 = false ∨ valuation q 1420 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1419)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 2 1 (meaning1392 q) (meaning1410 q) (meaning1419 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1410 = false ∨ valuation q 1419 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1420)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 2 2 (meaning1392 q) (meaning1411 q) (meaning1420 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1411 = false ∨ valuation q 1420 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1421 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1421)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 2 3 (meaning1392 q) (meaning1412 q) (meaning1421 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1412 = false ∨ valuation q 1421 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1420)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 3 1 (meaning1393 q) (meaning1410 q) (meaning1420 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1410 = false ∨ valuation q 1420 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1421 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1421)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 3 2 (meaning1393 q) (meaning1411 q) (meaning1421 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1411 = false ∨ valuation q 1421 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1422 = true := by
  have hs : count1417 q = (countLit q [-29, -31, -32, -35, -38, -40]) + (countLit q [-41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32, -35, -38, -40]) (l₂ := [-41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1422)) (countLit q [-29, -31, -32, -35, -38, -40]) (countLit q [-41, -43, -46, -47, -49, -54, -56]) (count1417 q) 4 2 (meaning1394 q) (meaning1411 q) (meaning1422 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1411 = false ∨ valuation q 1422 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1432 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1369)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1432)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 1 3 (meaning1369 q) (meaning1419 q) (meaning1432 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1419 = false ∨ valuation q 1432 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1433 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1369)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1433)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 1 4 (meaning1369 q) (meaning1420 q) (meaning1433 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1420 = false ∨ valuation q 1433 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1434 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1369)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1434)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 1 5 (meaning1369 q) (meaning1421 q) (meaning1434 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1421 = false ∨ valuation q 1434 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1432 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1432)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 2 2 (meaning1370 q) (meaning1418 q) (meaning1432 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1418 = false ∨ valuation q 1432 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1433 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1433)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 2 3 (meaning1370 q) (meaning1419 q) (meaning1433 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1419 = false ∨ valuation q 1433 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1434 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1434)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 2 4 (meaning1370 q) (meaning1420 q) (meaning1434 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1420 = false ∨ valuation q 1434 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1435 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1435)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 2 5 (meaning1370 q) (meaning1421 q) (meaning1435 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1421 = false ∨ valuation q 1435 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E183.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112183
