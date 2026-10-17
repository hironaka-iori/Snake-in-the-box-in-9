import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1421 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1421)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 2 4 (meaning1406 q) (meaning1415 q) (meaning1421 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1415 = false ∨ valuation q 1421 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_left (literal (valuationOf q) (1407)) (literal (valuationOf q) (1418)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 3 (meaning1407 q) (meaning1418 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1418 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1419)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 3 1 (meaning1407 q) (meaning1412 q) (meaning1419 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1412 = false ∨ valuation q 1419 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1420 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1420)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 3 2 (meaning1407 q) (meaning1413 q) (meaning1420 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1413 = false ∨ valuation q 1420 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1421 = true := by
  have hs : count1416 q = (countLit q [-26, -30, -31]) + (countLit q [-33, -35, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-26, -30, -31]) (l₂ := [-33, -35, -37, -39])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1421)) (countLit q [-26, -30, -31]) (countLit q [-33, -35, -37, -39]) (count1416 q) 3 3 (meaning1407 q) (meaning1414 q) (meaning1421 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1414 = false ∨ valuation q 1421 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1423)) (countLit q [-40]) (countLit q [-41]) (count1423 q) 1 (meaningNeg41 q) (meaning1423 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1423 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1423)) (countLit q [-40]) (countLit q [-41]) (count1423 q) 1 (meaningNeg40 q) (meaning1423 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1423 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1424)) (countLit q [-40]) (countLit q [-41]) (count1423 q) 1 1 (meaningNeg40 q) (meaningNeg41 q) (meaning1424 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 41 = true ∨ valuation q 1424 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1425)) (countLit q [-43]) (countLit q [-46]) (count1425 q) 1 (meaningNeg46 q) (meaning1425 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1425 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1425)) (countLit q [-43]) (countLit q [-46]) (count1425 q) 1 (meaningNeg43 q) (meaning1425 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1425 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1426)) (countLit q [-43]) (countLit q [-46]) (count1425 q) 1 1 (meaningNeg43 q) (meaningNeg46 q) (meaning1426 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 46 = true ∨ valuation q 1426 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1427 = true := by
  have hs : count1427 q = (countLit q [-40, -41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-43, -46])
  have hm := merge_right (literal (valuationOf q) (1425)) (literal (valuationOf q) (1427)) (countLit q [-40, -41]) (countLit q [-43, -46]) (count1427 q) 1 (meaning1425 q) (meaning1427 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1427 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1428 = true := by
  have hs : count1427 q = (countLit q [-40, -41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-43, -46])
  have hm := merge_right (literal (valuationOf q) (1426)) (literal (valuationOf q) (1428)) (countLit q [-40, -41]) (countLit q [-43, -46]) (count1427 q) 2 (meaning1426 q) (meaning1428 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1428 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1427 = true := by
  have hs : count1427 q = (countLit q [-40, -41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-43, -46])
  have hm := merge_left (literal (valuationOf q) (1423)) (literal (valuationOf q) (1427)) (countLit q [-40, -41]) (countLit q [-43, -46]) (count1427 q) 1 (meaning1423 q) (meaning1427 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1427 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1428 = true := by
  have hs : count1427 q = (countLit q [-40, -41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1425)) (literal (valuationOf q) (1428)) (countLit q [-40, -41]) (countLit q [-43, -46]) (count1427 q) 1 1 (meaning1423 q) (meaning1425 q) (meaning1428 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1425 = false ∨ valuation q 1428 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1429 = true := by
  have hs : count1427 q = (countLit q [-40, -41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1426)) (literal (valuationOf q) (1429)) (countLit q [-40, -41]) (countLit q [-43, -46]) (count1427 q) 1 2 (meaning1423 q) (meaning1426 q) (meaning1429 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1426 = false ∨ valuation q 1429 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1428 = true := by
  have hs : count1427 q = (countLit q [-40, -41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-43, -46])
  have hm := merge_left (literal (valuationOf q) (1424)) (literal (valuationOf q) (1428)) (countLit q [-40, -41]) (countLit q [-43, -46]) (count1427 q) 2 (meaning1424 q) (meaning1428 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1428 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1429 = true := by
  have hs : count1427 q = (countLit q [-40, -41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1425)) (literal (valuationOf q) (1429)) (countLit q [-40, -41]) (countLit q [-43, -46]) (count1427 q) 2 1 (meaning1424 q) (meaning1425 q) (meaning1429 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1425 = false ∨ valuation q 1429 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1431 = true := by
  have hs : count1431 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1431)) (countLit q [-48]) (countLit q [-51]) (count1431 q) 1 (meaningNeg51 q) (meaning1431 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1431 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1431 = true := by
  have hs : count1431 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1431)) (countLit q [-48]) (countLit q [-51]) (count1431 q) 1 (meaningNeg48 q) (meaning1431 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1431 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1432 = true := by
  have hs : count1431 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1432)) (countLit q [-48]) (countLit q [-51]) (count1431 q) 1 1 (meaningNeg48 q) (meaningNeg51 q) (meaning1432 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 51 = true ∨ valuation q 1432 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1433)) (countLit q [-53]) (countLit q [-55]) (count1433 q) 1 (meaningNeg55 q) (meaning1433 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1433 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1433)) (countLit q [-53]) (countLit q [-55]) (count1433 q) 1 (meaningNeg53 q) (meaning1433 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1433 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 55 = true ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (1434)) (countLit q [-53]) (countLit q [-55]) (count1433 q) 1 1 (meaningNeg53 q) (meaningNeg55 q) (meaning1434 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 1434 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-48, -51]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-48, -51]) (l₂ := [-53, -55])
  have hm := merge_right (literal (valuationOf q) (1433)) (literal (valuationOf q) (1435)) (countLit q [-48, -51]) (countLit q [-53, -55]) (count1435 q) 1 (meaning1433 q) (meaning1435 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1435 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1436 = true := by
  have hs : count1435 q = (countLit q [-48, -51]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-48, -51]) (l₂ := [-53, -55])
  have hm := merge_right (literal (valuationOf q) (1434)) (literal (valuationOf q) (1436)) (countLit q [-48, -51]) (countLit q [-53, -55]) (count1435 q) 2 (meaning1434 q) (meaning1436 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1436 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-48, -51]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-48, -51]) (l₂ := [-53, -55])
  have hm := merge_left (literal (valuationOf q) (1431)) (literal (valuationOf q) (1435)) (countLit q [-48, -51]) (countLit q [-53, -55]) (count1435 q) 1 (meaning1431 q) (meaning1435 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1435 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1436 = true := by
  have hs : count1435 q = (countLit q [-48, -51]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-48, -51]) (l₂ := [-53, -55])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1436)) (countLit q [-48, -51]) (countLit q [-53, -55]) (count1435 q) 1 1 (meaning1431 q) (meaning1433 q) (meaning1436 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1433 = false ∨ valuation q 1436 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1437 = true := by
  have hs : count1435 q = (countLit q [-48, -51]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-48, -51]) (l₂ := [-53, -55])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1437)) (countLit q [-48, -51]) (countLit q [-53, -55]) (count1435 q) 1 2 (meaning1431 q) (meaning1434 q) (meaning1437 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1434 = false ∨ valuation q 1437 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1436 = true := by
  have hs : count1435 q = (countLit q [-48, -51]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-48, -51]) (l₂ := [-53, -55])
  have hm := merge_left (literal (valuationOf q) (1432)) (literal (valuationOf q) (1436)) (countLit q [-48, -51]) (countLit q [-53, -55]) (count1435 q) 2 (meaning1432 q) (meaning1436 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1436 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1437 = true := by
  have hs : count1435 q = (countLit q [-48, -51]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-48, -51]) (l₂ := [-53, -55])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1437)) (countLit q [-48, -51]) (countLit q [-53, -55]) (count1435 q) 2 1 (meaning1432 q) (meaning1433 q) (meaning1437 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1433 = false ∨ valuation q 1437 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-40, -41, -43, -46]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-40, -41, -43, -46]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_right (literal (valuationOf q) (1435)) (literal (valuationOf q) (1439)) (countLit q [-40, -41, -43, -46]) (countLit q [-48, -51, -53, -55]) (count1439 q) 1 (meaning1435 q) (meaning1439 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1439 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E146.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112146
