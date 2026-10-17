import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1402)) (countLit q [-48]) (countLit q [-51]) (count1402 q) 1 (meaningNeg51 q) (meaning1402 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1402 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1402)) (countLit q [-48]) (countLit q [-51]) (count1402 q) 1 (meaningNeg48 q) (meaning1402 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1402 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1404 = true := by
  have hs : count1404 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1404)) (countLit q [-53]) (countLit q [-55]) (count1404 q) 1 (meaningNeg53 q) (meaning1404 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1404 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-48, -51]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-48, -51]) (l₂ := [-53, -55])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1406)) (countLit q [-48, -51]) (countLit q [-53, -55]) (count1406 q) 1 (meaning1404 q) (meaning1406 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1406 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-48, -51]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-48, -51]) (l₂ := [-53, -55])
  have hm := merge_left (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-48, -51]) (countLit q [-53, -55]) (count1406 q) 1 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-42, -45, -47]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -47]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_right (literal (valuationOf q) (1406)) (literal (valuationOf q) (1410)) (countLit q [-42, -45, -47]) (countLit q [-48, -51, -53, -55]) (count1410 q) 1 (meaning1406 q) (meaning1410 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1410 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-42, -45, -47]) + (countLit q [-48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-42, -45, -47]) (l₂ := [-48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1411)) (countLit q [-42, -45, -47]) (countLit q [-48, -51, -53, -55]) (count1410 q) 1 1 (meaning1399 q) (meaning1406 q) (meaning1411 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1406 = false ∨ valuation q 1411 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-28, -30, -33, -36, -37, -40]) + (countLit q [-42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -36, -37, -40]) (l₂ := [-42, -45, -47, -48, -51, -53, -55])
  have hm := merge_right (literal (valuationOf q) (1411)) (literal (valuationOf q) (1418)) (countLit q [-28, -30, -33, -36, -37, -40]) (countLit q [-42, -45, -47, -48, -51, -53, -55]) (count1417 q) 2 (meaning1411 q) (meaning1418 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1418 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-28, -30, -33, -36, -37, -40]) + (countLit q [-42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -36, -37, -40]) (l₂ := [-42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1418)) (countLit q [-28, -30, -33, -36, -37, -40]) (countLit q [-42, -45, -47, -48, -51, -53, -55]) (count1417 q) 1 1 (meaning1391 q) (meaning1410 q) (meaning1418 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1410 = false ∨ valuation q 1418 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-28, -30, -33, -36, -37, -40]) + (countLit q [-42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -36, -37, -40]) (l₂ := [-42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1419)) (countLit q [-28, -30, -33, -36, -37, -40]) (countLit q [-42, -45, -47, -48, -51, -53, -55]) (count1417 q) 1 2 (meaning1391 q) (meaning1411 q) (meaning1419 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1411 = false ∨ valuation q 1419 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-28, -30, -33, -36, -37, -40]) + (countLit q [-42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -36, -37, -40]) (l₂ := [-42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1419)) (countLit q [-28, -30, -33, -36, -37, -40]) (countLit q [-42, -45, -47, -48, -51, -53, -55]) (count1417 q) 2 1 (meaning1392 q) (meaning1410 q) (meaning1419 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1410 = false ∨ valuation q 1419 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-28, -30, -33, -36, -37, -40]) + (countLit q [-42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -36, -37, -40]) (l₂ := [-42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1420)) (countLit q [-28, -30, -33, -36, -37, -40]) (countLit q [-42, -45, -47, -48, -51, -53, -55]) (count1417 q) 2 2 (meaning1392 q) (meaning1411 q) (meaning1420 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1411 = false ∨ valuation q 1420 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-28, -30, -33, -36, -37, -40]) + (countLit q [-42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -36, -37, -40]) (l₂ := [-42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1420)) (countLit q [-28, -30, -33, -36, -37, -40]) (countLit q [-42, -45, -47, -48, -51, -53, -55]) (count1417 q) 3 1 (meaning1393 q) (meaning1410 q) (meaning1420 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1410 = false ∨ valuation q 1420 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1421 = true := by
  have hs : count1417 q = (countLit q [-28, -30, -33, -36, -37, -40]) + (countLit q [-42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -36, -37, -40]) (l₂ := [-42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1421)) (countLit q [-28, -30, -33, -36, -37, -40]) (countLit q [-42, -45, -47, -48, -51, -53, -55]) (count1417 q) 3 2 (meaning1393 q) (meaning1411 q) (meaning1421 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1411 = false ∨ valuation q 1421 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1421 = true := by
  have hs : count1417 q = (countLit q [-28, -30, -33, -36, -37, -40]) + (countLit q [-42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -36, -37, -40]) (l₂ := [-42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1421)) (countLit q [-28, -30, -33, -36, -37, -40]) (countLit q [-42, -45, -47, -48, -51, -53, -55]) (count1417 q) 4 1 (meaning1394 q) (meaning1410 q) (meaning1421 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1410 = false ∨ valuation q 1421 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1433 = true := by
  have hs : count1429 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) + (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (l₂ := [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1433)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (count1429 q) 2 3 (meaning1370 q) (meaning1419 q) (meaning1433 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1419 = false ∨ valuation q 1433 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1434 = true := by
  have hs : count1429 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) + (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (l₂ := [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1434)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (count1429 q) 2 4 (meaning1370 q) (meaning1420 q) (meaning1434 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1420 = false ∨ valuation q 1434 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1435 = true := by
  have hs : count1429 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) + (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (l₂ := [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1435)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (count1429 q) 2 5 (meaning1370 q) (meaning1421 q) (meaning1435 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1421 = false ∨ valuation q 1435 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1433 = true := by
  have hs : count1429 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) + (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (l₂ := [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1433)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (count1429 q) 3 2 (meaning1371 q) (meaning1418 q) (meaning1433 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1418 = false ∨ valuation q 1433 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1434 = true := by
  have hs : count1429 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) + (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (l₂ := [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1434)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (count1429 q) 3 3 (meaning1371 q) (meaning1419 q) (meaning1434 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1419 = false ∨ valuation q 1434 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1435 = true := by
  have hs : count1429 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) + (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (l₂ := [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1435)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (count1429 q) 3 4 (meaning1371 q) (meaning1420 q) (meaning1435 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1420 = false ∨ valuation q 1435 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1436 = true := by
  have hs : count1429 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) + (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (l₂ := [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1436)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (count1429 q) 3 5 (meaning1371 q) (meaning1421 q) (meaning1436 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1421 = false ∨ valuation q 1436 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1434 = true := by
  have hs : count1429 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) + (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (l₂ := [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1434)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (count1429 q) 4 2 (meaning1372 q) (meaning1418 q) (meaning1434 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1418 = false ∨ valuation q 1434 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1435 = true := by
  have hs : count1429 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) + (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (l₂ := [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1435)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (count1429 q) 4 3 (meaning1372 q) (meaning1419 q) (meaning1435 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1419 = false ∨ valuation q 1435 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1435 = true := by
  have hs : count1429 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) + (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (l₂ := [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1435)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27]) (countLit q [-28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (count1429 q) 5 2 (meaning1373 q) (meaning1418 q) (meaning1435 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1418 = false ∨ valuation q 1435 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1441)) (countLit q [-61]) (countLit q [-63]) (count1441 q) 1 (meaningNeg63 q) (meaning1441 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1441 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1441)) (countLit q [-61]) (countLit q [-63]) (count1441 q) 1 (meaningNeg61 q) (meaning1441 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1441 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1442)) (countLit q [-61]) (countLit q [-63]) (count1441 q) 1 1 (meaningNeg61 q) (meaningNeg63 q) (meaning1442 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 1442 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (countLit q [-59]) (countLit q [-61, -63]) (count1443 q) 1 (meaning1441 q) (meaning1443 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1442)) (literal (valuationOf q) (1444)) (countLit q [-59]) (countLit q [-61, -63]) (count1443 q) 2 (meaning1442 q) (meaning1444 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1444 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1443)) (countLit q [-59]) (countLit q [-61, -63]) (count1443 q) 1 (meaningNeg59 q) (meaning1443 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1443 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1446)) (countLit q [-66]) (countLit q [-68]) (count1446 q) 1 (meaningNeg68 q) (meaning1446 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1446 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E079.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112079
