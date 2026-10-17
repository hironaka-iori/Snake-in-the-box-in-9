import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1408)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 3 (meaning1404 q) (meaning1408 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1408 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1409 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_right (literal (valuationOf q) (1405)) (literal (valuationOf q) (1409)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 4 (meaning1405 q) (meaning1409 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1409 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_left (literal (valuationOf q) (1395)) (literal (valuationOf q) (1406)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 1 (meaning1395 q) (meaning1406 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1406 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1407)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 1 1 (meaning1395 q) (meaning1402 q) (meaning1407 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1402 = false ∨ valuation q 1407 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1408)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 1 2 (meaning1395 q) (meaning1403 q) (meaning1408 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1403 = false ∨ valuation q 1408 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1409 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1409)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 1 3 (meaning1395 q) (meaning1404 q) (meaning1409 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1404 = false ∨ valuation q 1409 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1410 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1410)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 1 4 (meaning1395 q) (meaning1405 q) (meaning1410 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1405 = false ∨ valuation q 1410 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_left (literal (valuationOf q) (1396)) (literal (valuationOf q) (1407)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 2 (meaning1396 q) (meaning1407 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1407 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1408)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 2 1 (meaning1396 q) (meaning1402 q) (meaning1408 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1402 = false ∨ valuation q 1408 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1409 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1409)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 2 2 (meaning1396 q) (meaning1403 q) (meaning1409 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1403 = false ∨ valuation q 1409 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1410 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1410)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 2 3 (meaning1396 q) (meaning1404 q) (meaning1410 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1404 = false ∨ valuation q 1410 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1413 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_left (literal (valuationOf q) (1386)) (literal (valuationOf q) (1413)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 1 (meaning1386 q) (meaning1413 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1413 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1414 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1414)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 1 1 (meaning1386 q) (meaning1406 q) (meaning1414 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1406 = false ∨ valuation q 1414 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1415 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1415)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 1 2 (meaning1386 q) (meaning1407 q) (meaning1415 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1407 = false ∨ valuation q 1415 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1416 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1416)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 1 3 (meaning1386 q) (meaning1408 q) (meaning1416 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1408 = false ∨ valuation q 1416 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1417 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1417)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 1 4 (meaning1386 q) (meaning1409 q) (meaning1417 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1409 = false ∨ valuation q 1417 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1418)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 1 5 (meaning1386 q) (meaning1410 q) (meaning1418 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1410 = false ∨ valuation q 1418 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1414 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_left (literal (valuationOf q) (1387)) (literal (valuationOf q) (1414)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 2 (meaning1387 q) (meaning1414 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1414 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1415 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1415)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 2 1 (meaning1387 q) (meaning1406 q) (meaning1415 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1406 = false ∨ valuation q 1415 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1416 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1416)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 2 2 (meaning1387 q) (meaning1407 q) (meaning1416 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1407 = false ∨ valuation q 1416 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1417 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1417)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 2 3 (meaning1387 q) (meaning1408 q) (meaning1417 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1408 = false ∨ valuation q 1417 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1418 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1418)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 2 4 (meaning1387 q) (meaning1409 q) (meaning1418 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1409 = false ∨ valuation q 1418 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 2 5 (meaning1387 q) (meaning1410 q) (meaning1419 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1410 = false ∨ valuation q 1419 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1415 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_left (literal (valuationOf q) (1388)) (literal (valuationOf q) (1415)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 3 (meaning1388 q) (meaning1415 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1415 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1416 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1416)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 3 1 (meaning1388 q) (meaning1406 q) (meaning1416 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1406 = false ∨ valuation q 1416 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1417 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1417)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 3 2 (meaning1388 q) (meaning1407 q) (meaning1417 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1407 = false ∨ valuation q 1417 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1418 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1418)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 3 3 (meaning1388 q) (meaning1408 q) (meaning1418 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1408 = false ∨ valuation q 1418 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1419 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 3 4 (meaning1388 q) (meaning1409 q) (meaning1419 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1409 = false ∨ valuation q 1419 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1420)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 3 5 (meaning1388 q) (meaning1410 q) (meaning1420 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1410 = false ∨ valuation q 1420 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1416 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_left (literal (valuationOf q) (1389)) (literal (valuationOf q) (1416)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 4 (meaning1389 q) (meaning1416 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1416 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1417 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1417)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 4 1 (meaning1389 q) (meaning1406 q) (meaning1417 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1406 = false ∨ valuation q 1417 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1418 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1418)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 4 2 (meaning1389 q) (meaning1407 q) (meaning1418 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1407 = false ∨ valuation q 1418 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E168.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112168
