import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1396 = false ∨ valuationOf q 1399 = true := by
  have hs : count1398 q = (countLit q [-43]) + (countLit q [-45, -47]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -47])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (1396)) (literal (valuationOf q) (1399)) (countLit q [-43]) (countLit q [-45, -47]) (count1398 q) 1 1 (meaningNeg43 q) (meaning1396 q) (meaning1399 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1396 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1396 = false ∨ valuation q 1399 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true := by
  have hs : count1398 q = (countLit q [-43]) + (countLit q [-45, -47]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -47])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1400)) (countLit q [-43]) (countLit q [-45, -47]) (count1398 q) 1 2 (meaningNeg43 q) (meaning1397 q) (meaning1400 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1397 = false ∨ valuation q 1400 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1401 = true := by
  have hs : count1401 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1401)) (countLit q [-49]) (countLit q [-50]) (count1401 q) 1 (meaningNeg50 q) (meaning1401 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1401 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1401 = true := by
  have hs : count1401 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1401)) (countLit q [-49]) (countLit q [-50]) (count1401 q) 1 (meaningNeg49 q) (meaning1401 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1401 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 50 = true ∨ valuationOf q 1402 = true := by
  have hs : count1401 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (1402)) (countLit q [-49]) (countLit q [-50]) (count1401 q) 1 1 (meaningNeg49 q) (meaningNeg50 q) (meaning1402 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 1402 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1403)) (countLit q [-52]) (countLit q [-53]) (count1403 q) 1 (meaningNeg53 q) (meaning1403 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1403 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1403)) (countLit q [-52]) (countLit q [-53]) (count1403 q) 1 (meaningNeg52 q) (meaning1403 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1403 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 53 = true ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (1404)) (countLit q [-52]) (countLit q [-53]) (count1403 q) 1 1 (meaningNeg52 q) (meaningNeg53 q) (meaning1404 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 1404 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1405 = true := by
  have hs : count1405 q = (countLit q [-49, -50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-52, -53])
  have hm := merge_right (literal (valuationOf q) (1403)) (literal (valuationOf q) (1405)) (countLit q [-49, -50]) (countLit q [-52, -53]) (count1405 q) 1 (meaning1403 q) (meaning1405 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1405 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1406 = true := by
  have hs : count1405 q = (countLit q [-49, -50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-52, -53])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1406)) (countLit q [-49, -50]) (countLit q [-52, -53]) (count1405 q) 2 (meaning1404 q) (meaning1406 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1406 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1405 = true := by
  have hs : count1405 q = (countLit q [-49, -50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-52, -53])
  have hm := merge_left (literal (valuationOf q) (1401)) (literal (valuationOf q) (1405)) (countLit q [-49, -50]) (countLit q [-52, -53]) (count1405 q) 1 (meaning1401 q) (meaning1405 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1405 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1406 = true := by
  have hs : count1405 q = (countLit q [-49, -50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1406)) (countLit q [-49, -50]) (countLit q [-52, -53]) (count1405 q) 1 1 (meaning1401 q) (meaning1403 q) (meaning1406 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1403 = false ∨ valuation q 1406 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1405 q = (countLit q [-49, -50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-52, -53])
  have hm := merge_left (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-49, -50]) (countLit q [-52, -53]) (count1405 q) 2 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1407 = true := by
  have hs : count1405 q = (countLit q [-49, -50]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1407)) (countLit q [-49, -50]) (countLit q [-52, -53]) (count1405 q) 2 1 (meaning1402 q) (meaning1403 q) (meaning1407 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1403 = false ∨ valuation q 1407 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1409 = true := by
  have hs : count1409 q = (countLit q [-43, -45, -47]) + (countLit q [-49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47]) (l₂ := [-49, -50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1405)) (literal (valuationOf q) (1409)) (countLit q [-43, -45, -47]) (countLit q [-49, -50, -52, -53]) (count1409 q) 1 (meaning1405 q) (meaning1409 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1409 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1410 = true := by
  have hs : count1409 q = (countLit q [-43, -45, -47]) + (countLit q [-49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47]) (l₂ := [-49, -50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1406)) (literal (valuationOf q) (1410)) (countLit q [-43, -45, -47]) (countLit q [-49, -50, -52, -53]) (count1409 q) 2 (meaning1406 q) (meaning1410 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1410 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1411 = true := by
  have hs : count1409 q = (countLit q [-43, -45, -47]) + (countLit q [-49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47]) (l₂ := [-49, -50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1407)) (literal (valuationOf q) (1411)) (countLit q [-43, -45, -47]) (countLit q [-49, -50, -52, -53]) (count1409 q) 3 (meaning1407 q) (meaning1411 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1411 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1409 = true := by
  have hs : count1409 q = (countLit q [-43, -45, -47]) + (countLit q [-49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47]) (l₂ := [-49, -50, -52, -53])
  have hm := merge_left (literal (valuationOf q) (1398)) (literal (valuationOf q) (1409)) (countLit q [-43, -45, -47]) (countLit q [-49, -50, -52, -53]) (count1409 q) 1 (meaning1398 q) (meaning1409 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1409 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1410 = true := by
  have hs : count1409 q = (countLit q [-43, -45, -47]) + (countLit q [-49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47]) (l₂ := [-49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1410)) (countLit q [-43, -45, -47]) (countLit q [-49, -50, -52, -53]) (count1409 q) 1 1 (meaning1398 q) (meaning1405 q) (meaning1410 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1405 = false ∨ valuation q 1410 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true := by
  have hs : count1409 q = (countLit q [-43, -45, -47]) + (countLit q [-49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47]) (l₂ := [-49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1411)) (countLit q [-43, -45, -47]) (countLit q [-49, -50, -52, -53]) (count1409 q) 1 2 (meaning1398 q) (meaning1406 q) (meaning1411 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1406 = false ∨ valuation q 1411 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1410 = true := by
  have hs : count1409 q = (countLit q [-43, -45, -47]) + (countLit q [-49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47]) (l₂ := [-49, -50, -52, -53])
  have hm := merge_left (literal (valuationOf q) (1399)) (literal (valuationOf q) (1410)) (countLit q [-43, -45, -47]) (countLit q [-49, -50, -52, -53]) (count1409 q) 2 (meaning1399 q) (meaning1410 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1410 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1411 = true := by
  have hs : count1409 q = (countLit q [-43, -45, -47]) + (countLit q [-49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47]) (l₂ := [-49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1411)) (countLit q [-43, -45, -47]) (countLit q [-49, -50, -52, -53]) (count1409 q) 2 1 (meaning1399 q) (meaning1405 q) (meaning1411 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1405 = false ∨ valuation q 1411 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1411 = true := by
  have hs : count1409 q = (countLit q [-43, -45, -47]) + (countLit q [-49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47]) (l₂ := [-49, -50, -52, -53])
  have hm := merge_left (literal (valuationOf q) (1400)) (literal (valuationOf q) (1411)) (countLit q [-43, -45, -47]) (countLit q [-49, -50, -52, -53]) (count1409 q) 3 (meaning1400 q) (meaning1411 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1411 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-30, -31, -33, -36, -37, -40, -42]) + (countLit q [-43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -36, -37, -40, -42]) (l₂ := [-43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1418)) (countLit q [-30, -31, -33, -36, -37, -40, -42]) (countLit q [-43, -45, -47, -49, -50, -52, -53]) (count1416 q) 1 2 (meaning1389 q) (meaning1410 q) (meaning1418 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1410 = false ∨ valuation q 1418 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-30, -31, -33, -36, -37, -40, -42]) + (countLit q [-43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -36, -37, -40, -42]) (l₂ := [-43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1419)) (countLit q [-30, -31, -33, -36, -37, -40, -42]) (countLit q [-43, -45, -47, -49, -50, -52, -53]) (count1416 q) 1 3 (meaning1389 q) (meaning1411 q) (meaning1419 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1411 = false ∨ valuation q 1419 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-30, -31, -33, -36, -37, -40, -42]) + (countLit q [-43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -36, -37, -40, -42]) (l₂ := [-43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1418)) (countLit q [-30, -31, -33, -36, -37, -40, -42]) (countLit q [-43, -45, -47, -49, -50, -52, -53]) (count1416 q) 2 1 (meaning1390 q) (meaning1409 q) (meaning1418 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1409 = false ∨ valuation q 1418 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-30, -31, -33, -36, -37, -40, -42]) + (countLit q [-43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -36, -37, -40, -42]) (l₂ := [-43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1419)) (countLit q [-30, -31, -33, -36, -37, -40, -42]) (countLit q [-43, -45, -47, -49, -50, -52, -53]) (count1416 q) 2 2 (meaning1390 q) (meaning1410 q) (meaning1419 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1410 = false ∨ valuation q 1419 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true := by
  have hs : count1416 q = (countLit q [-30, -31, -33, -36, -37, -40, -42]) + (countLit q [-43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -36, -37, -40, -42]) (l₂ := [-43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1420)) (countLit q [-30, -31, -33, -36, -37, -40, -42]) (countLit q [-43, -45, -47, -49, -50, -52, -53]) (count1416 q) 2 3 (meaning1390 q) (meaning1411 q) (meaning1420 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1411 = false ∨ valuation q 1420 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-30, -31, -33, -36, -37, -40, -42]) + (countLit q [-43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -36, -37, -40, -42]) (l₂ := [-43, -45, -47, -49, -50, -52, -53])
  have hm := merge_left (literal (valuationOf q) (1391)) (literal (valuationOf q) (1418)) (countLit q [-30, -31, -33, -36, -37, -40, -42]) (countLit q [-43, -45, -47, -49, -50, -52, -53]) (count1416 q) 3 (meaning1391 q) (meaning1418 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1418 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-30, -31, -33, -36, -37, -40, -42]) + (countLit q [-43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -36, -37, -40, -42]) (l₂ := [-43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1419)) (countLit q [-30, -31, -33, -36, -37, -40, -42]) (countLit q [-43, -45, -47, -49, -50, -52, -53]) (count1416 q) 3 1 (meaning1391 q) (meaning1409 q) (meaning1419 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1409 = false ∨ valuation q 1419 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true := by
  have hs : count1416 q = (countLit q [-30, -31, -33, -36, -37, -40, -42]) + (countLit q [-43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -36, -37, -40, -42]) (l₂ := [-43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1420)) (countLit q [-30, -31, -33, -36, -37, -40, -42]) (countLit q [-43, -45, -47, -49, -50, -52, -53]) (count1416 q) 3 2 (meaning1391 q) (meaning1410 q) (meaning1420 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1410 = false ∨ valuation q 1420 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-30, -31, -33, -36, -37, -40, -42]) + (countLit q [-43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -36, -37, -40, -42]) (l₂ := [-43, -45, -47, -49, -50, -52, -53])
  have hm := merge_left (literal (valuationOf q) (1392)) (literal (valuationOf q) (1419)) (countLit q [-30, -31, -33, -36, -37, -40, -42]) (countLit q [-43, -45, -47, -49, -50, -52, -53]) (count1416 q) 4 (meaning1392 q) (meaning1419 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1419 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E148.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112148
