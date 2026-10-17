import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1391 = true := by
  have hs : count1390 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1391)) (countLit q [-43]) (countLit q [-46]) (count1390 q) 1 1 (meaningNeg43 q) (meaningNeg46 q) (meaning1391 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 46 = true ∨ valuation q 1391 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-40]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -46])
  have hm := merge_right (literal (valuationOf q) (1390)) (literal (valuationOf q) (1392)) (countLit q [-40]) (countLit q [-43, -46]) (count1392 q) 1 (meaning1390 q) (meaning1392 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1392 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-40]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -46])
  have hm := merge_right (literal (valuationOf q) (1391)) (literal (valuationOf q) (1393)) (countLit q [-40]) (countLit q [-43, -46]) (count1392 q) 2 (meaning1391 q) (meaning1393 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1393 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-40]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -46])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1392)) (countLit q [-40]) (countLit q [-43, -46]) (count1392 q) 1 (meaningNeg40 q) (meaning1392 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1392 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1390 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-40]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (1390)) (literal (valuationOf q) (1393)) (countLit q [-40]) (countLit q [-43, -46]) (count1392 q) 1 1 (meaningNeg40 q) (meaning1390 q) (meaning1393 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1390 = false ∨ valuation q 1393 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1391 = false ∨ valuationOf q 1394 = true := by
  have hs : count1392 q = (countLit q [-40]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (1391)) (literal (valuationOf q) (1394)) (countLit q [-40]) (countLit q [-43, -46]) (count1392 q) 1 2 (meaningNeg40 q) (meaning1391 q) (meaning1394 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1391 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1391 = false ∨ valuation q 1394 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1395)) (countLit q [-49]) (countLit q [-50]) (count1395 q) 1 (meaningNeg50 q) (meaning1395 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1395 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1395)) (countLit q [-49]) (countLit q [-50]) (count1395 q) 1 (meaningNeg49 q) (meaning1395 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1395 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 50 = true ∨ valuationOf q 1396 = true := by
  have hs : count1395 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (1396)) (countLit q [-49]) (countLit q [-50]) (count1395 q) 1 1 (meaningNeg49 q) (meaningNeg50 q) (meaning1396 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 1396 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-51]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1397)) (countLit q [-51]) (countLit q [-54]) (count1397 q) 1 (meaningNeg54 q) (meaning1397 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1397 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-51]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1397)) (countLit q [-51]) (countLit q [-54]) (count1397 q) 1 (meaningNeg51 q) (meaning1397 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1397 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1398 = true := by
  have hs : count1397 q = (countLit q [-51]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1398)) (countLit q [-51]) (countLit q [-54]) (count1397 q) 1 1 (meaningNeg51 q) (meaningNeg54 q) (meaning1398 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 54 = true ∨ valuation q 1398 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-49, -50]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-51, -54])
  have hm := merge_right (literal (valuationOf q) (1397)) (literal (valuationOf q) (1399)) (countLit q [-49, -50]) (countLit q [-51, -54]) (count1399 q) 1 (meaning1397 q) (meaning1399 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1399 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-49, -50]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-51, -54])
  have hm := merge_right (literal (valuationOf q) (1398)) (literal (valuationOf q) (1400)) (countLit q [-49, -50]) (countLit q [-51, -54]) (count1399 q) 2 (meaning1398 q) (meaning1400 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1400 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-49, -50]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-51, -54])
  have hm := merge_left (literal (valuationOf q) (1395)) (literal (valuationOf q) (1399)) (countLit q [-49, -50]) (countLit q [-51, -54]) (count1399 q) 1 (meaning1395 q) (meaning1399 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1399 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-49, -50]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-51, -54])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1400)) (countLit q [-49, -50]) (countLit q [-51, -54]) (count1399 q) 1 1 (meaning1395 q) (meaning1397 q) (meaning1400 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1397 = false ∨ valuation q 1400 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-49, -50]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-51, -54])
  have hm := merge_left (literal (valuationOf q) (1396)) (literal (valuationOf q) (1400)) (countLit q [-49, -50]) (countLit q [-51, -54]) (count1399 q) 2 (meaning1396 q) (meaning1400 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1400 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-49, -50]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-51, -54])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1401)) (countLit q [-49, -50]) (countLit q [-51, -54]) (count1399 q) 2 1 (meaning1396 q) (meaning1397 q) (meaning1401 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1397 = false ∨ valuation q 1401 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-49, -50]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-49, -50]) (l₂ := [-51, -54])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1398)) (literal (valuationOf q) (1402)) (countLit q [-49, -50]) (countLit q [-51, -54]) (count1399 q) 2 2 (meaning1396 q) (meaning1398 q) (meaning1402 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1398 = false ∨ valuation q 1402 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_right (literal (valuationOf q) (1399)) (literal (valuationOf q) (1403)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 1 (meaning1399 q) (meaning1403 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1403 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_right (literal (valuationOf q) (1400)) (literal (valuationOf q) (1404)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 2 (meaning1400 q) (meaning1404 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1404 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1405 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_right (literal (valuationOf q) (1401)) (literal (valuationOf q) (1405)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 3 (meaning1401 q) (meaning1405 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1405 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_right (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 4 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_left (literal (valuationOf q) (1392)) (literal (valuationOf q) (1403)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 1 (meaning1392 q) (meaning1403 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1403 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1404)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 1 1 (meaning1392 q) (meaning1399 q) (meaning1404 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1399 = false ∨ valuation q 1404 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1405 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1405)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 1 2 (meaning1392 q) (meaning1400 q) (meaning1405 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1400 = false ∨ valuation q 1405 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1406 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1406)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 1 3 (meaning1392 q) (meaning1401 q) (meaning1406 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1401 = false ∨ valuation q 1406 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_left (literal (valuationOf q) (1393)) (literal (valuationOf q) (1404)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 2 (meaning1393 q) (meaning1404 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1404 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1405 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1405)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 2 1 (meaning1393 q) (meaning1399 q) (meaning1405 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1399 = false ∨ valuation q 1405 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1406 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1406)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 2 2 (meaning1393 q) (meaning1400 q) (meaning1406 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1400 = false ∨ valuation q 1406 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1405 = true := by
  have hs : count1403 q = (countLit q [-40, -43, -46]) + (countLit q [-49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -46]) (l₂ := [-49, -50, -51, -54])
  have hm := merge_left (literal (valuationOf q) (1394)) (literal (valuationOf q) (1405)) (countLit q [-40, -43, -46]) (countLit q [-49, -50, -51, -54]) (count1403 q) 3 (meaning1394 q) (meaning1405 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1405 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-30, -31, -33, -37, -38, -39]) + (countLit q [-40, -43, -46, -49, -50, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -37, -38, -39]) (l₂ := [-40, -43, -46, -49, -50, -51, -54])
  have hm := merge_right (literal (valuationOf q) (1403)) (literal (valuationOf q) (1410)) (countLit q [-30, -31, -33, -37, -38, -39]) (countLit q [-40, -43, -46, -49, -50, -51, -54]) (count1410 q) 1 (meaning1403 q) (meaning1410 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1410 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E107.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112107
