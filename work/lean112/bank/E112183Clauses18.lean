import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_right (literal (valuationOf q) (-32)) (literal (valuationOf q) (1381)) (countLit q [-31]) (countLit q [-32]) (count1381 q) 1 (meaningNeg32 q) (meaning1381 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1381 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1381)) (countLit q [-31]) (countLit q [-32]) (count1381 q) 1 (meaningNeg31 q) (meaning1381 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1381 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 32 = true ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-32)) (literal (valuationOf q) (1382)) (countLit q [-31]) (countLit q [-32]) (count1381 q) 1 1 (meaningNeg31 q) (meaningNeg32 q) (meaning1382 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 32)) = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 32 = true ∨ valuation q 1382 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-29]) + (countLit q [-31, -32]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31, -32])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1383)) (countLit q [-29]) (countLit q [-31, -32]) (count1383 q) 1 (meaning1381 q) (meaning1383 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1383 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-29]) + (countLit q [-31, -32]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31, -32])
  have hm := merge_right (literal (valuationOf q) (1382)) (literal (valuationOf q) (1384)) (countLit q [-29]) (countLit q [-31, -32]) (count1383 q) 2 (meaning1382 q) (meaning1384 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1384 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-29]) + (countLit q [-31, -32]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31, -32])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1383)) (countLit q [-29]) (countLit q [-31, -32]) (count1383 q) 1 (meaningNeg29 q) (meaning1383 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1383 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-29]) + (countLit q [-31, -32]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31, -32])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1384)) (countLit q [-29]) (countLit q [-31, -32]) (count1383 q) 1 1 (meaningNeg29 q) (meaning1381 q) (meaning1384 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1381 = false ∨ valuation q 1384 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1382 = false ∨ valuationOf q 1385 = true := by
  have hs : count1383 q = (countLit q [-29]) + (countLit q [-31, -32]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31, -32])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1385)) (countLit q [-29]) (countLit q [-31, -32]) (count1383 q) 1 2 (meaningNeg29 q) (meaning1382 q) (meaning1385 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1382 = false ∨ valuation q 1385 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1386)) (countLit q [-38]) (countLit q [-40]) (count1386 q) 1 (meaningNeg40 q) (meaning1386 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1386 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1386)) (countLit q [-38]) (countLit q [-40]) (count1386 q) 1 (meaningNeg38 q) (meaning1386 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1386 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 40 = true ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (1387)) (countLit q [-38]) (countLit q [-40]) (count1386 q) 1 1 (meaningNeg38 q) (meaningNeg40 q) (meaning1387 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 1387 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-35]) (countLit q [-38, -40]) (count1388 q) 1 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1387)) (literal (valuationOf q) (1389)) (countLit q [-35]) (countLit q [-38, -40]) (count1388 q) 2 (meaning1387 q) (meaning1389 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1389 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1388)) (countLit q [-35]) (countLit q [-38, -40]) (count1388 q) 1 (meaningNeg35 q) (meaning1388 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1388 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1389)) (countLit q [-35]) (countLit q [-38, -40]) (count1388 q) 1 1 (meaningNeg35 q) (meaning1386 q) (meaning1389 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1386 = false ∨ valuation q 1389 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1391 = true := by
  have hs : count1391 q = (countLit q [-29, -31, -32]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32]) (l₂ := [-35, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1388)) (literal (valuationOf q) (1391)) (countLit q [-29, -31, -32]) (countLit q [-35, -38, -40]) (count1391 q) 1 (meaning1388 q) (meaning1391 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1391 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-29, -31, -32]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32]) (l₂ := [-35, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1389)) (literal (valuationOf q) (1392)) (countLit q [-29, -31, -32]) (countLit q [-35, -38, -40]) (count1391 q) 2 (meaning1389 q) (meaning1392 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1392 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1391 = true := by
  have hs : count1391 q = (countLit q [-29, -31, -32]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32]) (l₂ := [-35, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1383)) (literal (valuationOf q) (1391)) (countLit q [-29, -31, -32]) (countLit q [-35, -38, -40]) (count1391 q) 1 (meaning1383 q) (meaning1391 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1391 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-29, -31, -32]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32]) (l₂ := [-35, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1392)) (countLit q [-29, -31, -32]) (countLit q [-35, -38, -40]) (count1391 q) 1 1 (meaning1383 q) (meaning1388 q) (meaning1392 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1388 = false ∨ valuation q 1392 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-29, -31, -32]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32]) (l₂ := [-35, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1393)) (countLit q [-29, -31, -32]) (countLit q [-35, -38, -40]) (count1391 q) 1 2 (meaning1383 q) (meaning1389 q) (meaning1393 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1389 = false ∨ valuation q 1393 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-29, -31, -32]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32]) (l₂ := [-35, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1384)) (literal (valuationOf q) (1392)) (countLit q [-29, -31, -32]) (countLit q [-35, -38, -40]) (count1391 q) 2 (meaning1384 q) (meaning1392 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1392 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-29, -31, -32]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32]) (l₂ := [-35, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1393)) (countLit q [-29, -31, -32]) (countLit q [-35, -38, -40]) (count1391 q) 2 1 (meaning1384 q) (meaning1388 q) (meaning1393 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1388 = false ∨ valuation q 1393 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1394 = true := by
  have hs : count1391 q = (countLit q [-29, -31, -32]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32]) (l₂ := [-35, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1394)) (countLit q [-29, -31, -32]) (countLit q [-35, -38, -40]) (count1391 q) 2 2 (meaning1384 q) (meaning1389 q) (meaning1394 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1389 = false ∨ valuation q 1394 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-29, -31, -32]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -32]) (l₂ := [-35, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1385)) (literal (valuationOf q) (1393)) (countLit q [-29, -31, -32]) (countLit q [-35, -38, -40]) (count1391 q) 3 (meaning1385 q) (meaning1393 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1393 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1397)) (countLit q [-43]) (countLit q [-46]) (count1397 q) 1 (meaningNeg46 q) (meaning1397 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1397 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1397)) (countLit q [-43]) (countLit q [-46]) (count1397 q) 1 (meaningNeg43 q) (meaning1397 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1397 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43, -46])
  have hm := merge_right (literal (valuationOf q) (1397)) (literal (valuationOf q) (1399)) (countLit q [-41]) (countLit q [-43, -46]) (count1399 q) 1 (meaning1397 q) (meaning1399 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1399 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43, -46])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1399)) (countLit q [-41]) (countLit q [-43, -46]) (count1399 q) 1 (meaningNeg41 q) (meaning1399 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1399 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-41]) + (countLit q [-43, -46]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43, -46])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1400)) (countLit q [-41]) (countLit q [-43, -46]) (count1399 q) 1 1 (meaningNeg41 q) (meaning1397 q) (meaning1400 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1397 = false ∨ valuation q 1400 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-47]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1402)) (countLit q [-47]) (countLit q [-49]) (count1402 q) 1 (meaningNeg49 q) (meaning1402 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1402 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-47]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1402)) (countLit q [-47]) (countLit q [-49]) (count1402 q) 1 (meaningNeg47 q) (meaning1402 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1402 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1404 = true := by
  have hs : count1404 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1404)) (countLit q [-54]) (countLit q [-56]) (count1404 q) 1 (meaningNeg56 q) (meaning1404 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1404 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E183.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112183
