import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1333)) (countLit q [-55]) (countLit q [-57]) (count1333 q) 1 (meaningNeg57 q) (meaning1333 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1333 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1334 = true := by
  have hs : count1333 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1334)) (countLit q [-55]) (countLit q [-57]) (count1333 q) 1 1 (meaningNeg55 q) (meaningNeg57 q) (meaning1334 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 1334 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-53]) + (countLit q [-55, -57]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55, -57])
  have hm := merge_right (literal (valuationOf q) (1333)) (literal (valuationOf q) (1335)) (countLit q [-53]) (countLit q [-55, -57]) (count1335 q) 1 (meaning1333 q) (meaning1335 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1335 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1336 = true := by
  have hs : count1335 q = (countLit q [-53]) + (countLit q [-55, -57]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55, -57])
  have hm := merge_right (literal (valuationOf q) (1334)) (literal (valuationOf q) (1336)) (countLit q [-53]) (countLit q [-55, -57]) (count1335 q) 2 (meaning1334 q) (meaning1336 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1336 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1335 = true := by
  have hs : count1335 q = (countLit q [-53]) + (countLit q [-55, -57]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55, -57])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1335)) (countLit q [-53]) (countLit q [-55, -57]) (count1335 q) 1 (meaningNeg53 q) (meaning1335 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1335 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1333 = false ∨ valuationOf q 1336 = true := by
  have hs : count1335 q = (countLit q [-53]) + (countLit q [-55, -57]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55, -57])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1336)) (countLit q [-53]) (countLit q [-55, -57]) (count1335 q) 1 1 (meaningNeg53 q) (meaning1333 q) (meaning1336 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1333 = false ∨ valuation q 1336 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-59]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1338)) (countLit q [-59]) (countLit q [-63]) (count1338 q) 1 (meaningNeg59 q) (meaning1338 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1338 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-58]) + (countLit q [-59, -63]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -63])
  have hm := merge_right (literal (valuationOf q) (1338)) (literal (valuationOf q) (1340)) (countLit q [-58]) (countLit q [-59, -63]) (count1340 q) 1 (meaning1338 q) (meaning1340 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1340 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-58]) + (countLit q [-59, -63]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59, -63])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1340)) (countLit q [-58]) (countLit q [-59, -63]) (count1340 q) 1 (meaningNeg58 q) (meaning1340 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1340 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-53, -55, -57]) + (countLit q [-58, -59, -63]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57]) (l₂ := [-58, -59, -63])
  have hm := merge_right (literal (valuationOf q) (1340)) (literal (valuationOf q) (1343)) (countLit q [-53, -55, -57]) (countLit q [-58, -59, -63]) (count1343 q) 1 (meaning1340 q) (meaning1343 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1343 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-53, -55, -57]) + (countLit q [-58, -59, -63]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57]) (l₂ := [-58, -59, -63])
  have hm := merge_left (literal (valuationOf q) (1335)) (literal (valuationOf q) (1343)) (countLit q [-53, -55, -57]) (countLit q [-58, -59, -63]) (count1343 q) 1 (meaning1335 q) (meaning1343 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1343 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-53, -55, -57]) + (countLit q [-58, -59, -63]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57]) (l₂ := [-58, -59, -63])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1344)) (countLit q [-53, -55, -57]) (countLit q [-58, -59, -63]) (count1343 q) 1 1 (meaning1335 q) (meaning1340 q) (meaning1344 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1340 = false ∨ valuation q 1344 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-53, -55, -57]) + (countLit q [-58, -59, -63]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57]) (l₂ := [-58, -59, -63])
  have hm := merge_left (literal (valuationOf q) (1336)) (literal (valuationOf q) (1344)) (countLit q [-53, -55, -57]) (countLit q [-58, -59, -63]) (count1343 q) 2 (meaning1336 q) (meaning1344 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1344 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1345 = true := by
  have hs : count1343 q = (countLit q [-53, -55, -57]) + (countLit q [-58, -59, -63]) := List.countP_append (p := literal q) (l₁ := [-53, -55, -57]) (l₂ := [-58, -59, -63])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1345)) (countLit q [-53, -55, -57]) (countLit q [-58, -59, -63]) (count1343 q) 2 1 (meaning1336 q) (meaning1340 q) (meaning1345 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1340 = false ∨ valuation q 1345 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1349)) (countLit q [-67]) (countLit q [-69]) (count1349 q) 1 (meaningNeg69 q) (meaning1349 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1349 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1349)) (countLit q [-67]) (countLit q [-69]) (count1349 q) 1 (meaningNeg67 q) (meaning1349 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1349 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 69 = true ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (1350)) (countLit q [-67]) (countLit q [-69]) (count1349 q) 1 1 (meaningNeg67 q) (meaningNeg69 q) (meaning1350 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 69 = true ∨ valuation q 1350 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-65]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -69])
  have hm := merge_right (literal (valuationOf q) (1349)) (literal (valuationOf q) (1351)) (countLit q [-65]) (countLit q [-67, -69]) (count1351 q) 1 (meaning1349 q) (meaning1351 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1351 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-65]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -69])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1352)) (countLit q [-65]) (countLit q [-67, -69]) (count1351 q) 2 (meaning1350 q) (meaning1352 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1352 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-65]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -69])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1351)) (countLit q [-65]) (countLit q [-67, -69]) (count1351 q) 1 (meaningNeg65 q) (meaning1351 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1351 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1349 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-65]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -69])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1352)) (countLit q [-65]) (countLit q [-67, -69]) (count1351 q) 1 1 (meaningNeg65 q) (meaning1349 q) (meaning1352 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1349 = false ∨ valuation q 1352 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1350 = false ∨ valuationOf q 1353 = true := by
  have hs : count1351 q = (countLit q [-65]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -69])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1353)) (countLit q [-65]) (countLit q [-67, -69]) (count1351 q) 1 2 (meaningNeg65 q) (meaning1350 q) (meaning1353 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1350 = false ∨ valuation q 1353 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1354)) (countLit q [-71]) (countLit q [-74]) (count1354 q) 1 (meaningNeg74 q) (meaning1354 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1354 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1354)) (countLit q [-71]) (countLit q [-74]) (count1354 q) 1 (meaningNeg71 q) (meaning1354 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1354 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1355 = true := by
  have hs : count1354 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1355)) (countLit q [-71]) (countLit q [-74]) (count1354 q) 1 1 (meaningNeg71 q) (meaningNeg74 q) (meaning1355 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 74 = true ∨ valuation q 1355 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1356)) (countLit q [-76]) (countLit q [-77]) (count1356 q) 1 (meaningNeg77 q) (meaning1356 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1356 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1356)) (countLit q [-76]) (countLit q [-77]) (count1356 q) 1 (meaningNeg76 q) (meaning1356 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1356 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1358 = true := by
  have hs : count1358 q = (countLit q [-71, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1356)) (literal (valuationOf q) (1358)) (countLit q [-71, -74]) (countLit q [-76, -77]) (count1358 q) 1 (meaning1356 q) (meaning1358 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1358 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1358 = true := by
  have hs : count1358 q = (countLit q [-71, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (1354)) (literal (valuationOf q) (1358)) (countLit q [-71, -74]) (countLit q [-76, -77]) (count1358 q) 1 (meaning1354 q) (meaning1358 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1358 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-71, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1359)) (countLit q [-71, -74]) (countLit q [-76, -77]) (count1358 q) 1 1 (meaning1354 q) (meaning1356 q) (meaning1359 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1356 = false ∨ valuation q 1359 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-71, -74]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (1355)) (literal (valuationOf q) (1359)) (countLit q [-71, -74]) (countLit q [-76, -77]) (count1358 q) 2 (meaning1355 q) (meaning1359 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1359 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-65, -67, -69]) + (countLit q [-71, -74, -76, -77]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69]) (l₂ := [-71, -74, -76, -77])
  have hm := merge_right (literal (valuationOf q) (1358)) (literal (valuationOf q) (1362)) (countLit q [-65, -67, -69]) (countLit q [-71, -74, -76, -77]) (count1362 q) 1 (meaning1358 q) (meaning1362 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1362 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E145.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112145
