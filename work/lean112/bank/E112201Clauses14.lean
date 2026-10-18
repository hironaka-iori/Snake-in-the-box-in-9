import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1337)) (literal (valuationOf q) (1341)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1340 q) 2 (meaning1337 q) (meaning1341 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1341 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1342 = true := by
  have hs : count1340 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1337)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1342)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1340 q) 2 1 (meaning1337 q) (meaning1338 q) (meaning1342 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1338 = false ∨ valuation q 1342 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1340)) (literal (valuationOf q) (1344)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 1 (meaning1340 q) (meaning1344 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1344 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1345 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1341)) (literal (valuationOf q) (1345)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 2 (meaning1341 q) (meaning1345 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1345 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1346 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1342)) (literal (valuationOf q) (1346)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 3 (meaning1342 q) (meaning1346 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1346 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1333)) (literal (valuationOf q) (1344)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 1 (meaning1333 q) (meaning1344 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1344 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1345 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1345)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 1 1 (meaning1333 q) (meaning1340 q) (meaning1345 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1340 = false ∨ valuation q 1345 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1346 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1346)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 1 2 (meaning1333 q) (meaning1341 q) (meaning1346 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1341 = false ∨ valuation q 1346 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1345 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1334)) (literal (valuationOf q) (1345)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 2 (meaning1334 q) (meaning1345 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1345 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1346 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1346)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 2 1 (meaning1334 q) (meaning1340 q) (meaning1346 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1340 = false ∨ valuation q 1346 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1344)) (literal (valuationOf q) (1351)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 1 (meaning1344 q) (meaning1351 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1351 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1345)) (literal (valuationOf q) (1352)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 2 (meaning1345 q) (meaning1352 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1352 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1353 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1346)) (literal (valuationOf q) (1353)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 3 (meaning1346 q) (meaning1353 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1353 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1325)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1352)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 1 1 (meaning1325 q) (meaning1344 q) (meaning1352 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1344 = false ∨ valuation q 1352 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1353 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1325)) (literal (valuationOf q) (1345)) (literal (valuationOf q) (1353)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 1 2 (meaning1325 q) (meaning1345 q) (meaning1353 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1345 = false ∨ valuation q 1353 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1353 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1326)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1353)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 2 1 (meaning1326 q) (meaning1344 q) (meaning1353 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1344 = false ∨ valuation q 1353 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1355 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1355)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 4 1 (meaning1328 q) (meaning1344 q) (meaning1355 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1344 = false ∨ valuation q 1355 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1357 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1357)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 6 1 (meaning1330 q) (meaning1344 q) (meaning1357 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1344 = false ∨ valuation q 1357 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (1363)) (countLit q [-31]) (countLit q [-34]) (count1363 q) 1 (meaningNeg34 q) (meaning1363 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1363 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1363)) (countLit q [-31]) (countLit q [-34]) (count1363 q) 1 (meaningNeg31 q) (meaning1363 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1363 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 34 = true ∨ valuationOf q 1364 = true := by
  have hs : count1363 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-34)) (literal (valuationOf q) (1364)) (countLit q [-31]) (countLit q [-34]) (count1363 q) 1 1 (meaningNeg31 q) (meaningNeg34 q) (meaning1364 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 34)) = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 34 = true ∨ valuation q 1364 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-28]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31, -34])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1365)) (countLit q [-28]) (countLit q [-31, -34]) (count1365 q) 1 (meaning1363 q) (meaning1365 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1365 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-28]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31, -34])
  have hm := merge_right (literal (valuationOf q) (1364)) (literal (valuationOf q) (1366)) (countLit q [-28]) (countLit q [-31, -34]) (count1365 q) 2 (meaning1364 q) (meaning1366 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1366 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-28]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31, -34])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1365)) (countLit q [-28]) (countLit q [-31, -34]) (count1365 q) 1 (meaningNeg28 q) (meaning1365 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1365 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1363 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-28]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31, -34])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1366)) (countLit q [-28]) (countLit q [-31, -34]) (count1365 q) 1 1 (meaningNeg28 q) (meaning1363 q) (meaning1366 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1363 = false ∨ valuation q 1366 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1364 = false ∨ valuationOf q 1367 = true := by
  have hs : count1365 q = (countLit q [-28]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31, -34])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1367)) (countLit q [-28]) (countLit q [-31, -34]) (count1365 q) 1 2 (meaningNeg28 q) (meaning1364 q) (meaning1367 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1364 = false ∨ valuation q 1367 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1368)) (countLit q [-38]) (countLit q [-40]) (count1368 q) 1 (meaningNeg40 q) (meaning1368 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1368 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1368)) (countLit q [-38]) (countLit q [-40]) (count1368 q) 1 (meaningNeg38 q) (meaning1368 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1368 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 40 = true ∨ valuationOf q 1369 = true := by
  have hs : count1368 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (1369)) (countLit q [-38]) (countLit q [-40]) (count1368 q) 1 1 (meaningNeg38 q) (meaningNeg40 q) (meaning1369 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 1369 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1368)) (literal (valuationOf q) (1370)) (countLit q [-35]) (countLit q [-38, -40]) (count1370 q) 1 (meaning1368 q) (meaning1370 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1370 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1369)) (literal (valuationOf q) (1371)) (countLit q [-35]) (countLit q [-38, -40]) (count1370 q) 2 (meaning1369 q) (meaning1371 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1371 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1370)) (countLit q [-35]) (countLit q [-38, -40]) (count1370 q) 1 (meaningNeg35 q) (meaning1370 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1370 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E201.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112201
