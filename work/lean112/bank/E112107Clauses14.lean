import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1337 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1332)) (literal (valuationOf q) (1337)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 2 1 (meaning1328 q) (meaning1332 q) (meaning1337 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1332 = false ∨ valuation q 1337 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1338 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1338)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 2 2 (meaning1328 q) (meaning1333 q) (meaning1338 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1333 = false ∨ valuation q 1338 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1337 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_left (literal (valuationOf q) (1329)) (literal (valuationOf q) (1337)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 3 (meaning1329 q) (meaning1337 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1337 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1338 = true := by
  have hs : count1335 q = (countLit q [-4, -6, -9]) + (countLit q [-10, -11, -15]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9]) (l₂ := [-10, -11, -15])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1332)) (literal (valuationOf q) (1338)) (countLit q [-4, -6, -9]) (countLit q [-10, -11, -15]) (count1335 q) 3 1 (meaning1329 q) (meaning1332 q) (meaning1338 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1332 = false ∨ valuation q 1338 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-17]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1341)) (countLit q [-17]) (countLit q [-21]) (count1341 q) 1 (meaningNeg21 q) (meaning1341 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1341 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-17]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1341)) (countLit q [-17]) (countLit q [-21]) (count1341 q) 1 (meaningNeg17 q) (meaning1341 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1341 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1342 = true := by
  have hs : count1341 q = (countLit q [-17]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1342)) (countLit q [-17]) (countLit q [-21]) (count1341 q) 1 1 (meaningNeg17 q) (meaningNeg21 q) (meaning1342 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 21 = true ∨ valuation q 1342 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-16]) + (countLit q [-17, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -21])
  have hm := merge_right (literal (valuationOf q) (1341)) (literal (valuationOf q) (1343)) (countLit q [-16]) (countLit q [-17, -21]) (count1343 q) 1 (meaning1341 q) (meaning1343 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1343 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-16]) + (countLit q [-17, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -21])
  have hm := merge_right (literal (valuationOf q) (1342)) (literal (valuationOf q) (1344)) (countLit q [-16]) (countLit q [-17, -21]) (count1343 q) 2 (meaning1342 q) (meaning1344 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1344 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-16]) + (countLit q [-17, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -21])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1343)) (countLit q [-16]) (countLit q [-17, -21]) (count1343 q) 1 (meaningNeg16 q) (meaning1343 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1343 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1341 = false ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-16]) + (countLit q [-17, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -21])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1344)) (countLit q [-16]) (countLit q [-17, -21]) (count1343 q) 1 1 (meaningNeg16 q) (meaning1341 q) (meaning1344 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1341 = false ∨ valuation q 1344 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1342 = false ∨ valuationOf q 1345 = true := by
  have hs : count1343 q = (countLit q [-16]) + (countLit q [-17, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -21])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (1342)) (literal (valuationOf q) (1345)) (countLit q [-16]) (countLit q [-17, -21]) (count1343 q) 1 2 (meaningNeg16 q) (meaning1342 q) (meaning1345 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1342 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1342 = false ∨ valuation q 1345 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1346)) (countLit q [-22]) (countLit q [-23]) (count1346 q) 1 (meaningNeg23 q) (meaning1346 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1346 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1346)) (countLit q [-22]) (countLit q [-23]) (count1346 q) 1 (meaningNeg22 q) (meaning1346 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1346 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1347 = true := by
  have hs : count1346 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1347)) (countLit q [-22]) (countLit q [-23]) (count1346 q) 1 1 (meaningNeg22 q) (meaningNeg23 q) (meaning1347 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 23 = true ∨ valuation q 1347 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-24]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (1348)) (countLit q [-24]) (countLit q [-28]) (count1348 q) 1 (meaningNeg28 q) (meaning1348 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1348 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-24]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1348)) (countLit q [-24]) (countLit q [-28]) (count1348 q) 1 (meaningNeg24 q) (meaning1348 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1348 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 28 = true ∨ valuationOf q 1349 = true := by
  have hs : count1348 q = (countLit q [-24]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-28])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-28)) (literal (valuationOf q) (1349)) (countLit q [-24]) (countLit q [-28]) (count1348 q) 1 1 (meaningNeg24 q) (meaningNeg28 q) (meaning1349 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 28)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 28 = true ∨ valuation q 1349 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-22, -23]) + (countLit q [-24, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-24, -28])
  have hm := merge_right (literal (valuationOf q) (1348)) (literal (valuationOf q) (1350)) (countLit q [-22, -23]) (countLit q [-24, -28]) (count1350 q) 1 (meaning1348 q) (meaning1350 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1350 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1351 = true := by
  have hs : count1350 q = (countLit q [-22, -23]) + (countLit q [-24, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-24, -28])
  have hm := merge_right (literal (valuationOf q) (1349)) (literal (valuationOf q) (1351)) (countLit q [-22, -23]) (countLit q [-24, -28]) (count1350 q) 2 (meaning1349 q) (meaning1351 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1351 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-22, -23]) + (countLit q [-24, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-24, -28])
  have hm := merge_left (literal (valuationOf q) (1346)) (literal (valuationOf q) (1350)) (countLit q [-22, -23]) (countLit q [-24, -28]) (count1350 q) 1 (meaning1346 q) (meaning1350 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1350 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1351 = true := by
  have hs : count1350 q = (countLit q [-22, -23]) + (countLit q [-24, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-24, -28])
  have hm := merge_two (literal (valuationOf q) (1346)) (literal (valuationOf q) (1348)) (literal (valuationOf q) (1351)) (countLit q [-22, -23]) (countLit q [-24, -28]) (count1350 q) 1 1 (meaning1346 q) (meaning1348 q) (meaning1351 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1348 = false ∨ valuation q 1351 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1352 = true := by
  have hs : count1350 q = (countLit q [-22, -23]) + (countLit q [-24, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-24, -28])
  have hm := merge_two (literal (valuationOf q) (1347)) (literal (valuationOf q) (1348)) (literal (valuationOf q) (1352)) (countLit q [-22, -23]) (countLit q [-24, -28]) (count1350 q) 2 1 (meaning1347 q) (meaning1348 q) (meaning1352 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1348 = false ∨ valuation q 1352 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1354)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 1 (meaning1350 q) (meaning1354 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1354 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1355 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_right (literal (valuationOf q) (1351)) (literal (valuationOf q) (1355)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 2 (meaning1351 q) (meaning1355 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1355 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1356 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_right (literal (valuationOf q) (1352)) (literal (valuationOf q) (1356)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 3 (meaning1352 q) (meaning1356 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1356 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_left (literal (valuationOf q) (1343)) (literal (valuationOf q) (1354)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 1 (meaning1343 q) (meaning1354 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1354 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1355 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1355)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 1 1 (meaning1343 q) (meaning1350 q) (meaning1355 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1350 = false ∨ valuation q 1355 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1356 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1356)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 1 2 (meaning1343 q) (meaning1351 q) (meaning1356 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1351 = false ∨ valuation q 1356 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1357 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1357)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 1 3 (meaning1343 q) (meaning1352 q) (meaning1357 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1352 = false ∨ valuation q 1357 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1355 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_left (literal (valuationOf q) (1344)) (literal (valuationOf q) (1355)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 2 (meaning1344 q) (meaning1355 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1355 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1356 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1356)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 2 1 (meaning1344 q) (meaning1350 q) (meaning1356 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1350 = false ∨ valuation q 1356 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E107.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112107
