import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1355 = true := by
  have hs : count1353 q = (countLit q [-25, -28, -29]) + (countLit q [-32, -34, -36, -37]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29]) (l₂ := [-32, -34, -36, -37])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1355)) (countLit q [-25, -28, -29]) (countLit q [-32, -34, -36, -37]) (count1353 q) 2 1 (meaning1343 q) (meaning1349 q) (meaning1355 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1349 = false ∨ valuation q 1355 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1360 = true := by
  have hs : count1360 q = (countLit q [-40]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1360)) (countLit q [-40]) (countLit q [-44]) (count1360 q) 1 (meaningNeg44 q) (meaning1360 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1360 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1360 = true := by
  have hs : count1360 q = (countLit q [-40]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1360)) (countLit q [-40]) (countLit q [-44]) (count1360 q) 1 (meaningNeg40 q) (meaning1360 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1360 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1361 = true := by
  have hs : count1360 q = (countLit q [-40]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1361)) (countLit q [-40]) (countLit q [-44]) (count1360 q) 1 1 (meaningNeg40 q) (meaningNeg44 q) (meaning1361 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 44 = true ∨ valuation q 1361 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -44])
  have hm := merge_right (literal (valuationOf q) (1360)) (literal (valuationOf q) (1362)) (countLit q [-39]) (countLit q [-40, -44]) (count1362 q) 1 (meaning1360 q) (meaning1362 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1362 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -44])
  have hm := merge_right (literal (valuationOf q) (1361)) (literal (valuationOf q) (1363)) (countLit q [-39]) (countLit q [-40, -44]) (count1362 q) 2 (meaning1361 q) (meaning1363 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1363 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -44])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1362)) (countLit q [-39]) (countLit q [-40, -44]) (count1362 q) 1 (meaningNeg39 q) (meaning1362 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1362 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1360 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -44])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1363)) (countLit q [-39]) (countLit q [-40, -44]) (count1362 q) 1 1 (meaningNeg39 q) (meaning1360 q) (meaning1363 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1360 = false ∨ valuation q 1363 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1365)) (countLit q [-45]) (countLit q [-47]) (count1365 q) 1 (meaningNeg47 q) (meaning1365 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1365 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1365)) (countLit q [-45]) (countLit q [-47]) (count1365 q) 1 (meaningNeg45 q) (meaning1365 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1365 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 47 = true ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (1366)) (countLit q [-45]) (countLit q [-47]) (count1365 q) 1 1 (meaningNeg45 q) (meaningNeg47 q) (meaning1366 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 1366 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1367)) (countLit q [-50]) (countLit q [-52]) (count1367 q) 1 (meaningNeg52 q) (meaning1367 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1367 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1367)) (countLit q [-50]) (countLit q [-52]) (count1367 q) 1 (meaningNeg50 q) (meaning1367 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1367 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1368 = true := by
  have hs : count1367 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1368)) (countLit q [-50]) (countLit q [-52]) (count1367 q) 1 1 (meaningNeg50 q) (meaningNeg52 q) (meaning1368 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 52 = true ∨ valuation q 1368 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_right (literal (valuationOf q) (1367)) (literal (valuationOf q) (1369)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count1369 q) 1 (meaning1367 q) (meaning1369 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1369 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_right (literal (valuationOf q) (1368)) (literal (valuationOf q) (1370)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count1369 q) 2 (meaning1368 q) (meaning1370 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1370 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_left (literal (valuationOf q) (1365)) (literal (valuationOf q) (1369)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count1369 q) 1 (meaning1365 q) (meaning1369 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1369 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1370)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count1369 q) 1 1 (meaning1365 q) (meaning1367 q) (meaning1370 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1367 = false ∨ valuation q 1370 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1371)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count1369 q) 1 2 (meaning1365 q) (meaning1368 q) (meaning1371 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1368 = false ∨ valuation q 1371 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_left (literal (valuationOf q) (1366)) (literal (valuationOf q) (1370)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count1369 q) 2 (meaning1366 q) (meaning1370 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1370 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1371)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count1369 q) 2 1 (meaning1366 q) (meaning1367 q) (meaning1371 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1367 = false ∨ valuation q 1371 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1372 = true := by
  have hs : count1369 q = (countLit q [-45, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-50, -52])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1372)) (countLit q [-45, -47]) (countLit q [-50, -52]) (count1369 q) 2 2 (meaning1366 q) (meaning1368 q) (meaning1372 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1368 = false ∨ valuation q 1372 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1369)) (literal (valuationOf q) (1373)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 1 (meaning1369 q) (meaning1373 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1373 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1370)) (literal (valuationOf q) (1374)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 2 (meaning1370 q) (meaning1374 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1374 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1371)) (literal (valuationOf q) (1375)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 3 (meaning1371 q) (meaning1375 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1375 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1376 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1372)) (literal (valuationOf q) (1376)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 4 (meaning1372 q) (meaning1376 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1376 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_left (literal (valuationOf q) (1362)) (literal (valuationOf q) (1373)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 1 (meaning1362 q) (meaning1373 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1373 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1374)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 1 1 (meaning1362 q) (meaning1369 q) (meaning1374 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1369 = false ∨ valuation q 1374 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1375)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 1 2 (meaning1362 q) (meaning1370 q) (meaning1375 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1370 = false ∨ valuation q 1375 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1376 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1376)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 1 3 (meaning1362 q) (meaning1371 q) (meaning1376 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1371 = false ∨ valuation q 1376 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1377 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1372)) (literal (valuationOf q) (1377)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 1 4 (meaning1362 q) (meaning1372 q) (meaning1377 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1372 = false ∨ valuation q 1377 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_left (literal (valuationOf q) (1363)) (literal (valuationOf q) (1374)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 2 (meaning1363 q) (meaning1374 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1374 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E166.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112166
