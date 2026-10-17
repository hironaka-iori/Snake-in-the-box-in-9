import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 40 = true ∨ valuationOf q 1369 = true := by
  have hs : count1368 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (1369)) (countLit q [-38]) (countLit q [-40]) (count1368 q) 1 1 (meaningNeg38 q) (meaningNeg40 q) (meaning1369 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 40 = true ∨ valuation q 1369 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1368)) (literal (valuationOf q) (1370)) (countLit q [-35]) (countLit q [-38, -40]) (count1370 q) 1 (meaning1368 q) (meaning1370 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1370 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1369)) (literal (valuationOf q) (1371)) (countLit q [-35]) (countLit q [-38, -40]) (count1370 q) 2 (meaning1369 q) (meaning1371 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1371 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1370)) (countLit q [-35]) (countLit q [-38, -40]) (count1370 q) 1 (meaningNeg35 q) (meaning1370 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1370 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1371)) (countLit q [-35]) (countLit q [-38, -40]) (count1370 q) 1 1 (meaningNeg35 q) (meaning1368 q) (meaning1371 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1368 = false ∨ valuation q 1371 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1370)) (literal (valuationOf q) (1373)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 1 (meaning1370 q) (meaning1373 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1373 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1371)) (literal (valuationOf q) (1374)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 2 (meaning1371 q) (meaning1374 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1374 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1365)) (literal (valuationOf q) (1373)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 1 (meaning1365 q) (meaning1373 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1373 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1374)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 1 1 (meaning1365 q) (meaning1370 q) (meaning1374 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1370 = false ∨ valuation q 1374 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1366)) (literal (valuationOf q) (1374)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 2 (meaning1366 q) (meaning1374 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1374 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1379)) (countLit q [-45]) (countLit q [-46]) (count1379 q) 1 (meaningNeg46 q) (meaning1379 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1379 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1380 = true := by
  have hs : count1379 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1380)) (countLit q [-45]) (countLit q [-46]) (count1379 q) 1 1 (meaningNeg45 q) (meaningNeg46 q) (meaning1380 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 46 = true ∨ valuation q 1380 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (1379)) (literal (valuationOf q) (1381)) (countLit q [-43]) (countLit q [-45, -46]) (count1381 q) 1 (meaning1379 q) (meaning1381 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1381 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (1380)) (literal (valuationOf q) (1382)) (countLit q [-43]) (countLit q [-45, -46]) (count1381 q) 2 (meaning1380 q) (meaning1382 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1382 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1380 = false ∨ valuationOf q 1383 = true := by
  have hs : count1381 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1383)) (countLit q [-43]) (countLit q [-45, -46]) (count1381 q) 1 2 (meaningNeg43 q) (meaning1380 q) (meaning1383 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1380 = false ∨ valuation q 1383 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1384)) (countLit q [-49]) (countLit q [-51]) (count1384 q) 1 (meaningNeg51 q) (meaning1384 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1384 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1384)) (countLit q [-49]) (countLit q [-51]) (count1384 q) 1 (meaningNeg49 q) (meaning1384 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1384 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1385 = true := by
  have hs : count1384 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1385)) (countLit q [-49]) (countLit q [-51]) (count1384 q) 1 1 (meaningNeg49 q) (meaningNeg51 q) (meaning1385 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 51 = true ∨ valuation q 1385 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-53]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1386)) (countLit q [-53]) (countLit q [-57]) (count1386 q) 1 (meaningNeg53 q) (meaning1386 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1386 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-53]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1387)) (countLit q [-53]) (countLit q [-57]) (count1386 q) 1 1 (meaningNeg53 q) (meaningNeg57 q) (meaning1387 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 57 = true ∨ valuation q 1387 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 1 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_left (literal (valuationOf q) (1384)) (literal (valuationOf q) (1388)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 1 (meaning1384 q) (meaning1388 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1388 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1389)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 1 1 (meaning1384 q) (meaning1386 q) (meaning1389 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1386 = false ∨ valuation q 1389 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_left (literal (valuationOf q) (1385)) (literal (valuationOf q) (1389)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 2 (meaning1385 q) (meaning1389 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1389 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1390 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1390)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 2 1 (meaning1385 q) (meaning1386 q) (meaning1390 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1386 = false ∨ valuation q 1390 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1391 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1391)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 2 2 (meaning1385 q) (meaning1387 q) (meaning1391 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1387 = false ∨ valuation q 1391 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_right (literal (valuationOf q) (1388)) (literal (valuationOf q) (1392)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 1 (meaning1388 q) (meaning1392 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1392 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_left (literal (valuationOf q) (1381)) (literal (valuationOf q) (1392)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 1 (meaning1381 q) (meaning1392 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1392 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1393)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 1 1 (meaning1381 q) (meaning1388 q) (meaning1393 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1388 = false ∨ valuation q 1393 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1394 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1394)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 1 2 (meaning1381 q) (meaning1389 q) (meaning1394 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1389 = false ∨ valuation q 1394 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1391 = false ∨ valuationOf q 1396 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1391)) (literal (valuationOf q) (1396)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 1 4 (meaning1381 q) (meaning1391 q) (meaning1396 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1391 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1391 = false ∨ valuation q 1396 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_left (literal (valuationOf q) (1382)) (literal (valuationOf q) (1393)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 2 (meaning1382 q) (meaning1393 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1393 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E205.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112205
