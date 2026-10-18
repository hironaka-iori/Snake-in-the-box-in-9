import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38, -40])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1371)) (countLit q [-35]) (countLit q [-38, -40]) (count1370 q) 1 1 (meaningNeg35 q) (meaning1368 q) (meaning1371 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1368 = false ∨ valuation q 1371 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1370)) (literal (valuationOf q) (1373)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 1 (meaning1370 q) (meaning1373 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1373 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1371)) (literal (valuationOf q) (1374)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 2 (meaning1371 q) (meaning1374 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1374 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1365)) (literal (valuationOf q) (1373)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 1 (meaning1365 q) (meaning1373 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1373 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1374)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 1 1 (meaning1365 q) (meaning1370 q) (meaning1374 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1370 = false ∨ valuation q 1374 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1366)) (literal (valuationOf q) (1374)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 2 (meaning1366 q) (meaning1374 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1374 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1375)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 2 1 (meaning1366 q) (meaning1370 q) (meaning1375 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1370 = false ∨ valuation q 1375 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-28, -31, -34]) + (countLit q [-35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34]) (l₂ := [-35, -38, -40])
  have hm := merge_left (literal (valuationOf q) (1367)) (literal (valuationOf q) (1375)) (countLit q [-28, -31, -34]) (countLit q [-35, -38, -40]) (count1373 q) 3 (meaning1367 q) (meaning1375 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1375 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1379)) (countLit q [-45]) (countLit q [-46]) (count1379 q) 1 (meaningNeg46 q) (meaning1379 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1379 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1380 = true := by
  have hs : count1379 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1380)) (countLit q [-45]) (countLit q [-46]) (count1379 q) 1 1 (meaningNeg45 q) (meaningNeg46 q) (meaning1380 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 46 = true ∨ valuation q 1380 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (1379)) (literal (valuationOf q) (1381)) (countLit q [-43]) (countLit q [-45, -46]) (count1381 q) 1 (meaning1379 q) (meaning1381 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1381 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (1380)) (literal (valuationOf q) (1382)) (countLit q [-43]) (countLit q [-45, -46]) (count1381 q) 2 (meaning1380 q) (meaning1382 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1382 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1381)) (countLit q [-43]) (countLit q [-45, -46]) (count1381 q) 1 (meaningNeg43 q) (meaning1381 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1381 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1379 = false ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1382)) (countLit q [-43]) (countLit q [-45, -46]) (count1381 q) 1 1 (meaningNeg43 q) (meaning1379 q) (meaning1382 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1379 = false ∨ valuation q 1382 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1380 = false ∨ valuationOf q 1383 = true := by
  have hs : count1381 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1383)) (countLit q [-43]) (countLit q [-45, -46]) (count1381 q) 1 2 (meaningNeg43 q) (meaning1380 q) (meaning1383 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1380 = false ∨ valuation q 1383 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1384)) (countLit q [-49]) (countLit q [-51]) (count1384 q) 1 (meaningNeg51 q) (meaning1384 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1384 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1384)) (countLit q [-49]) (countLit q [-51]) (count1384 q) 1 (meaningNeg49 q) (meaning1384 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1384 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1385 = true := by
  have hs : count1384 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1385)) (countLit q [-49]) (countLit q [-51]) (count1384 q) 1 1 (meaningNeg49 q) (meaningNeg51 q) (meaning1385 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 51 = true ∨ valuation q 1385 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-53]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1386)) (countLit q [-53]) (countLit q [-57]) (count1386 q) 1 (meaningNeg57 q) (meaning1386 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1386 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-53]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1386)) (countLit q [-53]) (countLit q [-57]) (count1386 q) 1 (meaningNeg53 q) (meaning1386 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1386 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-53]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1387)) (countLit q [-53]) (countLit q [-57]) (count1386 q) 1 1 (meaningNeg53 q) (meaningNeg57 q) (meaning1387 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 57 = true ∨ valuation q 1387 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 1 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_left (literal (valuationOf q) (1384)) (literal (valuationOf q) (1388)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 1 (meaning1384 q) (meaning1388 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1388 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_left (literal (valuationOf q) (1385)) (literal (valuationOf q) (1389)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 2 (meaning1385 q) (meaning1389 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1389 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1390 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1390)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 2 1 (meaning1385 q) (meaning1386 q) (meaning1390 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1386 = false ∨ valuation q 1390 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1391 = true := by
  have hs : count1388 q = (countLit q [-49, -51]) + (countLit q [-53, -57]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-53, -57])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1391)) (countLit q [-49, -51]) (countLit q [-53, -57]) (count1388 q) 2 2 (meaning1385 q) (meaning1387 q) (meaning1391 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1387 = false ∨ valuation q 1391 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_right (literal (valuationOf q) (1388)) (literal (valuationOf q) (1392)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 1 (meaning1388 q) (meaning1392 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1392 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_left (literal (valuationOf q) (1381)) (literal (valuationOf q) (1392)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 1 (meaning1381 q) (meaning1392 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1392 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1393)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 1 1 (meaning1381 q) (meaning1388 q) (meaning1393 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1388 = false ∨ valuation q 1393 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1395 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1390)) (literal (valuationOf q) (1395)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 1 3 (meaning1381 q) (meaning1390 q) (meaning1395 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1390 = false ∨ valuation q 1395 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1391 = false ∨ valuationOf q 1396 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1391)) (literal (valuationOf q) (1396)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 1 4 (meaning1381 q) (meaning1391 q) (meaning1396 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1391 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1391 = false ∨ valuation q 1396 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_left (literal (valuationOf q) (1382)) (literal (valuationOf q) (1393)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 2 (meaning1382 q) (meaning1393 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1393 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E201.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112201
