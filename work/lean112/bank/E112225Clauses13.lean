import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-66, -68, -70]) + (countLit q [-73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-66, -68, -70]) (l₂ := [-73, -74, -76])
  have hm := merge_left (literal (valuationOf q) (1357)) (literal (valuationOf q) (1365)) (countLit q [-66, -68, -70]) (countLit q [-73, -74, -76]) (count1365 q) 1 (meaning1357 q) (meaning1365 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1365 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1371 = true := by
  have hs : count1371 q = (countLit q [-52, -55, -58, -59, -61, -64]) + (countLit q [-66, -68, -70, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64]) (l₂ := [-66, -68, -70, -73, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1365)) (literal (valuationOf q) (1371)) (countLit q [-52, -55, -58, -59, -61, -64]) (countLit q [-66, -68, -70, -73, -74, -76]) (count1371 q) 1 (meaning1365 q) (meaning1371 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1371 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1372 = true := by
  have hs : count1371 q = (countLit q [-52, -55, -58, -59, -61, -64]) + (countLit q [-66, -68, -70, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64]) (l₂ := [-66, -68, -70, -73, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1366)) (literal (valuationOf q) (1372)) (countLit q [-52, -55, -58, -59, -61, -64]) (countLit q [-66, -68, -70, -73, -74, -76]) (count1371 q) 2 (meaning1366 q) (meaning1372 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1372 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1371 = true := by
  have hs : count1371 q = (countLit q [-52, -55, -58, -59, -61, -64]) + (countLit q [-66, -68, -70, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64]) (l₂ := [-66, -68, -70, -73, -74, -76])
  have hm := merge_left (literal (valuationOf q) (1349)) (literal (valuationOf q) (1371)) (countLit q [-52, -55, -58, -59, -61, -64]) (countLit q [-66, -68, -70, -73, -74, -76]) (count1371 q) 1 (meaning1349 q) (meaning1371 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1371 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1372 = true := by
  have hs : count1371 q = (countLit q [-52, -55, -58, -59, -61, -64]) + (countLit q [-66, -68, -70, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64]) (l₂ := [-66, -68, -70, -73, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1372)) (countLit q [-52, -55, -58, -59, -61, -64]) (countLit q [-66, -68, -70, -73, -74, -76]) (count1371 q) 1 1 (meaning1349 q) (meaning1365 q) (meaning1372 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1365 = false ∨ valuation q 1372 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1373 = true := by
  have hs : count1371 q = (countLit q [-52, -55, -58, -59, -61, -64]) + (countLit q [-66, -68, -70, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64]) (l₂ := [-66, -68, -70, -73, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1366)) (literal (valuationOf q) (1373)) (countLit q [-52, -55, -58, -59, -61, -64]) (countLit q [-66, -68, -70, -73, -74, -76]) (count1371 q) 1 2 (meaning1349 q) (meaning1366 q) (meaning1373 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1366 = false ∨ valuation q 1373 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1372 = true := by
  have hs : count1371 q = (countLit q [-52, -55, -58, -59, -61, -64]) + (countLit q [-66, -68, -70, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64]) (l₂ := [-66, -68, -70, -73, -74, -76])
  have hm := merge_left (literal (valuationOf q) (1350)) (literal (valuationOf q) (1372)) (countLit q [-52, -55, -58, -59, -61, -64]) (countLit q [-66, -68, -70, -73, -74, -76]) (count1371 q) 2 (meaning1350 q) (meaning1372 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1372 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1373 = true := by
  have hs : count1371 q = (countLit q [-52, -55, -58, -59, -61, -64]) + (countLit q [-66, -68, -70, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64]) (l₂ := [-66, -68, -70, -73, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1350)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1373)) (countLit q [-52, -55, -58, -59, -61, -64]) (countLit q [-66, -68, -70, -73, -74, -76]) (count1371 q) 2 1 (meaning1350 q) (meaning1365 q) (meaning1373 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1365 = false ∨ valuation q 1373 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1374 = true := by
  have hs : count1371 q = (countLit q [-52, -55, -58, -59, -61, -64]) + (countLit q [-66, -68, -70, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58, -59, -61, -64]) (l₂ := [-66, -68, -70, -73, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1350)) (literal (valuationOf q) (1366)) (literal (valuationOf q) (1374)) (countLit q [-52, -55, -58, -59, -61, -64]) (countLit q [-66, -68, -70, -73, -74, -76]) (count1371 q) 2 2 (meaning1350 q) (meaning1366 q) (meaning1374 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1366 = false ∨ valuation q 1374 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1381)) (countLit q [-81]) (countLit q [-83]) (count1381 q) 1 (meaningNeg83 q) (meaning1381 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1381 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1381)) (countLit q [-81]) (countLit q [-83]) (count1381 q) 1 (meaningNeg81 q) (meaning1381 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1381 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 83 = true ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-83)) (literal (valuationOf q) (1382)) (countLit q [-81]) (countLit q [-83]) (count1381 q) 1 1 (meaningNeg81 q) (meaningNeg83 q) (meaning1382 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 83)) = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 1382 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-77]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-81, -83])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1383)) (countLit q [-77]) (countLit q [-81, -83]) (count1383 q) 1 (meaning1381 q) (meaning1383 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1383 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-77]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-81, -83])
  have hm := merge_right (literal (valuationOf q) (1382)) (literal (valuationOf q) (1384)) (countLit q [-77]) (countLit q [-81, -83]) (count1383 q) 2 (meaning1382 q) (meaning1384 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1384 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-77]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-81, -83])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1383)) (countLit q [-77]) (countLit q [-81, -83]) (count1383 q) 1 (meaningNeg77 q) (meaning1383 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1383 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-77]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-81, -83])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1384)) (countLit q [-77]) (countLit q [-81, -83]) (count1383 q) 1 1 (meaningNeg77 q) (meaning1381 q) (meaning1384 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1381 = false ∨ valuation q 1384 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1382 = false ∨ valuationOf q 1385 = true := by
  have hs : count1383 q = (countLit q [-77]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-81, -83])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1385)) (countLit q [-77]) (countLit q [-81, -83]) (count1383 q) 1 2 (meaningNeg77 q) (meaning1382 q) (meaning1385 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1382 = false ∨ valuation q 1385 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1386)) (countLit q [-87]) (countLit q [-88]) (count1386 q) 1 (meaningNeg88 q) (meaning1386 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1386 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1386)) (countLit q [-87]) (countLit q [-88]) (count1386 q) 1 (meaningNeg87 q) (meaning1386 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1386 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1387)) (countLit q [-87]) (countLit q [-88]) (count1386 q) 1 1 (meaningNeg87 q) (meaningNeg88 q) (meaning1387 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 1387 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-85]) (countLit q [-87, -88]) (count1388 q) 1 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (1387)) (literal (valuationOf q) (1389)) (countLit q [-85]) (countLit q [-87, -88]) (count1388 q) 2 (meaning1387 q) (meaning1389 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1389 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1388)) (countLit q [-85]) (countLit q [-87, -88]) (count1388 q) 1 (meaningNeg85 q) (meaning1388 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1388 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1389)) (countLit q [-85]) (countLit q [-87, -88]) (count1388 q) 1 1 (meaningNeg85 q) (meaning1386 q) (meaning1389 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1386 = false ∨ valuation q 1389 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1387 = false ∨ valuationOf q 1390 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1390)) (countLit q [-85]) (countLit q [-87, -88]) (count1388 q) 1 2 (meaningNeg85 q) (meaning1387 q) (meaning1390 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1387 = false ∨ valuation q 1390 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1391 = true := by
  have hs : count1391 q = (countLit q [-77, -81, -83]) + (countLit q [-85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83]) (l₂ := [-85, -87, -88])
  have hm := merge_right (literal (valuationOf q) (1388)) (literal (valuationOf q) (1391)) (countLit q [-77, -81, -83]) (countLit q [-85, -87, -88]) (count1391 q) 1 (meaning1388 q) (meaning1391 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1391 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-77, -81, -83]) + (countLit q [-85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83]) (l₂ := [-85, -87, -88])
  have hm := merge_right (literal (valuationOf q) (1389)) (literal (valuationOf q) (1392)) (countLit q [-77, -81, -83]) (countLit q [-85, -87, -88]) (count1391 q) 2 (meaning1389 q) (meaning1392 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1392 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-77, -81, -83]) + (countLit q [-85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83]) (l₂ := [-85, -87, -88])
  have hm := merge_right (literal (valuationOf q) (1390)) (literal (valuationOf q) (1393)) (countLit q [-77, -81, -83]) (countLit q [-85, -87, -88]) (count1391 q) 3 (meaning1390 q) (meaning1393 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1393 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1391 = true := by
  have hs : count1391 q = (countLit q [-77, -81, -83]) + (countLit q [-85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83]) (l₂ := [-85, -87, -88])
  have hm := merge_left (literal (valuationOf q) (1383)) (literal (valuationOf q) (1391)) (countLit q [-77, -81, -83]) (countLit q [-85, -87, -88]) (count1391 q) 1 (meaning1383 q) (meaning1391 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1391 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-77, -81, -83]) + (countLit q [-85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83]) (l₂ := [-85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1392)) (countLit q [-77, -81, -83]) (countLit q [-85, -87, -88]) (count1391 q) 1 1 (meaning1383 q) (meaning1388 q) (meaning1392 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1388 = false ∨ valuation q 1392 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-77, -81, -83]) + (countLit q [-85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83]) (l₂ := [-85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1393)) (countLit q [-77, -81, -83]) (countLit q [-85, -87, -88]) (count1391 q) 1 2 (meaning1383 q) (meaning1389 q) (meaning1393 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1389 = false ∨ valuation q 1393 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-77, -81, -83]) + (countLit q [-85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83]) (l₂ := [-85, -87, -88])
  have hm := merge_left (literal (valuationOf q) (1384)) (literal (valuationOf q) (1392)) (countLit q [-77, -81, -83]) (countLit q [-85, -87, -88]) (count1391 q) 2 (meaning1384 q) (meaning1392 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1392 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E225.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112225
