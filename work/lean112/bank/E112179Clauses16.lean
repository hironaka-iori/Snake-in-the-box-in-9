import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1355 = false ∨ valuationOf q 1358 = true := by
  have hs : count1357 q = (countLit q [-67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1358)) (countLit q [-67]) (countLit q [-69, -70]) (count1357 q) 1 1 (meaningNeg67 q) (meaning1355 q) (meaning1358 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1355 = false ∨ valuation q 1358 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1360 = true := by
  have hs : count1360 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1360)) (countLit q [-75]) (countLit q [-77]) (count1360 q) 1 (meaningNeg77 q) (meaning1360 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1360 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1360 = true := by
  have hs : count1360 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1360)) (countLit q [-75]) (countLit q [-77]) (count1360 q) 1 (meaningNeg75 q) (meaning1360 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1360 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-71]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-75, -77])
  have hm := merge_right (literal (valuationOf q) (1360)) (literal (valuationOf q) (1362)) (countLit q [-71]) (countLit q [-75, -77]) (count1362 q) 1 (meaning1360 q) (meaning1362 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1362 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-71]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-75, -77])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1362)) (countLit q [-71]) (countLit q [-75, -77]) (count1362 q) 1 (meaningNeg71 q) (meaning1362 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1362 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1360 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-71]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-75, -77])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1363)) (countLit q [-71]) (countLit q [-75, -77]) (count1362 q) 1 1 (meaningNeg71 q) (meaning1360 q) (meaning1363 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1360 = false ∨ valuation q 1363 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-67, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1362)) (literal (valuationOf q) (1365)) (countLit q [-67, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 1 (meaning1362 q) (meaning1365 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1365 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-67, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1366)) (countLit q [-67, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 2 (meaning1363 q) (meaning1366 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1366 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-67, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_left (literal (valuationOf q) (1357)) (literal (valuationOf q) (1365)) (countLit q [-67, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 1 (meaning1357 q) (meaning1365 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1365 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-67, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1366)) (countLit q [-67, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 1 1 (meaning1357 q) (meaning1362 q) (meaning1366 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1362 = false ∨ valuation q 1366 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1367 = true := by
  have hs : count1365 q = (countLit q [-67, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1367)) (countLit q [-67, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 1 2 (meaning1357 q) (meaning1363 q) (meaning1367 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1363 = false ∨ valuation q 1367 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1367 = true := by
  have hs : count1365 q = (countLit q [-67, -69, -70]) + (countLit q [-71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -70]) (l₂ := [-71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1358)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1367)) (countLit q [-67, -69, -70]) (countLit q [-71, -75, -77]) (count1365 q) 2 1 (meaning1358 q) (meaning1362 q) (meaning1367 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1362 = false ∨ valuation q 1367 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1371 = true := by
  have hs : count1371 q = (countLit q [-53, -54, -58, -60, -61, -63]) + (countLit q [-67, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63]) (l₂ := [-67, -69, -70, -71, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1365)) (literal (valuationOf q) (1371)) (countLit q [-53, -54, -58, -60, -61, -63]) (countLit q [-67, -69, -70, -71, -75, -77]) (count1371 q) 1 (meaning1365 q) (meaning1371 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1371 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1372 = true := by
  have hs : count1371 q = (countLit q [-53, -54, -58, -60, -61, -63]) + (countLit q [-67, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63]) (l₂ := [-67, -69, -70, -71, -75, -77])
  have hm := merge_right (literal (valuationOf q) (1366)) (literal (valuationOf q) (1372)) (countLit q [-53, -54, -58, -60, -61, -63]) (countLit q [-67, -69, -70, -71, -75, -77]) (count1371 q) 2 (meaning1366 q) (meaning1372 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1372 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1372 = true := by
  have hs : count1371 q = (countLit q [-53, -54, -58, -60, -61, -63]) + (countLit q [-67, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63]) (l₂ := [-67, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1372)) (countLit q [-53, -54, -58, -60, -61, -63]) (countLit q [-67, -69, -70, -71, -75, -77]) (count1371 q) 1 1 (meaning1349 q) (meaning1365 q) (meaning1372 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1365 = false ∨ valuation q 1372 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1373 = true := by
  have hs : count1371 q = (countLit q [-53, -54, -58, -60, -61, -63]) + (countLit q [-67, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63]) (l₂ := [-67, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1366)) (literal (valuationOf q) (1373)) (countLit q [-53, -54, -58, -60, -61, -63]) (countLit q [-67, -69, -70, -71, -75, -77]) (count1371 q) 1 2 (meaning1349 q) (meaning1366 q) (meaning1373 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1366 = false ∨ valuation q 1373 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1374 = true := by
  have hs : count1371 q = (countLit q [-53, -54, -58, -60, -61, -63]) + (countLit q [-67, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63]) (l₂ := [-67, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1374)) (countLit q [-53, -54, -58, -60, -61, -63]) (countLit q [-67, -69, -70, -71, -75, -77]) (count1371 q) 1 3 (meaning1349 q) (meaning1367 q) (meaning1374 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1367 = false ∨ valuation q 1374 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1373 = true := by
  have hs : count1371 q = (countLit q [-53, -54, -58, -60, -61, -63]) + (countLit q [-67, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63]) (l₂ := [-67, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1350)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1373)) (countLit q [-53, -54, -58, -60, -61, -63]) (countLit q [-67, -69, -70, -71, -75, -77]) (count1371 q) 2 1 (meaning1350 q) (meaning1365 q) (meaning1373 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1365 = false ∨ valuation q 1373 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1374 = true := by
  have hs : count1371 q = (countLit q [-53, -54, -58, -60, -61, -63]) + (countLit q [-67, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63]) (l₂ := [-67, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1350)) (literal (valuationOf q) (1366)) (literal (valuationOf q) (1374)) (countLit q [-53, -54, -58, -60, -61, -63]) (countLit q [-67, -69, -70, -71, -75, -77]) (count1371 q) 2 2 (meaning1350 q) (meaning1366 q) (meaning1374 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1366 = false ∨ valuation q 1374 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1375 = true := by
  have hs : count1371 q = (countLit q [-53, -54, -58, -60, -61, -63]) + (countLit q [-67, -69, -70, -71, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63]) (l₂ := [-67, -69, -70, -71, -75, -77])
  have hm := merge_two (literal (valuationOf q) (1350)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1375)) (countLit q [-53, -54, -58, -60, -61, -63]) (countLit q [-67, -69, -70, -71, -75, -77]) (count1371 q) 2 3 (meaning1350 q) (meaning1367 q) (meaning1375 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1367 = false ∨ valuation q 1375 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1381)) (countLit q [-80]) (countLit q [-81]) (count1381 q) 1 (meaningNeg81 q) (meaning1381 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1381 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1381)) (countLit q [-80]) (countLit q [-81]) (count1381 q) 1 (meaningNeg80 q) (meaning1381 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1381 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-79]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1383)) (countLit q [-79]) (countLit q [-80, -81]) (count1383 q) 1 (meaning1381 q) (meaning1383 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1383 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-79]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80, -81])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1383)) (countLit q [-79]) (countLit q [-80, -81]) (count1383 q) 1 (meaningNeg79 q) (meaning1383 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1383 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1386)) (countLit q [-87]) (countLit q [-90]) (count1386 q) 1 (meaningNeg90 q) (meaning1386 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1386 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1386)) (countLit q [-87]) (countLit q [-90]) (count1386 q) 1 (meaningNeg87 q) (meaning1386 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1386 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1387)) (countLit q [-87]) (countLit q [-90]) (count1386 q) 1 1 (meaningNeg87 q) (meaningNeg90 q) (meaning1387 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 90 = true ∨ valuation q 1387 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -90])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-85]) (countLit q [-87, -90]) (count1388 q) 1 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -90])
  have hm := merge_right (literal (valuationOf q) (1387)) (literal (valuationOf q) (1389)) (countLit q [-85]) (countLit q [-87, -90]) (count1388 q) 2 (meaning1387 q) (meaning1389 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1389 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -90])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1388)) (countLit q [-85]) (countLit q [-87, -90]) (count1388 q) 1 (meaningNeg85 q) (meaning1388 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1388 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-85]) + (countLit q [-87, -90]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -90])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1389)) (countLit q [-85]) (countLit q [-87, -90]) (count1388 q) 1 1 (meaningNeg85 q) (meaning1386 q) (meaning1389 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1386 = false ∨ valuation q 1389 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1391 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_left (literal (valuationOf q) (1383)) (literal (valuationOf q) (1391)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 1 (meaning1383 q) (meaning1391 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1391 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E179.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112179
