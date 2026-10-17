import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1376 = true := by
  have hs : count1376 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1376)) (countLit q [-22]) (countLit q [-23]) (count1376 q) 1 (meaningNeg22 q) (meaning1376 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1376 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1377 = true := by
  have hs : count1376 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1377)) (countLit q [-22]) (countLit q [-23]) (count1376 q) 1 1 (meaningNeg22 q) (meaningNeg23 q) (meaning1377 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 23 = true ∨ valuation q 1377 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1379 = true := by
  have hs : count1378 q = (countLit q [-20, -21]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-22, -23])
  have hm := merge_right (literal (valuationOf q) (1377)) (literal (valuationOf q) (1379)) (countLit q [-20, -21]) (countLit q [-22, -23]) (count1378 q) 2 (meaning1377 q) (meaning1379 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1379 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1379 = true := by
  have hs : count1378 q = (countLit q [-20, -21]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1379)) (countLit q [-20, -21]) (countLit q [-22, -23]) (count1378 q) 1 1 (meaning1374 q) (meaning1376 q) (meaning1379 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1376 = false ∨ valuation q 1379 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1380 = true := by
  have hs : count1378 q = (countLit q [-20, -21]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1377)) (literal (valuationOf q) (1380)) (countLit q [-20, -21]) (countLit q [-22, -23]) (count1378 q) 1 2 (meaning1374 q) (meaning1377 q) (meaning1380 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1377 = false ∨ valuation q 1380 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1380 = true := by
  have hs : count1378 q = (countLit q [-20, -21]) + (countLit q [-22, -23]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-22, -23])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1380)) (countLit q [-20, -21]) (countLit q [-22, -23]) (count1378 q) 2 1 (meaning1375 q) (meaning1376 q) (meaning1380 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1376 = false ∨ valuation q 1380 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1383 = true := by
  have hs : count1382 q = (countLit q [-13, -15, -18]) + (countLit q [-20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -18]) (l₂ := [-20, -21, -22, -23])
  have hm := merge_right (literal (valuationOf q) (1379)) (literal (valuationOf q) (1383)) (countLit q [-13, -15, -18]) (countLit q [-20, -21, -22, -23]) (count1382 q) 2 (meaning1379 q) (meaning1383 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1383 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1384 = true := by
  have hs : count1382 q = (countLit q [-13, -15, -18]) + (countLit q [-20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -18]) (l₂ := [-20, -21, -22, -23])
  have hm := merge_right (literal (valuationOf q) (1380)) (literal (valuationOf q) (1384)) (countLit q [-13, -15, -18]) (countLit q [-20, -21, -22, -23]) (count1382 q) 3 (meaning1380 q) (meaning1384 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1384 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1384 = true := by
  have hs : count1382 q = (countLit q [-13, -15, -18]) + (countLit q [-20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -18]) (l₂ := [-20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1384)) (countLit q [-13, -15, -18]) (countLit q [-20, -21, -22, -23]) (count1382 q) 1 2 (meaning1371 q) (meaning1379 q) (meaning1384 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1379 = false ∨ valuation q 1384 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1385 = true := by
  have hs : count1382 q = (countLit q [-13, -15, -18]) + (countLit q [-20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -18]) (l₂ := [-20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1385)) (countLit q [-13, -15, -18]) (countLit q [-20, -21, -22, -23]) (count1382 q) 1 3 (meaning1371 q) (meaning1380 q) (meaning1385 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1380 = false ∨ valuation q 1385 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1385 = true := by
  have hs : count1382 q = (countLit q [-13, -15, -18]) + (countLit q [-20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -18]) (l₂ := [-20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1385)) (countLit q [-13, -15, -18]) (countLit q [-20, -21, -22, -23]) (count1382 q) 2 2 (meaning1372 q) (meaning1379 q) (meaning1385 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1379 = false ∨ valuation q 1385 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1386 = true := by
  have hs : count1382 q = (countLit q [-13, -15, -18]) + (countLit q [-20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -18]) (l₂ := [-20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1386)) (countLit q [-13, -15, -18]) (countLit q [-20, -21, -22, -23]) (count1382 q) 2 3 (meaning1372 q) (meaning1380 q) (meaning1386 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1380 = false ∨ valuation q 1386 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1386 = true := by
  have hs : count1382 q = (countLit q [-13, -15, -18]) + (countLit q [-20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -18]) (l₂ := [-20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1386)) (countLit q [-13, -15, -18]) (countLit q [-20, -21, -22, -23]) (count1382 q) 3 2 (meaning1373 q) (meaning1379 q) (meaning1386 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1379 = false ∨ valuation q 1386 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1387 = true := by
  have hs : count1382 q = (countLit q [-13, -15, -18]) + (countLit q [-20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -18]) (l₂ := [-20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1387)) (countLit q [-13, -15, -18]) (countLit q [-20, -21, -22, -23]) (count1382 q) 3 3 (meaning1373 q) (meaning1380 q) (meaning1387 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1380 = false ∨ valuation q 1387 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1393 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1393)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 1 4 (meaning1362 q) (meaning1385 q) (meaning1393 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1385 = false ∨ valuation q 1393 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1394 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1394)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 1 5 (meaning1362 q) (meaning1386 q) (meaning1394 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1386 = false ∨ valuation q 1394 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1395 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1395)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 1 6 (meaning1362 q) (meaning1387 q) (meaning1395 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1387 = false ∨ valuation q 1395 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1393 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1393)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 2 3 (meaning1363 q) (meaning1384 q) (meaning1393 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1384 = false ∨ valuation q 1393 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1394 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1394)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 2 4 (meaning1363 q) (meaning1385 q) (meaning1394 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1385 = false ∨ valuation q 1394 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1395 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1395)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 2 5 (meaning1363 q) (meaning1386 q) (meaning1395 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1386 = false ∨ valuation q 1395 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1396 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1396)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 2 6 (meaning1363 q) (meaning1387 q) (meaning1396 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1387 = false ∨ valuation q 1396 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1393 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1393)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 3 2 (meaning1364 q) (meaning1383 q) (meaning1393 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1383 = false ∨ valuation q 1393 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1394 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1394)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 3 3 (meaning1364 q) (meaning1384 q) (meaning1394 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1384 = false ∨ valuation q 1394 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1395 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1395)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 3 4 (meaning1364 q) (meaning1385 q) (meaning1395 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1385 = false ∨ valuation q 1395 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1396 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1396)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 3 5 (meaning1364 q) (meaning1386 q) (meaning1396 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1386 = false ∨ valuation q 1396 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1397 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1397)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 3 6 (meaning1364 q) (meaning1387 q) (meaning1397 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1387 = false ∨ valuation q 1397 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1394 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1394)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 4 2 (meaning1365 q) (meaning1383 q) (meaning1394 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1383 = false ∨ valuation q 1394 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1395 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1395)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 4 3 (meaning1365 q) (meaning1384 q) (meaning1395 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1384 = false ∨ valuation q 1395 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1396 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1396)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 4 4 (meaning1365 q) (meaning1385 q) (meaning1396 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1385 = false ∨ valuation q 1396 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1395 = true := by
  have hs : count1389 q = (countLit q [-2, -3, -5, -6, -9, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -22, -23]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -22, -23])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1395)) (countLit q [-2, -3, -5, -6, -9, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -22, -23]) (count1389 q) 5 2 (meaning1366 q) (meaning1383 q) (meaning1395 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1383 = false ∨ valuation q 1395 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-30]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1403)) (countLit q [-30]) (countLit q [-31]) (count1403 q) 1 (meaningNeg31 q) (meaning1403 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1403 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-30]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1403)) (countLit q [-30]) (countLit q [-31]) (count1403 q) 1 (meaningNeg30 q) (meaning1403 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1403 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E146.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112146
