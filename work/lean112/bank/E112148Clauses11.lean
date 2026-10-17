import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1367 = true := by
  have hs : count1363 q = (countLit q [-1, -2, -6, -10, -12, -13]) + (countLit q [-15, -16, -18, -20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13]) (l₂ := [-15, -16, -18, -20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1340)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1367)) (countLit q [-1, -2, -6, -10, -12, -13]) (countLit q [-15, -16, -18, -20, -24, -26, -28]) (count1363 q) 4 1 (meaning1340 q) (meaning1356 q) (meaning1367 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1356 = false ∨ valuation q 1367 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1368 = true := by
  have hs : count1363 q = (countLit q [-1, -2, -6, -10, -12, -13]) + (countLit q [-15, -16, -18, -20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13]) (l₂ := [-15, -16, -18, -20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1340)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1368)) (countLit q [-1, -2, -6, -10, -12, -13]) (countLit q [-15, -16, -18, -20, -24, -26, -28]) (count1363 q) 4 2 (meaning1340 q) (meaning1357 q) (meaning1368 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1357 = false ∨ valuation q 1368 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1368 = true := by
  have hs : count1363 q = (countLit q [-1, -2, -6, -10, -12, -13]) + (countLit q [-15, -16, -18, -20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13]) (l₂ := [-15, -16, -18, -20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1368)) (countLit q [-1, -2, -6, -10, -12, -13]) (countLit q [-15, -16, -18, -20, -24, -26, -28]) (count1363 q) 5 1 (meaning1341 q) (meaning1356 q) (meaning1368 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1356 = false ∨ valuation q 1368 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1376 = true := by
  have hs : count1376 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1376)) (countLit q [-31]) (countLit q [-33]) (count1376 q) 1 (meaningNeg33 q) (meaning1376 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1376 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1376 = true := by
  have hs : count1376 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1376)) (countLit q [-31]) (countLit q [-33]) (count1376 q) 1 (meaningNeg31 q) (meaning1376 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1376 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1377 = true := by
  have hs : count1376 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1377)) (countLit q [-31]) (countLit q [-33]) (count1376 q) 1 1 (meaningNeg31 q) (meaningNeg33 q) (meaning1377 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 33 = true ∨ valuation q 1377 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1378 = true := by
  have hs : count1378 q = (countLit q [-30]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -33])
  have hm := merge_right (literal (valuationOf q) (1376)) (literal (valuationOf q) (1378)) (countLit q [-30]) (countLit q [-31, -33]) (count1378 q) 1 (meaning1376 q) (meaning1378 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1378 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1379 = true := by
  have hs : count1378 q = (countLit q [-30]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -33])
  have hm := merge_right (literal (valuationOf q) (1377)) (literal (valuationOf q) (1379)) (countLit q [-30]) (countLit q [-31, -33]) (count1378 q) 2 (meaning1377 q) (meaning1379 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1379 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1378 = true := by
  have hs : count1378 q = (countLit q [-30]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -33])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1378)) (countLit q [-30]) (countLit q [-31, -33]) (count1378 q) 1 (meaningNeg30 q) (meaning1378 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1378 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1376 = false ∨ valuationOf q 1379 = true := by
  have hs : count1378 q = (countLit q [-30]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1379)) (countLit q [-30]) (countLit q [-31, -33]) (count1378 q) 1 1 (meaningNeg30 q) (meaning1376 q) (meaning1379 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1376 = false ∨ valuation q 1379 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1381)) (countLit q [-36]) (countLit q [-37]) (count1381 q) 1 (meaningNeg37 q) (meaning1381 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1381 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1381)) (countLit q [-36]) (countLit q [-37]) (count1381 q) 1 (meaningNeg36 q) (meaning1381 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1381 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1383)) (countLit q [-40]) (countLit q [-42]) (count1383 q) 1 (meaningNeg42 q) (meaning1383 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1383 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1383)) (countLit q [-40]) (countLit q [-42]) (count1383 q) 1 (meaningNeg40 q) (meaning1383 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1383 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1384)) (countLit q [-40]) (countLit q [-42]) (count1383 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning1384 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 1384 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1385 = true := by
  have hs : count1385 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1383)) (literal (valuationOf q) (1385)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1385 q) 1 (meaning1383 q) (meaning1385 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1385 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1386 = true := by
  have hs : count1385 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1384)) (literal (valuationOf q) (1386)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1385 q) 2 (meaning1384 q) (meaning1386 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1386 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1385 = true := by
  have hs : count1385 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_left (literal (valuationOf q) (1381)) (literal (valuationOf q) (1385)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1385 q) 1 (meaning1381 q) (meaning1385 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1385 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1386 = true := by
  have hs : count1385 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1386)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1385 q) 1 1 (meaning1381 q) (meaning1383 q) (meaning1386 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1383 = false ∨ valuation q 1386 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1387 = true := by
  have hs : count1385 q = (countLit q [-36, -37]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -37]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1387)) (countLit q [-36, -37]) (countLit q [-40, -42]) (count1385 q) 1 2 (meaning1381 q) (meaning1384 q) (meaning1387 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1384 = false ∨ valuation q 1387 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1389 = true := by
  have hs : count1389 q = (countLit q [-30, -31, -33]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1378)) (literal (valuationOf q) (1389)) (countLit q [-30, -31, -33]) (countLit q [-36, -37, -40, -42]) (count1389 q) 1 (meaning1378 q) (meaning1389 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1389 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1390 = true := by
  have hs : count1389 q = (countLit q [-30, -31, -33]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1390)) (countLit q [-30, -31, -33]) (countLit q [-36, -37, -40, -42]) (count1389 q) 1 1 (meaning1378 q) (meaning1385 q) (meaning1390 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1385 = false ∨ valuation q 1390 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1391 = true := by
  have hs : count1389 q = (countLit q [-30, -31, -33]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1391)) (countLit q [-30, -31, -33]) (countLit q [-36, -37, -40, -42]) (count1389 q) 1 2 (meaning1378 q) (meaning1386 q) (meaning1391 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1386 = false ∨ valuation q 1391 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1392 = true := by
  have hs : count1389 q = (countLit q [-30, -31, -33]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1392)) (countLit q [-30, -31, -33]) (countLit q [-36, -37, -40, -42]) (count1389 q) 1 3 (meaning1378 q) (meaning1387 q) (meaning1392 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1387 = false ∨ valuation q 1392 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1390 = true := by
  have hs : count1389 q = (countLit q [-30, -31, -33]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1379)) (literal (valuationOf q) (1390)) (countLit q [-30, -31, -33]) (countLit q [-36, -37, -40, -42]) (count1389 q) 2 (meaning1379 q) (meaning1390 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1390 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1391 = true := by
  have hs : count1389 q = (countLit q [-30, -31, -33]) + (countLit q [-36, -37, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33]) (l₂ := [-36, -37, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1391)) (countLit q [-30, -31, -33]) (countLit q [-36, -37, -40, -42]) (count1389 q) 2 1 (meaning1379 q) (meaning1385 q) (meaning1391 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1385 = false ∨ valuation q 1391 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1396 = true := by
  have hs : count1396 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1396)) (countLit q [-45]) (countLit q [-47]) (count1396 q) 1 (meaningNeg47 q) (meaning1396 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1396 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1396 = true := by
  have hs : count1396 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1396)) (countLit q [-45]) (countLit q [-47]) (count1396 q) 1 (meaningNeg45 q) (meaning1396 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1396 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 47 = true ∨ valuationOf q 1397 = true := by
  have hs : count1396 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (1397)) (countLit q [-45]) (countLit q [-47]) (count1396 q) 1 1 (meaningNeg45 q) (meaningNeg47 q) (meaning1397 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 1397 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-43]) + (countLit q [-45, -47]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -47])
  have hm := merge_right (literal (valuationOf q) (1396)) (literal (valuationOf q) (1398)) (countLit q [-43]) (countLit q [-45, -47]) (count1398 q) 1 (meaning1396 q) (meaning1398 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1398 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1399 = true := by
  have hs : count1398 q = (countLit q [-43]) + (countLit q [-45, -47]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -47])
  have hm := merge_right (literal (valuationOf q) (1397)) (literal (valuationOf q) (1399)) (countLit q [-43]) (countLit q [-45, -47]) (count1398 q) 2 (meaning1397 q) (meaning1399 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1399 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-43]) + (countLit q [-45, -47]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -47])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1398)) (countLit q [-43]) (countLit q [-45, -47]) (count1398 q) 1 (meaningNeg43 q) (meaning1398 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1398 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E148.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112148
