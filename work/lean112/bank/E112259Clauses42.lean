import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1407)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 1 1 (meaning1395 q) (meaning1402 q) (meaning1407 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1402 = false ∨ valuation q 1407 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1408)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 1 2 (meaning1395 q) (meaning1403 q) (meaning1408 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1403 = false ∨ valuation q 1408 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1409 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1409)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 1 3 (meaning1395 q) (meaning1404 q) (meaning1409 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1404 = false ∨ valuation q 1409 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1396)) (literal (valuationOf q) (1407)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 2 (meaning1396 q) (meaning1407 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1407 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1408)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 2 1 (meaning1396 q) (meaning1402 q) (meaning1408 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1402 = false ∨ valuation q 1408 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1409 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1409)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 2 2 (meaning1396 q) (meaning1403 q) (meaning1409 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1403 = false ∨ valuation q 1409 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1397)) (literal (valuationOf q) (1408)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 3 (meaning1397 q) (meaning1408 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1408 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1409 = true := by
  have hs : count1406 q = (countLit q [-3, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1397)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1409)) (countLit q [-3, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1406 q) 3 1 (meaning1397 q) (meaning1402 q) (meaning1409 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1402 = false ∨ valuation q 1409 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1413 = true := by
  have hs : count1413 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1413)) (countLit q [-18]) (countLit q [-20]) (count1413 q) 1 (meaningNeg20 q) (meaning1413 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1413 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1413 = true := by
  have hs : count1413 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1413)) (countLit q [-18]) (countLit q [-20]) (count1413 q) 1 (meaningNeg18 q) (meaning1413 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1413 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1415 = true := by
  have hs : count1415 q = (countLit q [-16]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18, -20])
  have hm := merge_right (literal (valuationOf q) (1413)) (literal (valuationOf q) (1415)) (countLit q [-16]) (countLit q [-18, -20]) (count1415 q) 1 (meaning1413 q) (meaning1415 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1415 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1415 = true := by
  have hs : count1415 q = (countLit q [-16]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18, -20])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1415)) (countLit q [-16]) (countLit q [-18, -20]) (count1415 q) 1 (meaningNeg16 q) (meaning1415 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1415 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1413 = false ∨ valuationOf q 1416 = true := by
  have hs : count1415 q = (countLit q [-16]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18, -20])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1416)) (countLit q [-16]) (countLit q [-18, -20]) (count1415 q) 1 1 (meaningNeg16 q) (meaning1413 q) (meaning1416 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1413 = false ∨ valuation q 1416 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1418)) (countLit q [-22]) (countLit q [-24]) (count1418 q) 1 (meaningNeg24 q) (meaning1418 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1418 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1418)) (countLit q [-22]) (countLit q [-24]) (count1418 q) 1 (meaningNeg22 q) (meaning1418 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1418 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1419)) (countLit q [-22]) (countLit q [-24]) (count1418 q) 1 1 (meaningNeg22 q) (meaningNeg24 q) (meaning1419 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 24 = true ∨ valuation q 1419 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1420 = true := by
  have hs : count1420 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (1420)) (countLit q [-26]) (countLit q [-28]) (count1420 q) 1 (meaningNeg28 q) (meaning1420 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1420 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1420 = true := by
  have hs : count1420 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1420)) (countLit q [-26]) (countLit q [-28]) (count1420 q) 1 (meaningNeg26 q) (meaning1420 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1420 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 28 = true ∨ valuationOf q 1421 = true := by
  have hs : count1420 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (-28)) (literal (valuationOf q) (1421)) (countLit q [-26]) (countLit q [-28]) (count1420 q) 1 1 (meaningNeg26 q) (meaningNeg28 q) (meaning1421 q) hs
  change (! (valuationOf q 26)) = false ∨ (! (valuationOf q 28)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 28 = true ∨ valuation q 1421 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-22, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-26, -28])
  have hm := merge_right (literal (valuationOf q) (1420)) (literal (valuationOf q) (1422)) (countLit q [-22, -24]) (countLit q [-26, -28]) (count1422 q) 1 (meaning1420 q) (meaning1422 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1422 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-22, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (1418)) (literal (valuationOf q) (1422)) (countLit q [-22, -24]) (countLit q [-26, -28]) (count1422 q) 1 (meaning1418 q) (meaning1422 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1422 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-22, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1423)) (countLit q [-22, -24]) (countLit q [-26, -28]) (count1422 q) 1 1 (meaning1418 q) (meaning1420 q) (meaning1423 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1420 = false ∨ valuation q 1423 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-22, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1424)) (countLit q [-22, -24]) (countLit q [-26, -28]) (count1422 q) 1 2 (meaning1418 q) (meaning1421 q) (meaning1424 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1421 = false ∨ valuation q 1424 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-22, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (1419)) (literal (valuationOf q) (1423)) (countLit q [-22, -24]) (countLit q [-26, -28]) (count1422 q) 2 (meaning1419 q) (meaning1423 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1423 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-22, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1424)) (countLit q [-22, -24]) (countLit q [-26, -28]) (count1422 q) 2 1 (meaning1419 q) (meaning1420 q) (meaning1424 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1420 = false ∨ valuation q 1424 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-16, -18, -20]) + (countLit q [-22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20]) (l₂ := [-22, -24, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1426)) (countLit q [-16, -18, -20]) (countLit q [-22, -24, -26, -28]) (count1426 q) 1 (meaning1422 q) (meaning1426 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1426 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-16, -18, -20]) + (countLit q [-22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20]) (l₂ := [-22, -24, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1423)) (literal (valuationOf q) (1427)) (countLit q [-16, -18, -20]) (countLit q [-22, -24, -26, -28]) (count1426 q) 2 (meaning1423 q) (meaning1427 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1427 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1428 = true := by
  have hs : count1426 q = (countLit q [-16, -18, -20]) + (countLit q [-22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20]) (l₂ := [-22, -24, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1424)) (literal (valuationOf q) (1428)) (countLit q [-16, -18, -20]) (countLit q [-22, -24, -26, -28]) (count1426 q) 3 (meaning1424 q) (meaning1428 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1428 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-16, -18, -20]) + (countLit q [-22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20]) (l₂ := [-22, -24, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1426)) (countLit q [-16, -18, -20]) (countLit q [-22, -24, -26, -28]) (count1426 q) 1 (meaning1415 q) (meaning1426 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1426 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-16, -18, -20]) + (countLit q [-22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20]) (l₂ := [-22, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1427)) (countLit q [-16, -18, -20]) (countLit q [-22, -24, -26, -28]) (count1426 q) 1 1 (meaning1415 q) (meaning1422 q) (meaning1427 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1422 = false ∨ valuation q 1427 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true := by
  have hs : count1426 q = (countLit q [-16, -18, -20]) + (countLit q [-22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20]) (l₂ := [-22, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1428)) (countLit q [-16, -18, -20]) (countLit q [-22, -24, -26, -28]) (count1426 q) 1 2 (meaning1415 q) (meaning1423 q) (meaning1428 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1423 = false ∨ valuation q 1428 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1429 = true := by
  have hs : count1426 q = (countLit q [-16, -18, -20]) + (countLit q [-22, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20]) (l₂ := [-22, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1424)) (literal (valuationOf q) (1429)) (countLit q [-16, -18, -20]) (countLit q [-22, -24, -26, -28]) (count1426 q) 1 3 (meaning1415 q) (meaning1424 q) (meaning1429 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1424 = false ∨ valuation q 1429 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E259.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112259
