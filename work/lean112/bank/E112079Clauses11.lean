import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-7]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10, -11])
  have hm := merge_right (literal (valuationOf q) (1339)) (literal (valuationOf q) (1341)) (countLit q [-7]) (countLit q [-10, -11]) (count1340 q) 2 (meaning1339 q) (meaning1341 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1341 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-7]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10, -11])
  have hm := merge_left (literal (valuationOf q) (-7)) (literal (valuationOf q) (1340)) (countLit q [-7]) (countLit q [-10, -11]) (count1340 q) 1 (meaningNeg7 q) (meaning1340 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1340 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1338 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-7]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1341)) (countLit q [-7]) (countLit q [-10, -11]) (count1340 q) 1 1 (meaningNeg7 q) (meaning1338 q) (meaning1341 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1338 = false ∨ valuation q 1341 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -11])
  have hm := merge_right (literal (valuationOf q) (1340)) (literal (valuationOf q) (1343)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -11]) (count1343 q) 1 (meaning1340 q) (meaning1343 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1343 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -11])
  have hm := merge_right (literal (valuationOf q) (1341)) (literal (valuationOf q) (1344)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -11]) (count1343 q) 2 (meaning1341 q) (meaning1344 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1344 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -11])
  have hm := merge_left (literal (valuationOf q) (1335)) (literal (valuationOf q) (1343)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -11]) (count1343 q) 1 (meaning1335 q) (meaning1343 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1343 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-2, -4, -5]) + (countLit q [-7, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-7, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1344)) (countLit q [-2, -4, -5]) (countLit q [-7, -10, -11]) (count1343 q) 1 1 (meaning1335 q) (meaning1340 q) (meaning1344 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1340 = false ∨ valuation q 1344 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-16]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1349)) (countLit q [-16]) (countLit q [-17]) (count1349 q) 1 (meaningNeg17 q) (meaning1349 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1349 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-16]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1349)) (countLit q [-16]) (countLit q [-17]) (count1349 q) 1 (meaningNeg16 q) (meaning1349 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1349 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-16]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1350)) (countLit q [-16]) (countLit q [-17]) (count1349 q) 1 1 (meaningNeg16 q) (meaningNeg17 q) (meaning1350 q) hs
  change (! (valuationOf q 16)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 17 = true ∨ valuation q 1350 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-12]) + (countLit q [-16, -17]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-16, -17])
  have hm := merge_right (literal (valuationOf q) (1349)) (literal (valuationOf q) (1351)) (countLit q [-12]) (countLit q [-16, -17]) (count1351 q) 1 (meaning1349 q) (meaning1351 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1351 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-12]) + (countLit q [-16, -17]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-16, -17])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1352)) (countLit q [-12]) (countLit q [-16, -17]) (count1351 q) 2 (meaning1350 q) (meaning1352 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1352 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1354)) (countLit q [-21]) (countLit q [-22]) (count1354 q) 1 (meaningNeg22 q) (meaning1354 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1354 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1354)) (countLit q [-21]) (countLit q [-22]) (count1354 q) 1 (meaningNeg21 q) (meaning1354 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1354 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1355 = true := by
  have hs : count1354 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1355)) (countLit q [-21]) (countLit q [-22]) (count1354 q) 1 1 (meaningNeg21 q) (meaningNeg22 q) (meaning1355 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 22 = true ∨ valuation q 1355 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-24]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (1356)) (countLit q [-24]) (countLit q [-27]) (count1356 q) 1 (meaningNeg27 q) (meaning1356 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1356 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-24]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1356)) (countLit q [-24]) (countLit q [-27]) (count1356 q) 1 (meaningNeg24 q) (meaning1356 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1356 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 27 = true ∨ valuationOf q 1357 = true := by
  have hs : count1356 q = (countLit q [-24]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-27])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-27)) (literal (valuationOf q) (1357)) (countLit q [-24]) (countLit q [-27]) (count1356 q) 1 1 (meaningNeg24 q) (meaningNeg27 q) (meaning1357 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 27)) = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 27 = true ∨ valuation q 1357 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1358 = true := by
  have hs : count1358 q = (countLit q [-21, -22]) + (countLit q [-24, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -27])
  have hm := merge_right (literal (valuationOf q) (1356)) (literal (valuationOf q) (1358)) (countLit q [-21, -22]) (countLit q [-24, -27]) (count1358 q) 1 (meaning1356 q) (meaning1358 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1358 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-21, -22]) + (countLit q [-24, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -27])
  have hm := merge_right (literal (valuationOf q) (1357)) (literal (valuationOf q) (1359)) (countLit q [-21, -22]) (countLit q [-24, -27]) (count1358 q) 2 (meaning1357 q) (meaning1359 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1359 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1358 = true := by
  have hs : count1358 q = (countLit q [-21, -22]) + (countLit q [-24, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -27])
  have hm := merge_left (literal (valuationOf q) (1354)) (literal (valuationOf q) (1358)) (countLit q [-21, -22]) (countLit q [-24, -27]) (count1358 q) 1 (meaning1354 q) (meaning1358 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1358 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-21, -22]) + (countLit q [-24, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -27])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1359)) (countLit q [-21, -22]) (countLit q [-24, -27]) (count1358 q) 1 1 (meaning1354 q) (meaning1356 q) (meaning1359 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1356 = false ∨ valuation q 1359 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1360 = true := by
  have hs : count1358 q = (countLit q [-21, -22]) + (countLit q [-24, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -27])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1360)) (countLit q [-21, -22]) (countLit q [-24, -27]) (count1358 q) 1 2 (meaning1354 q) (meaning1357 q) (meaning1360 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1357 = false ∨ valuation q 1360 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-21, -22]) + (countLit q [-24, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -27])
  have hm := merge_left (literal (valuationOf q) (1355)) (literal (valuationOf q) (1359)) (countLit q [-21, -22]) (countLit q [-24, -27]) (count1358 q) 2 (meaning1355 q) (meaning1359 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1359 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-12, -16, -17]) + (countLit q [-21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-12, -16, -17]) (l₂ := [-21, -22, -24, -27])
  have hm := merge_right (literal (valuationOf q) (1358)) (literal (valuationOf q) (1362)) (countLit q [-12, -16, -17]) (countLit q [-21, -22, -24, -27]) (count1362 q) 1 (meaning1358 q) (meaning1362 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1362 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-12, -16, -17]) + (countLit q [-21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-12, -16, -17]) (l₂ := [-21, -22, -24, -27])
  have hm := merge_right (literal (valuationOf q) (1359)) (literal (valuationOf q) (1363)) (countLit q [-12, -16, -17]) (countLit q [-21, -22, -24, -27]) (count1362 q) 2 (meaning1359 q) (meaning1363 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1363 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-12, -16, -17]) + (countLit q [-21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-12, -16, -17]) (l₂ := [-21, -22, -24, -27])
  have hm := merge_right (literal (valuationOf q) (1360)) (literal (valuationOf q) (1364)) (countLit q [-12, -16, -17]) (countLit q [-21, -22, -24, -27]) (count1362 q) 3 (meaning1360 q) (meaning1364 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1364 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-12, -16, -17]) + (countLit q [-21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-12, -16, -17]) (l₂ := [-21, -22, -24, -27])
  have hm := merge_left (literal (valuationOf q) (1351)) (literal (valuationOf q) (1362)) (countLit q [-12, -16, -17]) (countLit q [-21, -22, -24, -27]) (count1362 q) 1 (meaning1351 q) (meaning1362 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1362 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-12, -16, -17]) + (countLit q [-21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-12, -16, -17]) (l₂ := [-21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1363)) (countLit q [-12, -16, -17]) (countLit q [-21, -22, -24, -27]) (count1362 q) 1 1 (meaning1351 q) (meaning1358 q) (meaning1363 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1358 = false ∨ valuation q 1363 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-12, -16, -17]) + (countLit q [-21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-12, -16, -17]) (l₂ := [-21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1364)) (countLit q [-12, -16, -17]) (countLit q [-21, -22, -24, -27]) (count1362 q) 1 2 (meaning1351 q) (meaning1359 q) (meaning1364 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1359 = false ∨ valuation q 1364 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-12, -16, -17]) + (countLit q [-21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-12, -16, -17]) (l₂ := [-21, -22, -24, -27])
  have hm := merge_left (literal (valuationOf q) (1352)) (literal (valuationOf q) (1363)) (countLit q [-12, -16, -17]) (countLit q [-21, -22, -24, -27]) (count1362 q) 2 (meaning1352 q) (meaning1363 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1363 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-12, -16, -17]) + (countLit q [-21, -22, -24, -27]) := List.countP_append (p := literal q) (l₁ := [-12, -16, -17]) (l₂ := [-21, -22, -24, -27])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1364)) (countLit q [-12, -16, -17]) (countLit q [-21, -22, -24, -27]) (count1362 q) 2 1 (meaning1352 q) (meaning1358 q) (meaning1364 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1358 = false ∨ valuation q 1364 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E079.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112079
