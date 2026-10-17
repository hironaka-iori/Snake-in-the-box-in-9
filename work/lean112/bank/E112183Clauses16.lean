import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1339 = true := by
  have hs : count1338 q = (countLit q [-10]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1339)) (countLit q [-10]) (countLit q [-13]) (count1338 q) 1 1 (meaningNeg10 q) (meaningNeg13 q) (meaning1339 q) hs
  change (! (valuationOf q 10)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 13 = true ∨ valuation q 1339 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -13])
  have hm := merge_right (literal (valuationOf q) (1338)) (literal (valuationOf q) (1340)) (countLit q [-8]) (countLit q [-10, -13]) (count1340 q) 1 (meaning1338 q) (meaning1340 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1340 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -13])
  have hm := merge_right (literal (valuationOf q) (1339)) (literal (valuationOf q) (1341)) (countLit q [-8]) (countLit q [-10, -13]) (count1340 q) 2 (meaning1339 q) (meaning1341 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1341 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -13])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1340)) (countLit q [-8]) (countLit q [-10, -13]) (count1340 q) 1 (meaningNeg8 q) (meaning1340 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1340 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1338 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-8]) + (countLit q [-10, -13]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -13])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1341)) (countLit q [-8]) (countLit q [-10, -13]) (count1340 q) 1 1 (meaningNeg8 q) (meaning1338 q) (meaning1341 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1338 = false ∨ valuation q 1341 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_right (literal (valuationOf q) (1340)) (literal (valuationOf q) (1343)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1343 q) 1 (meaning1340 q) (meaning1343 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1343 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_right (literal (valuationOf q) (1341)) (literal (valuationOf q) (1344)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1343 q) 2 (meaning1341 q) (meaning1344 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1344 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1343 = true := by
  have hs : count1343 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_left (literal (valuationOf q) (1335)) (literal (valuationOf q) (1343)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1343 q) 1 (meaning1335 q) (meaning1343 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1343 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1344)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1343 q) 1 1 (meaning1335 q) (meaning1340 q) (meaning1344 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1340 = false ∨ valuation q 1344 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1345 = true := by
  have hs : count1343 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1345)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1343 q) 1 2 (meaning1335 q) (meaning1341 q) (meaning1345 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1341 = false ∨ valuation q 1345 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1344 = true := by
  have hs : count1343 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_left (literal (valuationOf q) (1336)) (literal (valuationOf q) (1344)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1343 q) 2 (meaning1336 q) (meaning1344 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1344 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1345 = true := by
  have hs : count1343 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1345)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1343 q) 2 1 (meaning1336 q) (meaning1340 q) (meaning1345 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1340 = false ∨ valuation q 1345 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1346 = true := by
  have hs : count1343 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1346)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1343 q) 2 2 (meaning1336 q) (meaning1341 q) (meaning1346 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1341 = false ∨ valuation q 1346 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1345 = true := by
  have hs : count1343 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -10, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -10, -13])
  have hm := merge_left (literal (valuationOf q) (1337)) (literal (valuationOf q) (1345)) (countLit q [-2, -3, -7]) (countLit q [-8, -10, -13]) (count1343 q) 3 (meaning1337 q) (meaning1345 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1345 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1349)) (countLit q [-16]) (countLit q [-19]) (count1349 q) 1 (meaningNeg19 q) (meaning1349 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1349 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1349)) (countLit q [-16]) (countLit q [-19]) (count1349 q) 1 (meaningNeg16 q) (meaning1349 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1349 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1350)) (countLit q [-16]) (countLit q [-19]) (count1349 q) 1 1 (meaningNeg16 q) (meaningNeg19 q) (meaning1350 q) hs
  change (! (valuationOf q 16)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 19 = true ∨ valuation q 1350 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_right (literal (valuationOf q) (1349)) (literal (valuationOf q) (1351)) (countLit q [-14]) (countLit q [-16, -19]) (count1351 q) 1 (meaning1349 q) (meaning1351 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1351 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1352)) (countLit q [-14]) (countLit q [-16, -19]) (count1351 q) 2 (meaning1350 q) (meaning1352 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1352 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1351)) (countLit q [-14]) (countLit q [-16, -19]) (count1351 q) 1 (meaningNeg14 q) (meaning1351 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1351 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1349 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-14]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16, -19])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1352)) (countLit q [-14]) (countLit q [-16, -19]) (count1351 q) 1 1 (meaningNeg14 q) (meaning1349 q) (meaning1352 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1349 = false ∨ valuation q 1352 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1354)) (countLit q [-21]) (countLit q [-23]) (count1354 q) 1 (meaningNeg23 q) (meaning1354 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1354 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1354)) (countLit q [-21]) (countLit q [-23]) (count1354 q) 1 (meaningNeg21 q) (meaning1354 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1354 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1355 = true := by
  have hs : count1354 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1355)) (countLit q [-21]) (countLit q [-23]) (count1354 q) 1 1 (meaningNeg21 q) (meaningNeg23 q) (meaning1355 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 1355 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1356)) (countLit q [-24]) (countLit q [-26]) (count1356 q) 1 (meaningNeg26 q) (meaning1356 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1356 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1356)) (countLit q [-24]) (countLit q [-26]) (count1356 q) 1 (meaningNeg24 q) (meaning1356 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1356 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1357 = true := by
  have hs : count1356 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1357)) (countLit q [-24]) (countLit q [-26]) (count1356 q) 1 1 (meaningNeg24 q) (meaningNeg26 q) (meaning1357 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 1357 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1358 = true := by
  have hs : count1358 q = (countLit q [-21, -23]) + (countLit q [-24, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-24, -26])
  have hm := merge_right (literal (valuationOf q) (1356)) (literal (valuationOf q) (1358)) (countLit q [-21, -23]) (countLit q [-24, -26]) (count1358 q) 1 (meaning1356 q) (meaning1358 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1358 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-21, -23]) + (countLit q [-24, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-24, -26])
  have hm := merge_right (literal (valuationOf q) (1357)) (literal (valuationOf q) (1359)) (countLit q [-21, -23]) (countLit q [-24, -26]) (count1358 q) 2 (meaning1357 q) (meaning1359 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1359 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1358 = true := by
  have hs : count1358 q = (countLit q [-21, -23]) + (countLit q [-24, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-24, -26])
  have hm := merge_left (literal (valuationOf q) (1354)) (literal (valuationOf q) (1358)) (countLit q [-21, -23]) (countLit q [-24, -26]) (count1358 q) 1 (meaning1354 q) (meaning1358 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1358 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-21, -23]) + (countLit q [-24, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-24, -26])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1359)) (countLit q [-21, -23]) (countLit q [-24, -26]) (count1358 q) 1 1 (meaning1354 q) (meaning1356 q) (meaning1359 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1356 = false ∨ valuation q 1359 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1360 = true := by
  have hs : count1358 q = (countLit q [-21, -23]) + (countLit q [-24, -26]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-24, -26])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1360)) (countLit q [-21, -23]) (countLit q [-24, -26]) (count1358 q) 1 2 (meaning1354 q) (meaning1357 q) (meaning1360 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1357 = false ∨ valuation q 1360 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E183.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112183
