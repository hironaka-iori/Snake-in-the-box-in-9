import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-15]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1331)) (countLit q [-15]) (countLit q [-19]) (count1331 q) 1 (meaningNeg19 q) (meaning1331 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1331 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1331 = true := by
  have hs : count1331 q = (countLit q [-15]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1331)) (countLit q [-15]) (countLit q [-19]) (count1331 q) 1 (meaningNeg15 q) (meaning1331 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1331 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-14]) + (countLit q [-15, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -19])
  have hm := merge_right (literal (valuationOf q) (1331)) (literal (valuationOf q) (1333)) (countLit q [-14]) (countLit q [-15, -19]) (count1333 q) 1 (meaning1331 q) (meaning1333 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1333 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1333 = true := by
  have hs : count1333 q = (countLit q [-14]) + (countLit q [-15, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -19])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1333)) (countLit q [-14]) (countLit q [-15, -19]) (count1333 q) 1 (meaningNeg14 q) (meaning1333 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1333 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1331 = false ∨ valuationOf q 1334 = true := by
  have hs : count1333 q = (countLit q [-14]) + (countLit q [-15, -19]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15, -19])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1334)) (countLit q [-14]) (countLit q [-15, -19]) (count1333 q) 1 1 (meaningNeg14 q) (meaning1331 q) (meaning1334 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1331 = false ∨ valuation q 1334 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1336 = true := by
  have hs : count1336 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1336)) (countLit q [-20]) (countLit q [-22]) (count1336 q) 1 (meaningNeg22 q) (meaning1336 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1336 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1336 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1337 = true := by
  have hs : count1336 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1337)) (countLit q [-20]) (countLit q [-22]) (count1336 q) 1 1 (meaningNeg20 q) (meaningNeg22 q) (meaning1337 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1337 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 1337 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1338)) (countLit q [-25]) (countLit q [-26]) (count1338 q) 1 (meaningNeg26 q) (meaning1338 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1338 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1338)) (countLit q [-25]) (countLit q [-26]) (count1338 q) 1 (meaningNeg25 q) (meaning1338 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1338 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_right (literal (valuationOf q) (1338)) (literal (valuationOf q) (1340)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1340 q) 1 (meaning1338 q) (meaning1340 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1340 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1336)) (literal (valuationOf q) (1340)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1340 q) 1 (meaning1336 q) (meaning1340 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1340 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1337)) (literal (valuationOf q) (1341)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1340 q) 2 (meaning1337 q) (meaning1341 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1341 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1340)) (literal (valuationOf q) (1344)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 1 (meaning1340 q) (meaning1344 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1344 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1345 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1341)) (literal (valuationOf q) (1345)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 2 (meaning1341 q) (meaning1345 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1345 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1333)) (literal (valuationOf q) (1344)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 1 (meaning1333 q) (meaning1344 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1344 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1345 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1345)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 1 1 (meaning1333 q) (meaning1340 q) (meaning1345 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1340 = false ∨ valuation q 1345 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1345 = true := by
  have hs : count1344 q = (countLit q [-14, -15, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1334)) (literal (valuationOf q) (1345)) (countLit q [-14, -15, -19]) (countLit q [-20, -22, -25, -26]) (count1344 q) 2 (meaning1334 q) (meaning1345 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1345 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1344)) (literal (valuationOf q) (1351)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 1 (meaning1344 q) (meaning1351 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1351 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1345)) (literal (valuationOf q) (1352)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 2 (meaning1345 q) (meaning1352 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1352 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1325 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1325)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1352)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 1 1 (meaning1325 q) (meaning1344 q) (meaning1352 q) hs
  change valuationOf q 1325 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1325 = false ∨ valuation q 1344 = false ∨ valuation q 1352 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1353 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1326)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1353)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 2 1 (meaning1326 q) (meaning1344 q) (meaning1353 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1344 = false ∨ valuation q 1353 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1354 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1326)) (literal (valuationOf q) (1345)) (literal (valuationOf q) (1354)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 2 2 (meaning1326 q) (meaning1345 q) (meaning1354 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1345 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1345 = false ∨ valuation q 1354 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1354 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1328)) (literal (valuationOf q) (1354)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 4 (meaning1328 q) (meaning1354 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1354 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1355 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1355)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 4 1 (meaning1328 q) (meaning1344 q) (meaning1355 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1344 = false ∨ valuation q 1355 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1357 = true := by
  have hs : count1351 q = (countLit q [-2, -3, -4, -8, -9, -10]) + (countLit q [-14, -15, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10]) (l₂ := [-14, -15, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1357)) (countLit q [-2, -3, -4, -8, -9, -10]) (countLit q [-14, -15, -19, -20, -22, -25, -26]) (count1351 q) 6 1 (meaning1330 q) (meaning1344 q) (meaning1357 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1344 = false ∨ valuation q 1357 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (1363)) (countLit q [-31]) (countLit q [-34]) (count1363 q) 1 (meaningNeg34 q) (meaning1363 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1363 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1363)) (countLit q [-31]) (countLit q [-34]) (count1363 q) 1 (meaningNeg31 q) (meaning1363 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1363 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 34 = true ∨ valuationOf q 1364 = true := by
  have hs : count1363 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-34)) (literal (valuationOf q) (1364)) (countLit q [-31]) (countLit q [-34]) (count1363 q) 1 1 (meaningNeg31 q) (meaningNeg34 q) (meaning1364 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 34)) = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 34 = true ∨ valuation q 1364 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-28]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31, -34])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1365)) (countLit q [-28]) (countLit q [-31, -34]) (count1365 q) 1 (meaning1363 q) (meaning1365 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1365 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-28]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31, -34])
  have hm := merge_right (literal (valuationOf q) (1364)) (literal (valuationOf q) (1366)) (countLit q [-28]) (countLit q [-31, -34]) (count1365 q) 2 (meaning1364 q) (meaning1366 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1366 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1368)) (countLit q [-38]) (countLit q [-40]) (count1368 q) 1 (meaningNeg40 q) (meaning1368 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1368 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1368)) (countLit q [-38]) (countLit q [-40]) (count1368 q) 1 (meaningNeg38 q) (meaning1368 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1368 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E205.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112205
