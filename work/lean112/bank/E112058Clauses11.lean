import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1429 = true := by
  have hs : count1428 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1429)) (countLit q [-27]) (countLit q [-30]) (count1428 q) 1 1 (meaningNeg27 q) (meaningNeg30 q) (meaning1429 q) hs
  change (! (valuationOf q 27)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 30 = true ∨ valuation q 1429 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-23, -24]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -30])
  have hm := merge_right (literal (valuationOf q) (1428)) (literal (valuationOf q) (1430)) (countLit q [-23, -24]) (countLit q [-27, -30]) (count1430 q) 1 (meaning1428 q) (meaning1430 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1430 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-23, -24]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -30])
  have hm := merge_right (literal (valuationOf q) (1429)) (literal (valuationOf q) (1431)) (countLit q [-23, -24]) (countLit q [-27, -30]) (count1430 q) 2 (meaning1429 q) (meaning1431 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1431 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-23, -24]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -30])
  have hm := merge_left (literal (valuationOf q) (1426)) (literal (valuationOf q) (1430)) (countLit q [-23, -24]) (countLit q [-27, -30]) (count1430 q) 1 (meaning1426 q) (meaning1430 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1430 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-23, -24]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -30])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1431)) (countLit q [-23, -24]) (countLit q [-27, -30]) (count1430 q) 1 1 (meaning1426 q) (meaning1428 q) (meaning1431 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1428 = false ∨ valuation q 1431 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true := by
  have hs : count1430 q = (countLit q [-23, -24]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -30])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1432)) (countLit q [-23, -24]) (countLit q [-27, -30]) (count1430 q) 1 2 (meaning1426 q) (meaning1429 q) (meaning1432 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1429 = false ∨ valuation q 1432 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-23, -24]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -30])
  have hm := merge_left (literal (valuationOf q) (1427)) (literal (valuationOf q) (1431)) (countLit q [-23, -24]) (countLit q [-27, -30]) (count1430 q) 2 (meaning1427 q) (meaning1431 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1431 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1432 = true := by
  have hs : count1430 q = (countLit q [-23, -24]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -30])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1432)) (countLit q [-23, -24]) (countLit q [-27, -30]) (count1430 q) 2 1 (meaning1427 q) (meaning1428 q) (meaning1432 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1428 = false ∨ valuation q 1432 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_right (literal (valuationOf q) (1430)) (literal (valuationOf q) (1434)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 1 (meaning1430 q) (meaning1434 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1434 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_right (literal (valuationOf q) (1431)) (literal (valuationOf q) (1435)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 2 (meaning1431 q) (meaning1435 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1435 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_right (literal (valuationOf q) (1432)) (literal (valuationOf q) (1436)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 3 (meaning1432 q) (meaning1436 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1436 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_left (literal (valuationOf q) (1423)) (literal (valuationOf q) (1434)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 1 (meaning1423 q) (meaning1434 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1434 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1435)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 1 1 (meaning1423 q) (meaning1430 q) (meaning1435 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1430 = false ∨ valuation q 1435 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1436)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 1 2 (meaning1423 q) (meaning1431 q) (meaning1436 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1431 = false ∨ valuation q 1436 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1437 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1437)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 1 3 (meaning1423 q) (meaning1432 q) (meaning1437 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1432 = false ∨ valuation q 1437 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_left (literal (valuationOf q) (1424)) (literal (valuationOf q) (1435)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 2 (meaning1424 q) (meaning1435 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1435 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1436)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 2 1 (meaning1424 q) (meaning1430 q) (meaning1436 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1430 = false ∨ valuation q 1436 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1437 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1437)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 2 2 (meaning1424 q) (meaning1431 q) (meaning1437 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1431 = false ∨ valuation q 1437 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1438 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1438)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 2 3 (meaning1424 q) (meaning1432 q) (meaning1438 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1432 = false ∨ valuation q 1438 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_left (literal (valuationOf q) (1425)) (literal (valuationOf q) (1436)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 3 (meaning1425 q) (meaning1436 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1436 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1437 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1437)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 3 1 (meaning1425 q) (meaning1430 q) (meaning1437 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1430 = false ∨ valuation q 1437 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1438 = true := by
  have hs : count1434 q = (countLit q [-18, -20, -22]) + (countLit q [-23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-18, -20, -22]) (l₂ := [-23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1438)) (countLit q [-18, -20, -22]) (countLit q [-23, -24, -27, -30]) (count1434 q) 3 2 (meaning1425 q) (meaning1431 q) (meaning1438 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1431 = false ∨ valuation q 1438 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_right (literal (valuationOf q) (1434)) (literal (valuationOf q) (1441)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 1 (meaning1434 q) (meaning1441 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1441 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_right (literal (valuationOf q) (1435)) (literal (valuationOf q) (1442)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 2 (meaning1435 q) (meaning1442 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1442 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_right (literal (valuationOf q) (1436)) (literal (valuationOf q) (1443)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 3 (meaning1436 q) (meaning1443 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1443 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_right (literal (valuationOf q) (1437)) (literal (valuationOf q) (1444)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 4 (meaning1437 q) (meaning1444 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1444 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_right (literal (valuationOf q) (1438)) (literal (valuationOf q) (1445)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 5 (meaning1438 q) (meaning1445 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1445 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1442)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 1 1 (meaning1414 q) (meaning1434 q) (meaning1442 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1434 = false ∨ valuation q 1442 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1443)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 1 2 (meaning1414 q) (meaning1435 q) (meaning1443 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1435 = false ∨ valuation q 1443 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1444)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 1 3 (meaning1414 q) (meaning1436 q) (meaning1444 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1436 = false ∨ valuation q 1444 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1445)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 1 4 (meaning1414 q) (meaning1437 q) (meaning1445 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1437 = false ∨ valuation q 1445 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-2, -5, -6, -10, -11, -13, -15]) + (countLit q [-18, -20, -22, -23, -24, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15]) (l₂ := [-18, -20, -22, -23, -24, -27, -30])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1442)) (countLit q [-2, -5, -6, -10, -11, -13, -15]) (countLit q [-18, -20, -22, -23, -24, -27, -30]) (count1441 q) 2 (meaning1415 q) (meaning1442 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1442 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E058.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112058
