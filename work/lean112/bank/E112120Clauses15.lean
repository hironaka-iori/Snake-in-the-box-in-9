import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-1, -2, -5]) + (countLit q [-8, -10, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-8, -10, -14, -15])
  have hm := merge_right (literal (valuationOf q) (1410)) (literal (valuationOf q) (1414)) (countLit q [-1, -2, -5]) (countLit q [-8, -10, -14, -15]) (count1414 q) 1 (meaning1410 q) (meaning1414 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1414 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-1, -2, -5]) + (countLit q [-8, -10, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-8, -10, -14, -15])
  have hm := merge_right (literal (valuationOf q) (1411)) (literal (valuationOf q) (1415)) (countLit q [-1, -2, -5]) (countLit q [-8, -10, -14, -15]) (count1414 q) 2 (meaning1411 q) (meaning1415 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1415 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1416 = true := by
  have hs : count1414 q = (countLit q [-1, -2, -5]) + (countLit q [-8, -10, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-8, -10, -14, -15])
  have hm := merge_right (literal (valuationOf q) (1412)) (literal (valuationOf q) (1416)) (countLit q [-1, -2, -5]) (countLit q [-8, -10, -14, -15]) (count1414 q) 3 (meaning1412 q) (meaning1416 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1416 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-1, -2, -5]) + (countLit q [-8, -10, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-8, -10, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1415)) (countLit q [-1, -2, -5]) (countLit q [-8, -10, -14, -15]) (count1414 q) 1 1 (meaning1403 q) (meaning1410 q) (meaning1415 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1410 = false ∨ valuation q 1415 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1416 = true := by
  have hs : count1414 q = (countLit q [-1, -2, -5]) + (countLit q [-8, -10, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-8, -10, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1416)) (countLit q [-1, -2, -5]) (countLit q [-8, -10, -14, -15]) (count1414 q) 1 2 (meaning1403 q) (meaning1411 q) (meaning1416 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1411 = false ∨ valuation q 1416 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1417 = true := by
  have hs : count1414 q = (countLit q [-1, -2, -5]) + (countLit q [-8, -10, -14, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-8, -10, -14, -15])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1417)) (countLit q [-1, -2, -5]) (countLit q [-8, -10, -14, -15]) (count1414 q) 1 3 (meaning1403 q) (meaning1412 q) (meaning1417 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1412 = false ∨ valuation q 1417 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1421)) (countLit q [-19]) (countLit q [-21]) (count1421 q) 1 (meaningNeg21 q) (meaning1421 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1421 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1421)) (countLit q [-19]) (countLit q [-21]) (count1421 q) 1 (meaningNeg19 q) (meaning1421 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1421 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-16]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (1421)) (literal (valuationOf q) (1423)) (countLit q [-16]) (countLit q [-19, -21]) (count1423 q) 1 (meaning1421 q) (meaning1423 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1423 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-16]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19, -21])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1423)) (countLit q [-16]) (countLit q [-19, -21]) (count1423 q) 1 (meaningNeg16 q) (meaning1423 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1423 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-16]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1424)) (countLit q [-16]) (countLit q [-19, -21]) (count1423 q) 1 1 (meaningNeg16 q) (meaning1421 q) (meaning1424 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1421 = false ∨ valuation q 1424 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1426)) (countLit q [-24]) (countLit q [-25]) (count1426 q) 1 (meaningNeg25 q) (meaning1426 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1426 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1426)) (countLit q [-24]) (countLit q [-25]) (count1426 q) 1 (meaningNeg24 q) (meaning1426 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1426 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1427)) (countLit q [-24]) (countLit q [-25]) (count1426 q) 1 1 (meaningNeg24 q) (meaningNeg25 q) (meaning1427 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 1427 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1428)) (countLit q [-28]) (countLit q [-30]) (count1428 q) 1 (meaningNeg30 q) (meaning1428 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1428 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1428)) (countLit q [-28]) (countLit q [-30]) (count1428 q) 1 (meaningNeg28 q) (meaning1428 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1428 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1429 = true := by
  have hs : count1428 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1429)) (countLit q [-28]) (countLit q [-30]) (count1428 q) 1 1 (meaningNeg28 q) (meaningNeg30 q) (meaning1429 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 30 = true ∨ valuation q 1429 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (1428)) (literal (valuationOf q) (1430)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1430 q) 1 (meaning1428 q) (meaning1430 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1430 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (1426)) (literal (valuationOf q) (1430)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1430 q) 1 (meaning1426 q) (meaning1430 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1430 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1431)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1430 q) 1 1 (meaning1426 q) (meaning1428 q) (meaning1431 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1428 = false ∨ valuation q 1431 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true := by
  have hs : count1430 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1432)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1430 q) 1 2 (meaning1426 q) (meaning1429 q) (meaning1432 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1429 = false ∨ valuation q 1432 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (1427)) (literal (valuationOf q) (1431)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1430 q) 2 (meaning1427 q) (meaning1431 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1431 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1432 = true := by
  have hs : count1430 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1432)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1430 q) 2 1 (meaning1427 q) (meaning1428 q) (meaning1432 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1428 = false ∨ valuation q 1432 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-16, -19, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1430)) (literal (valuationOf q) (1434)) (countLit q [-16, -19, -21]) (countLit q [-24, -25, -28, -30]) (count1434 q) 1 (meaning1430 q) (meaning1434 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1434 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-16, -19, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1431)) (literal (valuationOf q) (1435)) (countLit q [-16, -19, -21]) (countLit q [-24, -25, -28, -30]) (count1434 q) 2 (meaning1431 q) (meaning1435 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1435 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-16, -19, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1432)) (literal (valuationOf q) (1436)) (countLit q [-16, -19, -21]) (countLit q [-24, -25, -28, -30]) (count1434 q) 3 (meaning1432 q) (meaning1436 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1436 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-16, -19, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1423)) (literal (valuationOf q) (1434)) (countLit q [-16, -19, -21]) (countLit q [-24, -25, -28, -30]) (count1434 q) 1 (meaning1423 q) (meaning1434 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1434 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-16, -19, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1435)) (countLit q [-16, -19, -21]) (countLit q [-24, -25, -28, -30]) (count1434 q) 1 1 (meaning1423 q) (meaning1430 q) (meaning1435 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1430 = false ∨ valuation q 1435 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-16, -19, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1436)) (countLit q [-16, -19, -21]) (countLit q [-24, -25, -28, -30]) (count1434 q) 1 2 (meaning1423 q) (meaning1431 q) (meaning1436 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1431 = false ∨ valuation q 1436 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1437 = true := by
  have hs : count1434 q = (countLit q [-16, -19, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1437)) (countLit q [-16, -19, -21]) (countLit q [-24, -25, -28, -30]) (count1434 q) 1 3 (meaning1423 q) (meaning1432 q) (meaning1437 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1432 = false ∨ valuation q 1437 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-16, -19, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1424)) (literal (valuationOf q) (1435)) (countLit q [-16, -19, -21]) (countLit q [-24, -25, -28, -30]) (count1434 q) 2 (meaning1424 q) (meaning1435 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1435 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-16, -19, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1436)) (countLit q [-16, -19, -21]) (countLit q [-24, -25, -28, -30]) (count1434 q) 2 1 (meaning1424 q) (meaning1430 q) (meaning1436 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1430 = false ∨ valuation q 1436 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E120.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112120
