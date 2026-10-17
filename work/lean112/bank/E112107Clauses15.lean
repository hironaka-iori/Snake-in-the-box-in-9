import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1356 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_left (literal (valuationOf q) (1345)) (literal (valuationOf q) (1356)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 3 (meaning1345 q) (meaning1356 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1356 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1357 = true := by
  have hs : count1354 q = (countLit q [-16, -17, -21]) + (countLit q [-22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -21]) (l₂ := [-22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1357)) (countLit q [-16, -17, -21]) (countLit q [-22, -23, -24, -28]) (count1354 q) 3 1 (meaning1345 q) (meaning1350 q) (meaning1357 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1350 = false ∨ valuation q 1357 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1364 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_right (literal (valuationOf q) (1357)) (literal (valuationOf q) (1364)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 4 (meaning1357 q) (meaning1364 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1364 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1361 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_left (literal (valuationOf q) (1335)) (literal (valuationOf q) (1361)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 1 (meaning1335 q) (meaning1361 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1361 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1362 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1362)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 1 1 (meaning1335 q) (meaning1354 q) (meaning1362 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1354 = false ∨ valuation q 1362 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1363 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1363)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 1 2 (meaning1335 q) (meaning1355 q) (meaning1363 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1355 = false ∨ valuation q 1363 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1365 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1365)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 1 4 (meaning1335 q) (meaning1357 q) (meaning1365 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1357 = false ∨ valuation q 1365 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1363 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1363)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 2 1 (meaning1336 q) (meaning1354 q) (meaning1363 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1354 = false ∨ valuation q 1363 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1364 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1364)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 2 2 (meaning1336 q) (meaning1355 q) (meaning1364 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1355 = false ∨ valuation q 1364 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1365 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1365)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 2 3 (meaning1336 q) (meaning1356 q) (meaning1365 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1356 = false ∨ valuation q 1365 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1366 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1366)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 2 4 (meaning1336 q) (meaning1357 q) (meaning1366 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1357 = false ∨ valuation q 1366 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1364 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1337)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1364)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 3 1 (meaning1337 q) (meaning1354 q) (meaning1364 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1354 = false ∨ valuation q 1364 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1365 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1337)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1365)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 3 2 (meaning1337 q) (meaning1355 q) (meaning1365 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1355 = false ∨ valuation q 1365 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1366 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1337)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1366)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 3 3 (meaning1337 q) (meaning1356 q) (meaning1366 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1356 = false ∨ valuation q 1366 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1367 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1337)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1367)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 3 4 (meaning1337 q) (meaning1357 q) (meaning1367 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1357 = false ∨ valuation q 1367 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1365 = true := by
  have hs : count1361 q = (countLit q [-4, -6, -9, -10, -11, -15]) + (countLit q [-16, -17, -21, -22, -23, -24, -28]) := List.countP_append (p := literal q) (l₁ := [-4, -6, -9, -10, -11, -15]) (l₂ := [-16, -17, -21, -22, -23, -24, -28])
  have hm := merge_two (literal (valuationOf q) (1338)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1365)) (countLit q [-4, -6, -9, -10, -11, -15]) (countLit q [-16, -17, -21, -22, -23, -24, -28]) (count1361 q) 4 1 (meaning1338 q) (meaning1354 q) (meaning1365 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1354 = false ∨ valuation q 1365 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1374 = true := by
  have hs : count1374 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1374)) (countLit q [-31]) (countLit q [-33]) (count1374 q) 1 (meaningNeg33 q) (meaning1374 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1374 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1374 = true := by
  have hs : count1374 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1374)) (countLit q [-31]) (countLit q [-33]) (count1374 q) 1 (meaningNeg31 q) (meaning1374 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1374 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1375 = true := by
  have hs : count1374 q = (countLit q [-31]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1375)) (countLit q [-31]) (countLit q [-33]) (count1374 q) 1 1 (meaningNeg31 q) (meaningNeg33 q) (meaning1375 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 33 = true ∨ valuation q 1375 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1376 = true := by
  have hs : count1376 q = (countLit q [-30]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -33])
  have hm := merge_right (literal (valuationOf q) (1374)) (literal (valuationOf q) (1376)) (countLit q [-30]) (countLit q [-31, -33]) (count1376 q) 1 (meaning1374 q) (meaning1376 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1376 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1377 = true := by
  have hs : count1376 q = (countLit q [-30]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -33])
  have hm := merge_right (literal (valuationOf q) (1375)) (literal (valuationOf q) (1377)) (countLit q [-30]) (countLit q [-31, -33]) (count1376 q) 2 (meaning1375 q) (meaning1377 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1377 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1376 = true := by
  have hs : count1376 q = (countLit q [-30]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -33])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1376)) (countLit q [-30]) (countLit q [-31, -33]) (count1376 q) 1 (meaningNeg30 q) (meaning1376 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1376 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1374 = false ∨ valuationOf q 1377 = true := by
  have hs : count1376 q = (countLit q [-30]) + (countLit q [-31, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1377)) (countLit q [-30]) (countLit q [-31, -33]) (count1376 q) 1 1 (meaningNeg30 q) (meaning1374 q) (meaning1377 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1374 = false ∨ valuation q 1377 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-38]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1379)) (countLit q [-38]) (countLit q [-39]) (count1379 q) 1 (meaningNeg39 q) (meaning1379 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1379 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-38]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1379)) (countLit q [-38]) (countLit q [-39]) (count1379 q) 1 (meaningNeg38 q) (meaning1379 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1379 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-37]) + (countLit q [-38, -39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38, -39])
  have hm := merge_right (literal (valuationOf q) (1379)) (literal (valuationOf q) (1381)) (countLit q [-37]) (countLit q [-38, -39]) (count1381 q) 1 (meaning1379 q) (meaning1381 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1381 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-37]) + (countLit q [-38, -39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38, -39])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1381)) (countLit q [-37]) (countLit q [-38, -39]) (count1381 q) 1 (meaningNeg37 q) (meaning1381 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1381 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-30, -31, -33]) + (countLit q [-37, -38, -39]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33]) (l₂ := [-37, -38, -39])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1384)) (countLit q [-30, -31, -33]) (countLit q [-37, -38, -39]) (count1384 q) 1 (meaning1381 q) (meaning1384 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1384 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1385 = true := by
  have hs : count1384 q = (countLit q [-30, -31, -33]) + (countLit q [-37, -38, -39]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33]) (l₂ := [-37, -38, -39])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1385)) (countLit q [-30, -31, -33]) (countLit q [-37, -38, -39]) (count1384 q) 1 1 (meaning1376 q) (meaning1381 q) (meaning1385 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1381 = false ∨ valuation q 1385 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1386 = true := by
  have hs : count1384 q = (countLit q [-30, -31, -33]) + (countLit q [-37, -38, -39]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33]) (l₂ := [-37, -38, -39])
  have hm := merge_two (literal (valuationOf q) (1377)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1386)) (countLit q [-30, -31, -33]) (countLit q [-37, -38, -39]) (count1384 q) 2 1 (meaning1377 q) (meaning1381 q) (meaning1386 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1381 = false ∨ valuation q 1386 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1390 = true := by
  have hs : count1390 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1390)) (countLit q [-43]) (countLit q [-46]) (count1390 q) 1 (meaningNeg46 q) (meaning1390 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1390 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1390 = true := by
  have hs : count1390 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1390)) (countLit q [-43]) (countLit q [-46]) (count1390 q) 1 (meaningNeg43 q) (meaning1390 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1390 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E107.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112107
