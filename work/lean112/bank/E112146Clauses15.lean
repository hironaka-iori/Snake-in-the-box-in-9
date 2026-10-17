import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-6, -9]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-10, -12])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1359)) (countLit q [-6, -9]) (countLit q [-10, -12]) (count1358 q) 1 1 (meaning1354 q) (meaning1356 q) (meaning1359 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1356 = false ∨ valuation q 1359 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1360 = true := by
  have hs : count1358 q = (countLit q [-6, -9]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-10, -12])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1360)) (countLit q [-6, -9]) (countLit q [-10, -12]) (count1358 q) 1 2 (meaning1354 q) (meaning1357 q) (meaning1360 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1357 = false ∨ valuation q 1360 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-6, -9]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-10, -12])
  have hm := merge_left (literal (valuationOf q) (1355)) (literal (valuationOf q) (1359)) (countLit q [-6, -9]) (countLit q [-10, -12]) (count1358 q) 2 (meaning1355 q) (meaning1359 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1359 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1360 = true := by
  have hs : count1358 q = (countLit q [-6, -9]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-10, -12])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1360)) (countLit q [-6, -9]) (countLit q [-10, -12]) (count1358 q) 2 1 (meaning1355 q) (meaning1356 q) (meaning1360 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1356 = false ∨ valuation q 1360 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1361 = true := by
  have hs : count1358 q = (countLit q [-6, -9]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-10, -12])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1361)) (countLit q [-6, -9]) (countLit q [-10, -12]) (count1358 q) 2 2 (meaning1355 q) (meaning1357 q) (meaning1361 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1357 = false ∨ valuation q 1361 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_right (literal (valuationOf q) (1358)) (literal (valuationOf q) (1362)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 1 (meaning1358 q) (meaning1362 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1362 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_right (literal (valuationOf q) (1359)) (literal (valuationOf q) (1363)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 2 (meaning1359 q) (meaning1363 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1363 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_right (literal (valuationOf q) (1360)) (literal (valuationOf q) (1364)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 3 (meaning1360 q) (meaning1364 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1364 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1351)) (literal (valuationOf q) (1362)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 1 (meaning1351 q) (meaning1362 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1362 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1363)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 1 1 (meaning1351 q) (meaning1358 q) (meaning1363 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1358 = false ∨ valuation q 1363 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1364)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 1 2 (meaning1351 q) (meaning1359 q) (meaning1364 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1359 = false ∨ valuation q 1364 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1365 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1365)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 1 3 (meaning1351 q) (meaning1360 q) (meaning1365 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1360 = false ∨ valuation q 1365 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1366 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1361)) (literal (valuationOf q) (1366)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 1 4 (meaning1351 q) (meaning1361 q) (meaning1366 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1361 = false ∨ valuation q 1366 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1352)) (literal (valuationOf q) (1363)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 2 (meaning1352 q) (meaning1363 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1363 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1364)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 2 1 (meaning1352 q) (meaning1358 q) (meaning1364 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1358 = false ∨ valuation q 1364 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1365 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1365)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 2 2 (meaning1352 q) (meaning1359 q) (meaning1365 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1359 = false ∨ valuation q 1365 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1366 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1366)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 2 3 (meaning1352 q) (meaning1360 q) (meaning1366 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1360 = false ∨ valuation q 1366 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1353)) (literal (valuationOf q) (1364)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 3 (meaning1353 q) (meaning1364 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1364 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1365 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1365)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 3 1 (meaning1353 q) (meaning1358 q) (meaning1365 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1358 = false ∨ valuation q 1365 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1366 = true := by
  have hs : count1362 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -9, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -9, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1366)) (countLit q [-2, -3, -5]) (countLit q [-6, -9, -10, -12]) (count1362 q) 3 2 (meaning1353 q) (meaning1359 q) (meaning1366 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1359 = false ∨ valuation q 1366 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1369)) (countLit q [-15]) (countLit q [-18]) (count1369 q) 1 (meaningNeg18 q) (meaning1369 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1369 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1369)) (countLit q [-15]) (countLit q [-18]) (count1369 q) 1 (meaningNeg15 q) (meaning1369 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1369 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 18 = true ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (1370)) (countLit q [-15]) (countLit q [-18]) (count1369 q) 1 1 (meaningNeg15 q) (meaningNeg18 q) (meaning1370 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 18 = true ∨ valuation q 1370 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1371 = true := by
  have hs : count1371 q = (countLit q [-13]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -18])
  have hm := merge_right (literal (valuationOf q) (1369)) (literal (valuationOf q) (1371)) (countLit q [-13]) (countLit q [-15, -18]) (count1371 q) 1 (meaning1369 q) (meaning1371 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1371 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1372 = true := by
  have hs : count1371 q = (countLit q [-13]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -18])
  have hm := merge_right (literal (valuationOf q) (1370)) (literal (valuationOf q) (1372)) (countLit q [-13]) (countLit q [-15, -18]) (count1371 q) 2 (meaning1370 q) (meaning1372 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1372 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1371 = true := by
  have hs : count1371 q = (countLit q [-13]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -18])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1371)) (countLit q [-13]) (countLit q [-15, -18]) (count1371 q) 1 (meaningNeg13 q) (meaning1371 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1371 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1369 = false ∨ valuationOf q 1372 = true := by
  have hs : count1371 q = (countLit q [-13]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -18])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1372)) (countLit q [-13]) (countLit q [-15, -18]) (count1371 q) 1 1 (meaningNeg13 q) (meaning1369 q) (meaning1372 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1369 = false ∨ valuation q 1372 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1370 = false ∨ valuationOf q 1373 = true := by
  have hs : count1371 q = (countLit q [-13]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -18])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1373)) (countLit q [-13]) (countLit q [-15, -18]) (count1371 q) 1 2 (meaningNeg13 q) (meaning1370 q) (meaning1373 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1370 = false ∨ valuation q 1373 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1374 = true := by
  have hs : count1374 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1374)) (countLit q [-20]) (countLit q [-21]) (count1374 q) 1 (meaningNeg21 q) (meaning1374 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1374 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1374 = true := by
  have hs : count1374 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1374)) (countLit q [-20]) (countLit q [-21]) (count1374 q) 1 (meaningNeg20 q) (meaning1374 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1374 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1375 = true := by
  have hs : count1374 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1375)) (countLit q [-20]) (countLit q [-21]) (count1374 q) 1 1 (meaningNeg20 q) (meaningNeg21 q) (meaning1375 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 1375 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1376 = true := by
  have hs : count1376 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1376)) (countLit q [-22]) (countLit q [-23]) (count1376 q) 1 (meaningNeg23 q) (meaning1376 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1376 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E146.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112146
