import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1345)) (countLit q [-33]) (countLit q [-35]) (count1345 q) 1 (meaningNeg33 q) (meaning1345 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1345 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1346 = true := by
  have hs : count1345 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1346)) (countLit q [-33]) (countLit q [-35]) (count1345 q) 1 1 (meaningNeg33 q) (meaningNeg35 q) (meaning1346 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 1346 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1347 = true := by
  have hs : count1347 q = (countLit q [-36]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1347)) (countLit q [-36]) (countLit q [-39]) (count1347 q) 1 (meaningNeg39 q) (meaning1347 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1347 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1347 = true := by
  have hs : count1347 q = (countLit q [-36]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1347)) (countLit q [-36]) (countLit q [-39]) (count1347 q) 1 (meaningNeg36 q) (meaning1347 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1347 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-33, -35]) + (countLit q [-36, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-36, -39])
  have hm := merge_right (literal (valuationOf q) (1347)) (literal (valuationOf q) (1349)) (countLit q [-33, -35]) (countLit q [-36, -39]) (count1349 q) 1 (meaning1347 q) (meaning1349 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1349 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-33, -35]) + (countLit q [-36, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-36, -39])
  have hm := merge_left (literal (valuationOf q) (1345)) (literal (valuationOf q) (1349)) (countLit q [-33, -35]) (countLit q [-36, -39]) (count1349 q) 1 (meaning1345 q) (meaning1349 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1349 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-33, -35]) + (countLit q [-36, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-36, -39])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1350)) (countLit q [-33, -35]) (countLit q [-36, -39]) (count1349 q) 1 1 (meaning1345 q) (meaning1347 q) (meaning1350 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1347 = false ∨ valuation q 1350 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-33, -35]) + (countLit q [-36, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-36, -39])
  have hm := merge_left (literal (valuationOf q) (1346)) (literal (valuationOf q) (1350)) (countLit q [-33, -35]) (countLit q [-36, -39]) (count1349 q) 2 (meaning1346 q) (meaning1350 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1350 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1351 = true := by
  have hs : count1349 q = (countLit q [-33, -35]) + (countLit q [-36, -39]) := List.countP_append (p := literal q) (l₁ := [-33, -35]) (l₂ := [-36, -39])
  have hm := merge_two (literal (valuationOf q) (1346)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1351)) (countLit q [-33, -35]) (countLit q [-36, -39]) (count1349 q) 2 1 (meaning1346 q) (meaning1347 q) (meaning1351 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1347 = false ∨ valuation q 1351 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1353 = true := by
  have hs : count1353 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -35, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -35, -36, -39])
  have hm := merge_left (literal (valuationOf q) (1342)) (literal (valuationOf q) (1353)) (countLit q [-27, -29, -31]) (countLit q [-33, -35, -36, -39]) (count1353 q) 1 (meaning1342 q) (meaning1353 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1353 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1354 = true := by
  have hs : count1353 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -35, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -35, -36, -39])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1354)) (countLit q [-27, -29, -31]) (countLit q [-33, -35, -36, -39]) (count1353 q) 1 1 (meaning1342 q) (meaning1349 q) (meaning1354 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1349 = false ∨ valuation q 1354 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1355 = true := by
  have hs : count1353 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -35, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -35, -36, -39])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1355)) (countLit q [-27, -29, -31]) (countLit q [-33, -35, -36, -39]) (count1353 q) 1 2 (meaning1342 q) (meaning1350 q) (meaning1355 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1350 = false ∨ valuation q 1355 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1354 = true := by
  have hs : count1353 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -35, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -35, -36, -39])
  have hm := merge_left (literal (valuationOf q) (1343)) (literal (valuationOf q) (1354)) (countLit q [-27, -29, -31]) (countLit q [-33, -35, -36, -39]) (count1353 q) 2 (meaning1343 q) (meaning1354 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1354 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1355 = true := by
  have hs : count1353 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -35, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -35, -36, -39])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1355)) (countLit q [-27, -29, -31]) (countLit q [-33, -35, -36, -39]) (count1353 q) 2 1 (meaning1343 q) (meaning1349 q) (meaning1355 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1349 = false ∨ valuation q 1355 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1357 = true := by
  have hs : count1353 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -35, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -35, -36, -39])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1357)) (countLit q [-27, -29, -31]) (countLit q [-33, -35, -36, -39]) (count1353 q) 2 3 (meaning1343 q) (meaning1351 q) (meaning1357 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1351 = false ∨ valuation q 1357 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1355 = true := by
  have hs : count1353 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -35, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -35, -36, -39])
  have hm := merge_left (literal (valuationOf q) (1344)) (literal (valuationOf q) (1355)) (countLit q [-27, -29, -31]) (countLit q [-33, -35, -36, -39]) (count1353 q) 3 (meaning1344 q) (meaning1355 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1355 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1356 = true := by
  have hs : count1353 q = (countLit q [-27, -29, -31]) + (countLit q [-33, -35, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-33, -35, -36, -39])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1356)) (countLit q [-27, -29, -31]) (countLit q [-33, -35, -36, -39]) (count1353 q) 3 1 (meaning1344 q) (meaning1349 q) (meaning1356 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1349 = false ∨ valuation q 1356 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1360 = true := by
  have hs : count1360 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1360)) (countLit q [-42]) (countLit q [-45]) (count1360 q) 1 (meaningNeg42 q) (meaning1360 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1360 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1361 = true := by
  have hs : count1360 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1361)) (countLit q [-42]) (countLit q [-45]) (count1360 q) 1 1 (meaningNeg42 q) (meaningNeg45 q) (meaning1361 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 45 = true ∨ valuation q 1361 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-40]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42, -45])
  have hm := merge_right (literal (valuationOf q) (1360)) (literal (valuationOf q) (1362)) (countLit q [-40]) (countLit q [-42, -45]) (count1362 q) 1 (meaning1360 q) (meaning1362 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1362 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-40]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42, -45])
  have hm := merge_right (literal (valuationOf q) (1361)) (literal (valuationOf q) (1363)) (countLit q [-40]) (countLit q [-42, -45]) (count1362 q) 2 (meaning1361 q) (meaning1363 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1363 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1360 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-40]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42, -45])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1363)) (countLit q [-40]) (countLit q [-42, -45]) (count1362 q) 1 1 (meaningNeg40 q) (meaning1360 q) (meaning1363 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1360 = false ∨ valuation q 1363 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1361 = false ∨ valuationOf q 1364 = true := by
  have hs : count1362 q = (countLit q [-40]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42, -45])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (1361)) (literal (valuationOf q) (1364)) (countLit q [-40]) (countLit q [-42, -45]) (count1362 q) 1 2 (meaningNeg40 q) (meaning1361 q) (meaning1364 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1361 = false ∨ valuation q 1364 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1365)) (countLit q [-46]) (countLit q [-48]) (count1365 q) 1 (meaningNeg48 q) (meaning1365 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1365 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1365)) (countLit q [-46]) (countLit q [-48]) (count1365 q) 1 (meaningNeg46 q) (meaning1365 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1365 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1366)) (countLit q [-46]) (countLit q [-48]) (count1365 q) 1 1 (meaningNeg46 q) (meaningNeg48 q) (meaning1366 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 1366 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1367)) (countLit q [-50]) (countLit q [-52]) (count1367 q) 1 (meaningNeg52 q) (meaning1367 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1367 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1367)) (countLit q [-50]) (countLit q [-52]) (count1367 q) 1 (meaningNeg50 q) (meaning1367 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1367 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1368 = true := by
  have hs : count1367 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1368)) (countLit q [-50]) (countLit q [-52]) (count1367 q) 1 1 (meaningNeg50 q) (meaningNeg52 q) (meaning1368 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 52 = true ∨ valuation q 1368 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-46, -48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-50, -52])
  have hm := merge_right (literal (valuationOf q) (1367)) (literal (valuationOf q) (1369)) (countLit q [-46, -48]) (countLit q [-50, -52]) (count1369 q) 1 (meaning1367 q) (meaning1369 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1369 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-46, -48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-50, -52])
  have hm := merge_right (literal (valuationOf q) (1368)) (literal (valuationOf q) (1370)) (countLit q [-46, -48]) (countLit q [-50, -52]) (count1369 q) 2 (meaning1368 q) (meaning1370 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1370 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-46, -48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-50, -52])
  have hm := merge_left (literal (valuationOf q) (1365)) (literal (valuationOf q) (1369)) (countLit q [-46, -48]) (countLit q [-50, -52]) (count1369 q) 1 (meaning1365 q) (meaning1369 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1369 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E090.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112090
