import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1375)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 2 1 (meaning1363 q) (meaning1369 q) (meaning1375 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1369 = false ∨ valuation q 1375 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1376 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1376)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 2 2 (meaning1363 q) (meaning1370 q) (meaning1376 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1370 = false ∨ valuation q 1376 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1377 = true := by
  have hs : count1373 q = (countLit q [-39, -40, -44]) + (countLit q [-45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1377)) (countLit q [-39, -40, -44]) (countLit q [-45, -47, -50, -52]) (count1373 q) 2 3 (meaning1363 q) (meaning1371 q) (meaning1377 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1371 = false ∨ valuation q 1377 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1380 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1373)) (literal (valuationOf q) (1380)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 1 (meaning1373 q) (meaning1380 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1380 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1381 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1374)) (literal (valuationOf q) (1381)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 2 (meaning1374 q) (meaning1381 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1381 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1382 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1375)) (literal (valuationOf q) (1382)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 3 (meaning1375 q) (meaning1382 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1382 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1383 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1376)) (literal (valuationOf q) (1383)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 4 (meaning1376 q) (meaning1383 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1383 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1384 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1377)) (literal (valuationOf q) (1384)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 5 (meaning1377 q) (meaning1384 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1384 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1373 = false ∨ valuationOf q 1381 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1373)) (literal (valuationOf q) (1381)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 1 1 (meaning1353 q) (meaning1373 q) (meaning1381 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1373 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1373 = false ∨ valuation q 1381 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1382 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1382)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 1 2 (meaning1353 q) (meaning1374 q) (meaning1382 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1374 = false ∨ valuation q 1382 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1383 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1383)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 1 3 (meaning1353 q) (meaning1375 q) (meaning1383 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1375 = false ∨ valuation q 1383 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1384 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1384)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 1 4 (meaning1353 q) (meaning1376 q) (meaning1384 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1376 = false ∨ valuation q 1384 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1385 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1377)) (literal (valuationOf q) (1385)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 1 5 (meaning1353 q) (meaning1377 q) (meaning1385 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1377 = false ∨ valuation q 1385 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1381 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_left (literal (valuationOf q) (1354)) (literal (valuationOf q) (1381)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 2 (meaning1354 q) (meaning1381 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1381 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1373 = false ∨ valuationOf q 1382 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1373)) (literal (valuationOf q) (1382)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 2 1 (meaning1354 q) (meaning1373 q) (meaning1382 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1373 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1373 = false ∨ valuation q 1382 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1383 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1383)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 2 2 (meaning1354 q) (meaning1374 q) (meaning1383 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1374 = false ∨ valuation q 1383 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1384 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1384)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 2 3 (meaning1354 q) (meaning1375 q) (meaning1384 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1375 = false ∨ valuation q 1384 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1385 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1385)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 2 4 (meaning1354 q) (meaning1376 q) (meaning1385 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1376 = false ∨ valuation q 1385 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1384 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1384)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 3 2 (meaning1355 q) (meaning1374 q) (meaning1384 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1374 = false ∨ valuation q 1384 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1385 = true := by
  have hs : count1380 q = (countLit q [-25, -28, -29, -32, -34, -36, -37]) + (countLit q [-39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29, -32, -34, -36, -37]) (l₂ := [-39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1385)) (countLit q [-25, -28, -29, -32, -34, -36, -37]) (countLit q [-39, -40, -44, -45, -47, -50, -52]) (count1380 q) 3 3 (meaning1355 q) (meaning1375 q) (meaning1385 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1375 = false ∨ valuation q 1385 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1398 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1398)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 1 4 (meaning1327 q) (meaning1383 q) (meaning1398 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1383 = false ∨ valuation q 1398 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1399 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1399)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 2 4 (meaning1328 q) (meaning1383 q) (meaning1399 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1383 = false ∨ valuation q 1399 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1400 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1400)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 2 5 (meaning1328 q) (meaning1384 q) (meaning1400 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1384 = false ∨ valuation q 1400 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1401 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1401)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 2 6 (meaning1328 q) (meaning1385 q) (meaning1401 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1385 = false ∨ valuation q 1401 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1398 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1398)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 3 2 (meaning1329 q) (meaning1381 q) (meaning1398 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1381 = false ∨ valuation q 1398 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1399 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1399)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 3 3 (meaning1329 q) (meaning1382 q) (meaning1399 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1382 = false ∨ valuation q 1399 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1400 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1400)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 3 4 (meaning1329 q) (meaning1383 q) (meaning1400 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1383 = false ∨ valuation q 1400 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1401 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1401)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 3 5 (meaning1329 q) (meaning1384 q) (meaning1401 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1384 = false ∨ valuation q 1401 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1399 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1399)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 4 2 (meaning1330 q) (meaning1381 q) (meaning1399 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1381 = false ∨ valuation q 1399 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1400 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1400)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 4 3 (meaning1330 q) (meaning1382 q) (meaning1400 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1382 = false ∨ valuation q 1400 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1401 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1401)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 4 4 (meaning1330 q) (meaning1383 q) (meaning1401 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1383 = false ∨ valuation q 1401 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1402 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1402)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 4 5 (meaning1330 q) (meaning1384 q) (meaning1402 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1384 = false ∨ valuation q 1402 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E166.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112166
