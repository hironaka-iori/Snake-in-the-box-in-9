import E112205Semantics
import B112E205Inputs
namespace Snake9.Regrowth.E112205
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1395 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1382)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1395)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 2 2 (meaning1382 q) (meaning1389 q) (meaning1395 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1389 = false ∨ valuation q 1395 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1396 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1382)) (literal (valuationOf q) (1390)) (literal (valuationOf q) (1396)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 2 3 (meaning1382 q) (meaning1390 q) (meaning1396 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1390 = false ∨ valuation q 1396 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1394 = true := by
  have hs : count1392 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -53, -57])
  have hm := merge_left (literal (valuationOf q) (1383)) (literal (valuationOf q) (1394)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -53, -57]) (count1392 q) 3 (meaning1383 q) (meaning1394 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1394 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-28, -31, -34, -35, -38, -40]) + (countLit q [-43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34, -35, -38, -40]) (l₂ := [-43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1400)) (countLit q [-28, -31, -34, -35, -38, -40]) (countLit q [-43, -45, -46, -49, -51, -53, -57]) (count1399 q) 1 1 (meaning1373 q) (meaning1392 q) (meaning1400 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1392 = false ∨ valuation q 1400 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-28, -31, -34, -35, -38, -40]) + (countLit q [-43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34, -35, -38, -40]) (l₂ := [-43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1401)) (countLit q [-28, -31, -34, -35, -38, -40]) (countLit q [-43, -45, -46, -49, -51, -53, -57]) (count1399 q) 1 2 (meaning1373 q) (meaning1393 q) (meaning1401 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1393 = false ∨ valuation q 1401 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-28, -31, -34, -35, -38, -40]) + (countLit q [-43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34, -35, -38, -40]) (l₂ := [-43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1402)) (countLit q [-28, -31, -34, -35, -38, -40]) (countLit q [-43, -45, -46, -49, -51, -53, -57]) (count1399 q) 1 3 (meaning1373 q) (meaning1394 q) (meaning1402 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1394 = false ∨ valuation q 1402 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1395 = false ∨ valuationOf q 1403 = true := by
  have hs : count1399 q = (countLit q [-28, -31, -34, -35, -38, -40]) + (countLit q [-43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34, -35, -38, -40]) (l₂ := [-43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1395)) (literal (valuationOf q) (1403)) (countLit q [-28, -31, -34, -35, -38, -40]) (countLit q [-43, -45, -46, -49, -51, -53, -57]) (count1399 q) 1 4 (meaning1373 q) (meaning1395 q) (meaning1403 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1395 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1395 = false ∨ valuation q 1403 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1396 = false ∨ valuationOf q 1404 = true := by
  have hs : count1399 q = (countLit q [-28, -31, -34, -35, -38, -40]) + (countLit q [-43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34, -35, -38, -40]) (l₂ := [-43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1396)) (literal (valuationOf q) (1404)) (countLit q [-28, -31, -34, -35, -38, -40]) (countLit q [-43, -45, -46, -49, -51, -53, -57]) (count1399 q) 1 5 (meaning1373 q) (meaning1396 q) (meaning1404 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1396 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1396 = false ∨ valuation q 1404 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-28, -31, -34, -35, -38, -40]) + (countLit q [-43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34, -35, -38, -40]) (l₂ := [-43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1401)) (countLit q [-28, -31, -34, -35, -38, -40]) (countLit q [-43, -45, -46, -49, -51, -53, -57]) (count1399 q) 2 1 (meaning1374 q) (meaning1392 q) (meaning1401 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1392 = false ∨ valuation q 1401 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-28, -31, -34, -35, -38, -40]) + (countLit q [-43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -34, -35, -38, -40]) (l₂ := [-43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1402)) (countLit q [-28, -31, -34, -35, -38, -40]) (countLit q [-43, -45, -46, -49, -51, -53, -57]) (count1399 q) 2 2 (meaning1374 q) (meaning1393 q) (meaning1402 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1393 = false ∨ valuation q 1402 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1414 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1414)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 1 3 (meaning1351 q) (meaning1401 q) (meaning1414 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1401 = false ∨ valuation q 1414 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1415 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1415)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 1 4 (meaning1351 q) (meaning1402 q) (meaning1415 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1402 = false ∨ valuation q 1415 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1416 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1416)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 1 5 (meaning1351 q) (meaning1403 q) (meaning1416 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1403 = false ∨ valuation q 1416 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 1351 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1417 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1351)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1417)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 1 6 (meaning1351 q) (meaning1404 q) (meaning1417 q) hs
  change valuationOf q 1351 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 1351 = false ∨ valuation q 1404 = false ∨ valuation q 1417 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1414 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1414)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 2 2 (meaning1352 q) (meaning1400 q) (meaning1414 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1400 = false ∨ valuation q 1414 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1416 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1352)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1416)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 2 4 (meaning1352 q) (meaning1402 q) (meaning1416 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1402 = false ∨ valuation q 1416 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1415 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1415)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 3 2 (meaning1353 q) (meaning1400 q) (meaning1415 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1400 = false ∨ valuation q 1415 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1416 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1416)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 3 3 (meaning1353 q) (meaning1401 q) (meaning1416 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1401 = false ∨ valuation q 1416 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1416 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1416)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 4 2 (meaning1354 q) (meaning1400 q) (meaning1416 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1400 = false ∨ valuation q 1416 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1417 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1417)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 5 2 (meaning1355 q) (meaning1400 q) (meaning1417 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1400 = false ∨ valuation q 1417 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1419 = true := by
  have hs : count1411 q = (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]) (count1411 q) 7 2 (meaning1357 q) (meaning1400 q) (meaning1419 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1400 = false ∨ valuation q 1419 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1423)) (countLit q [-61]) (countLit q [-63]) (count1423 q) 1 (meaningNeg63 q) (meaning1423 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1423 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1423)) (countLit q [-61]) (countLit q [-63]) (count1423 q) 1 (meaningNeg61 q) (meaning1423 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1423 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1424)) (countLit q [-61]) (countLit q [-63]) (count1423 q) 1 1 (meaningNeg61 q) (meaningNeg63 q) (meaning1424 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 1424 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1423)) (literal (valuationOf q) (1425)) (countLit q [-59]) (countLit q [-61, -63]) (count1425 q) 1 (meaning1423 q) (meaning1425 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1425 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1424)) (literal (valuationOf q) (1426)) (countLit q [-59]) (countLit q [-61, -63]) (count1425 q) 2 (meaning1424 q) (meaning1426 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1426 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1425)) (countLit q [-59]) (countLit q [-61, -63]) (count1425 q) 1 (meaningNeg59 q) (meaning1425 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1425 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1423 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1426)) (countLit q [-59]) (countLit q [-61, -63]) (count1425 q) 1 1 (meaningNeg59 q) (meaning1423 q) (meaning1426 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1423 = false ∨ valuation q 1426 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-66]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1428)) (countLit q [-66]) (countLit q [-69]) (count1428 q) 1 (meaningNeg69 q) (meaning1428 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1428 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-66]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1428)) (countLit q [-66]) (countLit q [-69]) (count1428 q) 1 (meaningNeg66 q) (meaning1428 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1428 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-64]) + (countLit q [-66, -69]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -69])
  have hm := merge_right (literal (valuationOf q) (1428)) (literal (valuationOf q) (1430)) (countLit q [-64]) (countLit q [-66, -69]) (count1430 q) 1 (meaning1428 q) (meaning1430 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1430 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-64]) + (countLit q [-66, -69]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -69])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1430)) (countLit q [-64]) (countLit q [-66, -69]) (count1430 q) 1 (meaningNeg64 q) (meaning1430 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1430 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E205.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112205
