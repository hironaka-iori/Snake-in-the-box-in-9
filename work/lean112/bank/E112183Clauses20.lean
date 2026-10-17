import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1432 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1432)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 3 1 (meaning1371 q) (meaning1417 q) (meaning1432 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1417 = false ∨ valuation q 1432 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1433 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1433)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 3 2 (meaning1371 q) (meaning1418 q) (meaning1433 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1418 = false ∨ valuation q 1433 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1434 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1434)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 3 3 (meaning1371 q) (meaning1419 q) (meaning1434 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1419 = false ∨ valuation q 1434 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1435 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1435)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 3 4 (meaning1371 q) (meaning1420 q) (meaning1435 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1420 = false ∨ valuation q 1435 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1436 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1436)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 3 5 (meaning1371 q) (meaning1421 q) (meaning1436 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1421 = false ∨ valuation q 1436 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1437 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1437)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 3 6 (meaning1371 q) (meaning1422 q) (meaning1437 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1422 = false ∨ valuation q 1437 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1433 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1433)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 4 1 (meaning1372 q) (meaning1417 q) (meaning1433 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1417 = false ∨ valuation q 1433 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1434 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1434)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 4 2 (meaning1372 q) (meaning1418 q) (meaning1434 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1418 = false ∨ valuation q 1434 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1435 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1435)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 4 3 (meaning1372 q) (meaning1419 q) (meaning1435 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1419 = false ∨ valuation q 1435 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1436 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1436)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 4 4 (meaning1372 q) (meaning1420 q) (meaning1436 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1420 = false ∨ valuation q 1436 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1437 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1437)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 4 5 (meaning1372 q) (meaning1421 q) (meaning1437 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1421 = false ∨ valuation q 1437 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1434 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1434)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 5 1 (meaning1373 q) (meaning1417 q) (meaning1434 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1417 = false ∨ valuation q 1434 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1435 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1435)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 5 2 (meaning1373 q) (meaning1418 q) (meaning1435 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1418 = false ∨ valuation q 1435 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1435 = true := by
  have hs : count1429 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) + (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (l₂ := [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1435)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]) (countLit q [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (count1429 q) 6 1 (meaning1374 q) (meaning1417 q) (meaning1435 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1417 = false ∨ valuation q 1435 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (1441)) (countLit q [-58]) (countLit q [-61]) (count1441 q) 1 (meaningNeg61 q) (meaning1441 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1441 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1441)) (countLit q [-58]) (countLit q [-61]) (count1441 q) 1 (meaningNeg58 q) (meaning1441 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1441 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 61 = true ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (-61)) (literal (valuationOf q) (1442)) (countLit q [-58]) (countLit q [-61]) (count1441 q) 1 1 (meaningNeg58 q) (meaningNeg61 q) (meaning1442 q) hs
  change (! (valuationOf q 58)) = false ∨ (! (valuationOf q 61)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 61 = true ∨ valuation q 1442 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-57]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58, -61])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (countLit q [-57]) (countLit q [-58, -61]) (count1443 q) 1 (meaning1441 q) (meaning1443 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-57]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58, -61])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1443)) (countLit q [-57]) (countLit q [-58, -61]) (count1443 q) 1 (meaningNeg57 q) (meaning1443 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1443 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-57]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58, -61])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1444)) (countLit q [-57]) (countLit q [-58, -61]) (count1443 q) 1 1 (meaningNeg57 q) (meaning1441 q) (meaning1444 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1441 = false ∨ valuation q 1444 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1442 = false ∨ valuationOf q 1445 = true := by
  have hs : count1443 q = (countLit q [-57]) + (countLit q [-58, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58, -61])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1445)) (countLit q [-57]) (countLit q [-58, -61]) (count1443 q) 1 2 (meaningNeg57 q) (meaning1442 q) (meaning1445 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1442 = false ∨ valuation q 1445 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1446)) (countLit q [-65]) (countLit q [-68]) (count1446 q) 1 (meaningNeg68 q) (meaning1446 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1446 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1446)) (countLit q [-65]) (countLit q [-68]) (count1446 q) 1 (meaningNeg65 q) (meaning1446 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1446 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 68 = true ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (1447)) (countLit q [-65]) (countLit q [-68]) (count1446 q) 1 1 (meaningNeg65 q) (meaningNeg68 q) (meaning1447 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 1447 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1448)) (countLit q [-63]) (countLit q [-65, -68]) (count1448 q) 1 (meaning1446 q) (meaning1448 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1448 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (countLit q [-63]) (countLit q [-65, -68]) (count1448 q) 2 (meaning1447 q) (meaning1449 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1448)) (countLit q [-63]) (countLit q [-65, -68]) (count1448 q) 1 (meaningNeg63 q) (meaning1448 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1448 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1449)) (countLit q [-63]) (countLit q [-65, -68]) (count1448 q) 1 1 (meaningNeg63 q) (meaning1446 q) (meaning1449 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1446 = false ∨ valuation q 1449 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true := by
  have hs : count1448 q = (countLit q [-63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1450)) (countLit q [-63]) (countLit q [-65, -68]) (count1448 q) 1 2 (meaningNeg63 q) (meaning1447 q) (meaning1450 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1447 = false ∨ valuation q 1450 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1451 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1451)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 1 (meaning1448 q) (meaning1451 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1451 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1452 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1452)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 2 (meaning1449 q) (meaning1452 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1452 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1453 = true := by
  have hs : count1451 q = (countLit q [-57, -58, -61]) + (countLit q [-63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61]) (l₂ := [-63, -65, -68])
  have hm := merge_right (literal (valuationOf q) (1450)) (literal (valuationOf q) (1453)) (countLit q [-57, -58, -61]) (countLit q [-63, -65, -68]) (count1451 q) 3 (meaning1450 q) (meaning1453 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1453 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E183.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112183
