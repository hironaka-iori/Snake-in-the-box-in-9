import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1420 = true := by
  have hs : count1416 q = (countLit q [-30, -31, -33, -36, -37, -40, -42]) + (countLit q [-43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -33, -36, -37, -40, -42]) (l₂ := [-43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1420)) (countLit q [-30, -31, -33, -36, -37, -40, -42]) (countLit q [-43, -45, -47, -49, -50, -52, -53]) (count1416 q) 4 1 (meaning1392 q) (meaning1409 q) (meaning1420 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1409 = false ∨ valuation q 1420 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1437 = true := by
  have hs : count1430 q = (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) + (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (l₂ := [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1437)) (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (count1430 q) 4 4 (meaning1366 q) (meaning1419 q) (meaning1437 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1419 = false ∨ valuation q 1437 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1438 = true := by
  have hs : count1430 q = (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) + (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (l₂ := [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1438)) (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (count1430 q) 4 5 (meaning1366 q) (meaning1420 q) (meaning1438 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1420 = false ∨ valuation q 1438 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1437 = true := by
  have hs : count1430 q = (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) + (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (l₂ := [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1437)) (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (count1430 q) 5 3 (meaning1367 q) (meaning1418 q) (meaning1437 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1418 = false ∨ valuation q 1437 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1438 = true := by
  have hs : count1430 q = (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) + (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (l₂ := [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1438)) (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (count1430 q) 5 4 (meaning1367 q) (meaning1419 q) (meaning1438 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1419 = false ∨ valuation q 1438 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1439 = true := by
  have hs : count1430 q = (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) + (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (l₂ := [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1439)) (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (count1430 q) 5 5 (meaning1367 q) (meaning1420 q) (meaning1439 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1420 = false ∨ valuation q 1439 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1439 = true := by
  have hs : count1430 q = (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) + (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (l₂ := [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1368)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1439)) (countLit q [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]) (countLit q [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]) (count1430 q) 6 4 (meaning1368 q) (meaning1419 q) (meaning1439 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1419 = false ∨ valuation q 1439 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1445)) (countLit q [-59]) (countLit q [-61]) (count1445 q) 1 (meaningNeg59 q) (meaning1445 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1445 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-57]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -61])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1447)) (countLit q [-57]) (countLit q [-59, -61]) (count1447 q) 1 (meaningNeg57 q) (meaning1447 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1447 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1445 = false ∨ valuationOf q 1448 = true := by
  have hs : count1447 q = (countLit q [-57]) + (countLit q [-59, -61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -61])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1448)) (countLit q [-57]) (countLit q [-59, -61]) (count1447 q) 1 1 (meaningNeg57 q) (meaning1445 q) (meaning1448 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1445 = false ∨ valuation q 1448 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (1450)) (countLit q [-62]) (countLit q [-64]) (count1450 q) 1 (meaningNeg64 q) (meaning1450 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1450 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1452)) (countLit q [-66]) (countLit q [-67]) (count1452 q) 1 (meaningNeg67 q) (meaning1452 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1452 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1452)) (countLit q [-66]) (countLit q [-67]) (count1452 q) 1 (meaningNeg66 q) (meaning1452 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1452 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1453)) (countLit q [-66]) (countLit q [-67]) (count1452 q) 1 1 (meaningNeg66 q) (meaningNeg67 q) (meaning1453 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 67 = true ∨ valuation q 1453 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-62, -64]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-62, -64]) (l₂ := [-66, -67])
  have hm := merge_right (literal (valuationOf q) (1452)) (literal (valuationOf q) (1454)) (countLit q [-62, -64]) (countLit q [-66, -67]) (count1454 q) 1 (meaning1452 q) (meaning1454 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1454 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-62, -64]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-62, -64]) (l₂ := [-66, -67])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1455)) (countLit q [-62, -64]) (countLit q [-66, -67]) (count1454 q) 2 (meaning1453 q) (meaning1455 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1455 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-62, -64]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-62, -64]) (l₂ := [-66, -67])
  have hm := merge_left (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-62, -64]) (countLit q [-66, -67]) (count1454 q) 1 (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1454 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-62, -64]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-62, -64]) (l₂ := [-66, -67])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1455)) (countLit q [-62, -64]) (countLit q [-66, -67]) (count1454 q) 1 1 (meaning1450 q) (meaning1452 q) (meaning1455 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1452 = false ∨ valuation q 1455 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1458 = true := by
  have hs : count1458 q = (countLit q [-57, -59, -61]) + (countLit q [-62, -64, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61]) (l₂ := [-62, -64, -66, -67])
  have hm := merge_right (literal (valuationOf q) (1454)) (literal (valuationOf q) (1458)) (countLit q [-57, -59, -61]) (countLit q [-62, -64, -66, -67]) (count1458 q) 1 (meaning1454 q) (meaning1458 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1458 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1459 = true := by
  have hs : count1458 q = (countLit q [-57, -59, -61]) + (countLit q [-62, -64, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61]) (l₂ := [-62, -64, -66, -67])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1459)) (countLit q [-57, -59, -61]) (countLit q [-62, -64, -66, -67]) (count1458 q) 2 (meaning1455 q) (meaning1459 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1459 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1458 = true := by
  have hs : count1458 q = (countLit q [-57, -59, -61]) + (countLit q [-62, -64, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61]) (l₂ := [-62, -64, -66, -67])
  have hm := merge_left (literal (valuationOf q) (1447)) (literal (valuationOf q) (1458)) (countLit q [-57, -59, -61]) (countLit q [-62, -64, -66, -67]) (count1458 q) 1 (meaning1447 q) (meaning1458 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1458 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1459 = true := by
  have hs : count1458 q = (countLit q [-57, -59, -61]) + (countLit q [-62, -64, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61]) (l₂ := [-62, -64, -66, -67])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1459)) (countLit q [-57, -59, -61]) (countLit q [-62, -64, -66, -67]) (count1458 q) 1 1 (meaning1447 q) (meaning1454 q) (meaning1459 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1454 = false ∨ valuation q 1459 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1460 = true := by
  have hs : count1458 q = (countLit q [-57, -59, -61]) + (countLit q [-62, -64, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61]) (l₂ := [-62, -64, -66, -67])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1460)) (countLit q [-57, -59, -61]) (countLit q [-62, -64, -66, -67]) (count1458 q) 1 2 (meaning1447 q) (meaning1455 q) (meaning1460 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1455 = false ∨ valuation q 1460 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1459 = true := by
  have hs : count1458 q = (countLit q [-57, -59, -61]) + (countLit q [-62, -64, -66, -67]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61]) (l₂ := [-62, -64, -66, -67])
  have hm := merge_left (literal (valuationOf q) (1448)) (literal (valuationOf q) (1459)) (countLit q [-57, -59, -61]) (countLit q [-62, -64, -66, -67]) (count1458 q) 2 (meaning1448 q) (meaning1459 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1459 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1465)) (countLit q [-71]) (countLit q [-74]) (count1465 q) 1 (meaningNeg74 q) (meaning1465 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1465 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1465)) (countLit q [-71]) (countLit q [-74]) (count1465 q) 1 (meaningNeg71 q) (meaning1465 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1465 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-69]) + (countLit q [-71, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -74])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1467)) (countLit q [-69]) (countLit q [-71, -74]) (count1467 q) 1 (meaning1465 q) (meaning1467 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1467 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-69]) + (countLit q [-71, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -74])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1467)) (countLit q [-69]) (countLit q [-71, -74]) (count1467 q) 1 (meaningNeg69 q) (meaning1467 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1467 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-69]) + (countLit q [-71, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71, -74])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1468)) (countLit q [-69]) (countLit q [-71, -74]) (count1467 q) 1 1 (meaningNeg69 q) (meaning1465 q) (meaning1468 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1465 = false ∨ valuation q 1468 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1470)) (countLit q [-75]) (countLit q [-77]) (count1470 q) 1 (meaningNeg77 q) (meaning1470 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1470 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1470)) (countLit q [-75]) (countLit q [-77]) (count1470 q) 1 (meaningNeg75 q) (meaning1470 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1470 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1471)) (countLit q [-75]) (countLit q [-77]) (count1470 q) 1 1 (meaningNeg75 q) (meaningNeg77 q) (meaning1471 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 1471 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E148.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112148
